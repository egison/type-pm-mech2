import TypePM.Source.M4Elaboration

/-!
# M4 single-result, source-ordered match typing

Paper 1 uses a single-result `match` in the whole-value multiset clause and
inside tuple-pattern lambdas.  Unlike `matchAll`, this form returns an arm
body directly rather than wrapping every result in a list.  The target and
matcher are elaborated once; arms are then checked from left to right.

The executable rules are parameterized by the expression elaborator used for
subexpressions.  The M3-specialized public wrapper is useful immediately, and
the same callback boundary lets the final mutually recursive M4 dispatcher
type nested matcher literals, `fixE`, and matches without duplicating this
rule.
-/

namespace TypePM.Source

namespace MatchFirstTyping

abbrev ExpressionElaborator :=
  Context → Expr → Supply → Option (Generated × Supply)

mutual

/-- Conservative structural test for a pattern that matches every value of
its target type.  Constructor, value, embedded, and named patterns may fail;
tuples are irrefutable exactly when all of their fields are. -/
def structurallyIrrefutable : Pattern → Bool
  | .var | .wild => true
  | .tuple fields => allStructurallyIrrefutable fields
  | .and left right =>
      structurallyIrrefutable left && structurallyIrrefutable right
  | .value _ | .ctor _ _ | .embed _ | .app _ _ => false

def allStructurallyIrrefutable : List Pattern → Bool
  | [] => true
  | pattern :: patterns =>
      structurallyIrrefutable pattern &&
        allStructurallyIrrefutable patterns

end


/-- The source-ordered list is exhaustive when its final arm is
structurally irrefutable. -/
def armsExhaustive : List MatchFirstArm → Bool
  | [] => false
  | [.mk pattern _] => structurallyIrrefutable pattern
  | _ :: arms => armsExhaustive arms

/-- Constraints contributed by the nonempty, source-ordered arm list. -/
structure GeneratedArms where
  target : Ty
  hard : List Equation
  pending : List CheckObligation
deriving Repr

/-- Constraints contributed by arms after the first one. -/
structure GeneratedTail where
  hard : List Equation
  pending : List CheckObligation
deriving Repr

/-- Constraints for one arm whose result must equal `expectedResult`. -/
def GeneratedTail.fromArm
    (targetType matcherType expectedResult : Ty)
    (pattern : GeneratedPattern) (body : Generated) : GeneratedTail :=
  { hard := [.ty pattern.dual.target targetType] ++ pattern.hard ++
      body.hard ++ [.ty body.target expectedResult]
    pending := pattern.pending ++
      [⟨matcherType, .slot pattern.dual.capability targetType⟩] ++
        body.pending }

/-- First-arm constraints.  Its body type is the direct result type; no list
constructor and no fresh result alias are introduced. -/
def GeneratedArms.fromFirst
    (targetType matcherType : Ty)
    (pattern : GeneratedPattern) (body : Generated)
    (tail : GeneratedTail) : GeneratedArms :=
  { target := body.target
    hard := [.ty pattern.dual.target targetType] ++ pattern.hard ++
      body.hard ++ tail.hard
    pending := pattern.pending ++
      [⟨matcherType, .slot pattern.dual.capability targetType⟩] ++
        body.pending ++ tail.pending }

/-- Add the once-only target and matcher blocks around the arms. -/
def Generated.fromMatchFirst
    (target matcher : Generated) (arms : GeneratedArms) : Generated :=
  { target := arms.target
    hard := target.hard ++ matcher.hard ++ arms.hard
    pending := target.pending ++ matcher.pending ++ arms.pending }

/-- Fuel-structural elaboration of every arm after the first, preserving
source order.  One unit is consumed for each tail cell. -/
def elaborateTailUsingFuel
    (elaborateExpression : ExpressionElaborator)
    (signature : FrozenSignature) (context : Context)
    (targetType matcherType expectedResult : Ty) :
    Nat → List MatchFirstArm → Supply → Option (GeneratedTail × Supply)
  | 0, _, _ => none
  | _ + 1, [], supply => some (⟨[], []⟩, supply)
  | fuel + 1, .mk pattern body :: arms, supply => do
      let (generatedPattern, afterPattern) ←
        elaboratePatternUsing elaborateExpression signature context [] pattern [] supply
      let (generatedBody, afterBody) ←
        elaborateExpression
          (Pattern.extendContext generatedPattern.bindings context)
          body afterPattern
      let (generatedTail, next) ←
        elaborateTailUsingFuel elaborateExpression signature context targetType
          matcherType expectedResult fuel arms afterBody
      let current := GeneratedTail.fromArm targetType matcherType
        expectedResult generatedPattern generatedBody
      pure
        (⟨current.hard ++ generatedTail.hard,
          current.pending ++ generatedTail.pending⟩,
          next)

/-- Public tail elaborator.  Its size-derived fuel is strictly larger than
the number of recursive tail calls. -/
def elaborateTailUsing
    (elaborateExpression : ExpressionElaborator)
    (signature : FrozenSignature) (context : Context)
    (targetType matcherType expectedResult : Ty)
    (arms : List MatchFirstArm) (supply : Supply) :
    Option (GeneratedTail × Supply) :=
  elaborateTailUsingFuel elaborateExpression signature context targetType
    matcherType expectedResult (MatchFirstArm.listComplexity arms * 2 + 1)
    arms supply

/-- Elaborate a nonempty arm list.  The first body fixes the direct result
type against which later bodies are equated. -/
def elaborateArmsUsing
    (elaborateExpression : ExpressionElaborator)
    (signature : FrozenSignature) (context : Context)
    (targetType matcherType : Ty) :
    List MatchFirstArm → Supply → Option (GeneratedArms × Supply)
  | [], _ => none
  | .mk pattern body :: arms, supply => do
      let (generatedPattern, afterPattern) ←
        elaboratePatternUsing elaborateExpression signature context [] pattern [] supply
      let (generatedBody, afterBody) ←
        elaborateExpression
          (Pattern.extendContext generatedPattern.bindings context)
          body afterPattern
      let (generatedTail, next) ←
        elaborateTailUsing elaborateExpression signature context targetType
          matcherType generatedBody.target arms afterBody
      pure
        (GeneratedArms.fromFirst targetType matcherType generatedPattern
          generatedBody generatedTail,
          next)

/-- Executable rule for a single-result match.  Target and matcher callbacks
are invoked exactly once before arm elaboration starts. -/
def elaborateUsing
    (elaborateExpression : ExpressionElaborator)
    (signature : FrozenSignature) (context : Context)
    (target matcher : Expr) (arms : List MatchFirstArm)
    (supply : Supply) : Option (Generated × Supply) := do
  if !armsExhaustive arms then none else pure ()
  let (generatedTarget, afterTarget) ←
    elaborateExpression context target supply
  let (generatedMatcher, afterMatcher) ←
    elaborateExpression context matcher afterTarget
  let (generatedArms, next) ←
    elaborateArmsUsing elaborateExpression signature context
      generatedTarget.target generatedMatcher.target arms afterMatcher
  pure
    (Generated.fromMatchFirst generatedTarget generatedMatcher generatedArms,
      next)

/-- M3-specialized root wrapper. -/
def elaborate
    (signature : FrozenSignature) (context : Context)
    (target matcher : Expr) (arms : List MatchFirstArm)
    (supply : Supply) : Option (Generated × Supply) :=
  elaborateUsing (TypePM.Source.elaborate signature.base) signature context
    target matcher arms supply

/-- Close and solve one M3-subexpression single-result match. -/
def infer
    (signature : FrozenSignature) (context : Context)
    (target matcher : Expr) (arms : List MatchFirstArm) : Option Ty := do
  let (generated, _) ←
    elaborate signature context target matcher arms context.initialSupply
  let closed ← inferGeneratedUsing unify generated
  pure closed.target

/-- Relational mirror of later-arm elaboration. -/
inductive TailElaboratesUsing
    (ExpressionElaborates :
      Context → Expr → Supply → Generated → Supply → Prop)
    (signature : FrozenSignature) (context : Context)
    (targetType matcherType expectedResult : Ty) :
    List MatchFirstArm → Supply → GeneratedTail → Supply → Prop where
  | nil {supply} :
      TailElaboratesUsing ExpressionElaborates signature context targetType
        matcherType expectedResult [] supply ⟨[], []⟩ supply
  | cons {pattern body arms supply generatedPattern afterPattern
      generatedBody afterBody generatedTail next}
      (patternElaboration :
        PatternElaboratesUsing ExpressionElaborates signature context [] pattern [] supply
          generatedPattern afterPattern)
      (bodyElaboration :
        ExpressionElaborates
          (Pattern.extendContext generatedPattern.bindings context)
          body afterPattern generatedBody afterBody)
      (tailElaboration :
        TailElaboratesUsing ExpressionElaborates signature context targetType
          matcherType expectedResult arms afterBody generatedTail next) :
      TailElaboratesUsing ExpressionElaborates signature context targetType
        matcherType expectedResult (.mk pattern body :: arms) supply
        ⟨(GeneratedTail.fromArm targetType matcherType expectedResult
              generatedPattern generatedBody).hard ++ generatedTail.hard,
          (GeneratedTail.fromArm targetType matcherType expectedResult
              generatedPattern generatedBody).pending ++ generatedTail.pending⟩
        next

/-- Relational mirror of nonempty arm elaboration. -/
inductive ArmsElaborateUsing
    (ExpressionElaborates :
      Context → Expr → Supply → Generated → Supply → Prop)
    (signature : FrozenSignature) (context : Context)
    (targetType matcherType : Ty) :
    List MatchFirstArm → Supply → GeneratedArms → Supply → Prop where
  | cons {pattern body arms supply generatedPattern afterPattern
      generatedBody afterBody generatedTail next}
      (patternElaboration :
        PatternElaboratesUsing ExpressionElaborates signature context [] pattern [] supply
          generatedPattern afterPattern)
      (bodyElaboration :
        ExpressionElaborates
          (Pattern.extendContext generatedPattern.bindings context)
          body afterPattern generatedBody afterBody)
      (tailElaboration :
        TailElaboratesUsing ExpressionElaborates signature context targetType
          matcherType generatedBody.target arms afterBody generatedTail next) :
      ArmsElaborateUsing ExpressionElaborates signature context targetType
        matcherType (.mk pattern body :: arms) supply
        (GeneratedArms.fromFirst targetType matcherType generatedPattern
          generatedBody generatedTail)
        next

/-- Independent relational single-result match rule. -/
inductive ElaboratesUsing
    (ExpressionElaborates :
      Context → Expr → Supply → Generated → Supply → Prop)
    (signature : FrozenSignature) (context : Context) :
    Expr → Supply → Generated → Supply → Prop where
  | matchFirst {target matcher arms supply generatedTarget afterTarget
      generatedMatcher afterMatcher generatedArms next}
      (exhaustive : armsExhaustive arms = true)
      (targetElaboration :
        ExpressionElaborates context target supply generatedTarget afterTarget)
      (matcherElaboration :
        ExpressionElaborates context matcher afterTarget generatedMatcher
          afterMatcher)
      (armsElaboration :
        ArmsElaborateUsing ExpressionElaborates signature context
          generatedTarget.target generatedMatcher.target arms afterMatcher
          generatedArms next) :
      ElaboratesUsing ExpressionElaborates signature context
        (.matchFirst target matcher arms) supply
        (Generated.fromMatchFirst generatedTarget generatedMatcher generatedArms)
        next

namespace ElaboratesUsing

/-- Every relational derivation records the conservative coverage gate used
by the executable rule. -/
theorem exhaustive
    {ExpressionElaborates :
      Context → Expr → Supply → Generated → Supply → Prop}
    {signature : FrozenSignature} {context : Context}
    {target matcher : Expr} {arms : List MatchFirstArm}
    {supply next : Supply} {generated : Generated}
    (elaboration :
      ElaboratesUsing ExpressionElaborates signature context
        (.matchFirst target matcher arms) supply generated next) :
    armsExhaustive arms = true := by
  cases elaboration
  assumption

end ElaboratesUsing

abbrev Elaborates
    (signature : FrozenSignature) (context : Context) :=
  ElaboratesUsing (TypePM.Source.Elaborates signature.base) signature context

theorem elaborateTailUsingFuel_sound
    {elaborateExpression : ExpressionElaborator}
    {ExpressionElaborates :
      Context → Expr → Supply → Generated → Supply → Prop}
    (expressionSound : ∀ {context expression supply generated next},
      elaborateExpression context expression supply = some (generated, next) →
        ExpressionElaborates context expression supply generated next)
    {signature : FrozenSignature} (wellFormed : signature.WellFormed)
    {context : Context} {targetType matcherType expectedResult : Ty}
    {fuel : Nat}
    {arms : List MatchFirstArm} {supply next : Supply}
    {generated : GeneratedTail}
    (success : elaborateTailUsingFuel elaborateExpression signature context
      targetType matcherType expectedResult fuel arms supply = some (generated, next)) :
    TailElaboratesUsing ExpressionElaborates signature context targetType
      matcherType expectedResult arms supply generated next := by
  induction fuel generalizing arms supply generated next with
  | zero => simp [elaborateTailUsingFuel] at success
  | succ fuel induction =>
      cases arms with
      | nil =>
          simp [elaborateTailUsingFuel] at success
          rcases success with ⟨rfl, rfl⟩
          exact .nil
      | cons arm arms =>
          cases arm with
          | mk pattern body =>
              cases patternResult : elaboratePatternUsing elaborateExpression signature context [] pattern []
                  supply with
              | none => simp [elaborateTailUsingFuel, patternResult] at success
              | some patternOutput =>
                  rcases patternOutput with ⟨generatedPattern, afterPattern⟩
                  cases bodyResult : elaborateExpression
                      (Pattern.extendContext generatedPattern.bindings context)
                      body afterPattern with
                  | none =>
                      simp [elaborateTailUsingFuel, patternResult, bodyResult] at success
                  | some bodyOutput =>
                      rcases bodyOutput with ⟨generatedBody, afterBody⟩
                      cases tailResult : elaborateTailUsingFuel elaborateExpression
                          signature context targetType matcherType expectedResult
                          fuel arms afterBody with
                      | none =>
                          simp [elaborateTailUsingFuel, patternResult, bodyResult,
                            tailResult] at success
                      | some tailOutput =>
                          rcases tailOutput with ⟨generatedTail, afterTail⟩
                          simp [elaborateTailUsingFuel, patternResult, bodyResult,
                            tailResult] at success
                          rcases success with ⟨rfl, rfl⟩
                          exact .cons
                            (elaboratePatternUsing_sound expressionSound wellFormed
                              patternResult)
                            (expressionSound bodyResult)
                            (induction tailResult)

theorem elaborateTailUsing_sound
    {elaborateExpression : ExpressionElaborator}
    {ExpressionElaborates :
      Context → Expr → Supply → Generated → Supply → Prop}
    (expressionSound : ∀ {context expression supply generated next},
      elaborateExpression context expression supply = some (generated, next) →
        ExpressionElaborates context expression supply generated next)
    {signature : FrozenSignature} (wellFormed : signature.WellFormed)
    {context : Context} {targetType matcherType expectedResult : Ty}
    {arms : List MatchFirstArm} {supply next : Supply}
    {generated : GeneratedTail}
    (success : elaborateTailUsing elaborateExpression signature context
      targetType matcherType expectedResult arms supply = some (generated, next)) :
    TailElaboratesUsing ExpressionElaborates signature context targetType
      matcherType expectedResult arms supply generated next :=
  elaborateTailUsingFuel_sound expressionSound wellFormed success

theorem elaborateArmsUsing_sound
    {elaborateExpression : ExpressionElaborator}
    {ExpressionElaborates :
      Context → Expr → Supply → Generated → Supply → Prop}
    (expressionSound : ∀ {context expression supply generated next},
      elaborateExpression context expression supply = some (generated, next) →
        ExpressionElaborates context expression supply generated next)
    {signature : FrozenSignature} (wellFormed : signature.WellFormed)
    {context : Context} {targetType matcherType : Ty}
    {arms : List MatchFirstArm} {supply next : Supply}
    {generated : GeneratedArms}
    (success : elaborateArmsUsing elaborateExpression signature context
      targetType matcherType arms supply = some (generated, next)) :
    ArmsElaborateUsing ExpressionElaborates signature context targetType
      matcherType arms supply generated next := by
  cases arms with
  | nil => simp [elaborateArmsUsing] at success
  | cons arm arms =>
      cases arm with
      | mk pattern body =>
          cases patternResult : elaboratePatternUsing elaborateExpression signature context [] pattern []
              supply with
          | none => simp [elaborateArmsUsing, patternResult] at success
          | some patternOutput =>
              rcases patternOutput with ⟨generatedPattern, afterPattern⟩
              cases bodyResult : elaborateExpression
                  (Pattern.extendContext generatedPattern.bindings context)
                  body afterPattern with
              | none =>
                  simp [elaborateArmsUsing, patternResult, bodyResult] at success
              | some bodyOutput =>
                  rcases bodyOutput with ⟨generatedBody, afterBody⟩
                  cases tailResult : elaborateTailUsing elaborateExpression
                      signature context targetType matcherType
                      generatedBody.target arms afterBody with
                  | none =>
                      simp [elaborateArmsUsing, patternResult, bodyResult,
                        tailResult] at success
                  | some tailOutput =>
                      rcases tailOutput with ⟨generatedTail, afterTail⟩
                      simp [elaborateArmsUsing, patternResult, bodyResult,
                        tailResult] at success
                      rcases success with ⟨rfl, rfl⟩
                      exact .cons
                        (elaboratePatternUsing_sound expressionSound wellFormed patternResult)
                        (expressionSound bodyResult)
                        (elaborateTailUsing_sound expressionSound wellFormed
                          tailResult)

theorem elaborateUsing_sound
    {elaborateExpression : ExpressionElaborator}
    {ExpressionElaborates :
      Context → Expr → Supply → Generated → Supply → Prop}
    (expressionSound : ∀ {context expression supply generated next},
      elaborateExpression context expression supply = some (generated, next) →
        ExpressionElaborates context expression supply generated next)
    {signature : FrozenSignature} (wellFormed : signature.WellFormed)
    {context : Context} {target matcher : Expr} {arms : List MatchFirstArm}
    {supply next : Supply} {generated : Generated}
    (success : elaborateUsing elaborateExpression signature context target
      matcher arms supply = some (generated, next)) :
    ElaboratesUsing ExpressionElaborates signature context
      (.matchFirst target matcher arms) supply generated next := by
  by_cases exhaustive : armsExhaustive arms = true
  · cases targetResult : elaborateExpression context target supply with
    | none => simp [elaborateUsing, exhaustive, targetResult] at success
    | some targetOutput =>
        rcases targetOutput with ⟨generatedTarget, afterTarget⟩
        cases matcherResult : elaborateExpression context matcher afterTarget with
        | none =>
            simp [elaborateUsing, exhaustive, targetResult, matcherResult]
              at success
        | some matcherOutput =>
            rcases matcherOutput with ⟨generatedMatcher, afterMatcher⟩
            cases armsResult : elaborateArmsUsing elaborateExpression signature
                context generatedTarget.target generatedMatcher.target arms
                afterMatcher with
            | none =>
                simp [elaborateUsing, exhaustive, targetResult, matcherResult,
                  armsResult] at success
            | some armsOutput =>
                rcases armsOutput with ⟨generatedArms, afterArms⟩
                simp [elaborateUsing, exhaustive, targetResult, matcherResult,
                  armsResult] at success
                rcases success with ⟨rfl, rfl⟩
                exact .matchFirst exhaustive
                  (expressionSound targetResult)
                  (expressionSound matcherResult)
                  (elaborateArmsUsing_sound expressionSound wellFormed armsResult)
  · simp [elaborateUsing, exhaustive] at success

theorem elaborate_sound
    {signature : FrozenSignature} (wellFormed : signature.WellFormed)
    {context : Context} {target matcher : Expr} {arms : List MatchFirstArm}
    {supply next : Supply} {generated : Generated}
    (success : elaborate signature context target matcher arms supply =
      some (generated, next)) :
    Elaborates signature context (.matchFirst target matcher arms) supply
      generated next := by
  apply elaborateUsing_sound
    (elaborateExpression := TypePM.Source.elaborate signature.base)
    (ExpressionElaborates := TypePM.Source.Elaborates signature.base)
    (fun expressionSuccess =>
      TypePM.Source.elaborate_sound wellFormed.baseWellFormed expressionSuccess)
    wellFormed
  simpa [elaborate] using success

end MatchFirstTyping

namespace Expr

/-- Exact source desugaring of a unary pattern lambda.  The anonymous
argument remains behind all source-order pattern binders in the arm body. -/
def patternLambda (pattern : Pattern) (matcher body : Expr) : Expr :=
  .lam (.matchFirst (.var 0) matcher [.mk pattern body])

/-- Paper 1's `\(left,right) -> body` form, using a product of `something`
matchers for the two tuple fields. -/
def tuplePatternLambda (body : Expr) : Expr :=
  patternLambda (.tuple [.var, .var])
    (.tuple [.something, .something]) body

@[simp] theorem tuplePatternLambda_eq (body : Expr) :
    tuplePatternLambda body =
      .lam (.matchFirst (.var 0) (.tuple [.something, .something])
        [.mk (.tuple [.var, .var]) body]) := rfl

end Expr

end TypePM.Source
