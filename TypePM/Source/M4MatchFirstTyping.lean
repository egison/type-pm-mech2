import TypePM.Source.M4Elaboration

/-!
# M4 single-result, source-ordered match typing

Paper 1 uses a single-result `match` in the whole-value multiset clause.
Unlike `matchAll`, this form returns one expression result directly rather
than wrapping results in a list.  The target and matcher are elaborated once;
ordinary arms are checked from left to right against the type of a separate,
mandatory fallback expression.  The fallback is typed in the original context
and is therefore independent of bindings introduced by any ordinary arm.

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

/-- Constraints contributed by the source-ordered ordinary arm list and the
mandatory fallback expression, typed in the original context without
arm-local bindings. -/
structure GeneratedArms where
  target : Ty
  hard : List Equation
  pending : List CheckObligation
deriving Repr

/-- Constraints contributed by ordinary arms. -/
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

/-- The fallback fixes the result type; every ordinary arm is checked against
that type.  The public source rule requires at least one ordinary arm, while
the generated tail itself still has an empty recursive endpoint. -/
def GeneratedArms.fromFallback
    (fallback : Generated) (arms : GeneratedTail) : GeneratedArms :=
  { target := fallback.target
    hard := fallback.hard ++ arms.hard
    pending := fallback.pending ++ arms.pending }

/-- Add the once-only target and matcher blocks around the arms. -/
def Generated.fromMatchFirst
    (target matcher : Generated) (arms : GeneratedArms) : Generated :=
  { target := arms.target
    hard := target.hard ++ matcher.hard ++ arms.hard
    pending := target.pending ++ matcher.pending ++ arms.pending }

/-- Fuel-structural elaboration of every ordinary arm, preserving source
order.  One unit is consumed for each list cell. -/
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

/-- Elaborate the mandatory fallback and then all ordinary arms.  The
fallback's type is the expected result type for every arm body. -/
def elaborateArmsUsing
    (elaborateExpression : ExpressionElaborator)
    (signature : FrozenSignature) (context : Context)
    (targetType matcherType : Ty) (fallback : Expr)
    (arms : List MatchFirstArm) (supply : Supply) :
    Option (GeneratedArms × Supply) :=
  match arms with
  | [] => none
  | first :: rest => do
      let (generatedFallback, afterFallback) ←
        elaborateExpression context fallback supply
      let (generatedArms, next) ←
        elaborateTailUsing elaborateExpression signature context targetType
          matcherType generatedFallback.target (first :: rest) afterFallback
      pure (GeneratedArms.fromFallback generatedFallback generatedArms, next)

/-- Executable rule for a single-result match.  Target and matcher callbacks
are invoked exactly once before arm elaboration starts. -/
def elaborateUsing
    (elaborateExpression : ExpressionElaborator)
    (signature : FrozenSignature) (context : Context)
    (target matcher : Expr) (arms : List MatchFirstArm) (fallback : Expr)
    (supply : Supply) : Option (Generated × Supply) := do
  let (generatedTarget, afterTarget) ←
    elaborateExpression context target supply
  let (generatedMatcher, afterMatcher) ←
    elaborateExpression context matcher afterTarget
  let (generatedArms, next) ←
    elaborateArmsUsing elaborateExpression signature context
      generatedTarget.target generatedMatcher.target fallback arms afterMatcher
  pure
    (Generated.fromMatchFirst generatedTarget generatedMatcher generatedArms,
      next)

/-- M3-specialized root wrapper. -/
def elaborate
    (signature : FrozenSignature) (context : Context)
    (target matcher : Expr) (arms : List MatchFirstArm) (fallback : Expr)
    (supply : Supply) : Option (Generated × Supply) :=
  elaborateUsing (TypePM.Source.elaborate signature.base) signature context
    target matcher arms fallback supply

/-- Close and solve one M3-subexpression single-result match. -/
def infer
    (signature : FrozenSignature) (context : Context)
    (target matcher : Expr) (arms : List MatchFirstArm) (fallback : Expr) : Option Ty := do
  let (generated, _) ←
    elaborate signature context target matcher arms fallback context.initialSupply
  let closed ← inferGeneratedUsing unify generated
  pure closed.target

/-- Relational mirror of ordinary-arm elaboration. -/
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

/-- Relational mirror of fallback and ordinary-arm elaboration. -/
inductive ArmsElaborateUsing
    (ExpressionElaborates :
      Context → Expr → Supply → Generated → Supply → Prop)
    (signature : FrozenSignature) (context : Context)
    (targetType matcherType : Ty) :
    Expr → List MatchFirstArm → Supply → GeneratedArms → Supply → Prop where
  | fromFallback {fallback first rest supply generatedFallback afterFallback
      generatedArms next}
      (fallbackElaboration :
        ExpressionElaborates context fallback supply generatedFallback afterFallback)
      (armsElaboration :
        TailElaboratesUsing ExpressionElaborates signature context targetType
          matcherType generatedFallback.target (first :: rest) afterFallback
          generatedArms next) :
      ArmsElaborateUsing ExpressionElaborates signature context targetType
        matcherType fallback (first :: rest) supply
        (GeneratedArms.fromFallback generatedFallback generatedArms) next

/-- Independent relational single-result match rule. -/
inductive ElaboratesUsing
    (ExpressionElaborates :
      Context → Expr → Supply → Generated → Supply → Prop)
    (signature : FrozenSignature) (context : Context) :
    Expr → Supply → Generated → Supply → Prop where
  | matchFirst {target matcher arms fallback supply generatedTarget afterTarget
      generatedMatcher afterMatcher generatedArms next}
      (targetElaboration :
        ExpressionElaborates context target supply generatedTarget afterTarget)
      (matcherElaboration :
        ExpressionElaborates context matcher afterTarget generatedMatcher
          afterMatcher)
      (armsElaboration :
        ArmsElaborateUsing ExpressionElaborates signature context
          generatedTarget.target generatedMatcher.target fallback arms afterMatcher
          generatedArms next) :
      ElaboratesUsing ExpressionElaborates signature context
        (.matchFirst target matcher arms fallback) supply
        (Generated.fromMatchFirst generatedTarget generatedMatcher generatedArms)
        next

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
    {context : Context} {targetType matcherType : Ty} {fallback : Expr}
    {arms : List MatchFirstArm} {supply next : Supply}
    {generated : GeneratedArms}
    (success : elaborateArmsUsing elaborateExpression signature context
      targetType matcherType fallback arms supply = some (generated, next)) :
    ArmsElaborateUsing ExpressionElaborates signature context targetType
      matcherType fallback arms supply generated next := by
  cases arms with
  | nil => simp [elaborateArmsUsing] at success
  | cons first rest =>
      cases fallbackResult : elaborateExpression context fallback supply with
      | none => simp [elaborateArmsUsing, fallbackResult] at success
      | some fallbackOutput =>
          rcases fallbackOutput with ⟨generatedFallback, afterFallback⟩
          cases armsResult : elaborateTailUsing elaborateExpression signature
              context targetType matcherType generatedFallback.target
              (first :: rest) afterFallback with
          | none =>
              simp [elaborateArmsUsing, fallbackResult, armsResult] at success
          | some armsOutput =>
              rcases armsOutput with ⟨generatedArms, afterArms⟩
              simp [elaborateArmsUsing, fallbackResult, armsResult] at success
              rcases success with ⟨rfl, rfl⟩
              exact .fromFallback (expressionSound fallbackResult)
                (elaborateTailUsing_sound expressionSound wellFormed armsResult)

theorem elaborateUsing_sound
    {elaborateExpression : ExpressionElaborator}
    {ExpressionElaborates :
      Context → Expr → Supply → Generated → Supply → Prop}
    (expressionSound : ∀ {context expression supply generated next},
      elaborateExpression context expression supply = some (generated, next) →
        ExpressionElaborates context expression supply generated next)
    {signature : FrozenSignature} (wellFormed : signature.WellFormed)
    {context : Context} {target matcher fallback : Expr} {arms : List MatchFirstArm}
    {supply next : Supply} {generated : Generated}
    (success : elaborateUsing elaborateExpression signature context target
      matcher arms fallback supply = some (generated, next)) :
    ElaboratesUsing ExpressionElaborates signature context
      (.matchFirst target matcher arms fallback) supply generated next := by
  cases targetResult : elaborateExpression context target supply with
  | none => simp [elaborateUsing, targetResult] at success
  | some targetOutput =>
      rcases targetOutput with ⟨generatedTarget, afterTarget⟩
      cases matcherResult : elaborateExpression context matcher afterTarget with
      | none => simp [elaborateUsing, targetResult, matcherResult] at success
      | some matcherOutput =>
          rcases matcherOutput with ⟨generatedMatcher, afterMatcher⟩
          cases armsResult : elaborateArmsUsing elaborateExpression signature
              context generatedTarget.target generatedMatcher.target fallback arms
              afterMatcher with
          | none =>
              simp [elaborateUsing, targetResult, matcherResult, armsResult] at success
          | some armsOutput =>
              rcases armsOutput with ⟨generatedArms, afterArms⟩
              simp [elaborateUsing, targetResult, matcherResult, armsResult] at success
              rcases success with ⟨rfl, rfl⟩
              exact .matchFirst (expressionSound targetResult)
                (expressionSound matcherResult)
                (elaborateArmsUsing_sound expressionSound wellFormed armsResult)

theorem elaborate_sound
    {signature : FrozenSignature} (wellFormed : signature.WellFormed)
    {context : Context} {target matcher fallback : Expr} {arms : List MatchFirstArm}
    {supply next : Supply} {generated : Generated}
    (success : elaborate signature context target matcher arms fallback supply =
      some (generated, next)) :
    Elaborates signature context (.matchFirst target matcher arms fallback) supply
      generated next := by
  apply elaborateUsing_sound
    (elaborateExpression := TypePM.Source.elaborate signature.base)
    (ExpressionElaborates := TypePM.Source.Elaborates signature.base)
    (fun expressionSuccess =>
      TypePM.Source.elaborate_sound wellFormed.baseWellFormed expressionSuccess)
    wellFormed
  simpa [elaborate] using success

end MatchFirstTyping

end TypePM.Source
