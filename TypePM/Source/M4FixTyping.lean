import TypePM.Source.M4Elaboration

/-!
# M4 singleton direct-self recursion

This module adds the static `fixE` checkpoint without pretending that matcher
literal typing is already available.  A fix body is unary and monomorphic:
inside the body, de Bruijn index zero is the argument, index one is the
recursive function, and the outer context follows them.

The direct-self gate is defined over the complete final mutual source syntax.
The recursive function may occur only at the head of an application spine.
It may not be returned, passed as an argument, stored by `letE`, or captured
by a nested `fixE`.  All source binders shift the tracked de Bruijn index.

The executable and relational elaborators in this module deliberately use the
M3 elaborator for the fix body.  Thus ordinary recursive functions are typed,
while a matcher literal at the root of a recursive body remains rejected until
the independent matcher-literal typing checkpoint is connected.
-/

namespace TypePM.Source

namespace DirectSelf

mutual

/-- Number of expression binders introduced by a user pattern. -/
def patternBindingCount : Pattern → Nat
  | .var => 1
  | .wild | .value _ | .embed _ => 0
  | .ctor _ fields | .tuple fields | .app _ fields =>
      patternBindingCountList fields

def patternBindingCountList : List Pattern → Nat
  | [] => 0
  | pattern :: patterns =>
      patternBindingCount pattern + patternBindingCountList patterns

end

mutual

/-- Whether the tracked variable occurs anywhere, including direct-call
position.  This is used to keep an outer recursive function from being
captured by a nested `fixE`. -/
def mentions (tracked : Nat) : Expr → Bool
  | .var index => index == tracked
  | .lit _ | .something => false
  | .lam body => mentions (tracked + 1) body
  | .app function argument => mentions tracked function || mentions tracked argument
  | .tuple items | .ctor _ items | .prim _ items => mentionsList tracked items
  | .letE value body => mentions tracked value || mentions (tracked + 1) body
  | .ifE condition thenBranch elseBranch =>
      mentions tracked condition || mentions tracked thenBranch ||
        mentions tracked elseBranch
  | .fixE body => mentions (tracked + 2) body
  | .matcher clauses => mentionsClauses tracked clauses
  | .matchAll target matcher pattern body =>
      mentions tracked target || mentions tracked matcher ||
        mentionsPattern tracked 0 pattern ||
        mentions (tracked + patternBindingCount pattern) body
  | .matchFirst target matcher arms =>
      mentions tracked target || mentions tracked matcher ||
        mentionsMatchFirstArms tracked arms

def mentionsList (tracked : Nat) : List Expr → Bool
  | [] => false
  | expression :: expressions =>
      mentions tracked expression || mentionsList tracked expressions

/-- The `before` parameter counts binders produced by patterns to the left. -/
def mentionsPattern (tracked before : Nat) : Pattern → Bool
  | .var | .wild | .embed _ => false
  | .value expression => mentions (tracked + before) expression
  | .ctor _ fields | .tuple fields | .app _ fields =>
      mentionsPatterns tracked before fields

def mentionsPatterns (tracked before : Nat) : List Pattern → Bool
  | [] => false
  | pattern :: patterns =>
      mentionsPattern tracked before pattern ||
        mentionsPatterns tracked (before + patternBindingCount pattern) patterns

/-- Clause captures are available to arm bodies after data-pattern binders.
The next-matcher expression is evaluated in the matcher definition context
and therefore introduces no binder shift. -/
def mentionsClause (tracked : Nat) : MatcherClause → Bool
  | .mk header nextMatchers arms =>
      mentions tracked nextMatchers ||
        mentionsArms tracked header.captureCount arms

def mentionsClauses (tracked : Nat) : List MatcherClause → Bool
  | [] => false
  | clause :: clauses =>
      mentionsClause tracked clause || mentionsClauses tracked clauses

def mentionsArm (tracked captures : Nat) : MatcherArm → Bool
  | .mk header body =>
      mentions (tracked + header.bindingCount + captures) body

def mentionsArms (tracked captures : Nat) : List MatcherArm → Bool
  | [] => false
  | arm :: arms =>
      mentionsArm tracked captures arm || mentionsArms tracked captures arms

def mentionsMatchFirstArm (tracked : Nat) : MatchFirstArm → Bool
  | .mk pattern body =>
      mentionsPattern tracked 0 pattern ||
        mentions (tracked + patternBindingCount pattern) body

def mentionsMatchFirstArms (tracked : Nat) : List MatchFirstArm → Bool
  | [] => false
  | arm :: arms =>
      mentionsMatchFirstArm tracked arm || mentionsMatchFirstArms tracked arms

end

mutual

/-- Check an expression in ordinary position.  Applications delegate their
function spine to `checkHead`, the only place where the tracked recursive
variable is accepted. -/
def check (tracked : Nat) : Expr → Bool
  | .var index => index != tracked
  | .lit _ | .something => true
  | .lam body => check (tracked + 1) body
  | .app function argument => checkHead tracked function && check tracked argument
  | .tuple items | .ctor _ items | .prim _ items => checkList tracked items
  | .letE value body => check tracked value && check (tracked + 1) body
  | .ifE condition thenBranch elseBranch =>
      check tracked condition && check tracked thenBranch &&
        check tracked elseBranch
  | .fixE body =>
      !mentions (tracked + 2) body && check 1 body
  | .matcher clauses => checkClauses tracked clauses
  | .matchAll target matcher pattern body =>
      check tracked target && check tracked matcher &&
        checkPattern tracked 0 pattern &&
        check (tracked + patternBindingCount pattern) body
  | .matchFirst target matcher arms =>
      check tracked target && check tracked matcher &&
        checkMatchFirstArms tracked arms
termination_by expression => expression.complexity * 3 + 1
decreasing_by all_goals simp_wf <;> omega

/-- Check the function spine of an application.  A variable at its head is a
direct callee.  Arguments in a curried spine remain ordinary positions. -/
def checkHead (tracked : Nat) : Expr → Bool
  | .var _ => true
  | .app function argument =>
      checkHead tracked function && check tracked argument
  | expression => check tracked expression
termination_by expression => expression.complexity * 3 + 2
decreasing_by all_goals simp_wf <;> omega

def checkList (tracked : Nat) : List Expr → Bool
  | [] => true
  | expression :: expressions =>
      check tracked expression && checkList tracked expressions
termination_by expressions => Expr.listComplexity expressions * 3
decreasing_by all_goals simp_wf <;> omega

/-- Check embedded expressions with the left-to-right pattern binder shift. -/
def checkPattern (tracked before : Nat) : Pattern → Bool
  | .var | .wild | .embed _ => true
  | .value expression => check (tracked + before) expression
  | .ctor _ fields | .tuple fields | .app _ fields =>
      checkPatterns tracked before fields
termination_by pattern => pattern.complexity * 3 + 1
decreasing_by all_goals simp_wf <;> omega

def checkPatterns (tracked before : Nat) : List Pattern → Bool
  | [] => true
  | pattern :: patterns =>
      checkPattern tracked before pattern &&
        checkPatterns tracked (before + patternBindingCount pattern) patterns
termination_by patterns => Pattern.listComplexity patterns * 3
decreasing_by all_goals simp_wf <;> omega

def checkClause (tracked : Nat) : MatcherClause → Bool
  | .mk header nextMatchers arms =>
      check tracked nextMatchers && checkArms tracked header.captureCount arms
termination_by clause => clause.complexity * 3 + 1
decreasing_by all_goals simp_wf <;> omega

def checkClauses (tracked : Nat) : List MatcherClause → Bool
  | [] => true
  | clause :: clauses =>
      checkClause tracked clause && checkClauses tracked clauses
termination_by clauses => MatcherClause.listComplexity clauses * 3
decreasing_by all_goals simp_wf <;> omega

def checkArm (tracked captures : Nat) : MatcherArm → Bool
  | .mk header body =>
      check (tracked + header.bindingCount + captures) body
termination_by arm => arm.complexity * 3 + 1
decreasing_by all_goals simp_wf <;> omega

def checkArms (tracked captures : Nat) : List MatcherArm → Bool
  | [] => true
  | arm :: arms =>
      checkArm tracked captures arm && checkArms tracked captures arms
termination_by arms => MatcherArm.listComplexity arms * 3
decreasing_by all_goals simp_wf <;> omega

def checkMatchFirstArm (tracked : Nat) : MatchFirstArm → Bool
  | .mk pattern body =>
      checkPattern tracked 0 pattern &&
        check (tracked + patternBindingCount pattern) body
termination_by arm => arm.complexity * 3 + 1
decreasing_by all_goals simp_wf <;> omega

def checkMatchFirstArms (tracked : Nat) : List MatchFirstArm → Bool
  | [] => true
  | arm :: arms =>
      checkMatchFirstArm tracked arm && checkMatchFirstArms tracked arms
termination_by arms => MatchFirstArm.listComplexity arms * 3
decreasing_by all_goals simp_wf <;> omega

end

/-- Proof-level direct-self side condition for a fix body. -/
def Holds (body : Expr) : Prop :=
  check 1 body = true

instance (body : Expr) : Decidable (Holds body) :=
  inferInstanceAs (Decidable (check 1 body = true))

@[simp] theorem bare_self_rejected : ¬ Holds (.var 1) := by
  simp [Holds, check]

@[simp] theorem direct_application_accepted (argument : Expr)
    (argumentSafe : check 1 argument = true) :
    Holds (.app (.var 1) argument) := by
  simp [Holds, check, checkHead, argumentSafe]

@[simp] theorem self_as_argument_rejected (function : Expr) :
    ¬ Holds (.app function (.var 1)) := by
  simp [Holds, check]

end DirectSelf

namespace Fix

/-- The monomorphic body context: argument, recursive self, then outer scope. -/
def bodyContext (domain codomain : Ty) (context : Context) : Context :=
  .mono domain :: .mono (.fn domain codomain) :: context

end Fix

/-- Assemble the constraint block produced by a unary monomorphic fix. -/
def Generated.fromFix (domain codomain : Ty) (body : Generated) : Generated :=
  { target := .fn domain codomain
    hard := body.hard ++ [.ty body.target codomain]
    pending := body.pending }

/-- Executable elaboration of one `fixE` node, parameterized by the expression
elaborator used for its body.  This is the composition point for the final M4
dispatcher: matcher-literal typing can supply a mutually recursive callback
without duplicating the fix rule. -/
def elaborateFixUsing
    (elaborateBody : Context → Expr → Supply → Option (Generated × Supply))
    (context : Context) (body : Expr)
    (supply : Supply) : Option (Generated × Supply) := do
  if DirectSelf.check 1 body then
    let domain : Ty := .var ⟨supply.ty⟩
    let codomain : Ty := .var ⟨supply.ty + 1⟩
    let (generatedBody, next) ←
      elaborateBody (Fix.bodyContext domain codomain context) body
        (supply.nextTy 2)
    pure (Generated.fromFix domain codomain generatedBody, next)
  else
    none

/-- M3-specialized executable wrapper.  It types ordinary recursive
functions but intentionally leaves matcher-root recursion for the final M4
dispatcher assembled with `elaborateFixUsing`. -/
def elaborateFix
    (signature : Signature) (context : Context) (body : Expr)
    (supply : Supply) : Option (Generated × Supply) :=
  elaborateFixUsing (elaborate signature) context body supply

/-- Abstract-solver helper for the `fixE` checkpoint. -/
def inferFixUsing
    (solveHard : List Equation → Option Subst)
    (signature : Signature) (context : Context) (body : Expr) :
    Option InferenceResult := do
  let (generated, _) ←
    elaborateFix signature context body context.initialSupply
  inferGeneratedUsing solveHard generated

/-- Public executable result for the `fixE` checkpoint. -/
def inferFix
    (signature : Signature) (context : Context) (body : Expr) : Option Ty := do
  let result ← inferFixUsing unify signature context body
  pure result.target

/-- Relational unary-fix rule parameterized by the relation used for the
body.  This mirrors `elaborateFixUsing` and is the proof-level composition
point for the final M4 dispatcher. -/
inductive FixElaboratesUsing
    (BodyElaborates : Context → Expr → Supply → Generated → Supply → Prop)
    (context : Context) :
    Expr → Supply → Generated → Supply → Prop where
  | fixE {body supply generatedBody next}
      (direct : DirectSelf.Holds body)
      (bodyElaboration :
        BodyElaborates
          (Fix.bodyContext (.var ⟨supply.ty⟩) (.var ⟨supply.ty + 1⟩) context)
          body (supply.nextTy 2) generatedBody next) :
      FixElaboratesUsing BodyElaborates context (.fixE body) supply
        (Generated.fromFix (.var ⟨supply.ty⟩) (.var ⟨supply.ty + 1⟩)
          generatedBody)
        next

/-- M3-specialized relational wrapper for this checkpoint. -/
abbrev FixElaborates
    (signature : Signature) (context : Context) :
    Expr → Supply → Generated → Supply → Prop :=
  FixElaboratesUsing (Elaborates signature) context

namespace FixElaborates

theorem direct
    {signature : Signature} {context : Context} {body : Expr}
    {supply next : Supply} {generated : Generated}
    (elaboration :
      FixElaborates signature context (.fixE body) supply generated next) :
    DirectSelf.Holds body := by
  cases elaboration
  assumption

end FixElaborates

/-- Callback-parametric executable soundness. -/
theorem elaborateFixUsing_sound
    {elaborateBody : Context → Expr → Supply → Option (Generated × Supply)}
    {BodyElaborates : Context → Expr → Supply → Generated → Supply → Prop}
    (bodySound : ∀ {context body supply generated next},
      elaborateBody context body supply = some (generated, next) →
        BodyElaborates context body supply generated next)
    {context : Context} {body : Expr} {supply next : Supply}
    {generated : Generated}
    (success : elaborateFixUsing elaborateBody context body supply =
      some (generated, next)) :
    FixElaboratesUsing BodyElaborates context (.fixE body) supply generated next := by
  by_cases direct : DirectSelf.check 1 body = true
  · let domain : Ty := .var ⟨supply.ty⟩
    let codomain : Ty := .var ⟨supply.ty + 1⟩
    cases bodyResult : elaborateBody (Fix.bodyContext domain codomain context)
        body (supply.nextTy 2) with
    | none =>
        simp [elaborateFixUsing, direct, domain, codomain, bodyResult] at success
    | some output =>
        rcases output with ⟨generatedBody, afterBody⟩
        simp [elaborateFixUsing, direct, domain, codomain, bodyResult] at success
        rcases success with ⟨rfl, rfl⟩
        exact .fixE direct (bodySound bodyResult)
  · simp [elaborateFixUsing, direct] at success

/-- The M3-specialized fix wrapper is sound for `FixElaborates`. -/
theorem elaborateFix_sound
    {signature : Signature} (wellFormed : signature.WellFormed)
    {context : Context} {body : Expr} {supply next : Supply}
    {generated : Generated}
    (success : elaborateFix signature context body supply =
      some (generated, next)) :
    FixElaborates signature context (.fixE body) supply generated next := by
  exact elaborateFixUsing_sound
    (elaborateBody := elaborate signature)
    (BodyElaborates := Elaborates signature)
    (fun bodySuccess => elaborate_sound wellFormed bodySuccess) success

/-- One blockwise-principal typing derivation for the fix checkpoint. -/
structure PrincipalFixTypingDerivation
    (signature : Signature) (context : Context) (body : Expr)
    (target : Ty) where
  generated : Generated
  next : Supply
  elaboration :
    FixElaborates signature context (.fixE body) context.initialSupply
      generated next
  closure : PrincipalBlockClosure generated
  absorbing : closure.Absorbing
  target_eq : target = closure.target

def PrincipalFixTyping
    (signature : Signature) (context : Context) (body : Expr)
    (target : Ty) : Prop :=
  Nonempty (PrincipalFixTypingDerivation signature context body target)

/-- Declarative static typing for this isolated `fixE` checkpoint. -/
def FixTyping
    (signature : Signature) (context : Context) (body : Expr)
    (target : Ty) : Prop :=
  ∃ principal,
    PrincipalFixTyping signature context body principal ∧
      IsInstance principal target

namespace PrincipalFixTyping

theorem toFixTyping
    {signature : Signature} {context : Context} {body : Expr} {target : Ty}
    (principal : PrincipalFixTyping signature context body target) :
    FixTyping signature context body target := by
  exact ⟨target, principal, Subst.id, by simp⟩

end PrincipalFixTyping

namespace FixInference

/-- Successful executable inference yields an independent relational
elaboration and an absorbing principal block closure. -/
theorem inferFix_success_principalFixTyping
    {signature : Signature} (wellFormed : signature.WellFormed)
    {context : Context} {body : Expr} {target : Ty}
    (success : inferFix signature context body = some target) :
    PrincipalFixTyping signature context body target := by
  unfold inferFix inferFixUsing at success
  cases elaborated : elaborateFix signature context body context.initialSupply with
  | none => simp [elaborated] at success
  | some output =>
      rcases output with ⟨generated, next⟩
      simp only [elaborated] at success
      change
        (inferGeneratedUsing unify generated).bind
          (fun result => some result.target) = some target at success
      cases closedResult : inferGeneratedUsing unify generated with
      | none => simp [closedResult] at success
      | some result =>
          simp only [closedResult, Option.bind_some, Option.some.injEq] at success
          subst target
          obtain ⟨closure, _, targetEquality, absorbing⟩ :=
            inferGeneratedUsing_absorbingPrincipalBlockClosure
              unify_absorbingMGUSolver closedResult
          exact ⟨
            { generated := generated
              next := next
              elaboration := elaborateFix_sound wellFormed elaborated
              closure := closure
              absorbing := absorbing
              target_eq := targetEquality }⟩

theorem inferFix_success_fixTyping
    {signature : Signature} (wellFormed : signature.WellFormed)
    {context : Context} {body : Expr} {target : Ty}
    (success : inferFix signature context body = some target) :
    FixTyping signature context body target :=
  (inferFix_success_principalFixTyping wellFormed success).toFixTyping

end FixInference

/-- A syntactically invalid self use has no relational fix typing. -/
theorem not_fixTyping_of_not_direct
    {signature : Signature} {context : Context} {body : Expr}
    (notDirect : ¬ DirectSelf.Holds body) (target : Ty) :
    ¬ FixTyping signature context body target := by
  intro typing
  rcases typing with ⟨_, ⟨derivation⟩, _⟩
  exact notDirect derivation.elaboration.direct

end TypePM.Source
