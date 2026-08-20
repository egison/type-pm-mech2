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
  | .and left right => patternBindingCount left + patternBindingCount right
  | .or left _ => patternBindingCount left

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
  | .matchFirst target matcher arms fallback =>
      mentions tracked target || mentions tracked matcher ||
        mentionsMatchFirstArms tracked arms || mentions tracked fallback

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
  | .and left right =>
      mentionsPattern tracked before left ||
        mentionsPattern tracked (before + patternBindingCount left) right
  | .or left right =>
      mentionsPattern tracked before left || mentionsPattern tracked before right

def mentionsPatterns (tracked before : Nat) : List Pattern → Bool
  | [] => false
  | pattern :: patterns =>
      mentionsPattern tracked before pattern ||
        mentionsPatterns tracked (before + patternBindingCount pattern) patterns

/-- Clause captures are prepended for both next-matcher expressions and arm
bodies; data-pattern binders additionally precede captures in arm bodies. -/
def mentionsClause (tracked : Nat) : MatcherClause → Bool
  | .mk header nextMatchers arms =>
      mentions (tracked + header.captureCount) nextMatchers ||
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

/-- Kernel-computable direct-self check.  The public wrappers below choose a
fuel amount from the finite source size. -/
def checkFuel : Nat → Nat → Expr → Bool
  | 0, _, _ => false
  | _ + 1, tracked, .var index => index != tracked
  | _ + 1, _, .lit _ | _ + 1, _, .something => true
  | fuel + 1, tracked, .lam body => checkFuel fuel (tracked + 1) body
  | fuel + 1, tracked, .app function argument =>
      checkHeadFuel fuel tracked function && checkFuel fuel tracked argument
  | fuel + 1, tracked, .tuple items
  | fuel + 1, tracked, .ctor _ items
  | fuel + 1, tracked, .prim _ items => checkListFuel fuel tracked items
  | fuel + 1, tracked, .letE value body =>
      checkFuel fuel tracked value && checkFuel fuel (tracked + 1) body
  | fuel + 1, tracked, .ifE condition thenBranch elseBranch =>
      checkFuel fuel tracked condition && checkFuel fuel tracked thenBranch &&
        checkFuel fuel tracked elseBranch
  | fuel + 1, tracked, .fixE body =>
      !mentions (tracked + 2) body && checkFuel fuel 1 body
  | fuel + 1, tracked, .matcher clauses => checkClausesFuel fuel tracked clauses
  | fuel + 1, tracked, .matchAll target matcher pattern body =>
      checkFuel fuel tracked target && checkFuel fuel tracked matcher &&
        checkPatternFuel fuel tracked 0 pattern &&
        checkFuel fuel (tracked + patternBindingCount pattern) body
  | fuel + 1, tracked, .matchFirst target matcher arms fallback =>
      checkFuel fuel tracked target && checkFuel fuel tracked matcher &&
        checkMatchFirstArmsFuel fuel tracked arms &&
        checkFuel fuel tracked fallback

/-- Check the function spine of an application. -/
def checkHeadFuel : Nat → Nat → Expr → Bool
  | 0, _, _ => false
  | _ + 1, _, .var _ => true
  | fuel + 1, tracked, .app function argument =>
      checkHeadFuel fuel tracked function && checkFuel fuel tracked argument
  | fuel + 1, tracked, expression => checkFuel fuel tracked expression

def checkListFuel : Nat → Nat → List Expr → Bool
  | 0, _, _ => false
  | _ + 1, _, [] => true
  | fuel + 1, tracked, expression :: expressions =>
      checkFuel fuel tracked expression && checkListFuel fuel tracked expressions

def checkPatternFuel : Nat → Nat → Nat → Pattern → Bool
  | 0, _, _, _ => false
  | _ + 1, _, _, .var | _ + 1, _, _, .wild | _ + 1, _, _, .embed _ => true
  | fuel + 1, tracked, before, .value expression =>
      checkFuel fuel (tracked + before) expression
  | fuel + 1, tracked, before, .ctor _ fields
  | fuel + 1, tracked, before, .tuple fields
  | fuel + 1, tracked, before, .app _ fields =>
      checkPatternsFuel fuel tracked before fields
  | fuel + 1, tracked, before, .and left right =>
      checkPatternFuel fuel tracked before left &&
        checkPatternFuel fuel tracked (before + patternBindingCount left) right
  | fuel + 1, tracked, before, .or left right =>
      checkPatternFuel fuel tracked before left &&
        checkPatternFuel fuel tracked before right

def checkPatternsFuel : Nat → Nat → Nat → List Pattern → Bool
  | 0, _, _, _ => false
  | _ + 1, _, _, [] => true
  | fuel + 1, tracked, before, pattern :: patterns =>
      checkPatternFuel fuel tracked before pattern &&
        checkPatternsFuel fuel tracked (before + patternBindingCount pattern)
          patterns

def checkClauseFuel : Nat → Nat → MatcherClause → Bool
  | 0, _, _ => false
  | fuel + 1, tracked, .mk header nextMatchers arms =>
      checkFuel fuel (tracked + header.captureCount) nextMatchers &&
        checkArmsFuel fuel tracked header.captureCount arms

def checkClausesFuel : Nat → Nat → List MatcherClause → Bool
  | 0, _, _ => false
  | _ + 1, _, [] => true
  | fuel + 1, tracked, clause :: clauses =>
      checkClauseFuel fuel tracked clause && checkClausesFuel fuel tracked clauses

def checkArmFuel : Nat → Nat → Nat → MatcherArm → Bool
  | 0, _, _, _ => false
  | fuel + 1, tracked, captures, .mk header body =>
      checkFuel fuel (tracked + header.bindingCount + captures) body

def checkArmsFuel : Nat → Nat → Nat → List MatcherArm → Bool
  | 0, _, _, _ => false
  | _ + 1, _, _, [] => true
  | fuel + 1, tracked, captures, arm :: arms =>
      checkArmFuel fuel tracked captures arm &&
        checkArmsFuel fuel tracked captures arms

def checkMatchFirstArmFuel : Nat → Nat → MatchFirstArm → Bool
  | 0, _, _ => false
  | fuel + 1, tracked, .mk pattern body =>
      checkPatternFuel fuel tracked 0 pattern &&
        checkFuel fuel (tracked + patternBindingCount pattern) body

def checkMatchFirstArmsFuel : Nat → Nat → List MatchFirstArm → Bool
  | 0, _, _ => false
  | _ + 1, _, [] => true
  | fuel + 1, tracked, arm :: arms =>
      checkMatchFirstArmFuel fuel tracked arm &&
        checkMatchFirstArmsFuel fuel tracked arms

end

/-- Check an expression in ordinary position. -/
def check (tracked : Nat) (expression : Expr) : Bool :=
  checkFuel (expression.complexity * 3 + 1) tracked expression

def checkHead (tracked : Nat) (expression : Expr) : Bool :=
  checkHeadFuel (expression.complexity * 3 + 2) tracked expression

def checkList (tracked : Nat) (expressions : List Expr) : Bool :=
  checkListFuel (Expr.listComplexity expressions * 3 + 1) tracked expressions

def checkPattern (tracked before : Nat) (pattern : Pattern) : Bool :=
  checkPatternFuel (pattern.complexity * 3 + 1) tracked before pattern

def checkPatterns (tracked before : Nat) (patterns : List Pattern) : Bool :=
  checkPatternsFuel (Pattern.listComplexity patterns * 3 + 1) tracked before
    patterns

def checkClause (tracked : Nat) (clause : MatcherClause) : Bool :=
  checkClauseFuel (clause.complexity * 3 + 1) tracked clause

def checkClauses (tracked : Nat) (clauses : List MatcherClause) : Bool :=
  checkClausesFuel (MatcherClause.listComplexity clauses * 3 + 1) tracked clauses

def checkArm (tracked captures : Nat) (arm : MatcherArm) : Bool :=
  checkArmFuel (arm.complexity * 3 + 1) tracked captures arm

def checkArms (tracked captures : Nat) (arms : List MatcherArm) : Bool :=
  checkArmsFuel (MatcherArm.listComplexity arms * 3 + 1) tracked captures arms

def checkMatchFirstArm (tracked : Nat) (arm : MatchFirstArm) : Bool :=
  checkMatchFirstArmFuel (arm.complexity * 3 + 1) tracked arm

def checkMatchFirstArms (tracked : Nat) (arms : List MatchFirstArm) : Bool :=
  checkMatchFirstArmsFuel (MatchFirstArm.listComplexity arms * 3 + 1) tracked arms

mutual

/-- Proof-level structural characterization of a successful ordinary-position
direct-self check.  Fuel is an index of the derivation, not a Boolean premise. -/
def ChecksFuel : Nat → Nat → Expr → Prop
  | 0, _, _ => False
  | _ + 1, tracked, .var index => index ≠ tracked
  | _ + 1, _, .lit _ | _ + 1, _, .something => True
  | fuel + 1, tracked, .lam body => ChecksFuel fuel (tracked + 1) body
  | fuel + 1, tracked, .app function argument =>
      ChecksHeadFuel fuel tracked function ∧ ChecksFuel fuel tracked argument
  | fuel + 1, tracked, .tuple items
  | fuel + 1, tracked, .ctor _ items
  | fuel + 1, tracked, .prim _ items => ChecksListFuel fuel tracked items
  | fuel + 1, tracked, .letE value body =>
      ChecksFuel fuel tracked value ∧ ChecksFuel fuel (tracked + 1) body
  | fuel + 1, tracked, .ifE condition thenBranch elseBranch =>
      ChecksFuel fuel tracked condition ∧ ChecksFuel fuel tracked thenBranch ∧
        ChecksFuel fuel tracked elseBranch
  | fuel + 1, tracked, .fixE body =>
      mentions (tracked + 2) body = false ∧ ChecksFuel fuel 1 body
  | fuel + 1, tracked, .matcher clauses => ChecksClausesFuel fuel tracked clauses
  | fuel + 1, tracked, .matchAll target matcher pattern body =>
      ChecksFuel fuel tracked target ∧ ChecksFuel fuel tracked matcher ∧
        ChecksPatternFuel fuel tracked 0 pattern ∧
        ChecksFuel fuel (tracked + patternBindingCount pattern) body
  | fuel + 1, tracked, .matchFirst target matcher arms fallback =>
      ChecksFuel fuel tracked target ∧ ChecksFuel fuel tracked matcher ∧
        ChecksMatchFirstArmsFuel fuel tracked arms ∧
        ChecksFuel fuel tracked fallback

def ChecksHeadFuel : Nat → Nat → Expr → Prop
  | 0, _, _ => False
  | _ + 1, _, .var _ => True
  | fuel + 1, tracked, .app function argument =>
      ChecksHeadFuel fuel tracked function ∧ ChecksFuel fuel tracked argument
  | fuel + 1, tracked, expression => ChecksFuel fuel tracked expression

def ChecksListFuel : Nat → Nat → List Expr → Prop
  | 0, _, _ => False
  | _ + 1, _, [] => True
  | fuel + 1, tracked, expression :: expressions =>
      ChecksFuel fuel tracked expression ∧ ChecksListFuel fuel tracked expressions

def ChecksPatternFuel : Nat → Nat → Nat → Pattern → Prop
  | 0, _, _, _ => False
  | _ + 1, _, _, .var | _ + 1, _, _, .wild | _ + 1, _, _, .embed _ => True
  | fuel + 1, tracked, before, .value expression =>
      ChecksFuel fuel (tracked + before) expression
  | fuel + 1, tracked, before, .ctor _ fields
  | fuel + 1, tracked, before, .tuple fields
  | fuel + 1, tracked, before, .app _ fields =>
      ChecksPatternsFuel fuel tracked before fields
  | fuel + 1, tracked, before, .and left right =>
      ChecksPatternFuel fuel tracked before left ∧
        ChecksPatternFuel fuel tracked (before + patternBindingCount left) right
  | fuel + 1, tracked, before, .or left right =>
      ChecksPatternFuel fuel tracked before left ∧
        ChecksPatternFuel fuel tracked before right

def ChecksPatternsFuel : Nat → Nat → Nat → List Pattern → Prop
  | 0, _, _, _ => False
  | _ + 1, _, _, [] => True
  | fuel + 1, tracked, before, pattern :: patterns =>
      ChecksPatternFuel fuel tracked before pattern ∧
        ChecksPatternsFuel fuel tracked (before + patternBindingCount pattern) patterns

def ChecksClauseFuel : Nat → Nat → MatcherClause → Prop
  | 0, _, _ => False
  | fuel + 1, tracked, .mk header nextMatchers arms =>
      ChecksFuel fuel (tracked + header.captureCount) nextMatchers ∧
        ChecksArmsFuel fuel tracked header.captureCount arms

def ChecksClausesFuel : Nat → Nat → List MatcherClause → Prop
  | 0, _, _ => False
  | _ + 1, _, [] => True
  | fuel + 1, tracked, clause :: clauses =>
      ChecksClauseFuel fuel tracked clause ∧ ChecksClausesFuel fuel tracked clauses

def ChecksArmFuel : Nat → Nat → Nat → MatcherArm → Prop
  | 0, _, _, _ => False
  | fuel + 1, tracked, captures, .mk header body =>
      ChecksFuel fuel (tracked + header.bindingCount + captures) body

def ChecksArmsFuel : Nat → Nat → Nat → List MatcherArm → Prop
  | 0, _, _, _ => False
  | _ + 1, _, _, [] => True
  | fuel + 1, tracked, captures, arm :: arms =>
      ChecksArmFuel fuel tracked captures arm ∧
        ChecksArmsFuel fuel tracked captures arms

def ChecksMatchFirstArmFuel : Nat → Nat → MatchFirstArm → Prop
  | 0, _, _ => False
  | fuel + 1, tracked, .mk pattern body =>
      ChecksPatternFuel fuel tracked 0 pattern ∧
        ChecksFuel fuel (tracked + patternBindingCount pattern) body

def ChecksMatchFirstArmsFuel : Nat → Nat → List MatchFirstArm → Prop
  | 0, _, _ => False
  | _ + 1, _, [] => True
  | fuel + 1, tracked, arm :: arms =>
      ChecksMatchFirstArmFuel fuel tracked arm ∧
        ChecksMatchFirstArmsFuel fuel tracked arms

end

structure FuelReflection (fuel : Nat) : Prop where
  expression : ∀ tracked expression,
    ChecksFuel fuel tracked expression ↔ checkFuel fuel tracked expression = true
  head : ∀ tracked expression,
    ChecksHeadFuel fuel tracked expression ↔ checkHeadFuel fuel tracked expression = true
  expressions : ∀ tracked expressions,
    ChecksListFuel fuel tracked expressions ↔ checkListFuel fuel tracked expressions = true
  pattern : ∀ tracked before pattern,
    ChecksPatternFuel fuel tracked before pattern ↔
      checkPatternFuel fuel tracked before pattern = true
  patterns : ∀ tracked before patterns,
    ChecksPatternsFuel fuel tracked before patterns ↔
      checkPatternsFuel fuel tracked before patterns = true
  clause : ∀ tracked clause,
    ChecksClauseFuel fuel tracked clause ↔ checkClauseFuel fuel tracked clause = true
  clauses : ∀ tracked clauses,
    ChecksClausesFuel fuel tracked clauses ↔ checkClausesFuel fuel tracked clauses = true
  arm : ∀ tracked captures arm,
    ChecksArmFuel fuel tracked captures arm ↔
      checkArmFuel fuel tracked captures arm = true
  arms : ∀ tracked captures arms,
    ChecksArmsFuel fuel tracked captures arms ↔
      checkArmsFuel fuel tracked captures arms = true
  matchFirstArm : ∀ tracked arm,
    ChecksMatchFirstArmFuel fuel tracked arm ↔
      checkMatchFirstArmFuel fuel tracked arm = true
  matchFirstArms : ∀ tracked arms,
    ChecksMatchFirstArmsFuel fuel tracked arms ↔
      checkMatchFirstArmsFuel fuel tracked arms = true

theorem fuelReflection (fuel : Nat) : FuelReflection fuel := by
  induction fuel with
  | zero =>
      constructor <;> intros <;>
        simp [ChecksFuel, ChecksHeadFuel, ChecksListFuel, ChecksPatternFuel,
          ChecksPatternsFuel, ChecksClauseFuel, ChecksClausesFuel, ChecksArmFuel,
          ChecksArmsFuel, ChecksMatchFirstArmFuel, ChecksMatchFirstArmsFuel,
          checkFuel, checkHeadFuel, checkListFuel, checkPatternFuel,
          checkPatternsFuel, checkClauseFuel, checkClausesFuel, checkArmFuel,
          checkArmsFuel, checkMatchFirstArmFuel, checkMatchFirstArmsFuel]
  | succ fuel induction =>
      constructor
      · intro tracked expression
        cases expression <;>
          simp [ChecksFuel, checkFuel, induction.expression, induction.head,
            induction.expressions, induction.pattern, induction.clauses,
            induction.matchFirstArms, and_assoc]
      · intro tracked expression
        cases expression <;>
          simp [ChecksHeadFuel, checkHeadFuel, induction.expression, induction.head]
      · intro tracked expressions
        cases expressions <;>
          simp [ChecksListFuel, checkListFuel, induction.expression,
            induction.expressions]
      · intro tracked before pattern
        cases pattern <;>
          simp [ChecksPatternFuel, checkPatternFuel, induction.expression,
            induction.patterns, induction.pattern]
      · intro tracked before patterns
        cases patterns <;>
          simp [ChecksPatternsFuel, checkPatternsFuel, induction.pattern,
            induction.patterns]
      · intro tracked clause
        cases clause
        simp [ChecksClauseFuel, checkClauseFuel, induction.expression,
          induction.arms]
      · intro tracked clauses
        cases clauses <;>
          simp [ChecksClausesFuel, checkClausesFuel, induction.clause,
            induction.clauses]
      · intro tracked captures arm
        cases arm
        simp [ChecksArmFuel, checkArmFuel, induction.expression]
      · intro tracked captures arms
        cases arms <;>
          simp [ChecksArmsFuel, checkArmsFuel, induction.arm, induction.arms]
      · intro tracked arm
        cases arm
        simp [ChecksMatchFirstArmFuel, checkMatchFirstArmFuel,
          induction.pattern, induction.expression]
      · intro tracked arms
        cases arms <;>
          simp [ChecksMatchFirstArmsFuel, checkMatchFirstArmsFuel,
            induction.matchFirstArm, induction.matchFirstArms]

@[simp] theorem checksFuel_iff {fuel tracked expression} :
    ChecksFuel fuel tracked expression ↔ checkFuel fuel tracked expression = true :=
  (fuelReflection fuel).expression tracked expression

theorem checksHeadFuel_iff {fuel tracked expression} :
    ChecksHeadFuel fuel tracked expression ↔ checkHeadFuel fuel tracked expression = true :=
  (fuelReflection fuel).head tracked expression

theorem checksListFuel_iff {fuel tracked expressions} :
    ChecksListFuel fuel tracked expressions ↔ checkListFuel fuel tracked expressions = true :=
  (fuelReflection fuel).expressions tracked expressions

theorem checksPatternFuel_iff {fuel tracked before pattern} :
    ChecksPatternFuel fuel tracked before pattern ↔
      checkPatternFuel fuel tracked before pattern = true :=
  (fuelReflection fuel).pattern tracked before pattern

theorem checksPatternsFuel_iff {fuel tracked before patterns} :
    ChecksPatternsFuel fuel tracked before patterns ↔
      checkPatternsFuel fuel tracked before patterns = true :=
  (fuelReflection fuel).patterns tracked before patterns

theorem checksClauseFuel_iff {fuel tracked clause} :
    ChecksClauseFuel fuel tracked clause ↔ checkClauseFuel fuel tracked clause = true :=
  (fuelReflection fuel).clause tracked clause

theorem checksClausesFuel_iff {fuel tracked clauses} :
    ChecksClausesFuel fuel tracked clauses ↔ checkClausesFuel fuel tracked clauses = true :=
  (fuelReflection fuel).clauses tracked clauses

theorem checksArmFuel_iff {fuel tracked captures arm} :
    ChecksArmFuel fuel tracked captures arm ↔
      checkArmFuel fuel tracked captures arm = true :=
  (fuelReflection fuel).arm tracked captures arm

theorem checksArmsFuel_iff {fuel tracked captures arms} :
    ChecksArmsFuel fuel tracked captures arms ↔
      checkArmsFuel fuel tracked captures arms = true :=
  (fuelReflection fuel).arms tracked captures arms

theorem checksMatchFirstArmFuel_iff {fuel tracked arm} :
    ChecksMatchFirstArmFuel fuel tracked arm ↔
      checkMatchFirstArmFuel fuel tracked arm = true :=
  (fuelReflection fuel).matchFirstArm tracked arm

theorem checksMatchFirstArmsFuel_iff {fuel tracked arms} :
    ChecksMatchFirstArmsFuel fuel tracked arms ↔
      checkMatchFirstArmsFuel fuel tracked arms = true :=
  (fuelReflection fuel).matchFirstArms tracked arms


/-- Proof-level direct-self side condition for a fix body. -/
def Holds (body : Expr) : Prop :=
  ChecksFuel (body.complexity * 3 + 1) 1 body

@[simp] theorem holds_iff_check (body : Expr) : Holds body ↔ check 1 body = true := by
  exact checksFuel_iff

instance (body : Expr) : Decidable (Holds body) :=
  decidable_of_iff (check 1 body = true) (holds_iff_check body).symm

end DirectSelf

namespace Fix

/-- The monomorphic body context: argument, recursive self, then outer scope. -/
def bodyContext (domain codomain : Ty) (context : Context) : Context :=
  .mono domain :: .mono (.fn domain codomain) :: context

/-- Matcher constructors consume their element matcher directionally, so the
recursive constructor's parameter starts as a matcher slot rather than as an
unconstrained ordinary type. -/
def domain (body : Expr) (supply : Supply) : Ty :=
  match body with
  | .matcher _ => .slot (.var ⟨supply.cap⟩) (.var ⟨supply.ty⟩)
  | _ => .var ⟨supply.ty⟩

/-- A matcher-root fix has a statically known result shape.  Seeding that
shape in the recursive self type is essential: nested `letE` blocks close
before the outer fix equation is appended, so an unconstrained codomain would
otherwise be prematurely unified with a `MatcherSlot`. -/
def codomain (body : Expr) (supply : Supply) : Ty :=
  match body with
  | .matcher _ =>
      .matcher (.var ⟨supply.cap + 1⟩) (.var ⟨supply.ty + 1⟩)
  | _ => .var ⟨supply.ty + 1⟩

/-- Supply after reserving the fix domain and codomain shape. -/
def bodySupply (body : Expr) (supply : Supply) : Supply :=
  match body with
  | .matcher _ => ⟨supply.ty + 2, supply.cap + 2⟩
  | _ => supply.nextTy 2

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
    let domain := Fix.domain body supply
    let codomain := Fix.codomain body supply
    let (generatedBody, next) ←
      elaborateBody (Fix.bodyContext domain codomain context) body
        (Fix.bodySupply body supply)
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
          (Fix.bodyContext (Fix.domain body supply) (Fix.codomain body supply)
            context)
          body (Fix.bodySupply body supply) generatedBody next) :
      FixElaboratesUsing BodyElaborates context (.fixE body) supply
        (Generated.fromFix (Fix.domain body supply) (Fix.codomain body supply)
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
  · let domain := Fix.domain body supply
    let codomain := Fix.codomain body supply
    cases bodyResult : elaborateBody (Fix.bodyContext domain codomain context)
        body (Fix.bodySupply body supply) with
    | none =>
        simp [elaborateFixUsing, direct, domain, codomain, bodyResult] at success
    | some output =>
        rcases output with ⟨generatedBody, afterBody⟩
        simp [elaborateFixUsing, direct, domain, codomain, bodyResult] at success
        rcases success with ⟨rfl, rfl⟩
        exact .fixE ((DirectSelf.holds_iff_check body).2 direct)
          (bodySound bodyResult)
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
