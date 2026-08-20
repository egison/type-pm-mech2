import TypePM.Runtime.OrderedDispatch
import TypePM.Runtime.Values

/-!
# Matching atoms and syntax-directed reductions

A matching atom is one pending request to compare a source pattern with a
target value using a matcher value.  This module implements the Paper-1
syntax-directed cases that do not inspect user-defined matcher clauses:
`something`, tuple matching, and delegation from a product matcher to
`something`.  Pattern-function nodes and matcher-clause dispatch are composed
with these cases in later modules.
-/

namespace TypePM.Runtime

open TypePM.Source

/-- One pending pattern/matcher/target request. -/
structure MatchingAtom where
  pattern : Pattern
  matcher : Value
  target : Value
deriving Repr

/-- One atom step returns ordered continuation alternatives and new bindings. -/
structure AtomReduction where
  branches : List (List MatchingAtom)
  bindings : List Value
deriving Repr

/-- A complete matching-search state.  The ordinary expression environment is
newest-first.  Pattern bindings form one source-ordered prefix, matching
`Pattern.extendContext`; pending work is source-ordered as well. -/
structure MatchingState where
  work : List MatchingAtom
  environment : ValueEnvironment
  bindings : List Value
deriving Repr

/-- Patterns still owned by matcher-clause dispatch after syntax-directed
reduction has run.  Conjunction and disjunction are excluded because their
built-in rules always handle them first, independently of the matcher value. -/
inductive MatcherDispatchable : Pattern → Prop where
  | var : MatcherDispatchable .var
  | wild : MatcherDispatchable .wild
  | value : MatcherDispatchable (.value expression)
  | ctor : MatcherDispatchable (.ctor constructor fields)
  | tuple : MatcherDispatchable (.tuple items)
  | embed : MatcherDispatchable (.embed index)
  | app : MatcherDispatchable (.app function arguments)

/-- Exact-arity construction of tuple child atoms. -/
def zipMatchingAtoms :
    List Pattern → List Value → List Value → Option (List MatchingAtom)
  | [], [], [] => some []
  | pattern :: patterns, matcher :: matchers, target :: targets => do
      let tail ← zipMatchingAtoms patterns matchers targets
      pure (⟨pattern, matcher, target⟩ :: tail)
  | _, _, _ => none

/-- Structural relation for exact-arity child atom construction. -/
inductive MatchingAtomsZip :
    List Pattern → List Value → List Value → List MatchingAtom → Prop where
  | nil : MatchingAtomsZip [] [] [] []
  | cons
      (tail : MatchingAtomsZip patterns matchers targets atoms) :
      MatchingAtomsZip (pattern :: patterns) (matcher :: matchers)
        (target :: targets) (⟨pattern, matcher, target⟩ :: atoms)

theorem zipMatchingAtoms_sound
    {patterns : List Pattern} {matchers targets : List Value}
    {atoms : List MatchingAtom}
    (success : zipMatchingAtoms patterns matchers targets = some atoms) :
    MatchingAtomsZip patterns matchers targets atoms := by
  cases patterns with
  | nil =>
      cases matchers <;> cases targets <;>
        simp [zipMatchingAtoms] at success
      cases success
      exact .nil
  | cons pattern patterns =>
      cases matchers with
      | nil => simp [zipMatchingAtoms] at success
      | cons matcher matchers =>
          cases targets with
          | nil => simp [zipMatchingAtoms] at success
          | cons target targets =>
              simp only [zipMatchingAtoms] at success
              cases tailResult : zipMatchingAtoms patterns matchers targets with
              | none => simp [tailResult] at success
              | some tail =>
                  simp [tailResult] at success
                  subst atoms
                  exact .cons (zipMatchingAtoms_sound tailResult)

theorem MatchingAtomsZip.complete
    {patterns : List Pattern} {matchers targets : List Value}
    {atoms : List MatchingAtom}
    (related : MatchingAtomsZip patterns matchers targets atoms) :
    zipMatchingAtoms patterns matchers targets = some atoms := by
  cases related with
  | nil => rfl
  | cons tail => simp [zipMatchingAtoms, MatchingAtomsZip.complete tail]

theorem zipMatchingAtoms_eq_some_iff
    (patterns : List Pattern) (matchers targets : List Value)
    (atoms : List MatchingAtom) :
    zipMatchingAtoms patterns matchers targets = some atoms ↔
      MatchingAtomsZip patterns matchers targets atoms :=
  ⟨zipMatchingAtoms_sound, MatchingAtomsZip.complete⟩

namespace AtomReduction

def success : AtomReduction := ⟨[[]], []⟩
def failure : AtomReduction := ⟨[], []⟩

end AtomReduction

/-- Syntax-directed atom reduction.  `miss` means that a later handler (most
notably user-defined matcher dispatch) must inspect the atom. -/
def reduceBuiltinAtom
    (eval : ValueEnvironment → Expr → FuelResult Value)
    (environment : ValueEnvironment) (atom : MatchingAtom) :
    FuelResult (DispatchResult AtomReduction) :=
  match atom.pattern, atom.matcher, atom.target with
  | .and left right, matcher, target =>
      .ok (.hit ⟨[[⟨left, matcher, target⟩, ⟨right, matcher, target⟩]], []⟩)
  | .or left right, matcher, target =>
      .ok (.hit ⟨[[⟨left, matcher, target⟩], [⟨right, matcher, target⟩]], []⟩)
  | .wild, .something, _ => .ok (.hit .success)
  | .var, .something, target =>
      .ok (.hit ⟨[[]], [target]⟩)
  | .value expression, .something, target =>
      FuelResult.map
        (fun actual =>
          .hit (if Value.structuralEq actual target then
            .success else .failure))
        (eval environment expression)
  | .tuple patterns, .tuple matchers, .tuple targets =>
      match zipMatchingAtoms patterns matchers targets with
      | some atoms => .ok (.hit ⟨[atoms], []⟩)
      | none => .ok .miss
  | pattern@(.var), .tuple _, target
  | pattern@(.wild), .tuple _, target
  | pattern@(.value _), .tuple _, target =>
      .ok (.hit ⟨[[⟨pattern, .something, target⟩]], []⟩)
  | _, _, _ => .ok .miss

/-- Independent relation for a successful built-in atom rule. -/
inductive BuiltinAtomReduces
    (eval : ValueEnvironment → Expr → FuelResult Value)
    (environment : ValueEnvironment) :
    MatchingAtom → AtomReduction → Prop where
  | somethingWild :
      BuiltinAtomReduces eval environment
        ⟨.wild, .something, target⟩ .success
  | somethingVar :
      BuiltinAtomReduces eval environment
        ⟨.var, .something, target⟩ ⟨[[]], [target]⟩
  | somethingValueSuccess
      (evaluated : eval environment expression = .ok actual)
      (equal : Value.structuralEq actual target = true) :
      BuiltinAtomReduces eval environment
        ⟨.value expression, .something, target⟩ .success
    | somethingValueFailure
      (evaluated : eval environment expression = .ok actual)
      (unequal : Value.structuralEq actual target = false) :
      BuiltinAtomReduces eval environment
        ⟨.value expression, .something, target⟩ .failure
  | and :
      BuiltinAtomReduces eval environment
        ⟨.and left right, matcher, target⟩
        ⟨[[⟨left, matcher, target⟩, ⟨right, matcher, target⟩]], []⟩
  | or :
      BuiltinAtomReduces eval environment
        ⟨.or left right, matcher, target⟩
        ⟨[[⟨left, matcher, target⟩], [⟨right, matcher, target⟩]], []⟩
  | tuple
      (zipped : MatchingAtomsZip patterns matchers targets atoms) :
      BuiltinAtomReduces eval environment
        ⟨.tuple patterns, .tuple matchers, .tuple targets⟩
        ⟨[atoms], []⟩
  | productSomethingVar :
      BuiltinAtomReduces eval environment
        ⟨.var, .tuple matchers, target⟩
        ⟨[[⟨.var, .something, target⟩]], []⟩
  | productSomethingWild :
      BuiltinAtomReduces eval environment
        ⟨.wild, .tuple matchers, target⟩
        ⟨[[⟨.wild, .something, target⟩]], []⟩
  | productSomethingValue :
      BuiltinAtomReduces eval environment
        ⟨.value expression, .tuple matchers, target⟩
        ⟨[[⟨.value expression, .something, target⟩]], []⟩

private theorem ok_miss_ne_ok_hit (reduction : AtomReduction) :
    (FuelResult.ok (DispatchResult.miss : DispatchResult AtomReduction)) ≠
      .ok (.hit reduction) := by
  intro equal
  injection equal with outcome
  cases outcome

/-- Every executable built-in hit has the corresponding structural rule. -/
theorem reduceBuiltinAtom_hit_sound
    {eval : ValueEnvironment → Expr → FuelResult Value}
    {environment : ValueEnvironment} {atom : MatchingAtom}
    {reduction : AtomReduction}
    (success : reduceBuiltinAtom eval environment atom =
      .ok (.hit reduction)) :
    BuiltinAtomReduces eval environment atom reduction := by
  rcases atom with ⟨pattern, matcher, target⟩
  cases pattern with
  | var =>
      cases matcher <;> simp only [reduceBuiltinAtom] at success
      case tuple matchers =>
        cases success
        exact .productSomethingVar
      case something =>
        cases success
        exact .somethingVar
      all_goals exact (ok_miss_ne_ok_hit _ success).elim
  | wild =>
      cases matcher <;> simp only [reduceBuiltinAtom] at success
      case tuple matchers =>
        cases success
        exact .productSomethingWild
      case something =>
        cases success
        exact .somethingWild
      all_goals exact (ok_miss_ne_ok_hit _ success).elim
  | value expression =>
      cases matcher <;> simp only [reduceBuiltinAtom] at success
      case tuple matchers =>
        cases success
        exact .productSomethingValue
      case something =>
        rw [FuelResult.map_eq_ok_iff] at success
        rcases success with ⟨actual, evaluated, output⟩
        split at output
        next equal =>
          cases output
          exact .somethingValueSuccess evaluated equal
        next unequal =>
          cases output
          have structuralFalse : Value.structuralEq actual target = false := by
            cases structural : Value.structuralEq actual target <;> simp_all
          exact .somethingValueFailure evaluated structuralFalse
      all_goals exact (ok_miss_ne_ok_hit _ success).elim
  | tuple patterns =>
      cases matcher <;> simp only [reduceBuiltinAtom] at success
      case tuple matchers =>
        cases target
        case tuple targets =>
          cases zipped : zipMatchingAtoms patterns matchers targets with
          | none =>
              simp only [zipped] at success
              exact (ok_miss_ne_ok_hit _ success).elim
          | some atoms =>
              simp only [zipped] at success
              cases success
              exact .tuple ((zipMatchingAtoms_eq_some_iff _ _ _ _).mp zipped)
        all_goals exact (ok_miss_ne_ok_hit _ success).elim
      all_goals exact (ok_miss_ne_ok_hit _ success).elim
  | and left right =>
      cases success
      exact .and
  | or left right =>
      cases success
      exact .or
  | ctor constructor arguments =>
      cases matcher <;> simp only [reduceBuiltinAtom] at success <;>
        exact (ok_miss_ne_ok_hit _ success).elim
  | embed index =>
      cases matcher <;> simp only [reduceBuiltinAtom] at success <;>
        exact (ok_miss_ne_ok_hit _ success).elim
  | app function arguments =>
      cases matcher <;> simp only [reduceBuiltinAtom] at success <;>
        exact (ok_miss_ne_ok_hit _ success).elim

/-- Every structural built-in rule executes as a hit. -/
theorem BuiltinAtomReduces.complete
    {eval : ValueEnvironment → Expr → FuelResult Value}
    {environment : ValueEnvironment} {atom : MatchingAtom}
    {reduction : AtomReduction}
    (derivation : BuiltinAtomReduces eval environment atom reduction) :
    reduceBuiltinAtom eval environment atom = .ok (.hit reduction) := by
  cases derivation with
  | somethingWild | somethingVar | and | or | productSomethingVar |
      productSomethingWild | productSomethingValue => rfl
  | somethingValueSuccess evaluated equal =>
      simp [reduceBuiltinAtom, evaluated, equal]
  | somethingValueFailure evaluated unequal =>
      simp [reduceBuiltinAtom, evaluated, unequal]
  | tuple zipped =>
      simp [reduceBuiltinAtom,
        (zipMatchingAtoms_eq_some_iff _ _ _ _).mpr zipped]

theorem reduceBuiltinAtom_hit_iff
    (eval : ValueEnvironment → Expr → FuelResult Value)
    (environment : ValueEnvironment) (atom : MatchingAtom)
    (reduction : AtomReduction) :
    reduceBuiltinAtom eval environment atom = .ok (.hit reduction) ↔
      BuiltinAtomReduces eval environment atom reduction :=
  ⟨reduceBuiltinAtom_hit_sound, BuiltinAtomReduces.complete⟩

/-- A built-in miss proves that the atom is eligible for the later matcher
clause handler; in particular it cannot be a conjunction. -/
theorem matcherDispatchable_of_reduceBuiltinAtom_miss
    {eval : ValueEnvironment → Expr → FuelResult Value}
    {environment : ValueEnvironment} {atom : MatchingAtom}
    (miss : reduceBuiltinAtom eval environment atom = .ok .miss) :
    MatcherDispatchable atom.pattern := by
  rcases atom with ⟨pattern, matcher, target⟩
  cases pattern <;> simp only [reduceBuiltinAtom] at miss
  case and => simp at miss
  case or => simp at miss
  case var => exact .var
  case wild => exact .wild
  case value => exact .value
  case ctor => exact .ctor
  case tuple => exact .tuple
  case embed => exact .embed
  case app => exact .app

/-- If embedded expression evaluation is non-stuck, built-in atom reduction
cannot introduce a stuck result. -/
theorem reduceBuiltinAtom_notStuck
    (eval : ValueEnvironment → Expr → FuelResult Value)
    (safe : ∀ environment expression, (eval environment expression).NotStuck)
    (environment : ValueEnvironment) (atom : MatchingAtom) :
    (reduceBuiltinAtom eval environment atom).NotStuck := by
  rcases atom with ⟨pattern, matcher, target⟩
  cases pattern with
  | value expression =>
      cases matcher with
      | something =>
          exact FuelResult.map_notStuck _ (safe environment expression)
      | _ => trivial
  | tuple patterns =>
      cases matcher with
      | tuple matchers =>
          cases target with
          | tuple targets =>
              simp only [reduceBuiltinAtom]
              cases zipMatchingAtoms patterns matchers targets <;> trivial
          | _ => trivial
      | _ => trivial
  | _ =>
      cases matcher <;> trivial

end TypePM.Runtime
