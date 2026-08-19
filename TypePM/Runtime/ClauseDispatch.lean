import TypePM.Runtime.OrderedDispatch
import TypePM.Runtime.MatchingState
import TypePM.Runtime.PatternPattern
import TypePM.Runtime.ValueDataPattern
import TypePM.Runtime.ValueShape

/-!
# Concrete matcher-clause dispatch

This module is the atomic A-MATCHER boundary from Paper 1.  It deliberately
takes expression evaluation as a callback, so expression evaluation and
matching-state reduction do not form a Lean definition cycle.

Pattern-pattern captures are evaluated in the atom environment.  Data-pattern
bindings, capture values, and the matcher definition environment are then
concatenated in that order for the selected arm body.  The expression for the
next matchers is evaluated in the matcher definition environment alone.

Only a pattern-pattern mismatch advances to the next clause.  Once a pattern
header matches, failure of every data-pattern arm is the normal empty matching
result and must not fall through to a less specific pattern clause.  Likewise,
an arm body returning an empty decomposition list stops both ordered searches.
`timeout` and `stuck` are propagated by `FuelResult.bind`.
-/

namespace TypePM.Runtime

open TypePM.Source

/-- One decomposition becomes one source-ordered branch of obligations. -/
abbrev MatchingBranch := List MatchingAtom

/-- All candidate branches produced by the first selected matcher arm. -/
abbrev MatchingBranches := List MatchingBranch

/-- Attach the same hole patterns and next matchers to every decomposition,
preserving both decomposition order and hole order. -/
def buildMatchingBranches
    (holes : List Pattern) (matchers : List Value)
    (decompositions : List (List Value)) : Option MatchingBranches :=
  decompositions.mapM (zipMatchingAtoms holes matchers)

/-- Try one data-pattern arm.  A data-pattern mismatch is the only normal
arm miss; all malformed body and next-matcher shapes are `stuck`. -/
def tryMatcherArm
    (eval : ValueEnvironment → Expr → FuelResult Value)
    (matcherEnvironment captureValues : ValueEnvironment)
    (holes : List Pattern) (nextMatchers : Expr) (target : Value) :
    MatcherArm → FuelResult (DispatchResult MatchingBranches)
  | .mk header body =>
      match matchValueDataPattern header target with
      | none => .ok .miss
      | some dataValues =>
          FuelResult.bind
            (eval (dataValues ++ captureValues ++ matcherEnvironment) body)
            fun decompositionValue =>
              match decodeDecompositions holes.length decompositionValue with
              | none => .stuck
              | some decompositions =>
                  FuelResult.bind (eval matcherEnvironment nextMatchers)
                    fun matcherProduct =>
                      match decodeProduct holes.length matcherProduct with
                      | none => .stuck
                      | some matchers =>
                          match buildMatchingBranches holes matchers
                              decompositions with
                          | none => .stuck
                          | some branches => .ok (.hit branches)

/-- A selected pattern clause owns the atom.  Exhausting its data arms is
therefore a successful reduction with no matching branches, not permission to
try a later pattern clause. -/
def closeMatcherArmsResult :
    DispatchResult MatchingBranches → DispatchResult MatchingBranches
  | .miss => .hit []
  | .hit branches => .hit branches

/-- Try one matcher clause.  Pattern-pattern captures are evaluated
left-to-right in the atom environment before ordered arm dispatch starts. -/
def tryMatcherClause
    (eval : ValueEnvironment → Expr → FuelResult Value)
    (atomEnvironment matcherEnvironment : ValueEnvironment)
    (pattern : Pattern) (target : Value) :
    MatcherClause → FuelResult (DispatchResult MatchingBranches)
  | .mk header nextMatchers arms =>
      match inspectPatternPattern header pattern with
      | none => .ok .miss
      | some dispatch =>
          FuelResult.bind
            (FuelResult.traverse (eval atomEnvironment) dispatch.captures)
            fun captureValues =>
              FuelResult.map closeMatcherArmsResult
                (firstHit
                  (tryMatcherArm eval matcherEnvironment captureValues
                    dispatch.holes nextMatchers target)
                  arms)

/-- Dispatch a source-ordered clause suffix. -/
def dispatchMatcherClauses
    (eval : ValueEnvironment → Expr → FuelResult Value)
    (atomEnvironment matcherEnvironment : ValueEnvironment)
    (clauses : List MatcherClause) (pattern : Pattern) (target : Value) :
    FuelResult (DispatchResult MatchingBranches) :=
  firstHit
    (tryMatcherClause eval atomEnvironment matcherEnvironment pattern target)
    clauses

/-- Dispatch the untried suffix stored in a matcher cursor.  Non-matcher
values are actual rule-coverage failures. -/
def dispatchMatcherValue
    (eval : ValueEnvironment → Expr → FuelResult Value)
    (atomEnvironment : ValueEnvironment) (matcher : Value)
    (pattern : Pattern) (target : Value) :
    FuelResult (DispatchResult MatchingBranches) :=
  match matcher with
  | .matcherV matcherEnvironment _ remaining =>
      dispatchMatcherClauses eval atomEnvironment matcherEnvironment remaining
        pattern target
  | _ => .stuck

/-- Convert a selected matcher-clause result to the common atom-reduction
interface.  Clause dispatch creates only recursive matching work; bindings
are collected later when those atoms reduce. -/
def clauseResultToAtomReduction :
    DispatchResult MatchingBranches → DispatchResult AtomReduction
  | .miss => .miss
  | .hit branches => .hit ⟨branches, []⟩

/-- Handle exactly user-defined matcher values at the shared atom boundary.
Other matcher forms are a normal miss so a separate composition layer can
try the built-in reducer. -/
def reduceMatcherAtom
    (eval : ValueEnvironment → Expr → FuelResult Value)
    (atomEnvironment : ValueEnvironment) (atom : MatchingAtom) :
    FuelResult (DispatchResult AtomReduction) :=
  match atom.matcher with
  | .matcherV matcherEnvironment _ remaining =>
      FuelResult.map clauseResultToAtomReduction
        (dispatchMatcherClauses eval atomEnvironment matcherEnvironment
          remaining atom.pattern atom.target)
  | _ => .ok .miss

/-! ## Independent successful-dispatch relations -/

/-- Independent specification of one completed arm attempt. -/
inductive MatcherArmDispatches
    (eval : ValueEnvironment → Expr → FuelResult Value)
    (matcherEnvironment captureValues : ValueEnvironment)
    (holes : List Pattern) (nextMatchers : Expr) (target : Value) :
    MatcherArm → DispatchResult MatchingBranches → Prop where
  | miss
      (mismatch : matchValueDataPattern header target = none) :
      MatcherArmDispatches eval matcherEnvironment captureValues holes
        nextMatchers target (.mk header body) .miss
  | hit
      (dataMatch : matchValueDataPattern header target = some dataValues)
      (bodyEval :
        eval (dataValues ++ captureValues ++ matcherEnvironment) body =
          .ok decompositionValue)
      (decompositionShape :
        decodeDecompositions holes.length decompositionValue =
          some decompositions)
      (matcherEval : eval matcherEnvironment nextMatchers = .ok matcherProduct)
      (matcherShape : decodeProduct holes.length matcherProduct = some matchers)
      (branchesBuilt :
        buildMatchingBranches holes matchers decompositions = some branches) :
      MatcherArmDispatches eval matcherEnvironment captureValues holes
        nextMatchers target (.mk header body) (.hit branches)

/-- Independent first-matching-arm relation. -/
inductive MatcherArmsDispatch
    (eval : ValueEnvironment → Expr → FuelResult Value)
    (matcherEnvironment captureValues : ValueEnvironment)
    (holes : List Pattern) (nextMatchers : Expr) (target : Value) :
    List MatcherArm → DispatchResult MatchingBranches → Prop where
  | nil : MatcherArmsDispatch eval matcherEnvironment captureValues holes
      nextMatchers target [] .miss
  | hit
      (selected : MatcherArmDispatches eval matcherEnvironment captureValues
        holes nextMatchers target arm (.hit branches)) :
      MatcherArmsDispatch eval matcherEnvironment captureValues holes
        nextMatchers target (arm :: rest) (.hit branches)
  | skip
      (missed : MatcherArmDispatches eval matcherEnvironment captureValues
        holes nextMatchers target arm .miss)
      (tail : MatcherArmsDispatch eval matcherEnvironment captureValues holes
        nextMatchers target rest result) :
      MatcherArmsDispatch eval matcherEnvironment captureValues holes
        nextMatchers target (arm :: rest) result

/-- Independent specification of one completed clause attempt. -/
inductive MatcherClauseDispatches
    (eval : ValueEnvironment → Expr → FuelResult Value)
    (atomEnvironment matcherEnvironment : ValueEnvironment)
    (pattern : Pattern) (target : Value) :
    MatcherClause → DispatchResult MatchingBranches → Prop where
  | miss
      (mismatch : inspectPatternPattern header pattern = none) :
      MatcherClauseDispatches eval atomEnvironment matcherEnvironment pattern
        target (.mk header nextMatchers arms) .miss
  | matched
      (headerMatch : PatternPatternMatches header pattern dispatch)
      (capturesEval : FuelResult.Traverses (eval atomEnvironment)
        dispatch.captures captureValues)
      (armsDispatch : MatcherArmsDispatch eval matcherEnvironment captureValues
        dispatch.holes nextMatchers target arms armsResult) :
      MatcherClauseDispatches eval atomEnvironment matcherEnvironment pattern
        target (.mk header nextMatchers arms)
          (closeMatcherArmsResult armsResult)

/-- Independent first-matching-clause relation. -/
inductive MatcherClausesDispatch
    (eval : ValueEnvironment → Expr → FuelResult Value)
    (atomEnvironment matcherEnvironment : ValueEnvironment)
    (pattern : Pattern) (target : Value) :
    List MatcherClause → DispatchResult MatchingBranches → Prop where
  | nil : MatcherClausesDispatch eval atomEnvironment matcherEnvironment
      pattern target [] .miss
  | hit
      (selected : MatcherClauseDispatches eval atomEnvironment matcherEnvironment
        pattern target clause (.hit branches)) :
      MatcherClausesDispatch eval atomEnvironment matcherEnvironment pattern
        target (clause :: rest) (.hit branches)
  | skip
      (missed : MatcherClauseDispatches eval atomEnvironment matcherEnvironment
        pattern target clause .miss)
      (tail : MatcherClausesDispatch eval atomEnvironment matcherEnvironment
        pattern target rest result) :
      MatcherClausesDispatch eval atomEnvironment matcherEnvironment pattern
        target (clause :: rest) result

/-- Independent successful relation for the matcher-value atom handler. -/
inductive MatcherAtomReduces
    (eval : ValueEnvironment → Expr → FuelResult Value)
    (atomEnvironment : ValueEnvironment) :
    MatchingAtom → AtomReduction → Prop where
  | matcher
      (clausesDispatch :
        MatcherClausesDispatch eval atomEnvironment matcherEnvironment
          pattern target remaining (.hit branches)) :
      MatcherAtomReduces eval atomEnvironment
        ⟨pattern, .matcherV matcherEnvironment original remaining, target⟩
        ⟨branches, []⟩

theorem tryMatcherArm_eq_ok_iff
    (eval : ValueEnvironment → Expr → FuelResult Value)
    (matcherEnvironment captureValues : ValueEnvironment)
    (holes : List Pattern) (nextMatchers : Expr) (target : Value)
    (arm : MatcherArm) (result : DispatchResult MatchingBranches) :
    tryMatcherArm eval matcherEnvironment captureValues holes nextMatchers
        target arm = .ok result ↔
      MatcherArmDispatches eval matcherEnvironment captureValues holes
        nextMatchers target arm result := by
  cases arm with
  | mk header body =>
      constructor
      · intro success
        simp only [tryMatcherArm] at success
        cases dataMatch : matchValueDataPattern header target with
        | none =>
            simp [dataMatch] at success
            subst result
            exact .miss dataMatch
        | some dataValues =>
            simp only [dataMatch] at success
            rw [FuelResult.bind_eq_ok_iff] at success
            rcases success with ⟨decompositionValue, bodyEval, continued⟩
            cases decompositionShape :
                decodeDecompositions holes.length decompositionValue with
            | none => simp [decompositionShape] at continued
            | some decompositions =>
                simp only [decompositionShape] at continued
                rw [FuelResult.bind_eq_ok_iff] at continued
                rcases continued with ⟨matcherProduct, matcherEval, completed⟩
                cases matcherShape : decodeProduct holes.length matcherProduct with
                | none => simp [matcherShape] at completed
                | some matchers =>
                    cases branchesBuilt :
                        buildMatchingBranches holes matchers decompositions with
                    | none => simp [matcherShape, branchesBuilt] at completed
                    | some branches =>
                        simp [matcherShape, branchesBuilt] at completed
                        subst result
                        exact .hit dataMatch bodyEval decompositionShape matcherEval
                          matcherShape branchesBuilt
      · intro dispatch
        cases dispatch with
        | miss mismatch => simp [tryMatcherArm, mismatch]
        | hit dataMatch bodyEval decompositionShape matcherEval matcherShape
            branchesBuilt =>
            simp only [tryMatcherArm, dataMatch]
            rw [bodyEval]
            simp only [FuelResult.bind_ok]
            rw [decompositionShape]
            rw [matcherEval]
            simp only [FuelResult.bind_ok]
            simp only [matcherShape, branchesBuilt]

theorem firstHit_arms_eq_ok_iff
    (eval : ValueEnvironment → Expr → FuelResult Value)
    (matcherEnvironment captureValues : ValueEnvironment)
    (holes : List Pattern) (nextMatchers : Expr) (target : Value)
    (arms : List MatcherArm) (result : DispatchResult MatchingBranches) :
    firstHit
        (tryMatcherArm eval matcherEnvironment captureValues holes nextMatchers
          target) arms = .ok result ↔
      MatcherArmsDispatch eval matcherEnvironment captureValues holes
        nextMatchers target arms result := by
  constructor
  · intro success
    have ordered := firstHit_sound success
    induction ordered with
    | nil => exact .nil
    | hit selected =>
        exact .hit ((tryMatcherArm_eq_ok_iff _ _ _ _ _ _ _ _).mp selected)
    | skip missed tail ih =>
        exact .skip
          ((tryMatcherArm_eq_ok_iff _ _ _ _ _ _ _ _).mp missed)
          (ih (FirstHit.complete tail))
  · intro dispatch
    induction dispatch with
    | nil => rfl
    | hit selected =>
        simp [firstHit,
          (tryMatcherArm_eq_ok_iff _ _ _ _ _ _ _ _).mpr selected]
    | skip missed tail ih =>
        simp [firstHit,
          (tryMatcherArm_eq_ok_iff _ _ _ _ _ _ _ _).mpr missed, ih]

theorem tryMatcherClause_eq_ok_iff
    (eval : ValueEnvironment → Expr → FuelResult Value)
    (atomEnvironment matcherEnvironment : ValueEnvironment)
    (pattern : Pattern) (target : Value) (clause : MatcherClause)
    (result : DispatchResult MatchingBranches) :
    tryMatcherClause eval atomEnvironment matcherEnvironment pattern target
        clause = .ok result ↔
      MatcherClauseDispatches eval atomEnvironment matcherEnvironment pattern
        target clause result := by
  cases clause with
  | mk header nextMatchers arms =>
      constructor
      · intro success
        simp only [tryMatcherClause] at success
        cases headerMatch : inspectPatternPattern header pattern with
        | none =>
            simp [headerMatch] at success
            subst result
            exact .miss headerMatch
        | some dispatch =>
            simp only [headerMatch] at success
            rw [FuelResult.bind_eq_ok_iff] at success
            rcases success with ⟨captureValues, capturesEval, continued⟩
            rw [FuelResult.map_eq_ok_iff] at continued
            rcases continued with ⟨armsResult, armResult, output⟩
            subst result
            exact .matched (inspectPatternPattern_sound headerMatch)
              ((FuelResult.traverse_eq_ok_iff _ _ _).mp capturesEval)
              ((firstHit_arms_eq_ok_iff _ _ _ _ _ _ _ _).mp armResult)
      · intro dispatch
        cases dispatch with
        | miss mismatch => simp [tryMatcherClause, mismatch]
        | matched headerMatch capturesEval armsDispatch =>
            have inspected := PatternPatternMatches.complete headerMatch
            have evaluated :=
              (FuelResult.traverse_eq_ok_iff _ _ _).mpr capturesEval
            have armsRan :=
              (firstHit_arms_eq_ok_iff _ _ _ _ _ _ _ _).mpr armsDispatch
            simp [tryMatcherClause, inspected, evaluated, armsRan,
              closeMatcherArmsResult]

theorem dispatchMatcherClauses_eq_ok_iff
    (eval : ValueEnvironment → Expr → FuelResult Value)
    (atomEnvironment matcherEnvironment : ValueEnvironment)
    (clauses : List MatcherClause) (pattern : Pattern) (target : Value)
    (result : DispatchResult MatchingBranches) :
    dispatchMatcherClauses eval atomEnvironment matcherEnvironment clauses
        pattern target = .ok result ↔
      MatcherClausesDispatch eval atomEnvironment matcherEnvironment pattern
        target clauses result := by
  constructor
  · intro success
    have ordered := firstHit_sound success
    induction ordered with
    | nil => exact .nil
    | hit selected =>
        exact .hit ((tryMatcherClause_eq_ok_iff _ _ _ _ _ _ _).mp selected)
    | skip missed tail ih =>
        exact .skip
          ((tryMatcherClause_eq_ok_iff _ _ _ _ _ _ _).mp missed)
          (ih (FirstHit.complete tail))
  · intro dispatch
    induction dispatch with
    | nil => rfl
    | hit selected =>
        simp [dispatchMatcherClauses, firstHit,
          (tryMatcherClause_eq_ok_iff _ _ _ _ _ _ _).mpr selected]
    | skip missed tail ih =>
        simp [dispatchMatcherClauses, firstHit,
          (tryMatcherClause_eq_ok_iff _ _ _ _ _ _ _).mpr missed]
        simpa [dispatchMatcherClauses] using ih

theorem reduceMatcherAtom_hit_iff
    (eval : ValueEnvironment → Expr → FuelResult Value)
    (atomEnvironment : ValueEnvironment) (atom : MatchingAtom)
    (reduction : AtomReduction) :
    reduceMatcherAtom eval atomEnvironment atom = .ok (.hit reduction) ↔
      MatcherAtomReduces eval atomEnvironment atom reduction := by
  rcases atom with ⟨pattern, matcher, target⟩
  cases matcher <;> simp only [reduceMatcherAtom]
  case matcherV matcherEnvironment original remaining =>
    constructor
    · intro success
      rw [FuelResult.map_eq_ok_iff] at success
      rcases success with ⟨outcome, dispatched, converted⟩
      cases outcome with
      | miss => simp [clauseResultToAtomReduction] at converted
      | hit branches =>
          simp [clauseResultToAtomReduction] at converted
          subst reduction
          exact .matcher
            ((dispatchMatcherClauses_eq_ok_iff _ _ _ _ _ _ _).mp dispatched)
    · intro related
      cases related with
      | matcher clausesDispatch =>
          have dispatched :=
            (dispatchMatcherClauses_eq_ok_iff _ _ _ _ _ _ _).mpr
              clausesDispatch
          simp [FuelResult.map, dispatched, clauseResultToAtomReduction]
  all_goals
    constructor
    · intro impossible
      simp at impossible
    · intro impossible
      cases impossible

end TypePM.Runtime
