import TypePM.Source.M4EnvironmentIndexedRecursiveSearchBridge

/-!
# Relation-parametric producer for environment-indexed recursive search

`M4EnvironmentIndexedRecursiveSearchBridge` reduces bounded DFS safety to
local reducer certificates, while the older M4 recursive-work relation fixes
its atom judgment to `FuelIndexedRecursiveMatchingAtomTyping`.  In particular,
that judgment's `user` constructor still asks for old `EnvironmentTyping` on
the runtime atom environment.

This module factors the producer through a caller-selected relation for one
atom.  The only structural requirement is downward closure in the search-fuel
index.  A local reducer law consumes one atom at index `fuel + 1` and, on a
hit, returns branch work at exactly `fuel`.  The producer appends each branch
before the old tail, prepends immediate bindings before the ordinary
environment at runtime, and recursively checks the successor at that strict
predecessor index.  Neither the local law nor the work relation contains a
complete-search result or an environment-indexed successor certificate.

An adapter embeds the existing M4 work family.  It is useful for ordinary
environments but does not remove the old `EnvironmentTyping` premise hidden
in that family's `user` constructor.  A fully M4-generated instance for a
recursive-closure invariant therefore still needs a relational user-work
constructor and a corresponding evaluator/dispatcher preservation theorem.
-/

namespace TypePM.Runtime

open TypePM.Source

/-- A fuel-, environment-, and binding-indexed relation for one matching
atom and the types of the bindings that it eventually contributes. -/
abbrev FuelIndexedMatchingAtomRelation :=
  Nat → List Ty → List Ty → MatchingAtom → List Ty → Prop

namespace FuelIndexedMatchingAtomRelation

/-- One available atom visit may be forgotten.  The two displayed indices
are the successor-state indices used by the work relation. -/
def DownwardClosed (atomRelation : FuelIndexedMatchingAtomRelation) : Prop :=
  ∀ {fuel environmentTypes bindingTypes atom newBindings},
    atomRelation (fuel + 2) environmentTypes bindingTypes atom newBindings →
    atomRelation (fuel + 1) environmentTypes bindingTypes atom newBindings

end FuelIndexedMatchingAtomRelation

/-- Pending work for a caller-selected atom relation.  Nonempty work is
unconditional at index zero because bounded DFS times out before inspecting
the state.  At a successor index the head is checked there and the tail at
the strict predecessor. -/
inductive RelationalFuelIndexedMatchingAtomsTyping
    (atomRelation : FuelIndexedMatchingAtomRelation) :
    Nat → List Ty → List Ty → List MatchingAtom → List Ty → Prop where
  | zero
      (nonempty : atoms ≠ []) :
      RelationalFuelIndexedMatchingAtomsTyping atomRelation 0 environmentTypes
        bindingTypes atoms newBindings
  | nil :
      RelationalFuelIndexedMatchingAtomsTyping atomRelation fuel
        environmentTypes bindingTypes [] []
  | cons
      (head : atomRelation (fuel + 1) environmentTypes bindingTypes atom
        headBindings)
      (tail : RelationalFuelIndexedMatchingAtomsTyping atomRelation fuel
        environmentTypes (bindingTypes ++ headBindings) atoms tailBindings) :
      RelationalFuelIndexedMatchingAtomsTyping atomRelation (fuel + 1)
        environmentTypes bindingTypes (atom :: atoms)
        (headBindings ++ tailBindings)

namespace RelationalFuelIndexedMatchingAtomsTyping

/-- Pending relational work is downward closed whenever its atom relation is
downward closed. -/
theorem previous
    (downward : FuelIndexedMatchingAtomRelation.DownwardClosed atomRelation)
    (typing : RelationalFuelIndexedMatchingAtomsTyping atomRelation (fuel + 1)
      environmentTypes bindingTypes atoms newBindings) :
    RelationalFuelIndexedMatchingAtomsTyping atomRelation fuel environmentTypes
      bindingTypes atoms newBindings := by
  induction fuel generalizing bindingTypes atoms newBindings with
  | zero =>
      cases typing with
      | nil => exact .nil
      | cons head tail => exact .zero (by simp)
  | succ fuel induction =>
      cases typing with
      | nil => exact .nil
      | cons head tail =>
          exact .cons (downward head) (induction tail)

/-- Concatenate two worklists at one DFS bound.  Each atom in the left list
uses one visit, so the right list is weakened before recursive appending. -/
theorem append
    (downward : FuelIndexedMatchingAtomRelation.DownwardClosed atomRelation) :
    ∀ fuel {bindingTypes leftAtoms leftBindings},
      RelationalFuelIndexedMatchingAtomsTyping atomRelation fuel
        environmentTypes bindingTypes leftAtoms leftBindings →
      ∀ {rightAtoms rightBindings},
        RelationalFuelIndexedMatchingAtomsTyping atomRelation fuel
          environmentTypes (bindingTypes ++ leftBindings)
          rightAtoms rightBindings →
        RelationalFuelIndexedMatchingAtomsTyping atomRelation fuel
          environmentTypes bindingTypes (leftAtoms ++ rightAtoms)
          (leftBindings ++ rightBindings) := by
  intro fuel
  induction fuel with
  | zero =>
      intro bindingTypes leftAtoms leftBindings left rightAtoms rightBindings
        right
      cases left with
      | zero nonempty => exact .zero (by simp [nonempty])
      | nil => simpa using right
  | succ fuel induction =>
      intro bindingTypes leftAtoms leftBindings left rightAtoms rightBindings
        right
      cases left with
      | nil => simpa using right
      | cons head tail =>
          rename_i atom headBindings atoms tailBindings
          have right' : RelationalFuelIndexedMatchingAtomsTyping atomRelation
              fuel environmentTypes
              ((bindingTypes ++ headBindings) ++ tailBindings)
              rightAtoms rightBindings := by
            simpa [List.append_assoc] using right.previous downward
          have combined := induction tail right'
          simpa [List.append_assoc] using
            (RelationalFuelIndexedMatchingAtomsTyping.cons head combined)

end RelationalFuelIndexedMatchingAtomsTyping

/-- Preservation data for one successful reduction.  Immediate bindings are
ordinary values; every returned branch carries relational work at the strict
predecessor index. -/
inductive RelationalFuelIndexedAtomReductionTyping
    (atomRelation : FuelIndexedMatchingAtomRelation)
    (fuel : Nat) (environmentTypes bindingTypes expectedBindings : List Ty)
    (reduction : AtomReduction) : Prop where
  | intro
      (immediateTypes : List Ty)
      (immediateTyped : ValueTypings reduction.bindings immediateTypes)
      (branchesTyped : ∀ branch ∈ reduction.branches,
        ∃ delayedTypes,
          RelationalFuelIndexedMatchingAtomsTyping atomRelation fuel
            environmentTypes (bindingTypes ++ immediateTypes)
            branch delayedTypes ∧
          immediateTypes ++ delayedTypes = expectedBindings) :
      RelationalFuelIndexedAtomReductionTyping atomRelation fuel
        environmentTypes bindingTypes expectedBindings reduction

/-- Local timeout-or-hit preservation under an arbitrary ordinary-environment
invariant.  Runtime atom environments are always `bindings ++ environment`.
The hit premise exposes only immediate relational branch work, not successor
state typing or a result of the complete DFS search. -/
def EnvironmentIndexedRelationalAtomReducerTypedSafe
    (environmentInvariant : MatchingEnvironmentInvariant)
    (atomRelation : FuelIndexedMatchingAtomRelation)
    (reduceAtom : AtomReducer) : Prop :=
  ∀ {fuel environmentTypes bindingTypes environment bindings atom
      newBindings},
    environmentInvariant environment environmentTypes →
    ValueTypings bindings bindingTypes →
    atomRelation (fuel + 1) environmentTypes bindingTypes atom newBindings →
    reduceAtom (bindings ++ environment) atom = .timeout ∨
      ∃ reduction,
        reduceAtom (bindings ++ environment) atom = .ok (.hit reduction) ∧
        RelationalFuelIndexedAtomReductionTyping atomRelation fuel
          environmentTypes bindingTypes newBindings reduction

namespace RelationalFuelIndexedMatchingAtomsTyping

/-- Produce the state certificate consumed by the generic environment-indexed
DFS theorem.  Successful reduction work is ordered `branch ++ remaining`, and
its immediate bindings are ordered `bindings ++ reduction.bindings`. -/
theorem toEnvironmentIndexedState
    (downward : FuelIndexedMatchingAtomRelation.DownwardClosed atomRelation)
    (reducerSafe : EnvironmentIndexedRelationalAtomReducerTypedSafe
      environmentInvariant atomRelation reduceAtom)
    (environmentTyped : environmentInvariant environment environmentTypes)
    (bindingsTyped : ValueTypings bindings bindingTypes)
    (workTyped : RelationalFuelIndexedMatchingAtomsTyping atomRelation fuel
      environmentTypes bindingTypes work futureBindings) :
    EnvironmentIndexedMatchingStateTyping environmentInvariant reduceAtom fuel
      ⟨work, environment, bindings⟩ (bindingTypes ++ futureBindings) := by
  induction fuel generalizing environment bindings bindingTypes work
      futureBindings with
  | zero => exact .zero
  | succ fuel induction =>
      cases workTyped with
      | nil =>
          simpa using
            (EnvironmentIndexedMatchingStateTyping.yield
              environmentTyped bindingsTyped)
      | cons headTyped tailTyped =>
          rename_i atom headBindings atoms tailBindings
          apply EnvironmentIndexedMatchingStateTyping.reduce
            environmentTyped bindingsTyped
          rcases reducerSafe environmentTyped bindingsTyped headTyped with
            timeout | ⟨reduction, reduced, reductionTyped⟩
          · exact .timeout timeout
          · cases reductionTyped with
            | intro immediateTypes immediateTyped branchesTyped =>
                apply EnvironmentIndexedAtomReducerCertificate.hit reduction
                  reduced
                intro successor successorMember
                simp only [MatchingState.successors] at successorMember
                rcases List.mem_map.mp successorMember with
                  ⟨branch, branchMember, rfl⟩
                obtain ⟨delayedTypes, branchTyped, bindingEq⟩ :=
                  branchesTyped branch branchMember
                have branchAndTail :=
                  RelationalFuelIndexedMatchingAtomsTyping.append downward fuel
                    branchTyped (by
                      simpa [List.append_assoc, bindingEq] using tailTyped)
                have newBindingsTyped := bindingsTyped.append immediateTyped
                have successorTyped := induction environmentTyped
                  newBindingsTyped branchAndTail
                have answerEq :
                    (bindingTypes ++ immediateTypes) ++
                        (delayedTypes ++ tailBindings) =
                      bindingTypes ++ (headBindings ++ tailBindings) := by
                  simp only [List.append_assoc]
                  rw [← List.append_assoc immediateTypes delayedTypes,
                    bindingEq]
                rw [answerEq] at successorTyped
                exact successorTyped

end RelationalFuelIndexedMatchingAtomsTyping

namespace EnvironmentIndexedAtomReducerCertificate

/-- Produce the one-step environment-indexed certificate from relational head
and tail work. -/
theorem ofRelationalFuelIndexedWork
    (downward : FuelIndexedMatchingAtomRelation.DownwardClosed atomRelation)
    (reducerSafe : EnvironmentIndexedRelationalAtomReducerTypedSafe
      environmentInvariant atomRelation reduceAtom)
    (environmentTyped : environmentInvariant environment environmentTypes)
    (bindingsTyped : ValueTypings bindings bindingTypes)
    (headTyped : atomRelation (fuel + 1) environmentTypes bindingTypes atom
      headBindings)
    (tailTyped : RelationalFuelIndexedMatchingAtomsTyping atomRelation fuel
      environmentTypes (bindingTypes ++ headBindings) remaining tailBindings) :
    EnvironmentIndexedAtomReducerCertificate environmentInvariant reduceAtom
      fuel environment bindings atom remaining
      (bindingTypes ++ (headBindings ++ tailBindings)) := by
  have stateTyped :=
    RelationalFuelIndexedMatchingAtomsTyping.toEnvironmentIndexedState
      downward reducerSafe environmentTyped bindingsTyped
      (RelationalFuelIndexedMatchingAtomsTyping.cons headTyped tailTyped)
  cases stateTyped with
  | reduce environmentTyped bindingsTyped atomSafe => exact atomSafe

end EnvironmentIndexedAtomReducerCertificate

/-- Initial-search endpoint derived solely from relational work and the local
reducer law. -/
theorem searchPatternFuel_environmentIndexedRelationalTypedSafe
    (downward : FuelIndexedMatchingAtomRelation.DownwardClosed atomRelation)
    (reducerSafe : EnvironmentIndexedRelationalAtomReducerTypedSafe
      environmentInvariant atomRelation (evaluationAtomReducer eval))
    (environmentTyped : environmentInvariant environment environmentTypes)
    (workTyped : RelationalFuelIndexedMatchingAtomsTyping atomRelation fuel
      environmentTypes [] [⟨pattern, matcher, target⟩] bindingTypes) :
    TypedMatchingSearchResult bindingTypes
      (searchPatternFuel eval fuel environment pattern matcher target) := by
  apply searchPatternFuel_environmentIndexedTypedSafe
    (environmentInvariant := environmentInvariant)
  simpa using
    (RelationalFuelIndexedMatchingAtomsTyping.toEnvironmentIndexedState
      downward reducerSafe environmentTyped (.nil) workTyped)

/-- The existing M4 atom family viewed as an instance of the relational
interface.  Its `user` cases still retain their old atom-environment typing
premise. -/
abbrev ExistingFuelIndexedRecursiveAtomRelation
    (expressionTyping : EmbeddedExpressionTyping)
    (eval : ValueEnvironment → Source.Expr → FuelResult Value) :
    FuelIndexedMatchingAtomRelation :=
  fun fuel environmentTypes bindingTypes atom newBindings =>
    FuelIndexedRecursiveMatchingAtomTyping expressionTyping eval fuel
      environmentTypes bindingTypes atom newBindings

theorem existingFuelIndexedRecursiveAtomRelation_downwardClosed :
    FuelIndexedMatchingAtomRelation.DownwardClosed
      (ExistingFuelIndexedRecursiveAtomRelation expressionTyping eval) := by
  intro fuel environmentTypes bindingTypes atom newBindings typed
  exact typed.previous

namespace RelationalFuelIndexedMatchingAtomsTyping

/-- Embed existing bounded M4 work into the relation-parametric work family.
This adapter does not manufacture new user-atom evidence. -/
theorem ofFuelIndexedRecursive :
    ∀ fuel {environmentTypes bindingTypes atoms newBindings},
      FuelIndexedRecursiveMatchingAtomsTyping expressionTyping eval fuel
        environmentTypes bindingTypes atoms newBindings →
      RelationalFuelIndexedMatchingAtomsTyping
        (ExistingFuelIndexedRecursiveAtomRelation expressionTyping eval) fuel
        environmentTypes bindingTypes atoms newBindings := by
  intro fuel
  induction fuel with
  | zero =>
      intro environmentTypes bindingTypes atoms newBindings typing
      cases typing with
      | zero nonempty => exact .zero nonempty
      | nil => exact .nil
  | succ fuel induction =>
      intro environmentTypes bindingTypes atoms newBindings typing
      cases typing with
      | nil => exact .nil
      | cons head tail => exact .cons head (induction tail)

end RelationalFuelIndexedMatchingAtomsTyping

end TypePM.Runtime
