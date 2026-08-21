import TypePM.Source.GeneralizedOccurrenceSolution
import TypePM.Source.M4LetRuntimeWorldStepRegression

/-!
# Regression for generalized occurrence solutions

The main fixture has an open monomorphic context containing `α0` and an
otherwise unconstrained right-hand-side target containing `α1`.  Generalizing
the exact identity-substitution principal closure keeps `α0` free and binds `α1`.
Different occurrence supplies therefore leave `α0` unchanged while selecting
different fresh representatives for `α1`.

The final fixture records why the module's context guarantee is scheme-level.
A polymorphic scheme is unchanged by `Scheme.applyFree`, yet opening its bound
variable at a colliding supply can expose a substitution difference.
-/

namespace TypePM.Source.GeneralizedOccurrenceSolutionRegression

def outerFree : TyVar := ⟨0⟩

def generalized : TyVar := ⟨1⟩

def openContext : Context := [.mono (.var outerFree)]

def rhsTarget : Ty := .prod [.var outerFree, .fn (.var generalized) (.var generalized)]

def rhsGenerated : Generated :=
  { target := rhsTarget
    hard := []
    pending := [] }

theorem idMostGeneralNil : MostGeneral [] Subst.id := by
  constructor
  · exact solves_nil _
  · intro solution _solved
    exact ⟨solution, by simp⟩

theorem idAbsorbingNil : AbsorbingPrincipal [] Subst.id := by
  constructor
  · exact idMostGeneralNil
  · intro solution _solved
    simp

def rhsClosure : PrincipalBlockClosure rhsGenerated :=
  { finalHard := []
    finalPending := []
    hardSubstitution := Subst.id
    residualSubstitution := Subst.id
    saturation :=
      { closure := .refl
        principal := idMostGeneralNil
        stable := by simp [promoteUnder] }
    residualPrincipal := by
      simpa [residualEquations] using idMostGeneralNil }

@[simp] theorem rhsClosure_substitution :
    rhsClosure.substitution = Subst.id := by
  rfl

@[simp] theorem rhsClosure_target : rhsClosure.target = rhsTarget := by
  change rhsGenerated.target.apply rhsClosure.substitution = rhsTarget
  rw [rhsClosure_substitution]
  simp [rhsGenerated]

@[simp] theorem closedContext_eq :
    openContext.applyFree rhsClosure.substitution = openContext := by
  rw [rhsClosure_substitution]
  exact Context.applyFree_id openContext

@[simp] theorem openContext_generalizedTyVars :
    openContext.generalizedTyVars rhsTarget = [generalized] := by
  decide

@[simp] theorem openContext_generalizedCapVars :
    openContext.generalizedCapVars rhsTarget = [] := by
  decide

@[simp] theorem closedContext_generalizedTyVars :
    (openContext.applyFree rhsClosure.substitution).generalizedTyVars
      rhsClosure.target = [generalized] := by
  rw [closedContext_eq, rhsClosure_target]
  exact openContext_generalizedTyVars

@[simp] theorem closedContext_generalizedCapVars :
    (openContext.applyFree rhsClosure.substitution).generalizedCapVars
      rhsClosure.target = [] := by
  rw [closedContext_eq, rhsClosure_target]
  exact openContext_generalizedCapVars

theorem rhsClosureAbsorbing : rhsClosure.Absorbing := by
  constructor
  · exact idAbsorbingNil
  · simpa [rhsClosure, residualEquations] using idAbsorbingNil

theorem outerSolvesInterface :
    Solves Subst.id
      (openContext.interfaceEquations rhsClosure.substitution) := by
  apply (openContext.solves_interfaceEquations_iff rhsClosure.substitution
    Subst.id).mpr
  constructor <;> intro index membership <;>
    simp [rhsClosure, PrincipalBlockClosure.substitution, Subst.compose]

def firstSupply : Supply := ⟨10, 20⟩

def secondSupply : Supply := ⟨30, 40⟩

def firstOccurrence :
    GeneralizedOccurrenceSolution openContext rhsClosure Subst.id firstSupply :=
  TypePM.Source.PrincipalBlockClosure.generalizedOccurrenceSolution rhsClosure
    rhsClosureAbsorbing openContext Subst.id outerSolvesInterface firstSupply

def secondOccurrence :
    GeneralizedOccurrenceSolution openContext rhsClosure Subst.id secondSupply :=
  TypePM.Source.PrincipalBlockClosure.generalizedOccurrenceSolution rhsClosure
    rhsClosureAbsorbing openContext Subst.id outerSolvesInterface secondSupply

/-- The open-context variable remains fixed, while the generalized variable
is renamed to the fresh name selected by each occurrence supply. -/
theorem freeFixed_generalizedChanges :
    firstOccurrence.solution.ty outerFree = .var outerFree ∧
      secondOccurrence.solution.ty outerFree = .var outerFree ∧
      firstOccurrence.solution.ty generalized = .var ⟨10⟩ ∧
      secondOccurrence.solution.ty generalized = .var ⟨30⟩ := by
  simp [firstOccurrence, secondOccurrence,
    TypePM.Source.PrincipalBlockClosure.generalizedOccurrenceSolution,
    Context.generalizedOccurrencePostSubstitution, firstSupply, secondSupply,
    outerFree, generalized]
  simp [Subst.id, Scheme.boundTyInstance]

/-- Both occurrence-specific substitutions solve the exact RHS block and
identify its target with their respective generalized scheme occurrence. -/
theorem semanticAndTargetEvidence :
    rhsGenerated.SemanticSolution firstOccurrence.solution ∧
      rhsGenerated.target.apply firstOccurrence.solution =
        (((openContext.applyFree rhsClosure.substitution).generalize
          rhsClosure.target).instantiate firstSupply).1.apply Subst.id ∧
      rhsGenerated.SemanticSolution secondOccurrence.solution ∧
      rhsGenerated.target.apply secondOccurrence.solution =
        (((openContext.applyFree rhsClosure.substitution).generalize
          rhsClosure.target).instantiate secondSupply).1.apply Subst.id := by
  exact ⟨firstOccurrence.semantic, firstOccurrence.target_eq,
    secondOccurrence.semantic, secondOccurrence.target_eq⟩

/-- The constructed child solutions preserve the exact open source context. -/
theorem openContextPreserved :
    openContext.applyFree firstOccurrence.solution =
        openContext.applyFree Subst.id ∧
      openContext.applyFree secondOccurrence.solution =
        openContext.applyFree Subst.id :=
  ⟨firstOccurrence.context_eq, secondOccurrence.context_eq⟩

def exactM4OccurrenceSupply : Supply := ⟨50, 0⟩

/-- The wrapper is inhabited by the exact RHS closure stored in the existing
public M4 `letE` runtime world. -/
theorem exactM4World_constructsOccurrenceSolution :
    ∃ fuel,
      ∃ world : M4.LetRuntimeWorld
        (signature := Paper1FrozenSignature.signature)
        (context := []) (value := .lam (.var 0))
        (body := M4LetRuntimeWorldStepRegression.body)
        (supply := Context.initialSupply [])
        (generated := M4LetRuntimeWorldStepRegression.derivation.generated)
        (next := M4LetRuntimeWorldStepRegression.derivation.next)
        fuel
        M4LetRuntimeWorldStepRegression.derivation.closure.substitution [] [],
      Nonempty
        (GeneralizedOccurrenceSolution [] world.valueClosure
          M4LetRuntimeWorldStepRegression.derivation.closure.substitution
          exactM4OccurrenceSupply) := by
  obtain ⟨fuel, ⟨world⟩⟩ := M4LetRuntimeWorldStepRegression.runtimeWorld
  exact ⟨fuel, world,
    ⟨M4.LetRuntimeWorld.generalizedOccurrenceSolution world
      exactM4OccurrenceSupply⟩⟩

def polymorphicIdentity : Scheme :=
  { tyArity := 1
    capArity := 0
    body := .bound 0
    wellScoped := by simp [PolyTy.WellScoped] }

def collidingSupply : Supply := ⟨0, 0⟩

def collisionChild : Subst := Subst.singleTy ⟨0⟩ (.var ⟨1⟩)

/-- Scheme-level equality does not imply equality after an arbitrary
colliding instantiation supply.  The bound body has no free variable, but
opening it at `α0` exposes the change made by `collisionChild`. -/
theorem schemeLevel_not_unconditionalOccurrenceLevel :
    polymorphicIdentity.applyFree collisionChild =
        polymorphicIdentity.applyFree Subst.id ∧
      (polymorphicIdentity.instantiate collidingSupply).1.apply
          collisionChild ≠
        (polymorphicIdentity.instantiate collidingSupply).1.apply Subst.id := by
  constructor
  · rfl
  · simp [polymorphicIdentity, collidingSupply, collisionChild,
      Scheme.instantiate, Scheme.boundTyInstance, PolyTy.openBound, Ty.apply,
      Subst.singleTy, Subst.id]

end TypePM.Source.GeneralizedOccurrenceSolutionRegression
