import TypePM.Solver
import TypePM.UnificationTermination

/-!
# Certified executable hard solver

The total two-sort unifier implements the abstract solver interface used by
the saturation and inference developments.  Its public result is principal,
and solvability is sufficient for executable success.
-/

namespace TypePM

/-- The fuel-free executable unifier is a complete most-general-unifier
solver. -/
theorem unify_completeMGUSolver : CompleteMGUSolver unify := by
  constructor
  · intro equations substitution success
    exact unify_mostGeneral success
  · intro equations solvable
    exact unify_complete solvable

end TypePM
