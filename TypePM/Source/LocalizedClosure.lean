import TypePM.Source.Elaboration
import TypePM.BlockClosureSupport

/-!
# Locality evidence carried by source closure witnesses

The source relation already requires every `letE` and root closure to be
absorbing.  Absorption semantically implies localization, so adding another
field to the core relation would duplicate evidence and disrupt transport
theorems without strengthening the judgment.
-/

namespace TypePM.Source

/-- Every root principal typing derivation carries a closure confined to the
finite support of its generated block. -/
theorem PrincipalTypingDerivation.closure_localized
    {context : Context} {expression : Expr} {target : Ty}
    (derivation : PrincipalTypingDerivation context expression target) :
    derivation.closure.Localized :=
  derivation.closure.localized_of_absorbing derivation.absorbing

/-- Existential principal typing exposes the same localized closure witness. -/
theorem PrincipalTyping.localizedClosure
    {context : Context} {expression : Expr} {target : Ty}
    (principal : PrincipalTyping context expression target) :
    ∃ derivation : PrincipalTypingDerivation context expression target,
      derivation.closure.Localized := by
  rcases principal with ⟨derivation⟩
  exact ⟨derivation, derivation.closure_localized⟩

end TypePM.Source
