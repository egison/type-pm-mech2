import TypePM.Regression

/-!
# Axiom audit for M0

These commands make the trusted assumptions of selected M0 results visible in
every full build.
-/

#print axioms TypePM.Cap.apply_compose
#print axioms TypePM.Ty.apply_compose
#print axioms TypePM.Regression.pair_principal
#print axioms TypePM.Regression.pair_checks_as_slot
#print axioms TypePM.Regression.structured_matcher_checks_at_any_slot
