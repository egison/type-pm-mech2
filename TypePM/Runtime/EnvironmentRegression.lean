import TypePM.Runtime.Environment

/-!
# Regressions for newest-first runtime environments
-/

namespace TypePM.Runtime.EnvironmentRegression

theorem newest_exact : ([30, 20, 10] : Environment Nat)[0]? = some 30 := by
  rfl

theorem older_exact : ([30, 20, 10] : Environment Nat)[2]? = some 10 := by
  rfl

theorem out_of_bounds_exact :
    ([30, 20, 10] : Environment Nat)[3]? = none := by
  rfl

theorem older_relational :
    Lookup ([30, 20, 10] : Environment Nat) 2 10 :=
  (getElem?_eq_some_iff_lookup [30, 20, 10] 2 10).mp older_exact

theorem weakening_shifts_index :
    Lookup ([40, 30, 20, 10] : Environment Nat) 3 10 :=
  older_relational.weaken 40

theorem lookup_is_deterministic
    (left : Lookup ([30, 20, 10] : Environment Nat) 1 leftValue)
    (right : Lookup ([30, 20, 10] : Environment Nat) 1 rightValue) :
    leftValue = rightValue :=
  left.deterministic right

end TypePM.Runtime.EnvironmentRegression
