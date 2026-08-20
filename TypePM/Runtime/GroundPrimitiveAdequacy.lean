import TypePM.Runtime.GroundPrimitive

/-!
# Relational ground-primitive specifications

The relations in this module do not call the primitive evaluator.  They state
the successful graphs of the five operations using canonical data encodings,
ordinary list membership/append, `DeletesFirst` from ordered-choice semantics,
and the relational `Traverses` graph of the callback used by `map`.
-/

namespace TypePM.Runtime

open GroundValue FuelResult

/-- A ground value is the canonical `nil`/`cons` encoding of these items. -/
inductive EncodesList : List GroundValue → GroundValue → Prop where
  | nil : EncodesList [] nilValue
  | cons {head : GroundValue} {tail : List GroundValue} {tailValue : GroundValue} :
      EncodesList tail tailValue →
      EncodesList (head :: tail) (consValue head tailValue)

namespace EncodesList

theorem view (encoding : EncodesList items value) :
    value.viewList = some items := by
  induction encoding with
  | nil => exact GroundValue.viewList_buildList []
  | cons tailEncoding ih =>
      simp [GroundValue.consValue, GroundValue.dataValue,
        GroundValues.ofList, GroundValue.viewList, ih]

theorem of_view {value : GroundValue} {items : List GroundValue}
    (result : value.viewList = some items) : EncodesList items value := by
  cases value with
  | int value => simp [GroundValue.viewList] at result
  | tuple tupleItems => simp [GroundValue.viewList] at result
  | data constructor arguments =>
      cases arguments with
      | nil =>
          by_cases canonical : constructor = DataCtor.nil
          · subst constructor
            simp [GroundValue.viewList] at result
            subst items
            exact .nil
          · simp [GroundValue.viewList, canonical] at result
      | cons head remaining =>
          cases remaining with
          | nil => simp [GroundValue.viewList] at result
          | cons tail trailing =>
              cases trailing with
              | nil =>
                  by_cases canonical : constructor = DataCtor.cons
                  · subst constructor
                    simp only [GroundValue.viewList, ↓reduceIte] at result
                    cases tailResult : tail.viewList with
                    | none => simp [tailResult] at result
                    | some tailItems =>
                        simp [tailResult] at result
                        subst items
                        exact .cons (of_view tailResult)
                  · simp [GroundValue.viewList, canonical] at result
              | cons next rest => simp [GroundValue.viewList] at result

theorem view_iff {value : GroundValue} {items : List GroundValue} :
    value.viewList = some items ↔ EncodesList items value :=
  ⟨of_view, view⟩

theorem deterministic
    (left : EncodesList leftItems value)
    (right : EncodesList rightItems value) :
    leftItems = rightItems := by
  rw [← Option.some.injEq, ← left.view, ← right.view]

end EncodesList

namespace GroundPrimitive

/-- Independent successful specification of `add`. -/
def Adds (arguments : List GroundValue) (result : GroundValue) : Prop :=
  ∃ left right, arguments = [.int left, .int right] ∧
    result = .int (left + right)

/-- Independent successful specification of `append`. -/
def Appends (arguments : List GroundValue) (result : GroundValue) : Prop :=
  ∃ leftValue rightValue leftItems rightItems,
    arguments = [leftValue, rightValue] ∧
    EncodesList leftItems leftValue ∧
    EncodesList rightItems rightValue ∧
    result = buildList (leftItems ++ rightItems)

/-- Independent successful specification of `member`. -/
def TestsMember (arguments : List GroundValue) (result : GroundValue) : Prop :=
  ∃ needle target items,
    arguments = [needle, target] ∧
    EncodesList items target ∧
    result = ofBool (needle ∈ items)

/-- Independent successful specification of first-occurrence deletion.
The second branch is the standard unchanged-list result for absence. -/
def DeletesFirstValue (arguments : List GroundValue)
    (result : GroundValue) : Prop :=
  ∃ needle target items,
    arguments = [needle, target] ∧
    EncodesList items target ∧
    ((∃ rest, DeletesFirst needle items rest ∧ result = buildList rest) ∨
      (needle ∉ items ∧ result = buildList items))

/-- Independent successful specification of callback-parameterized `map`. -/
def Maps (apply : GroundValue → FuelResult GroundValue)
    (arguments : List GroundValue) (result : GroundValue) : Prop :=
  ∃ target inputs outputs,
    arguments = [target] ∧
    EncodesList inputs target ∧
    Traverses apply inputs outputs ∧
    result = buildList outputs

/-- Independent successful specification of first pair projection. -/
def ProjectsFirst (arguments : List GroundValue) (result : GroundValue) : Prop :=
  ∃ first second,
    arguments = [tupleValue [first, second]] ∧ result = first

/-- Independent successful specification of second pair projection. -/
def ProjectsSecond (arguments : List GroundValue) (result : GroundValue) : Prop :=
  ∃ first second,
    arguments = [tupleValue [first, second]] ∧ result = second

theorem evalAdd_adequate {arguments result} :
    evalAdd arguments = .ok result → Adds arguments result := by
  intro success
  rcases arguments with _ | ⟨first, tail⟩
  · simp [evalAdd] at success
  rcases tail with _ | ⟨second, tail⟩
  · simp [evalAdd] at success
  rcases tail with _ | ⟨extra, tail⟩
  · cases first <;> cases second <;> simp [evalAdd] at success
    subst result
    exact ⟨_, _, rfl, rfl⟩
  · simp [evalAdd] at success

theorem evalAdd_complete {arguments result} :
    Adds arguments result → evalAdd arguments = .ok result := by
  rintro ⟨left, right, rfl, rfl⟩
  rfl

theorem evalAppend_adequate {arguments result} :
    evalAppend arguments = .ok result → Appends arguments result := by
  intro success
  rcases arguments with _ | ⟨left, tail⟩
  · simp [evalAppend] at success
  rcases tail with _ | ⟨right, tail⟩
  · simp [evalAppend] at success
  rcases tail with _ | ⟨extra, tail⟩
  · cases leftView : left.viewList <;>
      cases rightView : right.viewList <;> simp [evalAppend, leftView, rightView] at success
    subst result
    exact ⟨left, right, _, _, rfl, EncodesList.of_view leftView,
      EncodesList.of_view rightView, rfl⟩
  · simp [evalAppend] at success

theorem evalAppend_complete {arguments result} :
    Appends arguments result → evalAppend arguments = .ok result := by
  rintro ⟨left, right, leftItems, rightItems, rfl,
    leftEncoding, rightEncoding, rfl⟩
  simp [evalAppend, leftEncoding.view, rightEncoding.view]

theorem evalMember_adequate {arguments result} :
    evalMember arguments = .ok result → TestsMember arguments result := by
  intro success
  rcases arguments with _ | ⟨needle, tail⟩
  · simp [evalMember] at success
  rcases tail with _ | ⟨target, tail⟩
  · simp [evalMember] at success
  rcases tail with _ | ⟨extra, tail⟩
  · cases targetView : target.viewList with
    | none => simp [evalMember, targetView] at success
    | some items =>
        simp [evalMember, targetView] at success
        subst result
        exact ⟨needle, target, items, rfl,
          EncodesList.of_view targetView, rfl⟩
  · simp [evalMember] at success

theorem evalMember_complete {arguments result} :
    TestsMember arguments result → evalMember arguments = .ok result := by
  rintro ⟨needle, target, items, rfl, encoding, rfl⟩
  simp [evalMember, encoding.view]

theorem evalDeleteFirst_adequate {arguments result} :
    evalDeleteFirst arguments = .ok result →
      DeletesFirstValue arguments result := by
  intro success
  rcases arguments with _ | ⟨needle, tail⟩
  · simp [evalDeleteFirst] at success
  rcases tail with _ | ⟨target, tail⟩
  · simp [evalDeleteFirst] at success
  rcases tail with _ | ⟨extra, tail⟩
  · cases targetView : target.viewList with
    | none => simp [evalDeleteFirst, targetView] at success
    | some items =>
        cases deletion : deleteFirst? needle items with
        | none =>
            simp [evalDeleteFirst, targetView, deletion] at success
            subst result
            exact ⟨needle, target, items, rfl,
              EncodesList.of_view targetView, Or.inr
                ⟨deleteFirst?_eq_none_iff.mp deletion, rfl⟩⟩
        | some rest =>
            simp [evalDeleteFirst, targetView, deletion] at success
            subst result
            exact ⟨needle, target, items, rfl,
              EncodesList.of_view targetView, Or.inl
                ⟨rest, deleteFirst?_eq_some_iff.mp deletion, rfl⟩⟩
  · simp [evalDeleteFirst] at success

theorem evalDeleteFirst_complete {arguments result} :
    DeletesFirstValue arguments result →
      evalDeleteFirst arguments = .ok result := by
  rintro ⟨needle, target, items, rfl, encoding, deleted | absent⟩
  · rcases deleted with ⟨rest, deletion, rfl⟩
    simp [evalDeleteFirst, encoding.view,
      deleteFirst?_eq_some_iff.mpr deletion]
  · rcases absent with ⟨notMember, rfl⟩
    simp [evalDeleteFirst, encoding.view,
      deleteFirst?_eq_none_iff.mpr notMember]

theorem evalMap_adequate {apply} {arguments result} :
    evalMap apply arguments = .ok result → Maps apply arguments result := by
  intro success
  rcases arguments with _ | ⟨target, tail⟩
  · simp [evalMap] at success
  rcases tail with _ | ⟨extra, tail⟩
  · cases targetView : target.viewList with
    | none => simp [evalMap, targetView] at success
    | some inputs =>
        cases traversal : FuelResult.traverse apply inputs with
        | timeout => simp [evalMap, targetView, traversal] at success
        | stuck => simp [evalMap, targetView, traversal] at success
        | ok outputs =>
            simp [evalMap, targetView, traversal] at success
            subst result
            exact ⟨target, inputs, outputs, rfl,
              EncodesList.of_view targetView,
              (FuelResult.traverse_eq_ok_iff apply inputs outputs).mp traversal,
              rfl⟩
  · simp [evalMap] at success

theorem evalMap_complete {apply} {arguments result} :
    Maps apply arguments result → evalMap apply arguments = .ok result := by
  rintro ⟨target, inputs, outputs, rfl, encoding, traversal, rfl⟩
  simp [evalMap, encoding.view,
    (FuelResult.traverse_eq_ok_iff apply inputs outputs).mpr traversal]

theorem evalPairFirst_adequate {arguments result} :
    evalPairFirst arguments = .ok result → ProjectsFirst arguments result := by
  intro success
  rcases arguments with _ | ⟨pair, tail⟩
  · simp [evalPairFirst] at success
  rcases tail with _ | ⟨extra, tail⟩
  · cases pair <;> simp [evalPairFirst] at success
    case tuple items =>
      rcases items with _ | ⟨first, items⟩
      · simp at success
      rcases items with _ | ⟨second, items⟩
      · simp at success
      rcases items with _ | ⟨third, items⟩
      · simp at success
        subst result
        exact ⟨first, second, rfl, rfl⟩
      · simp at success
  · simp [evalPairFirst] at success

theorem evalPairFirst_complete {arguments result} :
    ProjectsFirst arguments result → evalPairFirst arguments = .ok result := by
  rintro ⟨first, second, rfl, rfl⟩
  rfl

theorem evalPairSecond_adequate {arguments result} :
    evalPairSecond arguments = .ok result → ProjectsSecond arguments result := by
  intro success
  rcases arguments with _ | ⟨pair, tail⟩
  · simp [evalPairSecond] at success
  rcases tail with _ | ⟨extra, tail⟩
  · cases pair <;> simp [evalPairSecond] at success
    case tuple items =>
      rcases items with _ | ⟨first, items⟩
      · simp at success
      rcases items with _ | ⟨second, items⟩
      · simp at success
      rcases items with _ | ⟨third, items⟩
      · simp at success
        subst result
        exact ⟨first, second, rfl, rfl⟩
      · simp at success
  · simp [evalPairSecond] at success

theorem evalPairSecond_complete {arguments result} :
    ProjectsSecond arguments result → evalPairSecond arguments = .ok result := by
  rintro ⟨first, second, rfl, rfl⟩
  rfl

/-- The operation-indexed relational graph of the ground fragment. -/
def Evaluates (apply : GroundValue → FuelResult GroundValue)
    (operation : PrimOp) (arguments : List GroundValue)
    (result : GroundValue) : Prop :=
  match operation with
  | .add => Adds arguments result
  | .append => Appends arguments result
  | .member => TestsMember arguments result
  | .deleteFirst => DeletesFirstValue arguments result
  | .map => Maps apply arguments result
  | .pairFirst => ProjectsFirst arguments result
  | .pairSecond => ProjectsSecond arguments result

theorem eval_adequate {apply operation arguments result} :
    eval apply operation arguments = .ok result →
      Evaluates apply operation arguments result := by
  cases operation with
  | add => exact evalAdd_adequate
  | append => exact evalAppend_adequate
  | member => exact evalMember_adequate
  | deleteFirst => exact evalDeleteFirst_adequate
  | map => exact evalMap_adequate
  | pairFirst => exact evalPairFirst_adequate
  | pairSecond => exact evalPairSecond_adequate

theorem eval_complete {apply operation arguments result} :
    Evaluates apply operation arguments result →
      eval apply operation arguments = .ok result := by
  cases operation with
  | add => exact evalAdd_complete
  | append => exact evalAppend_complete
  | member => exact evalMember_complete
  | deleteFirst => exact evalDeleteFirst_complete
  | map => exact evalMap_complete
  | pairFirst => exact evalPairFirst_complete
  | pairSecond => exact evalPairSecond_complete

theorem eval_eq_ok_iff {apply operation arguments result} :
    eval apply operation arguments = .ok result ↔
      Evaluates apply operation arguments result :=
  ⟨eval_adequate, eval_complete⟩

end GroundPrimitive

end TypePM.Runtime
