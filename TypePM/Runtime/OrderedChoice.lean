import TypePM.Primitive

/-!
# Ordered choices used by matching

The matching runtime represents alternatives by ordinary `List`s.  These
functions deliberately preserve source order and position multiplicity:
equal values at different positions remain different branches.
-/

namespace TypePM.Runtime

/-- Choose one input position and return the chosen value together with the
remaining values.  Earlier input positions produce earlier alternatives. -/
def chooseOne : List α → List (α × List α)
  | [] => []
  | value :: tail =>
      (value, tail) ::
        (chooseOne tail).map fun (chosen, rest) => (chosen, value :: rest)

/-- Enumerate every ordered prefix/suffix assignment of the input positions.
For each recursively produced split, the current value is put on the right
first and on the left second.  This is the order used by the paper's
multiset `join` clause. -/
def splitAll : List α → List (List α × List α)
  | [] => [([], [])]
  | value :: tail =>
      let splits := splitAll tail
      splits.map (fun (left, right) => (left, value :: right)) ++
        splits.map (fun (left, right) => (value :: left, right))

/-- Remove the first equal value, if it occurs. -/
def deleteFirst? [DecidableEq α] (value : α) : List α → Option (List α)
  | [] => none
  | head :: tail =>
      if value = head then
        some tail
      else
        (deleteFirst? value tail).map fun rest => head :: rest

/-- The alternatives produced by the value-head multiset clause: one tail
when the captured value occurs, and no alternative otherwise. -/
def chooseValue [DecidableEq α] (value : α) (target : List α) : List (List α) :=
  match deleteFirst? value target with
  | some rest => [rest]
  | none => []

@[simp] theorem chooseOne_nil : chooseOne ([] : List α) = [] := by
  rfl

@[simp] theorem chooseOne_cons (value : α) (tail : List α) :
    chooseOne (value :: tail) =
      (value, tail) ::
        (chooseOne tail).map (fun (chosen, rest) =>
          (chosen, value :: rest)) := by
  rfl

@[simp] theorem splitAll_nil :
    splitAll ([] : List α) = [([], [])] := by
  rfl

@[simp] theorem splitAll_cons (value : α) (tail : List α) :
    splitAll (value :: tail) =
      (splitAll tail).map (fun (left, right) =>
        (left, value :: right)) ++
      (splitAll tail).map (fun (left, right) =>
        (value :: left, right)) := by
  rfl

theorem chooseOne_length (target : List α) :
    (chooseOne target).length = target.length := by
  induction target with
  | nil => rfl
  | cons value tail ih =>
      simp [chooseOne, ih]

theorem splitAll_length (target : List α) :
    (splitAll target).length = 2 ^ target.length := by
  induction target with
  | nil => rfl
  | cons value tail ih =>
      simp [splitAll, ih, Nat.pow_succ, Nat.mul_two]

end TypePM.Runtime
