import TypePM.Generation
import TypePM.Regression

/-!
# M1 source-order and no-guess examples

This module fixes the source programs and their generated constraints.  Their
acceptance and rejection are proved only after saturation and resolution are
available.
-/

namespace TypePM
namespace M1Examples

def slotInt : Ty := .slot .any .int
def consumerFunction : Ty := .fn slotInt .int
def useType : Ty := .fn consumerFunction .int
def useContext : Context := [useType]

/-- Inside each lambda, index zero is `f` and index one is `use`. -/
def useFirst : Expr :=
  .lam (.tuple [
    .app (.var 1) (.var 0),
    .app (.var 0) .something])

def applicationFirst : Expr :=
  .lam (.tuple [
    .app (.var 0) .something,
    .app (.var 1) (.var 0)])

def singletonFirst : Expr :=
  .lam (.tuple [
    .app (.var 0) .something,
    .app (.var 0) Regression.pair])

def pairFirst : Expr :=
  .lam (.tuple [
    .app (.var 0) Regression.pair,
    .app (.var 0) .something])

def acceptedType : Ty :=
  .fn consumerFunction (.prod [.int, .int])

private def fresh (index : Nat) : Ty :=
  .var ⟨index⟩

def pairGenerated : Generated :=
  { target := .prod [
      .matcher .any (fresh 0),
      .matcher .any (fresh 1)]
    hard := []
    pending := [] }

theorem generate_pair_exact :
    generateRoot [] Regression.pair = some pairGenerated := by
  rfl

def useFirstGenerated : Generated :=
  { target := .fn (fresh 0) (.prod [fresh 2, fresh 5])
    hard := [
      .ty useType (.fn (fresh 1) (fresh 2)),
      .ty (fresh 0) (.fn (fresh 4) (fresh 5))]
    pending := [
      ⟨fresh 0, fresh 1⟩,
      ⟨.matcher .any (fresh 3), fresh 4⟩] }

theorem generate_useFirst_exact :
    generateRoot useContext useFirst = some useFirstGenerated := by
  rfl

def applicationFirstGenerated : Generated :=
  { target := .fn (fresh 0) (.prod [fresh 3, fresh 5])
    hard := [
      .ty (fresh 0) (.fn (fresh 2) (fresh 3)),
      .ty useType (.fn (fresh 4) (fresh 5))]
    pending := [
      ⟨.matcher .any (fresh 1), fresh 2⟩,
      ⟨fresh 0, fresh 4⟩] }

theorem generate_applicationFirst_exact :
    generateRoot useContext applicationFirst =
      some applicationFirstGenerated := by
  rfl

end M1Examples
end TypePM
