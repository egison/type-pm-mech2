import TypePM.Types

/-!
# M0 source syntax

Variables use natural-number indices into a monomorphic context.  Lambda,
application, and polymorphic schemes are intentionally absent until M1/M2.
-/

namespace TypePM

inductive Expr where
  | var (index : Nat)
  | lit (value : Int)
  | something
  | tuple (items : List Expr)
deriving Repr

abbrev Context := List Ty

end TypePM
