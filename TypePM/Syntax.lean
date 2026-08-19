import TypePM.Types

/-!
# Source syntax through M1

Variables use natural-number indices into a monomorphic context.  Lambda and
application form the M1 extension; polymorphic schemes remain absent until M2.
-/

namespace TypePM

inductive Expr where
  | var (index : Nat)
  | lit (value : Int)
  | something
  | lam (body : Expr)
  | app (function argument : Expr)
  | tuple (items : List Expr)
deriving Repr

abbrev Context := List Ty

end TypePM
