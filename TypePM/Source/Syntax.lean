import TypePM.Scheme
import TypePM.Primitive

/-!
# Source syntax through M2

The public source language is separate from the verified M1 let-free block
syntax.  This avoids treating a polymorphic context as a monomorphic M1
context while retaining all M1 constraint and solver infrastructure.
-/

namespace TypePM.Source

/-- Source expressions through M3. -/
inductive Expr where
  | var (index : Nat)
  | lit (value : Int)
  | something
  | lam (body : Expr)
  | app (function argument : Expr)
  | tuple (items : List Expr)
  | letE (value body : Expr)
  | ctor (constructor : DataCtor) (arguments : List Expr)
  | prim (operation : PrimOp) (arguments : List Expr)
  | ifE (condition thenBranch elseBranch : Expr)
deriving Repr

end TypePM.Source
