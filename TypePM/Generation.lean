import TypePM.Constraints
import TypePM.Fresh

/-!
# Pure M1 constraint generation

Generation allocates fresh ordinary type variables but never solves an
equality and never selects a checking conversion.  All sibling constraints
are collected before either operation is attempted.
-/

namespace TypePM

mutual

def generate (context : Context) : Expr → Nat → Option (Generated × Nat)
  | .var index, supply => do
      let target ← context[index]?
      pure (⟨target, [], []⟩, supply)
  | .lit _, supply =>
      some (⟨.int, [], []⟩, supply)
  | .something, supply =>
      let target : Ty := .var ⟨supply⟩
      some (⟨.matcher .any target, [], []⟩, supply + 1)
  | .lam body, supply => do
      let domain : Ty := .var ⟨supply⟩
      let (generatedBody, next) ← generate (domain :: context) body (supply + 1)
      pure (⟨.fn domain generatedBody.target,
        generatedBody.hard, generatedBody.pending⟩, next)
  | .app function argument, supply => do
      let (generatedFunction, afterFunction) ← generate context function supply
      let (generatedArgument, afterArgument) ←
        generate context argument afterFunction
      let domain : Ty := .var ⟨afterArgument⟩
      let target : Ty := .var ⟨afterArgument + 1⟩
      pure
        (⟨target,
          generatedFunction.hard ++ generatedArgument.hard ++
            [.ty generatedFunction.target (.fn domain target)],
          generatedFunction.pending ++ generatedArgument.pending ++
            [⟨generatedArgument.target, domain⟩]⟩,
        afterArgument + 2)
  | .tuple items, supply => do
      let (generatedItems, next) ← generateItems context items supply
      pure (⟨.prod generatedItems.targets,
        generatedItems.hard, generatedItems.pending⟩, next)

def generateItems (context : Context) :
    List Expr → Nat → Option (GeneratedItems × Nat)
  | [], supply => some (⟨[], [], []⟩, supply)
  | item :: items, supply => do
      let (generatedItem, afterItem) ← generate context item supply
      let (generatedItems, next) ← generateItems context items afterItem
      pure
        (⟨generatedItem.target :: generatedItems.targets,
          generatedItem.hard ++ generatedItems.hard,
          generatedItem.pending ++ generatedItems.pending⟩,
        next)

end


/-- Generate a complete M1 problem above all variables already present in the
external monomorphic context. -/
def generateRoot (context : Context) (expression : Expr) : Option Generated :=
  (generate context expression context.nextVar).map Prod.fst

end TypePM
