import TypePM.Source.Syntax

/-!
# Total pair destructuring

Pair destructuring is expressed with the ordinary, statically typed first and
second projections.  It does not invoke a user-defined matcher and therefore
cannot receive an empty matching result.  As with every eliminator in the
typed core, totality is claimed for well-typed inputs: the runtime typing proof
ensures that both projections receive a pair.
-/

namespace TypePM.Source

namespace Expr

/-- A unary function whose pair argument is exposed to `body` in source
order.  In `body`, index zero is the first field, index one is the second
field, and index two is the original pair argument.

The second field is bound first so that the subsequent first-field binding is
the newest entry in the nameless environment. -/
def pairDestructuringLambda (body : Expr) : Expr :=
  .lam
    (.letE (.prim .pairSecond [.var 0])
      (.letE (.prim .pairFirst [.var 1]) body))

@[simp] theorem pairDestructuringLambda_eq (body : Expr) :
    pairDestructuringLambda body =
      .lam
        (.letE (.prim .pairSecond [.var 0])
          (.letE (.prim .pairFirst [.var 1]) body)) := by
  rfl

end Expr

end TypePM.Source
