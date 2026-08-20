import Lean.Elab.Command
import Lean.Elab.InfoTree.Main
import Lean.Util.CollectAxioms

/-!
# Build-failing axiom audit command

`#assert_allowed_axioms declaration` computes the declaration's transitive axiom
dependencies and rejects every dependency outside Lean's standard logical
allowlist below.  Unlike `#print axioms`, this makes the audit enforceable by
`lake build` and continuous integration.
-/

open Lean Elab Command

namespace TypePM.AxiomAudit

/-- Standard Lean assumptions permitted in public milestone theorems. -/
private def allowedAxioms : Array Name :=
  #[``propext, ``Classical.choice, ``Quot.sound]

syntax (name := assertAllowedAxioms)
  "#assert_allowed_axioms " ident : command

@[command_elab assertAllowedAxioms]
def elabAssertAllowedAxioms : CommandElab
  | `(#assert_allowed_axioms%$tk $id:ident) => withRef tk do
      let declarations ← liftCoreM <| realizeGlobalConstWithInfos id
      for declaration in declarations do
        let axioms ← collectAxioms declaration
        let forbidden := axioms.filter fun axiomName =>
          !allowedAxioms.contains axiomName
        unless forbidden.isEmpty do
          throwError m!"'{declaration}' depends on forbidden axioms: \
            {forbidden.qsort Name.lt |>.map MessageData.ofConstName |>.toList}"
  | _ => throwUnsupportedSyntax

end TypePM.AxiomAudit
