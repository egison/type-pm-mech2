import TypePM.PatternFunctionSafety

/-!
# Automatic structural plans for checked pattern-function bodies

The plan algebra is independent of tuple arity and conjunction depth, but an
application still needs runtime evidence for every exported actual argument.
This module separates those two concerns.  `checkedBodyPlanShape` is an
executable precheck for the private-binding-neutral fragment, while
`CheckedBodyExecution` retains exactly the runtime export evidence that a
successful precheck cannot manufacture.
-/

namespace TypePM.Runtime

open TypePM.Source

/-- Fuel-bounded executable recognition of the fragment handled by the
structural body-plan algebra.  Fuel decreases before inspecting children, so
tuple arity does not require a separate recursive definition. -/
def checkedBodyPlanShapeFuel : Nat → Nat → MatchingAtom → Bool
  | 0, _, _ => false
  | fuel + 1, argumentCount, atom =>
      match atom.pattern, atom.matcher, atom.target with
      | .embed index, _, _ => decide (index < argumentCount)
      | .and left right, .something, target =>
          checkedBodyPlanShapeFuel fuel argumentCount
              ⟨left, .something, target⟩ &&
            checkedBodyPlanShapeFuel fuel argumentCount
              ⟨right, .something, target⟩
      | .tuple patterns, .tuple matchers, .tuple targets =>
          match zipMatchingAtoms patterns matchers targets with
          | some atoms =>
              atoms.all (checkedBodyPlanShapeFuel fuel argumentCount)
          | none => false
      | _, _, _ => false

/-- Executable syntax-and-arity precheck for the maximal fragment currently
supported by `CheckedBodyAtomPlan`: embedded parameters, conjunction under
`something`, and exact-arity tuple decomposition. -/
def checkedBodyPlanShape (arguments : List Pattern)
    (atom : MatchingAtom) : Bool :=
  checkedBodyPlanShapeFuel (atom.pattern.complexity + 1) arguments.length atom

/-- A compiled source-ordered child list.  The wrapper keeps tuple recursion
outside the mutually recursive evidence while preserving every binding index. -/
structure CheckedBodyExecutions
    (signature : FrozenSignature)
    (definitions : PatternFunctionDefinitions)
    (environmentTypes : List Ty) (arguments : List Pattern)
    (outerBindingTypes : List Ty) (atoms : List MatchingAtom)
    (answerTypes : List Ty) : Type where private mk ::
  plan : CheckedBodyAtomsPlan signature definitions environmentTypes arguments
    outerBindingTypes atoms answerTypes

/-- Runtime evidence for one structurally supported body atom.  Structural
nodes are reconstructed automatically; only an embedded leaf carries an
outer-work certificate, because its binding effect belongs to the actual
argument rather than to the checked definition body. -/
structure CheckedBodyExecution
    (signature : FrozenSignature)
    (definitions : PatternFunctionDefinitions)
    (environmentTypes : List Ty) (arguments : List Pattern)
    (outerBindingTypes : List Ty) (atom : MatchingAtom)
    (answerTypes : List Ty) : Type where private mk ::
  plan : CheckedBodyAtomPlan signature definitions environmentTypes arguments
    outerBindingTypes atom answerTypes

namespace CheckedBodyExecution

/-- Supply the unavoidable call-site evidence for one embedded actual
argument. -/
def parameter
    (lookup : arguments[index]? = some argument)
    (exported : CheckedScopedWorkTyping signature definitions environmentTypes
      outerBindingTypes [.atom ⟨argument, matcher, target⟩] answerTypes) :
    CheckedBodyExecution signature definitions environmentTypes arguments
      outerBindingTypes ⟨.embed index, matcher, target⟩ answerTypes :=
  ⟨CheckedBodyAtomPlan.parameter lookup exported⟩

/-- Compile a conjunction of any recursively supported children. -/
def and
    (left : CheckedBodyExecution signature definitions environmentTypes
      arguments outerBindingTypes
      ⟨leftPattern, .something, target⟩ middleTypes)
    (right : CheckedBodyExecution signature definitions environmentTypes
      arguments middleTypes
      ⟨rightPattern, .something, target⟩ answerTypes) :
    CheckedBodyExecution signature definitions environmentTypes arguments
      outerBindingTypes
      ⟨.and leftPattern rightPattern, .something, target⟩ answerTypes :=
  ⟨CheckedBodyAtomPlan.expand CheckedBodyAtomExpansion.and
    (CheckedBodyAtomsPlan.cons left.plan
      (CheckedBodyAtomsPlan.cons right.plan CheckedBodyAtomsPlan.nil))⟩

/-- Compile an exact-arity tuple with an arbitrary source-ordered child list. -/
def tuple
    (zipped : zipMatchingAtoms patterns matchers targets = some atoms)
    (children : CheckedBodyExecutions signature definitions environmentTypes
      arguments outerBindingTypes atoms answerTypes) :
    CheckedBodyExecution signature definitions environmentTypes arguments
      outerBindingTypes
      ⟨.tuple patterns, .tuple matchers, .tuple targets⟩ answerTypes :=
  ⟨CheckedBodyAtomPlan.expand (CheckedBodyAtomExpansion.tuple zipped)
    children.plan⟩

/-- Repackage the existing checked nested-call rule whose checked callee body
is one embedded parameter.  This adds no new work-typing constructor. -/
def applicationParameter
    (found : definitions.lookup name = some definition)
    (checked : Nonempty (definition.Checked signature))
    (arity : nestedArguments.length = definition.parameterCount)
    (body : definition.body = .embed parameterIndex)
    (nestedLookup : nestedArguments[parameterIndex]? = some (.embed outerIndex))
    (outerLookup : arguments[outerIndex]? = some outerArgument)
    (exported : CheckedScopedWorkTyping signature definitions environmentTypes
      outerBindingTypes [.atom ⟨outerArgument, matcher, target⟩]
      afterExportTypes) :
    CheckedBodyExecution signature definitions environmentTypes arguments
      outerBindingTypes ⟨.app name nestedArguments, matcher, target⟩
      afterExportTypes :=
  ⟨⟨fun tail => .applicationParameter found checked arity body nestedLookup
    outerLookup exported tail⟩⟩

/-- Repackage the existing checked nested-call rule for the already-supported
two-parameter conjunction body.  Binding types are threaded from the left
actual argument to the right one by the two exported certificates. -/
def applicationAndParameters
    (found : definitions.lookup name = some definition)
    (checked : Nonempty (definition.Checked signature))
    (arity : nestedArguments.length = definition.parameterCount)
    (body : definition.body =
      .and (.embed leftParameterIndex) (.embed rightParameterIndex))
    (matcherEq : matcher = .something)
    (leftNestedLookup : nestedArguments[leftParameterIndex]? =
      some (.embed leftOuterIndex))
    (rightNestedLookup : nestedArguments[rightParameterIndex]? =
      some (.embed rightOuterIndex))
    (leftOuterLookup : arguments[leftOuterIndex]? = some leftArgument)
    (rightOuterLookup : arguments[rightOuterIndex]? = some rightArgument)
    (leftExported : CheckedScopedWorkTyping signature definitions
      environmentTypes outerBindingTypes
      [.atom ⟨leftArgument, matcher, target⟩] afterLeftTypes)
    (rightExported : CheckedScopedWorkTyping signature definitions
      environmentTypes afterLeftTypes
      [.atom ⟨rightArgument, matcher, target⟩] afterRightTypes) :
    CheckedBodyExecution signature definitions environmentTypes arguments
      outerBindingTypes ⟨.app name nestedArguments, matcher, target⟩
      afterRightTypes :=
  ⟨⟨fun tail => .applicationAndParameters found checked arity body matcherEq
    leftNestedLookup rightNestedLookup leftOuterLookup rightOuterLookup
    leftExported rightExported tail⟩⟩

end CheckedBodyExecution

namespace CheckedBodyExecutions

def nil : CheckedBodyExecutions signature definitions environmentTypes
    arguments bindingTypes [] bindingTypes :=
  CheckedBodyExecutions.mk CheckedBodyAtomsPlan.nil

/-- Source-ordered composition threads the exact outer binding index between
tuple children without exposing any private MNode frame. -/
def cons
    (head : CheckedBodyExecution signature definitions environmentTypes
      arguments bindingTypes atom middleTypes)
    (tail : CheckedBodyExecutions signature definitions environmentTypes
      arguments middleTypes atoms answerTypes) :
    CheckedBodyExecutions signature definitions environmentTypes arguments
      bindingTypes (atom :: atoms) answerTypes :=
  CheckedBodyExecutions.mk (CheckedBodyAtomsPlan.cons head.plan tail.plan)

end CheckedBodyExecutions

/-- A call-site resolver supplies only embedded leaves.  Returning `none`
means that this concrete parameter/matcher/target combination has no export
certificate; structural compilation never asks it to assemble conjunction or
tuple work. -/
structure CheckedBodyExportResolver
    (signature : FrozenSignature)
    (definitions : PatternFunctionDefinitions)
    (environmentTypes : List Ty) (arguments : List Pattern) : Type where
  resolve : (outerBindingTypes : List Ty) → (index : Nat) →
    (matcher target : Value) →
    Option (Σ answerTypes, CheckedBodyExecution signature definitions
      environmentTypes arguments outerBindingTypes
      ⟨.embed index, matcher, target⟩ answerTypes)

/-- The dependent result of compiling one atom. -/
abbrev CheckedBodyCompileResult
    (signature : FrozenSignature)
    (definitions : PatternFunctionDefinitions)
    (environmentTypes : List Ty) (arguments : List Pattern)
    (outerBindingTypes : List Ty) (atom : MatchingAtom) :=
  Σ answerTypes, CheckedBodyExecution signature definitions environmentTypes
    arguments outerBindingTypes atom answerTypes

/-- One structural recursion compiles every accepted body shape.  Tuple
children are folded left-to-right, so each resolver call receives exactly the
binding type list produced by its predecessors. -/
def CheckedBodyExecution.compileFuel
    (resolver : CheckedBodyExportResolver signature definitions
      environmentTypes arguments) :
    (fuel : Nat) → (outerBindingTypes : List Ty) → (atom : MatchingAtom) →
      Option (CheckedBodyCompileResult signature definitions environmentTypes
        arguments outerBindingTypes atom)
  | 0, _, _ => none
  | _ + 1, outerBindingTypes, ⟨.embed index, matcher, target⟩ =>
      resolver.resolve outerBindingTypes index matcher target
  | fuel + 1, outerBindingTypes,
      ⟨.and left right, .something, target⟩ => do
      let ⟨middleTypes, leftExecution⟩ ←
        CheckedBodyExecution.compileFuel resolver fuel outerBindingTypes
          ⟨left, .something, target⟩
      let ⟨answerTypes, rightExecution⟩ ←
        CheckedBodyExecution.compileFuel resolver fuel middleTypes
          ⟨right, .something, target⟩
      pure ⟨answerTypes,
        CheckedBodyExecution.and leftExecution rightExecution⟩
  | fuel + 1, outerBindingTypes,
      ⟨.tuple patterns, .tuple matchers, .tuple targets⟩ =>
      match zipped : zipMatchingAtoms patterns matchers targets with
      | none => none
      | some atoms =>
          let rec compileAtoms (bindingTypes : List Ty) :
              (remaining : List MatchingAtom) →
                Option (Σ answerTypes,
                  CheckedBodyExecutions signature definitions environmentTypes
                    arguments bindingTypes remaining answerTypes)
            | [] => some ⟨bindingTypes, CheckedBodyExecutions.nil⟩
            | head :: tail => do
                let ⟨middleTypes, headExecution⟩ ←
                  CheckedBodyExecution.compileFuel resolver fuel bindingTypes
                    head
                let ⟨answerTypes, tailExecutions⟩ ←
                  compileAtoms middleTypes tail
                pure ⟨answerTypes,
                  CheckedBodyExecutions.cons headExecution tailExecutions⟩
          match compileAtoms outerBindingTypes atoms with
          | none => none
          | some ⟨answerTypes, children⟩ =>
              some ⟨answerTypes,
                CheckedBodyExecution.tuple zipped children⟩
  | _ + 1, _, _ => none

/-- Compile the complete atom with structurally sufficient fuel.  Success is
already the requested dependent execution certificate; no tuple-arity or
conjunction-depth constructor remains at the call site. -/
def CheckedBodyExecution.compile
    (resolver : CheckedBodyExportResolver signature definitions
      environmentTypes arguments)
    (outerBindingTypes : List Ty) (atom : MatchingAtom) :
    Option (CheckedBodyCompileResult signature definitions environmentTypes
      arguments outerBindingTypes atom) :=
  CheckedBodyExecution.compileFuel resolver (atom.pattern.complexity + 1)
    outerBindingTypes atom

namespace CheckedScopedWorkTyping

/-- A checked frozen lookup plus one structural execution certificate opens
the MNode with no hand-written `CheckedBodyAtomPlan`.  Agreement supplies the
source check for the exact looked-up body; `execution` supplies only facts
about this concrete matcher, target, and actual-argument export. -/
theorem applicationOfCheckedBodyExecution
    (agreement : definitions.Agree signature)
    (found : definitions.lookup name = some definition)
    (arity : arguments.length = definition.parameterCount)
    (execution : CheckedBodyExecution signature definitions environmentTypes
      arguments bindingTypes ⟨definition.body, matcher, target⟩ afterNodeTypes)
    (tail : CheckedScopedWorkTyping signature definitions environmentTypes
      afterNodeTypes remaining answerTypes) :
    CheckedScopedWorkTyping signature definitions environmentTypes bindingTypes
      (.atom ⟨.app name arguments, matcher, target⟩ :: remaining)
      answerTypes :=
  applicationOfBodyPlan agreement found arity execution.plan tail

end CheckedScopedWorkTyping

/-!
`PatternFunctionDefinition.Checked` proves canonical source elaboration and
constraint satisfaction.  It does not type the concrete matcher/target values
at an application site, and an embedded parameter contributes the bindings of
the actual argument rather than `generated.bindings` of the definition body.
Consequently `checkedBodyPlanShape = true` is intentionally only a structural
precheck.  `CheckedBodyExecution.parameter` is the reusable, exact boundary
for the missing call-site information.  Private-binding forms (`var`, `wild`,
`value`, and branching `or`), constructor dispatch, and nested applications
remain outside this private-binding-neutral compiler.
-/

end TypePM.Runtime
