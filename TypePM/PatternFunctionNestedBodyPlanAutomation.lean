import TypePM.PatternFunctionBodyPlanAutomation

/-!
# Automatic checked-body plans with nested applications

The structural compiler delegates only proof-bearing leaves.  Embedded
parameters use the existing export resolver.  A nested application resolver
must additionally retain the exact frozen lookup, arity equality, checked
callee certificate, and a sound execution assembled from the existing MNode
application rules.  A successful lookup alone is therefore never treated as
callee safety.
-/

namespace TypePM.Runtime

open TypePM.Source

/-- Proof-bearing result of resolving one nested pattern-function call. -/
structure CheckedBodyResolvedApplication
    (signature : FrozenSignature)
    (definitions : PatternFunctionDefinitions)
    (environmentTypes : List Ty) (arguments : List Pattern)
    (outerBindingTypes : List Ty) (name : PatternFunName)
    (nestedArguments : List Pattern) (matcher target : Value) : Type where
  definition : PatternFunctionDefinition
  found : definitions.lookup name = some definition
  checked : Nonempty (definition.Checked signature)
  arity : nestedArguments.length = definition.parameterCount
  answerTypes : List Ty
  execution : CheckedBodyExecution signature definitions environmentTypes
    arguments outerBindingTypes ⟨.app name nestedArguments, matcher, target⟩
    answerTypes

/-- Resolver for both kinds of non-structural leaf.  Every nested application
result contains its own checked frozen lookup and execution proof. -/
structure CheckedNestedBodyResolver
    (signature : FrozenSignature)
    (definitions : PatternFunctionDefinitions)
    (environmentTypes : List Ty) (arguments : List Pattern) : Type where
  exports : CheckedBodyExportResolver signature definitions environmentTypes
    arguments
  applications : (outerBindingTypes : List Ty) → (name : PatternFunName) →
    (nestedArguments : List Pattern) → (matcher target : Value) →
    Option (CheckedBodyResolvedApplication signature definitions
      environmentTypes arguments outerBindingTypes name nestedArguments matcher
      target)

/-- Structural compiler extended with proof-bearing nested applications.
Tuple children and conjunction children thread their exact output binding
types left-to-right, just as in the application-free compiler. -/
def CheckedBodyExecution.compileNestedFuel
    (resolver : CheckedNestedBodyResolver signature definitions
      environmentTypes arguments) :
    (fuel : Nat) → (outerBindingTypes : List Ty) → (atom : MatchingAtom) →
      Option (CheckedBodyCompileResult signature definitions environmentTypes
        arguments outerBindingTypes atom)
  | 0, _, _ => none
  | _ + 1, outerBindingTypes, ⟨.embed index, matcher, target⟩ =>
      resolver.exports.resolve outerBindingTypes index matcher target
  | _ + 1, outerBindingTypes,
      ⟨.app name nestedArguments, matcher, target⟩ => do
      let resolved ← resolver.applications outerBindingTypes name
        nestedArguments matcher target
      pure ⟨resolved.answerTypes, resolved.execution⟩
  | fuel + 1, outerBindingTypes,
      ⟨.and left right, .something, target⟩ => do
      let ⟨middleTypes, leftExecution⟩ ←
        CheckedBodyExecution.compileNestedFuel resolver fuel outerBindingTypes
          ⟨left, .something, target⟩
      let ⟨answerTypes, rightExecution⟩ ←
        CheckedBodyExecution.compileNestedFuel resolver fuel middleTypes
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
                  CheckedBodyExecution.compileNestedFuel resolver fuel
                    bindingTypes head
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

def CheckedBodyExecution.compileNested
    (resolver : CheckedNestedBodyResolver signature definitions
      environmentTypes arguments)
    (outerBindingTypes : List Ty) (atom : MatchingAtom) :
    Option (CheckedBodyCompileResult signature definitions environmentTypes
      arguments outerBindingTypes atom) :=
  CheckedBodyExecution.compileNestedFuel resolver
    (atom.pattern.complexity + 1) outerBindingTypes atom

end TypePM.Runtime
