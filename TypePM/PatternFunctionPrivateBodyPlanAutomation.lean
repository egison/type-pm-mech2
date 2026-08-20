import TypePM.PatternFunctionNestedBodyPlanAutomation

/-!
# Automatic plans with private pattern-function bindings

The first body-plan compiler quantifies over an unchanged private binding
frame.  That is exactly right for embedded parameters and structural nodes,
but it cannot express an ordinary body variable, whose binding belongs only
to the MNode.

This module keeps both frames in the plan index.  Structural composition
threads the outer and private type lists independently.  Variables and
wildcards are constructed from typing evidence for the concrete target value.
Nested applications reuse proof-bearing application resolutions and preserve
the current private frame.  Value patterns and disjunctions are accepted only
through an exact ordinary atom certificate; in particular, no user-matcher
branch is reconstructed from an erased lookup result.
-/

namespace TypePM.Runtime

open TypePM.Source

/-- One body atom, indexed by both its outer and private frame transitions. -/
structure CheckedPrivateBodyExecution
    (signature : FrozenSignature)
    (definitions : PatternFunctionDefinitions)
    (environmentTypes : List Ty) (arguments : List Pattern)
    (outerBindingTypes privateEnvironmentTypes privateBindingTypes : List Ty)
    (atom : MatchingAtom)
    (answerTypes answerPrivateBindingTypes : List Ty) : Type where private mk ::
  prepend : ∀ {remaining finalTypes},
    CheckedMNodeWorkTyping signature definitions environmentTypes answerTypes
      arguments privateEnvironmentTypes answerPrivateBindingTypes remaining
      finalTypes →
    CheckedMNodeWorkTyping signature definitions environmentTypes
      outerBindingTypes arguments privateEnvironmentTypes privateBindingTypes
      (.atom atom :: remaining) finalTypes

/-- A source-ordered child list with exact outer and private frame indices. -/
structure CheckedPrivateBodyExecutions
    (signature : FrozenSignature)
    (definitions : PatternFunctionDefinitions)
    (environmentTypes : List Ty) (arguments : List Pattern)
    (outerBindingTypes privateEnvironmentTypes privateBindingTypes : List Ty)
    (atoms : List MatchingAtom)
    (answerTypes answerPrivateBindingTypes : List Ty) : Type where private mk ::
  prepend : ∀ {remaining finalTypes},
    CheckedMNodeWorkTyping signature definitions environmentTypes answerTypes
      arguments privateEnvironmentTypes answerPrivateBindingTypes remaining
      finalTypes →
    CheckedMNodeWorkTyping signature definitions environmentTypes
      outerBindingTypes arguments privateEnvironmentTypes privateBindingTypes
      (MatchingTree.ofAtoms atoms ++ remaining) finalTypes

namespace CheckedPrivateBodyExecution

/-- Export an actual argument in the outer frame without changing the private
frame.  The concrete matcher and target remain part of `exported`. -/
def parameter
    (lookup : arguments[index]? = some argument)
    (exported : CheckedScopedWorkTyping signature definitions environmentTypes
      outerBindingTypes [.atom ⟨argument, matcher, target⟩] answerTypes) :
    CheckedPrivateBodyExecution signature definitions environmentTypes
      arguments outerBindingTypes privateEnvironmentTypes privateBindingTypes
      ⟨.embed index, matcher, target⟩ answerTypes privateBindingTypes where
  prepend tail := .parameter lookup exported tail

/-- A private ordinary atom changes only the MNode-local binding frame. -/
def ordinary
    (typed : CheckedOrdinaryAtomTyping privateEnvironmentTypes
      privateBindingTypes atom newPrivateBindings) :
    CheckedPrivateBodyExecution signature definitions environmentTypes
      arguments outerBindingTypes privateEnvironmentTypes privateBindingTypes
      atom outerBindingTypes (privateBindingTypes ++ newPrivateBindings) where
  prepend tail := .ordinary typed tail

/-- A private wildcard is frame-neutral. -/
def wild
    (targetTyped : ValueTyping target targetType) :
    CheckedPrivateBodyExecution signature definitions environmentTypes
      arguments outerBindingTypes privateEnvironmentTypes privateBindingTypes
      ⟨.wild, .something, target⟩ outerBindingTypes privateBindingTypes where
  prepend tail := .ordinary
    (CheckedOrdinaryAtomTyping.ofBuiltin (.somethingWild targetTyped)) (by
      simpa using tail)

/-- A private variable appends the concrete target type to the private frame. -/
def var
    (targetTyped : ValueTyping target targetType) :
    CheckedPrivateBodyExecution signature definitions environmentTypes
      arguments outerBindingTypes privateEnvironmentTypes privateBindingTypes
      ⟨.var, .something, target⟩ outerBindingTypes
      (privateBindingTypes ++ [targetType]) :=
  ordinary (CheckedOrdinaryAtomTyping.ofBuiltin (.somethingVar targetTyped))

/-- A checked nested application changes only the outer frame.  Its callee
certificate is already a `CheckedBodyExecution`, whose continuation is
polymorphic in the surrounding private frame; consequently private bindings
created earlier in the caller are preserved exactly. -/
def application
    (resolved : CheckedBodyResolvedApplication signature definitions
      environmentTypes arguments outerBindingTypes name nestedArguments matcher
      target) :
    CheckedPrivateBodyExecution signature definitions environmentTypes
      arguments outerBindingTypes privateEnvironmentTypes privateBindingTypes
      ⟨.app name nestedArguments, matcher, target⟩ resolved.answerTypes
      privateBindingTypes where
  prepend tail := resolved.execution.plan.prepend tail

/-- Compile a conjunction after independently compiling its two children. -/
def and
    (left : CheckedPrivateBodyExecution signature definitions environmentTypes
      arguments outerBindingTypes privateEnvironmentTypes privateBindingTypes
      ⟨leftPattern, .something, target⟩ middleTypes middlePrivateBindingTypes)
    (right : CheckedPrivateBodyExecution signature definitions environmentTypes
      arguments middleTypes privateEnvironmentTypes middlePrivateBindingTypes
      ⟨rightPattern, .something, target⟩ answerTypes
      answerPrivateBindingTypes) :
    CheckedPrivateBodyExecution signature definitions environmentTypes
      arguments outerBindingTypes privateEnvironmentTypes privateBindingTypes
      ⟨.and leftPattern rightPattern, .something, target⟩ answerTypes
      answerPrivateBindingTypes where
  prepend tail := .expand CheckedBodyAtomExpansion.and
    (left.prepend (right.prepend tail))

/-- Compile an exact-arity tuple from a source-ordered child plan. -/
def tuple
    (zipped : zipMatchingAtoms patterns matchers targets = some atoms)
    (children : CheckedPrivateBodyExecutions signature definitions
      environmentTypes arguments outerBindingTypes privateEnvironmentTypes
      privateBindingTypes atoms answerTypes answerPrivateBindingTypes) :
    CheckedPrivateBodyExecution signature definitions environmentTypes
      arguments outerBindingTypes privateEnvironmentTypes privateBindingTypes
      ⟨.tuple patterns, .tuple matchers, .tuple targets⟩ answerTypes
      answerPrivateBindingTypes where
  prepend tail := .expand (CheckedBodyAtomExpansion.tuple zipped)
    (children.prepend tail)

end CheckedPrivateBodyExecution

namespace CheckedPrivateBodyExecutions

def nil : CheckedPrivateBodyExecutions signature definitions environmentTypes
    arguments outerBindingTypes privateEnvironmentTypes privateBindingTypes []
    outerBindingTypes privateBindingTypes where
  prepend tail := by simpa [MatchingTree.ofAtoms] using tail

def cons
    (head : CheckedPrivateBodyExecution signature definitions environmentTypes
      arguments outerBindingTypes privateEnvironmentTypes privateBindingTypes
      atom middleTypes middlePrivateBindingTypes)
    (tail : CheckedPrivateBodyExecutions signature definitions environmentTypes
      arguments middleTypes privateEnvironmentTypes middlePrivateBindingTypes
      atoms answerTypes answerPrivateBindingTypes) :
    CheckedPrivateBodyExecutions signature definitions environmentTypes
      arguments outerBindingTypes privateEnvironmentTypes privateBindingTypes
      (atom :: atoms) answerTypes answerPrivateBindingTypes where
  prepend rest := by
    simp only [MatchingTree.ofAtoms, List.map_cons, List.cons_append]
    exact head.prepend (tail.prepend rest)

end CheckedPrivateBodyExecutions

/-- A concrete runtime target together with its retained type evidence. -/
structure CheckedPrivateBodyTarget (target : Value) : Type where
  targetType : Ty
  typed : ValueTyping target targetType

/-- An exact ordinary private leaf and the bindings it contributes. -/
structure CheckedPrivateBodyOrdinaryLeaf
    (privateEnvironmentTypes privateBindingTypes : List Ty)
    (atom : MatchingAtom) : Type where
  newPrivateBindings : List Ty
  typed : CheckedOrdinaryAtomTyping privateEnvironmentTypes privateBindingTypes
    atom newPrivateBindings

/-- Evidence that cannot be manufactured from a checked definition alone.
`targets` types the actual runtime target used by private variables and
wildcards.  `ordinary` is queried only for value patterns and disjunctions;
its exact atom certificate retains expression typing and every branch.
`constructors` is a separate proof-bearing boundary for constructor patterns:
the compiler does not infer a user matcher's decomposition from its erased
runtime value, but accepts an exact ordinary-atom certificate for the concrete
constructor, matcher, and target.
`applications` supplies the checked frozen lookup and concrete execution for
a nested call, using the same proof-bearing boundary as the nested compiler. -/
structure CheckedPrivateBodyResolver
    (signature : FrozenSignature)
    (definitions : PatternFunctionDefinitions)
    (environmentTypes : List Ty) (arguments : List Pattern) : Type where
  exports : CheckedBodyExportResolver signature definitions environmentTypes
    arguments
  targets : (target : Value) → Option (CheckedPrivateBodyTarget target)
  ordinary : (privateEnvironmentTypes privateBindingTypes : List Ty) →
    (atom : MatchingAtom) →
    Option (CheckedPrivateBodyOrdinaryLeaf privateEnvironmentTypes
      privateBindingTypes atom)
  constructors : (privateEnvironmentTypes privateBindingTypes : List Ty) →
    (constructor : PatternCtor) → (fields : List Pattern) →
    (matcher target : Value) →
    Option (CheckedPrivateBodyOrdinaryLeaf privateEnvironmentTypes
      privateBindingTypes ⟨.ctor constructor fields, matcher, target⟩)
  applications : (outerBindingTypes : List Ty) → (name : PatternFunName) →
    (nestedArguments : List Pattern) → (matcher target : Value) →
    Option (CheckedBodyResolvedApplication signature definitions
      environmentTypes arguments outerBindingTypes name nestedArguments matcher
      target)

/-- The dependent result of compiling one body atom with both frame outputs. -/
abbrev CheckedPrivateBodyCompileResult
    (signature : FrozenSignature)
    (definitions : PatternFunctionDefinitions)
    (environmentTypes : List Ty) (arguments : List Pattern)
    (outerBindingTypes privateEnvironmentTypes privateBindingTypes : List Ty)
    (atom : MatchingAtom) :=
  Σ answerTypes, Σ answerPrivateBindingTypes,
    CheckedPrivateBodyExecution signature definitions environmentTypes arguments
      outerBindingTypes privateEnvironmentTypes privateBindingTypes atom
      answerTypes answerPrivateBindingTypes

/-- Recursive compilation for embedded arguments, private variables and
wildcards, proof-bearing nested applications, structural conjunctions and
tuples, and explicitly certified value or disjunction atoms. -/
def CheckedPrivateBodyExecution.compileFuel
    (resolver : CheckedPrivateBodyResolver signature definitions
      environmentTypes arguments) :
    (fuel : Nat) → (outerBindingTypes privateEnvironmentTypes
      privateBindingTypes : List Ty) → (atom : MatchingAtom) →
      Option (CheckedPrivateBodyCompileResult signature definitions
        environmentTypes arguments outerBindingTypes privateEnvironmentTypes
        privateBindingTypes atom)
  | 0, _, _, _, _ => none
  | _ + 1, outerBindingTypes, privateEnvironmentTypes, privateBindingTypes,
      ⟨.embed index, matcher, target⟩ => do
      let ⟨answerTypes, execution⟩ ←
        resolver.exports.resolve outerBindingTypes index matcher target
      pure ⟨answerTypes, privateBindingTypes,
        ⟨fun tail => execution.plan.prepend tail⟩⟩
  | _ + 1, outerBindingTypes, privateEnvironmentTypes, privateBindingTypes,
      ⟨.var, .something, target⟩ => do
      let resolved ← resolver.targets target
      pure ⟨outerBindingTypes, privateBindingTypes ++ [resolved.targetType],
        CheckedPrivateBodyExecution.var resolved.typed⟩
  | _ + 1, outerBindingTypes, privateEnvironmentTypes, privateBindingTypes,
      ⟨.wild, .something, target⟩ => do
      let resolved ← resolver.targets target
      pure ⟨outerBindingTypes, privateBindingTypes,
        CheckedPrivateBodyExecution.wild resolved.typed⟩
  | _ + 1, outerBindingTypes, privateEnvironmentTypes, privateBindingTypes,
      ⟨.value expression, matcher, target⟩ => do
      let resolved ←
        resolver.ordinary privateEnvironmentTypes privateBindingTypes
          ⟨.value expression, matcher, target⟩
      pure ⟨outerBindingTypes,
        privateBindingTypes ++ resolved.newPrivateBindings,
        CheckedPrivateBodyExecution.ordinary resolved.typed⟩
  | _ + 1, outerBindingTypes, privateEnvironmentTypes, privateBindingTypes,
      ⟨.or left right, matcher, target⟩ => do
      let resolved ←
        resolver.ordinary privateEnvironmentTypes privateBindingTypes
          ⟨.or left right, matcher, target⟩
      pure ⟨outerBindingTypes,
        privateBindingTypes ++ resolved.newPrivateBindings,
        CheckedPrivateBodyExecution.ordinary resolved.typed⟩
  | _ + 1, outerBindingTypes, privateEnvironmentTypes, privateBindingTypes,
      ⟨.ctor constructor fields, matcher, target⟩ => do
      let resolved ← resolver.constructors privateEnvironmentTypes
        privateBindingTypes constructor fields matcher target
      pure ⟨outerBindingTypes,
        privateBindingTypes ++ resolved.newPrivateBindings,
        CheckedPrivateBodyExecution.ordinary resolved.typed⟩
  | _ + 1, outerBindingTypes, privateEnvironmentTypes, privateBindingTypes,
      ⟨.app name nestedArguments, matcher, target⟩ => do
      let resolved ← resolver.applications outerBindingTypes name
        nestedArguments matcher target
      pure ⟨resolved.answerTypes, privateBindingTypes,
        CheckedPrivateBodyExecution.application resolved⟩
  | fuel + 1, outerBindingTypes, privateEnvironmentTypes, privateBindingTypes,
      ⟨.and left right, .something, target⟩ => do
      let ⟨middleTypes, middlePrivateBindingTypes, leftExecution⟩ ←
        CheckedPrivateBodyExecution.compileFuel resolver fuel outerBindingTypes
          privateEnvironmentTypes privateBindingTypes
          ⟨left, .something, target⟩
      let ⟨answerTypes, answerPrivateBindingTypes, rightExecution⟩ ←
        CheckedPrivateBodyExecution.compileFuel resolver fuel middleTypes
          privateEnvironmentTypes middlePrivateBindingTypes
          ⟨right, .something, target⟩
      pure ⟨answerTypes, answerPrivateBindingTypes,
        CheckedPrivateBodyExecution.and leftExecution rightExecution⟩
  | fuel + 1, outerBindingTypes, privateEnvironmentTypes, privateBindingTypes,
      ⟨.tuple patterns, .tuple matchers, .tuple targets⟩ =>
      match zipped : zipMatchingAtoms patterns matchers targets with
      | none => none
      | some atoms =>
          let rec compileAtoms (outerTypes privateTypes : List Ty) :
              (remaining : List MatchingAtom) →
                Option (Σ answerTypes, Σ answerPrivateBindingTypes,
                  CheckedPrivateBodyExecutions signature definitions
                    environmentTypes arguments outerTypes
                    privateEnvironmentTypes privateTypes remaining answerTypes
                    answerPrivateBindingTypes)
            | [] => some ⟨outerTypes, privateTypes,
                CheckedPrivateBodyExecutions.nil⟩
            | head :: tail => do
                let ⟨middleTypes, middlePrivateTypes, headExecution⟩ ←
                  CheckedPrivateBodyExecution.compileFuel resolver fuel
                    outerTypes privateEnvironmentTypes privateTypes head
                let ⟨answerTypes, answerPrivateTypes, tailExecutions⟩ ←
                  compileAtoms middleTypes middlePrivateTypes tail
                pure ⟨answerTypes, answerPrivateTypes,
                  CheckedPrivateBodyExecutions.cons headExecution
                    tailExecutions⟩
          match compileAtoms outerBindingTypes privateBindingTypes atoms with
          | none => none
          | some ⟨answerTypes, answerPrivateBindingTypes, children⟩ =>
              some ⟨answerTypes, answerPrivateBindingTypes,
                CheckedPrivateBodyExecution.tuple zipped children⟩
  | _ + 1, _, _, _, _ => none

def CheckedPrivateBodyExecution.compile
    (resolver : CheckedPrivateBodyResolver signature definitions
      environmentTypes arguments)
    (outerBindingTypes privateEnvironmentTypes privateBindingTypes : List Ty)
    (atom : MatchingAtom) :
    Option (CheckedPrivateBodyCompileResult signature definitions
      environmentTypes arguments outerBindingTypes privateEnvironmentTypes
      privateBindingTypes atom) :=
  CheckedPrivateBodyExecution.compileFuel resolver
    (atom.pattern.complexity + 1) outerBindingTypes privateEnvironmentTypes
    privateBindingTypes atom

namespace CheckedScopedWorkTyping

/-- Open a checked body plan at the actual fresh private frame used by an
MNode.  Private bindings may change while outer exports remain independently
indexed; node completion discards the final private frame. -/
theorem applicationOfCheckedPrivateBodyExecution
    (agreement : definitions.Agree signature)
    (found : definitions.lookup name = some definition)
    (arity : arguments.length = definition.parameterCount)
    (execution : CheckedPrivateBodyExecution signature definitions
      environmentTypes arguments bindingTypes environmentTypes []
      ⟨definition.body, matcher, target⟩ afterNodeTypes
      afterPrivateBindingTypes)
    (tail : CheckedScopedWorkTyping signature definitions environmentTypes
      afterNodeTypes remaining answerTypes) :
    CheckedScopedWorkTyping signature definitions environmentTypes bindingTypes
      (.atom ⟨.app name arguments, matcher, target⟩ :: remaining)
      answerTypes :=
  applicationOfAgreement agreement found arity
    (execution.prepend (.nil : CheckedMNodeWorkTyping signature definitions
      environmentTypes afterNodeTypes arguments environmentTypes
      afterPrivateBindingTypes [] afterNodeTypes)) tail

end CheckedScopedWorkTyping

end TypePM.Runtime
