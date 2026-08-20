import TypePM.Source.M4FixCoherence

/-!
# Constructor-local executable replay for M4

This module isolates the computation-preserving part of M4 replay.  An exact
fuel replay says that the executable elaborator returns the same generated
block and finishing supply as a fuel-indexed relational derivation.  Exactness
is stronger than the final public replay interface, but it is precisely the
property that composes through source-ordered children without an additional
supply-coherence argument.

The ordinary M2 roots and `fixE` preserve exact replay of their recursive
expression positions.  A representative-changing `letE` does not in general
preserve it; integrating that case therefore remains a separate boundary.
-/

namespace TypePM.Source.M4.CompletenessArchitecture

open TypePM.Source

/-- A fuel-indexed relational derivation is returned literally by the
fuel-indexed executable elaborator. -/
def ExactM4FuelReplayProperty (expression : Expr) : Prop :=
  ∀ {signature : FrozenSignature} {fuel : Nat} {context : Context}
      {supply next : Supply} {generated : Generated},
    ElaboratesFuel signature fuel context expression supply generated next →
      M4.elaborateFuel signature fuel context expression supply =
        some (generated, next)

/-- Exact fuel replay immediately supplies the architecture's public replay
witness at the syntax-complexity fuel. -/
theorem ExactM4FuelReplayProperty.executableReplay
    {expression : Expr} (replay : ExactM4FuelReplayProperty expression)
    {signature : FrozenSignature} {context : Context} {supply next : Supply}
    {generated : Generated}
    (derivation : ElaboratesFuel signature (expression.complexity + 1) context
      expression supply generated next) :
    ExecutableElaborationReplay signature context expression supply := by
  refine ⟨generated, next, ?_, ⟨expression.complexity + 1, derivation⟩⟩
  simpa [M4.elaborate] using replay derivation

/-- A successful fuel-indexed executable run together with a derivation of
the block and supply returned by that run. -/
def ExecutableM4FuelReplay
    (signature : FrozenSignature) (fuel : Nat) (context : Context)
    (expression : Expr) (supply : Supply) : Prop :=
  ∃ generated next,
    M4.elaborateFuel signature fuel context expression supply =
        some (generated, next) ∧
      ElaboratesFuel signature fuel context expression supply generated next

/-- Fuel-local replay permits the executable representative to differ from
the independently chosen relational representative.  Signature
well-formedness makes the already proved M4 coherence theorem available for
aligning the finishing supplies of sequential children. -/
def M4FuelReplayProperty (expression : Expr) : Prop :=
  ∀ {signature : FrozenSignature} {fuel : Nat} {context : Context}
      {supply next : Supply} {generated : Generated},
    ElaboratesFuel signature fuel context expression supply generated next →
      signature.WellFormed → supply.WellFormedFor context →
        ExecutableM4FuelReplay signature fuel context expression supply

/-- A fuel-local replay at the public fuel is already the public executable
replay required by the architecture. -/
theorem M4FuelReplayProperty.executableReplay
    {expression : Expr} (replay : M4FuelReplayProperty expression)
    {signature : FrozenSignature} {context : Context} {supply next : Supply}
    {generated : Generated}
    (derivation : ElaboratesFuel signature (expression.complexity + 1) context
      expression supply generated next)
    (signatureWellFormed : signature.WellFormed)
    (wellFormed : supply.WellFormedFor context) :
    ExecutableElaborationReplay signature context expression supply := by
  obtain ⟨computed, computedNext, executable, computedDerivation⟩ :=
    replay derivation signatureWellFormed wellFormed
  exact ⟨computed, computedNext, by simpa [M4.elaborate] using executable,
    ⟨expression.complexity + 1, computedDerivation⟩⟩

/-- Exact replay for every expression occurring in a source-ordered sibling
list makes the callback-parametric list elaborator replay literally. -/
theorem exactItemsReplay_of_each
    {items : List Expr}
    (each : ∀ item, item ∈ items → ExactM4FuelReplayProperty item)
    {signature : FrozenSignature} {fuel : Nat} {context : Context}
    {supply next : Supply} {generated : GeneratedItems}
    (derivation : ItemsElaborateUsing (ElaboratesFuel signature fuel) context
      items supply generated next) :
    M4.elaborateItemsUsing (M4.elaborateFuel signature fuel) context items
      supply = some (generated, next) := by
  induction derivation with
  | nil => simp [M4.elaborateItemsUsing]
  | @cons item items supply generatedItem afterItem generatedItems next
      head tail induction =>
      have headReplay := each item (by simp) head
      have tailReplay := induction (by
        intro candidate member
        exact each candidate (by simp [member]))
      simp [M4.elaborateItemsUsing, headReplay, tailReplay]

/-- Exact replay for every remaining call argument makes the call fold replay
literally, for any fixed accumulated generated block. -/
theorem exactCallReplay_of_each
    {arguments : List Expr}
    (each : ∀ argument, argument ∈ arguments →
      ExactM4FuelReplayProperty argument)
    {signature : FrozenSignature} {fuel : Nat} {context : Context}
    {accumulated generated : Generated} {supply next : Supply}
    (derivation : CallElaboratesUsing (ElaboratesFuel signature fuel) context
      accumulated arguments supply generated next) :
    M4.elaborateCallUsing (M4.elaborateFuel signature fuel) context accumulated
      arguments supply = some (generated, next) := by
  induction derivation with
  | nil => simp [M4.elaborateCallUsing]
  | @cons accumulated argument arguments supply generatedArgument afterArgument
      generated next head tail induction =>
      have headReplay := each argument (by simp) head
      have tailReplay := induction (by
        intro candidate member
        exact each candidate (by simp [member]))
      simp [M4.elaborateCallUsing, headReplay, tailReplay]

/-- Non-exact list replay, retaining a derivation of the executable list
result so that an enclosing constructor can continue composition. -/
def ExecutableM4ItemsFuelReplay
    (signature : FrozenSignature) (fuel : Nat) (context : Context)
    (items : List Expr) (supply : Supply) : Prop :=
  ∃ generated next,
    M4.elaborateItemsUsing (M4.elaborateFuel signature fuel) context items
        supply = some (generated, next) ∧
      ItemsElaborateUsing (ElaboratesFuel signature fuel) context items supply
        generated next

/-- Non-exact call-fold replay. -/
def ExecutableM4CallFuelReplay
    (signature : FrozenSignature) (fuel : Nat) (context : Context)
    (accumulated : Generated) (arguments : List Expr)
    (supply : Supply) : Prop :=
  ∃ generated next,
    M4.elaborateCallUsing (M4.elaborateFuel signature fuel) context accumulated
        arguments supply = some (generated, next) ∧
      CallElaboratesUsing (ElaboratesFuel signature fuel) context accumulated
        arguments supply generated next

/-- Sibling expressions replay in source order.  Coherence identifies the
finishing supply chosen for each replayed head with the supply at which the
original tail derivation starts. -/
theorem executableItemsFuelReplay_of_each
    {items : List Expr}
    (coherent : ∀ item, item ∈ items → FullM4FuelPairProperty item)
    (replay : ∀ item, item ∈ items → M4FuelReplayProperty item)
    {signature : FrozenSignature} {fuel : Nat} {context : Context}
    {supply next : Supply} {generated : GeneratedItems}
    (derivation : ItemsElaborateUsing (ElaboratesFuel signature fuel) context
      items supply generated next)
    (signatureWellFormed : signature.WellFormed)
    (wellFormed : supply.WellFormedFor context) :
    ExecutableM4ItemsFuelReplay signature fuel context items supply := by
  induction derivation with
  | nil => exact ⟨_, _, by simp [M4.elaborateItemsUsing], .nil⟩
  | @cons item items supply generatedItem afterItem generatedItems next
      head tail induction =>
      obtain ⟨computedItem, computedAfterItem, headExecutable,
          computedHead⟩ :=
        replay item (by simp) head signatureWellFormed wellFormed
      obtain ⟨headCoherence⟩ := coherent item (by simp)
        signatureWellFormed wellFormed head computedHead
      cases headCoherence.next_eq
      obtain ⟨computedItems, computedNext, tailExecutable, computedTail⟩ :=
        induction
          (by
            intro candidate member
            exact coherent candidate (by simp [member]))
          (by
            intro candidate member
            exact replay candidate (by simp [member]))
          (wellFormed.mono computedHead.supply_le_next)
      exact ⟨_, computedNext,
        by simp [M4.elaborateItemsUsing, headExecutable, tailExecutable],
        .cons computedHead computedTail⟩

/-- Call arguments replay in source order, while allowing the accumulated
generated block to be replaced by an enclosing executable replay. -/
theorem executableCallFuelReplay_of_each
    {arguments : List Expr}
    (coherent : ∀ argument, argument ∈ arguments →
      FullM4FuelPairProperty argument)
    (replay : ∀ argument, argument ∈ arguments →
      M4FuelReplayProperty argument)
    {signature : FrozenSignature} {fuel : Nat} {context : Context}
    {accumulated generated : Generated} {supply next : Supply}
    (derivation : CallElaboratesUsing (ElaboratesFuel signature fuel) context
      accumulated arguments supply generated next)
    (replayAccumulated : Generated)
    (signatureWellFormed : signature.WellFormed)
    (wellFormed : supply.WellFormedFor context) :
    ExecutableM4CallFuelReplay signature fuel context replayAccumulated arguments
      supply := by
  induction derivation generalizing replayAccumulated with
  | nil => exact ⟨_, _, by simp [M4.elaborateCallUsing], .nil⟩
  | @cons accumulated argument arguments supply generatedArgument afterArgument
      generated next head tail induction =>
      obtain ⟨computedArgument, computedAfterArgument, headExecutable,
          computedHead⟩ :=
        replay argument (by simp) head signatureWellFormed wellFormed
      obtain ⟨headCoherence⟩ := coherent argument (by simp)
        signatureWellFormed wellFormed head computedHead
      cases headCoherence.next_eq
      obtain ⟨computed, computedNext, tailExecutable, computedTail⟩ :=
        induction
          (by
            intro candidate member
            exact coherent candidate (by simp [member]))
          (by
            intro candidate member
            exact replay candidate (by simp [member]))
          (Generated.fromApp replayAccumulated computedArgument
            (.var ⟨afterArgument.ty⟩)
            (.var ⟨afterArgument.ty + 1⟩))
          ((wellFormed.mono computedHead.supply_le_next).nextTy 2)
      exact ⟨computed, computedNext,
        by simp [M4.elaborateCallUsing, headExecutable, tailExecutable],
        .cons computedHead computedTail⟩

/-- Constructor-local exact replay obligation for roots inherited from M2.
The recursive premise deliberately ranges over all smaller expressions, so a
later complexity induction may instantiate it at lambda bodies, siblings, and
call arguments. -/
def OrdinaryM4ExactReplayStep : Prop :=
  ∀ (expression : Expr), M2NonLetRoot expression →
    (∀ smaller : Expr, smaller.complexity < expression.complexity →
      ExactM4FuelReplayProperty smaller) →
    ExactM4FuelReplayProperty expression

private theorem expression_complexity_lt_list_succ
    {expression : Expr} {expressions : List Expr}
    (member : expression ∈ expressions) :
    expression.complexity < Expr.listComplexity expressions + 1 := by
  induction expressions with
  | nil => simp at member
  | cons head tail induction =>
      simp only [List.mem_cons] at member
      rcases member with equality | tailMember
      · subst expression
        simp [Expr.listComplexity]
        omega
      · have smaller := induction tailMember
        simp [Expr.listComplexity]
        omega

/-- Every ordinary M2 root preserves exact executable replay of its recursive
M4 children.  No signature well-formedness premise is needed: constructor
lookup and arity evidence are reused directly from the given derivation. -/
theorem ordinaryM4ExactReplayStep : OrdinaryM4ExactReplayStep := by
  intro expression root induction
  intro signature fuel context supply next generated derivation
  cases fuel with
  | zero => simp [ElaboratesFuel] at derivation
  | succ fuel =>
      cases root with
      | var index =>
          simp only [ElaboratesFuel] at derivation
          obtain ⟨scheme, lookup, rfl, rfl⟩ := derivation
          simp [M4.elaborateFuel, M4.elaborateFuelUsing, lookup]
      | lit value =>
          simp only [ElaboratesFuel] at derivation
          obtain ⟨rfl, rfl⟩ := derivation
          simp [M4.elaborateFuel, M4.elaborateFuelUsing]
      | something =>
          simp only [ElaboratesFuel] at derivation
          obtain ⟨rfl, rfl⟩ := derivation
          simp [M4.elaborateFuel, M4.elaborateFuelUsing]
      | lam body =>
          simp only [ElaboratesFuel] at derivation
          obtain ⟨generatedBody, bodyDerivation, rfl⟩ := derivation
          have bodyReplay := induction body (by
            simp [Expr.complexity]) bodyDerivation
          have bodyReplayUsing :
              M4.elaborateFuelUsing unify signature fuel
                  (.mono (.var ⟨supply.ty⟩) :: context) body
                  (supply.nextTy 1) = some (generatedBody, next) := by
            simpa [M4.elaborateFuel] using bodyReplay
          simp [M4.elaborateFuel, M4.elaborateFuelUsing, bodyReplayUsing]
      | app function argument =>
          simp only [ElaboratesFuel] at derivation
          obtain ⟨generatedFunction, afterFunction, generatedArgument,
            afterArgument, functionDerivation, argumentDerivation, rfl, rfl⟩ :=
            derivation
          have functionReplay := induction function (by
            simp [Expr.complexity]
            omega) functionDerivation
          have argumentReplay := induction argument (by
            simp [Expr.complexity]
            omega) argumentDerivation
          have functionReplayUsing :
              M4.elaborateFuelUsing unify signature fuel context function
                supply = some (generatedFunction, afterFunction) := by
            simpa [M4.elaborateFuel] using functionReplay
          have argumentReplayUsing :
              M4.elaborateFuelUsing unify signature fuel context argument
                afterFunction = some (generatedArgument, afterArgument) := by
            simpa [M4.elaborateFuel] using argumentReplay
          simp [M4.elaborateFuel, M4.elaborateFuelUsing, functionReplayUsing,
            argumentReplayUsing]
      | tuple items =>
          simp only [ElaboratesFuel] at derivation
          obtain ⟨generatedItems, itemsDerivation, rfl⟩ := derivation
          have itemsReplay := exactItemsReplay_of_each (derivation := itemsDerivation)
            (fun item member => induction item (by
              have smaller := expression_complexity_lt_list_succ member
              simpa [Expr.complexity] using smaller))
          have itemsReplayUsing :
              M4.elaborateItemsUsing
                  (M4.elaborateFuelUsing unify signature fuel) context items
                  supply = some (generatedItems, next) := by
            simpa [M4.elaborateFuel] using itemsReplay
          simp [M4.elaborateFuel, M4.elaborateFuelUsing, itemsReplayUsing]
      | ctor constructor arguments =>
          simp only [ElaboratesFuel] at derivation
          obtain ⟨scheme, lookup, arity, _closed, callDerivation⟩ := derivation
          have callReplay := exactCallReplay_of_each (derivation := callDerivation)
            (fun argument member => induction argument (by
              have smaller := expression_complexity_lt_list_succ member
              simpa [Expr.complexity] using smaller))
          have callReplayUsing :
              M4.elaborateCallUsing
                  (M4.elaborateFuelUsing unify signature fuel) context
                  ⟨(scheme.instantiate supply).1, [], []⟩ arguments
                  (scheme.instantiate supply).2 = some (generated, next) := by
            simpa [M4.elaborateFuel] using callReplay
          simp [M4.elaborateFuel, M4.elaborateFuelUsing, lookup, arity,
            callReplayUsing]
      | prim operation arguments =>
          simp only [ElaboratesFuel] at derivation
          obtain ⟨scheme, lookup, arity, _closed, callDerivation⟩ := derivation
          have callReplay := exactCallReplay_of_each (derivation := callDerivation)
            (fun argument member => induction argument (by
              have smaller := expression_complexity_lt_list_succ member
              simpa [Expr.complexity] using smaller))
          have callReplayUsing :
              M4.elaborateCallUsing
                  (M4.elaborateFuelUsing unify signature fuel) context
                  ⟨(scheme.instantiate supply).1, [], []⟩ arguments
                  (scheme.instantiate supply).2 = some (generated, next) := by
            simpa [M4.elaborateFuel] using callReplay
          simp [M4.elaborateFuel, M4.elaborateFuelUsing, lookup, arity,
            callReplayUsing]
      | ifE condition thenBranch elseBranch =>
          simp only [ElaboratesFuel] at derivation
          have callReplay := exactCallReplay_of_each (derivation := derivation)
            (fun argument member => induction argument (by
              simp only [List.mem_cons, List.not_mem_nil, or_false] at member
              rcases member with rfl | rfl | rfl
              <;> simp [Expr.complexity]
              <;> omega))
          simpa [M4.elaborateFuel, M4.elaborateFuelUsing] using callReplay

/-- Constructor-local non-exact replay for ordinary roots.  Recursive replay
produces fresh executable representatives; recursive coherence is used only
to identify the finishing supplies needed by sequential composition. -/
def OrdinaryM4FuelReplayStep : Prop :=
  ∀ (expression : Expr), M2NonLetRoot expression →
    (∀ smaller : Expr, smaller.complexity < expression.complexity →
      FullM4FuelPairProperty smaller) →
    (∀ smaller : Expr, smaller.complexity < expression.complexity →
      M4FuelReplayProperty smaller) →
    M4FuelReplayProperty expression

/-- All ordinary roots preserve fuel-local executable replay. -/
theorem ordinaryM4FuelReplayStep : OrdinaryM4FuelReplayStep := by
  intro expression root coherent replay
  intro signature fuel context supply next generated derivation
    signatureWellFormed wellFormed
  cases fuel with
  | zero => simp [ElaboratesFuel] at derivation
  | succ fuel =>
      cases root with
      | var index =>
          simp only [ElaboratesFuel] at derivation
          obtain ⟨scheme, lookup, rfl, rfl⟩ := derivation
          exact ⟨_, _, by simp [M4.elaborateFuel, M4.elaborateFuelUsing, lookup],
            ⟨scheme, lookup, rfl, rfl⟩⟩
      | lit value =>
          simp only [ElaboratesFuel] at derivation
          obtain ⟨rfl, rfl⟩ := derivation
          exact ⟨_, _, by simp [M4.elaborateFuel, M4.elaborateFuelUsing],
            ⟨rfl, rfl⟩⟩
      | something =>
          simp only [ElaboratesFuel] at derivation
          obtain ⟨rfl, rfl⟩ := derivation
          exact ⟨_, _, by simp [M4.elaborateFuel, M4.elaborateFuelUsing],
            ⟨rfl, rfl⟩⟩
      | lam body =>
          simp only [ElaboratesFuel] at derivation
          obtain ⟨generatedBody, bodyDerivation, rfl⟩ := derivation
          obtain ⟨computedBody, computedNext, bodyExecutable,
              computedBodyDerivation⟩ :=
            replay body (by simp [Expr.complexity]) bodyDerivation
              signatureWellFormed wellFormed.monomorphic_cons_nextTy
          have bodyExecutableUsing :
              M4.elaborateFuelUsing unify signature fuel
                  (.mono (.var ⟨supply.ty⟩) :: context) body
                  (supply.nextTy 1) = some (computedBody, computedNext) := by
            simpa [M4.elaborateFuel] using bodyExecutable
          exact ⟨_, computedNext,
            by simp [M4.elaborateFuel, M4.elaborateFuelUsing,
              bodyExecutableUsing],
            ⟨computedBody, computedBodyDerivation, rfl⟩⟩
      | app function argument =>
          simp only [ElaboratesFuel] at derivation
          obtain ⟨generatedFunction, afterFunction, generatedArgument,
            afterArgument, functionDerivation, argumentDerivation, rfl, rfl⟩ :=
            derivation
          obtain ⟨computedFunction, computedAfterFunction,
              functionExecutable, computedFunctionDerivation⟩ :=
            replay function (by
              simp [Expr.complexity]
              omega) functionDerivation signatureWellFormed wellFormed
          obtain ⟨functionCoherence⟩ := coherent function (by
            simp [Expr.complexity]
            omega) signatureWellFormed wellFormed functionDerivation
              computedFunctionDerivation
          cases functionCoherence.next_eq
          obtain ⟨computedArgument, computedAfterArgument,
              argumentExecutable, computedArgumentDerivation⟩ :=
            replay argument (by
              simp [Expr.complexity]
              omega) argumentDerivation signatureWellFormed
                (wellFormed.mono computedFunctionDerivation.supply_le_next)
          have functionExecutableUsing :
              M4.elaborateFuelUsing unify signature fuel context function supply =
                some (computedFunction, afterFunction) := by
            simpa [M4.elaborateFuel] using functionExecutable
          have argumentExecutableUsing :
              M4.elaborateFuelUsing unify signature fuel context argument
                  afterFunction =
                some (computedArgument, computedAfterArgument) := by
            simpa [M4.elaborateFuel] using argumentExecutable
          exact ⟨_, computedAfterArgument.nextTy 2,
            by simp [M4.elaborateFuel, M4.elaborateFuelUsing,
              functionExecutableUsing, argumentExecutableUsing],
            ⟨computedFunction, afterFunction, computedArgument,
              computedAfterArgument, computedFunctionDerivation,
              computedArgumentDerivation, rfl, rfl⟩⟩
      | tuple items =>
          simp only [ElaboratesFuel] at derivation
          obtain ⟨generatedItems, itemsDerivation, rfl⟩ := derivation
          obtain ⟨computedItems, computedNext, itemsExecutable,
              computedItemsDerivation⟩ :=
            executableItemsFuelReplay_of_each
              (fun item member => coherent item (by
                have smaller := expression_complexity_lt_list_succ member
                simpa [Expr.complexity] using smaller))
              (fun item member => replay item (by
                have smaller := expression_complexity_lt_list_succ member
                simpa [Expr.complexity] using smaller))
              itemsDerivation signatureWellFormed wellFormed
          have itemsExecutableUsing :
              M4.elaborateItemsUsing
                  (M4.elaborateFuelUsing unify signature fuel) context items
                  supply = some (computedItems, computedNext) := by
            simpa [M4.elaborateFuel] using itemsExecutable
          exact ⟨_, computedNext,
            by simp [M4.elaborateFuel, M4.elaborateFuelUsing,
              itemsExecutableUsing],
            ⟨computedItems, computedItemsDerivation, rfl⟩⟩
      | ctor constructor arguments =>
          simp only [ElaboratesFuel] at derivation
          obtain ⟨scheme, lookup, arity, closed, callDerivation⟩ := derivation
          obtain ⟨computed, computedNext, callExecutable, computedCall⟩ :=
            executableCallFuelReplay_of_each
              (fun argument member => coherent argument (by
                have smaller := expression_complexity_lt_list_succ member
                simpa [Expr.complexity] using smaller))
              (fun argument member => replay argument (by
                have smaller := expression_complexity_lt_list_succ member
                simpa [Expr.complexity] using smaller))
              callDerivation _ signatureWellFormed
              (wellFormed.mono (by simp [Supply.Le, Scheme.instantiate]))
          have callExecutableUsing :
              M4.elaborateCallUsing
                  (M4.elaborateFuelUsing unify signature fuel) context
                  ⟨(scheme.instantiate supply).1, [], []⟩ arguments
                  (scheme.instantiate supply).2 =
                some (computed, computedNext) := by
            simpa [M4.elaborateFuel] using callExecutable
          exact ⟨computed, computedNext,
            by simp [M4.elaborateFuel, M4.elaborateFuelUsing, lookup, arity,
              callExecutableUsing],
            ⟨scheme, lookup, arity, closed, computedCall⟩⟩
      | prim operation arguments =>
          simp only [ElaboratesFuel] at derivation
          obtain ⟨scheme, lookup, arity, closed, callDerivation⟩ := derivation
          obtain ⟨computed, computedNext, callExecutable, computedCall⟩ :=
            executableCallFuelReplay_of_each
              (fun argument member => coherent argument (by
                have smaller := expression_complexity_lt_list_succ member
                simpa [Expr.complexity] using smaller))
              (fun argument member => replay argument (by
                have smaller := expression_complexity_lt_list_succ member
                simpa [Expr.complexity] using smaller))
              callDerivation _ signatureWellFormed
              (wellFormed.mono (by simp [Supply.Le, Scheme.instantiate]))
          have callExecutableUsing :
              M4.elaborateCallUsing
                  (M4.elaborateFuelUsing unify signature fuel) context
                  ⟨(scheme.instantiate supply).1, [], []⟩ arguments
                  (scheme.instantiate supply).2 =
                some (computed, computedNext) := by
            simpa [M4.elaborateFuel] using callExecutable
          exact ⟨computed, computedNext,
            by simp [M4.elaborateFuel, M4.elaborateFuelUsing, lookup, arity,
              callExecutableUsing],
            ⟨scheme, lookup, arity, closed, computedCall⟩⟩
      | ifE condition thenBranch elseBranch =>
          simp only [ElaboratesFuel] at derivation
          obtain ⟨computed, computedNext, callExecutable, computedCall⟩ :=
            executableCallFuelReplay_of_each
              (fun argument member => coherent argument (by
                simp only [List.mem_cons, List.not_mem_nil, or_false] at member
                rcases member with rfl | rfl | rfl
                <;> simp [Expr.complexity]
                <;> omega))
              (fun argument member => replay argument (by
                simp only [List.mem_cons, List.not_mem_nil, or_false] at member
                rcases member with rfl | rfl | rfl
                <;> simp [Expr.complexity]
                <;> omega))
              derivation _ signatureWellFormed
              (wellFormed.mono (by
                simp [Supply.Le, Scheme.instantiate]))
          have callExecutableUsing :
              M4.elaborateCallUsing
                  (M4.elaborateFuelUsing unify signature fuel) context
                  ⟨(conditionalScheme.instantiate supply).1, [], []⟩
                  [condition, thenBranch, elseBranch]
                  (conditionalScheme.instantiate supply).2 =
                some (computed, computedNext) := by
            simpa [M4.elaborateFuel] using callExecutable
          exact ⟨computed, computedNext,
            by simpa [M4.elaborateFuel, M4.elaborateFuelUsing] using
              callExecutableUsing,
            computedCall⟩

/-- Constructor-local exact replay obligation for recursive-function roots. -/
def FixM4ExactReplayStep : Prop :=
  ∀ (body : Expr),
    (∀ smaller : Expr,
      smaller.complexity < (Expr.fixE body).complexity →
      ExactM4FuelReplayProperty smaller) →
    ExactM4FuelReplayProperty (.fixE body)

/-- `fixE` preserves exact replay because its direct-self check, reserved
domain/codomain, body context, and body supply are all syntax-determined. -/
theorem fixM4ExactReplayStep : FixM4ExactReplayStep := by
  intro body induction
  intro signature fuel context supply next generated derivation
  cases fuel with
  | zero => simp [ElaboratesFuel] at derivation
  | succ fuel =>
      simp only [ElaboratesFuel] at derivation
      cases derivation with
      | @fixE _ _ generatedBody _ direct bodyDerivation =>
          have directCheck : DirectSelf.check 1 body = true :=
            (DirectSelf.holds_iff_check body).1 direct
          have bodyReplay := induction body (by
            simp [Expr.complexity]) bodyDerivation
          have bodyReplayUsing :
              M4.elaborateFuelUsing unify signature fuel
                  (Fix.bodyContext (Fix.domain body supply)
                  (Fix.codomain body supply) context)
                  body (Fix.bodySupply body supply) =
                some (generatedBody, next) := by
            simpa [M4.elaborateFuel] using bodyReplay
          simp [M4.elaborateFuel, M4.elaborateFuelUsing, elaborateFixUsing,
            directCheck, bodyReplayUsing]

/-- Constructor-local non-exact replay obligation for recursive functions. -/
def FixM4FuelReplayStep : Prop :=
  ∀ (body : Expr),
    (∀ smaller : Expr,
      smaller.complexity < (Expr.fixE body).complexity →
      M4FuelReplayProperty smaller) →
    M4FuelReplayProperty (.fixE body)

private theorem fixBodyWellFormedForReplay
    {signature : FrozenSignature} {fuel : Nat} {context : Context}
    {body : Expr} {start finish : Supply} {generated : Generated}
    (wellFormed : start.WellFormedFor context)
    (derivation : FixElaboratesUsing (ElaboratesFuel signature fuel) context
      (.fixE body) start generated finish) :
    (Fix.bodySupply body start).WellFormedFor
      (Fix.bodyContext (Fix.domain body start) (Fix.codomain body start)
        context) := by
  have tracked := M4FreshRenaming.FixElaboratesUsing.trackScope wellFormed
    (Supply.le_refl start) derivation
  cases tracked with
  | fixE _ bodyDerivation => exact bodyDerivation.2.1

/-- A recursive-function root preserves non-exact fuel-local replay of its
body.  Unlike sequential ordinary roots, it needs no coherence premise. -/
theorem fixM4FuelReplayStep : FixM4FuelReplayStep := by
  intro body replay
  intro signature fuel context supply next generated derivation
    signatureWellFormed wellFormed
  cases fuel with
  | zero => simp [ElaboratesFuel] at derivation
  | succ fuel =>
      simp only [ElaboratesFuel] at derivation
      have bodyWellFormed := fixBodyWellFormedForReplay wellFormed derivation
      cases derivation with
      | @fixE _ _ generatedBody _ direct bodyDerivation =>
          obtain ⟨computedBody, computedNext, bodyExecutable,
              computedBodyDerivation⟩ :=
            replay body (by simp [Expr.complexity]) bodyDerivation
              signatureWellFormed bodyWellFormed
          have directCheck : DirectSelf.check 1 body = true :=
            (DirectSelf.holds_iff_check body).1 direct
          have bodyExecutableUsing :
              M4.elaborateFuelUsing unify signature fuel
                  (Fix.bodyContext (Fix.domain body supply)
                    (Fix.codomain body supply) context)
                  body (Fix.bodySupply body supply) =
                some (computedBody, computedNext) := by
            simpa [M4.elaborateFuel] using bodyExecutable
          exact ⟨_, computedNext,
            by simp [M4.elaborateFuel, M4.elaborateFuelUsing,
              elaborateFixUsing, directCheck, bodyExecutableUsing],
            .fixE direct computedBodyDerivation⟩

private theorem blockAccepts_of_principal
    {generated : Generated} (closure : PrincipalBlockClosure generated) :
    BlockAccepts generated :=
  ⟨closure.finalHard, closure.finalPending, closure.hardSubstitution,
    closure.residualSubstitution, closure.saturation,
    closure.residualPrincipal.1⟩

/-- Fuel-local replay obligation for the representative-changing `letE`
root.  Value coherence supplies both finishing-supply equality and closure
alignment; the body replay theorem then runs in the executable closure's
generalized context. -/
def LetM4FuelReplayStep : Prop :=
  ∀ (value body : Expr),
    FullM4FuelPairProperty value →
    M4FuelReplayProperty value →
    M4FuelReplayProperty body →
    M4FuelReplayProperty (.letE value body)

/-- The M4 `letE` rule preserves non-exact fuel-local replay. -/
theorem letM4FuelReplayStep : LetM4FuelReplayStep := by
  intro value body valueCoherent valueReplay bodyReplay
  intro signature fuel context supply next generated derivation
    signatureWellFormed wellFormed
  cases fuel with
  | zero => simp [ElaboratesFuel] at derivation
  | succ fuel =>
      simp only [ElaboratesFuel] at derivation
      obtain ⟨generatedValue, afterValue, valueDerivation, closure,
        generatedBody, absorbing, bodyDerivation, rfl⟩ := derivation
      obtain ⟨computedValue, computedAfterValue, valueExecutable,
          computedValueDerivation⟩ :=
        valueReplay valueDerivation signatureWellFormed wellFormed
      obtain ⟨valueCoherence⟩ := valueCoherent signatureWellFormed wellFormed
        valueDerivation computedValueDerivation
      cases valueCoherence.next_eq
      have computedAccepts : BlockAccepts computedValue := by
        have transferred :=
          (valueCoherence.blockAccepts_iff .hole trivial).mp
            (blockAccepts_of_principal closure)
        change BlockAccepts computedValue at transferred
        exact transferred
      have closureIsSome :=
        computedAccepts.inferGeneratedUsing_isSome unify_completeMGUSolver
      cases closureResult : inferGeneratedUsing unify computedValue with
      | none => exact (closureIsSome closureResult).elim
      | some closedValue =>
          obtain ⟨computedClosure, substitutionEquality, targetEquality,
              computedAbsorbing⟩ :=
            inferGeneratedUsing_absorbingPrincipalBlockClosure
              unify_absorbingMGUSolver closureResult
          obtain ⟨alignment⟩ := valueCoherence.closureAlignment closure
            computedClosure absorbing computedAbsorbing
          have valueProvenance :=
            valueDerivation.supportProvenance signatureWellFormed
          have computedValueProvenance :=
            computedValueDerivation.supportProvenance signatureWellFormed
          have originalBodyStart := PrincipalBlockClosure.letBodySupply_eq
            closure absorbing valueProvenance wellFormed
            valueDerivation.supply_le_next
          have computedBodyStart := PrincipalBlockClosure.letBodySupply_eq
            computedClosure computedAbsorbing computedValueProvenance wellFormed
            computedValueDerivation.supply_le_next
          have originalBodyAtBoundary := bodyDerivation
          rw [originalBodyStart] at originalBodyAtBoundary
          have originalClosedWellFormed : afterValue.WellFormedFor
              (context.applyFree closure.substitution) :=
            PrincipalBlockClosure.closedContext_initialSupply_le closure absorbing
              valueProvenance wellFormed valueDerivation.supply_le_next
          have originalBodyWellFormed : afterValue.WellFormedFor
              ((context.applyFree closure.substitution).generalize closure.target ::
                context.applyFree closure.substitution) :=
            originalClosedWellFormed.generalized_cons closure.target
          have transported := M4FreshRenaming.m4FreshRenamingTransport
            signatureWellFormed originalBodyAtBoundary originalBodyWellFormed
            alignment.alignment.fixesAtOrAbove
          have bodyContextExact :
              ElaborationRenaming.renameContext alignment.alignment.alignment.rho
                  ((context.applyFree closure.substitution).generalize
                      closure.target :: context.applyFree closure.substitution) =
                ((context.applyFree computedClosure.substitution).generalize
                    computedClosure.target ::
                  context.applyFree computedClosure.substitution) := by
            change
              (((context.applyFree closure.substitution).generalize closure.target ::
                  context.applyFree closure.substitution).map
                (Scheme.applyFree
                  alignment.alignment.alignment.rho.substitution)) = _
            exact alignment.alignment.bodyContext_exact
          rw [bodyContextExact] at transported
          have computedClosedWellFormed : afterValue.WellFormedFor
              (context.applyFree computedClosure.substitution) :=
            PrincipalBlockClosure.closedContext_initialSupply_le computedClosure
              computedAbsorbing computedValueProvenance wellFormed
              computedValueDerivation.supply_le_next
          have computedBodyWellFormed : afterValue.WellFormedFor
              ((context.applyFree computedClosure.substitution).generalize
                  computedClosure.target ::
                context.applyFree computedClosure.substitution) :=
            computedClosedWellFormed.generalized_cons computedClosure.target
          obtain ⟨computedBody, computedNext, bodyExecutable,
              computedBodyAtBoundary⟩ :=
            bodyReplay transported signatureWellFormed computedBodyWellFormed
          have computedBodyDerivation := computedBodyAtBoundary
          rw [← computedBodyStart] at computedBodyDerivation
          have valueExecutableUsing :
              M4.elaborateFuelUsing unify signature fuel context value supply =
                some (computedValue, afterValue) := by
            simpa [M4.elaborateFuel] using valueExecutable
          have bodyExecutableUsing :
              M4.elaborateFuelUsing unify signature fuel
                  ((context.applyFree computedClosure.substitution).generalize
                      computedClosure.target ::
                    context.applyFree computedClosure.substitution)
                  body afterValue = some (computedBody, computedNext) := by
            simpa [M4.elaborateFuel] using bodyExecutable
          refine ⟨Generated.fromLet
              (context.interfaceEquations computedClosure.substitution)
              computedBody,
            computedNext, ?_, ?_⟩
          · simp [M4.elaborateFuel, M4.elaborateFuelUsing,
              valueExecutableUsing, closureResult, substitutionEquality,
              targetEquality, computedBodyStart, bodyExecutableUsing]
          · exact ⟨computedValue, afterValue, computedValueDerivation,
              computedClosure, computedBody, computedAbsorbing,
              computedBodyDerivation, rfl⟩

/-! The three pattern-bearing roots have distinct callback-parametric
elaborators and relations, so their exact-replay obligations are kept
separate.  These definitions are the remaining constructor-local boundary;
unlike the proved ordinary and `fixE` steps above, no theorem in this module
claims them. -/

/-- Exact replay step for matcher literals. -/
def MatcherM4ExactReplayStep : Prop :=
  ∀ (clauses : List MatcherClause),
    (∀ smaller : Expr,
      smaller.complexity < (Expr.matcher clauses).complexity →
      ExactM4FuelReplayProperty smaller) →
    ExactM4FuelReplayProperty (.matcher clauses)

/-- Exact replay step for multi-result matching. -/
def MatchAllM4ExactReplayStep : Prop :=
  ∀ (target matcher : Expr) (pattern : Pattern) (body : Expr),
    (∀ smaller : Expr,
      smaller.complexity <
        (Expr.matchAll target matcher pattern body).complexity →
      ExactM4FuelReplayProperty smaller) →
    ExactM4FuelReplayProperty (.matchAll target matcher pattern body)

/-- Exact replay step for ordered single-result matching. -/
def MatchFirstM4ExactReplayStep : Prop :=
  ∀ (target matcher : Expr) (arms : List MatchFirstArm) (fallback : Expr),
    (∀ smaller : Expr,
      smaller.complexity < (Expr.matchFirst target matcher arms fallback).complexity →
      ExactM4FuelReplayProperty smaller) →
    ExactM4FuelReplayProperty (.matchFirst target matcher arms fallback)

/-! Non-exact pattern-root steps are the interfaces needed by the full replay
induction.  Their coherence premise aligns supplies when a recursively
replayed expression (in particular a `letE`) changes representatives. -/

/-- Fuel-local replay step for matcher literals. -/
def MatcherM4FuelReplayStep : Prop :=
  ∀ (clauses : List MatcherClause),
    (∀ smaller : Expr,
      smaller.complexity < (Expr.matcher clauses).complexity →
      FullM4FuelPairProperty smaller) →
    (∀ smaller : Expr,
      smaller.complexity < (Expr.matcher clauses).complexity →
      M4FuelReplayProperty smaller) →
    M4FuelReplayProperty (.matcher clauses)

/-- Fuel-local replay step for multi-result matching. -/
def MatchAllM4FuelReplayStep : Prop :=
  ∀ (target matcher : Expr) (pattern : Pattern) (body : Expr),
    (∀ smaller : Expr,
      smaller.complexity <
        (Expr.matchAll target matcher pattern body).complexity →
      FullM4FuelPairProperty smaller) →
    (∀ smaller : Expr,
      smaller.complexity <
        (Expr.matchAll target matcher pattern body).complexity →
      M4FuelReplayProperty smaller) →
    M4FuelReplayProperty (.matchAll target matcher pattern body)

/-- Fuel-local replay step for ordered single-result matching. -/
def MatchFirstM4FuelReplayStep : Prop :=
  ∀ (target matcher : Expr) (arms : List MatchFirstArm) (fallback : Expr),
    (∀ smaller : Expr,
      smaller.complexity < (Expr.matchFirst target matcher arms fallback).complexity →
      FullM4FuelPairProperty smaller) →
    (∀ smaller : Expr,
      smaller.complexity < (Expr.matchFirst target matcher arms fallback).complexity →
      M4FuelReplayProperty smaller) →
    M4FuelReplayProperty (.matchFirst target matcher arms fallback)

/-- Public coherence also compares arbitrary fuel-indexed derivations after
their witnesses are hidden. -/
theorem fullM4FuelPairProperty_of_publicCoherence
    (coherent : FullM4Coherence) (expression : Expr) :
    FullM4FuelPairProperty expression := by
  intro signature context start leftGenerated rightGenerated leftNext rightNext
    leftFuel rightFuel signatureWellFormed wellFormed leftDerivation
    rightDerivation
  exact coherent expression signatureWellFormed wellFormed
    ⟨leftFuel, leftDerivation⟩ ⟨rightFuel, rightDerivation⟩

/-- Assemble fuel-local replay by expression complexity.  Ordinary roots,
`fixE`, and `letE` are discharged by the concrete theorems in this module;
only the three pattern-bearing constructor steps remain parameters. -/
theorem fullM4FuelReplay_of_patternSteps
    (coherent : FullM4Coherence)
    (matcher : MatcherM4FuelReplayStep)
    (matchAll : MatchAllM4FuelReplayStep)
    (matchFirst : MatchFirstM4FuelReplayStep) :
    ∀ expression, M4FuelReplayProperty expression := by
  intro expression
  apply (measure Expr.complexity).wf.induction expression
  intro current induction
  have fuelCoherent : ∀ smaller : Expr,
      smaller.complexity < current.complexity →
      FullM4FuelPairProperty smaller := by
    intro smaller _
    exact fullM4FuelPairProperty_of_publicCoherence coherent smaller
  cases current with
  | var index =>
      exact (ordinaryM4FuelReplayStep _ (.var index) fuelCoherent induction :
        M4FuelReplayProperty (.var index))
  | lit value =>
      exact (ordinaryM4FuelReplayStep _ (.lit value) fuelCoherent induction :
        M4FuelReplayProperty (.lit value))
  | something =>
      exact (ordinaryM4FuelReplayStep _ .something fuelCoherent induction :
        M4FuelReplayProperty .something)
  | lam body =>
      exact (ordinaryM4FuelReplayStep _ (.lam body) fuelCoherent induction :
        M4FuelReplayProperty (.lam body))
  | app function argument =>
      exact (ordinaryM4FuelReplayStep _ (.app function argument) fuelCoherent
        induction : M4FuelReplayProperty (.app function argument))
  | tuple items =>
      exact (ordinaryM4FuelReplayStep _ (.tuple items) fuelCoherent induction :
        M4FuelReplayProperty (.tuple items))
  | letE value body =>
      exact (letM4FuelReplayStep value body
        (fullM4FuelPairProperty_of_publicCoherence coherent value)
        (induction value (by
          show value.complexity < value.complexity + body.complexity + 1
          omega))
        (induction body (by
          show body.complexity < value.complexity + body.complexity + 1
          omega)) : M4FuelReplayProperty (.letE value body))
  | ctor constructor arguments =>
      exact (ordinaryM4FuelReplayStep _ (.ctor constructor arguments)
        fuelCoherent induction :
          M4FuelReplayProperty (.ctor constructor arguments))
  | prim operation arguments =>
      exact (ordinaryM4FuelReplayStep _ (.prim operation arguments)
        fuelCoherent induction :
          M4FuelReplayProperty (.prim operation arguments))
  | ifE condition thenBranch elseBranch =>
      exact (ordinaryM4FuelReplayStep _
        (.ifE condition thenBranch elseBranch) fuelCoherent induction :
          M4FuelReplayProperty (.ifE condition thenBranch elseBranch))
  | fixE body =>
      exact (fixM4FuelReplayStep body induction :
        M4FuelReplayProperty (.fixE body))
  | matcher clauses =>
      exact (matcher clauses fuelCoherent induction :
        M4FuelReplayProperty (.matcher clauses))
  | matchAll target matcherExpression pattern body =>
      exact (matchAll target matcherExpression pattern body fuelCoherent
        induction : M4FuelReplayProperty
          (.matchAll target matcherExpression pattern body))
  | matchFirst target matcherExpression arms fallback =>
      exact (matchFirst target matcherExpression arms fallback fuelCoherent induction :
        M4FuelReplayProperty (.matchFirst target matcherExpression arms fallback))

/-- Full fuel replay yields the architecture's representative-changing
`letE` agreement. -/
theorem m4LetClosureRepresentativeAgreement_of_fuelReplay
    (replay : ∀ expression, M4FuelReplayProperty expression) :
    M4LetClosureRepresentativeAgreement := by
  intro signature context value body supply generated next derivation
    signatureWellFormed wellFormed
  exact M4FuelReplayProperty.executableReplay (replay (.letE value body))
    derivation signatureWellFormed wellFormed

/-- Full fuel replay yields the architecture's non-`let` structural replay. -/
theorem m4StructuralReplay_of_fuelReplay
    (replay : ∀ expression, M4FuelReplayProperty expression) :
    M4StructuralReplay := by
  intro signature context expression supply generated next _notLet derivation
    signatureWellFormed wellFormed
  exact M4FuelReplayProperty.executableReplay (replay expression) derivation
    signatureWellFormed wellFormed

/-- Conditional final replay theorem.  Once the three pattern-bearing local
steps are supplied, coherence and the concrete ordinary/fix/let replay steps
produce the final public executable replay interface. -/
theorem fullM4ExecutableReplay_of_coherence_and_patternSteps
    (coherent : FullM4Coherence)
    (matcher : MatcherM4FuelReplayStep)
    (matchAll : MatchAllM4FuelReplayStep)
    (matchFirst : MatchFirstM4FuelReplayStep) :
    FullM4ExecutableReplay := by
  let replay := fullM4FuelReplay_of_patternSteps coherent matcher matchAll
    matchFirst
  exact (fullM4ExecutableReplay_of_components m4FuelNormalization
    (m4LetClosureRepresentativeAgreement_of_fuelReplay replay)
    (m4StructuralReplay_of_fuelReplay replay) : FullM4ExecutableReplay)

end TypePM.Source.M4.CompletenessArchitecture
