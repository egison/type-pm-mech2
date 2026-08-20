import TypePM.Source.FullM2Completion
import TypePM.Source.M4ElaborationFuelMonotonicity

/-!
# M4 completeness architecture

This module records the proof boundary for extending the completed M2--M3
completeness and principality argument to M4.  It is intentionally not
imported by the public inference modules yet.

The central comparison object remains `FullM2PairCoherence`.  Despite its
historical name, that structure compares two generated constraint blocks and
does not depend on the source syntax.  In particular, it contains:

* equality of the finishing fresh-name supplies;
* a semantic certificate saying that both blocks accept in the same cases;
* an alignment of their principal closures for use by a surrounding `let`.

Here, **alignment** means a finite, consistent renaming of generated type and
capability variables.  **Principal closure** means the most general solved
form of one generated constraint block.

The M2 fragment theorem below is a checked reuse result: every M4 relational
derivation that uses only M2--M3 constructors can be translated to the old
relation.  Consequently, the complete M2 graph-based `let` proof applies
unchanged to that fragment, including arbitrarily nested `let` expressions.
For a `let` whose value or body contains an M4 constructor, the old theorem
cannot be applied directly: the old relation has no derivation constructor for
that child.  The remaining interfaces at the end of this file isolate exactly
the four new source rules and the new support/renaming bridge required before
the same generated-block assembly can be reused.
-/

namespace TypePM.Source.M4.CompletenessArchitecture

open TypePM.Source

mutual

/-- Expressions in the already completed M2--M3 source fragment.  This is a
syntactic condition: it excludes `fixE`, matcher literals, `matchAll`, and
`matchFirst` everywhere, including below `let` and lambda. -/
inductive M2Fragment : Expr → Prop where
  | var (index : Nat) : M2Fragment (.var index)
  | lit (value : Int) : M2Fragment (.lit value)
  | something : M2Fragment .something
  | lam {body} : M2Fragment body → M2Fragment (.lam body)
  | app {function argument} :
      M2Fragment function → M2Fragment argument →
        M2Fragment (.app function argument)
  | tuple {items} : M2FragmentList items → M2Fragment (.tuple items)
  | letE {value body} :
      M2Fragment value → M2Fragment body → M2Fragment (.letE value body)
  | ctor {constructor arguments} :
      M2FragmentList arguments → M2Fragment (.ctor constructor arguments)
  | prim {operation arguments} :
      M2FragmentList arguments → M2Fragment (.prim operation arguments)
  | ifE {condition thenBranch elseBranch} :
      M2Fragment condition → M2Fragment thenBranch →
        M2Fragment elseBranch →
          M2Fragment (.ifE condition thenBranch elseBranch)

/-- Pointwise M2--M3 membership for a source-ordered expression list. -/
inductive M2FragmentList : List Expr → Prop where
  | nil : M2FragmentList []
  | cons {head tail} :
      M2Fragment head → M2FragmentList tail → M2FragmentList (head :: tail)

end

/-- Translate an M4 sibling-list derivation once every expression edge has a
translation.  This lemma is independent of fuel and is reused by tuples. -/
theorem itemsElaborateUsing_toM2
    {signature : FrozenSignature}
    {ExpressionElaborates : Context → Expr → Supply → Generated → Supply → Prop}
    (translate : ∀ {context expression supply generated next},
      M2Fragment expression →
        ExpressionElaborates context expression supply generated next →
          Source.Elaborates signature.base context expression supply generated next)
    {context items supply generated next}
    (fragment : M2FragmentList items)
    (derivation : ItemsElaborateUsing ExpressionElaborates context items supply
      generated next) :
    Source.ElaboratesItems signature.base context items supply generated next := by
  induction derivation with
  | nil => exact .nil
  | @cons item items supply generatedItem afterItem generatedItems next
      head tail induction =>
      cases fragment with
      | cons headFragment tailFragment =>
          exact .cons (translate headFragment head) (induction tailFragment)

/-- Translate an M4 fixed-arity call fold once every argument expression has
a translation.  A call fold is repeated ordinary function application. -/
theorem callElaboratesUsing_toM2
    {signature : FrozenSignature}
    {ExpressionElaborates : Context → Expr → Supply → Generated → Supply → Prop}
    (translate : ∀ {context expression supply generated next},
      M2Fragment expression →
        ExpressionElaborates context expression supply generated next →
          Source.Elaborates signature.base context expression supply generated next)
    {context accumulated arguments supply generated next}
    (fragment : M2FragmentList arguments)
    (derivation : CallElaboratesUsing ExpressionElaborates context accumulated
      arguments supply generated next) :
    Source.ElaboratesCall signature.base context accumulated arguments supply
      generated next := by
  induction derivation with
  | nil => exact .nil
  | @cons accumulated argument arguments supply generatedArgument afterArgument
      generated next head tail induction =>
      cases fragment with
      | cons headFragment tailFragment =>
          exact .cons (translate headFragment head) (induction tailFragment)

/-- Every fuel-indexed M4 derivation in the M2--M3 fragment is literally an
old relational elaboration after forgetting the frozen-signature wrapper. -/
theorem elaboratesFuel_toM2_of_m2Fragment
    {signature : FrozenSignature} {fuel : Nat}
    {context : Context} {expression : Expr} {supply : Supply}
    {generated : Generated} {next : Supply}
    (fragment : M2Fragment expression)
    (derivation : ElaboratesFuel signature fuel context expression supply
      generated next) :
    Source.Elaborates signature.base context expression supply generated next := by
  induction fuel generalizing context expression supply generated next with
  | zero => simp [ElaboratesFuel] at derivation
  | succ fuel induction =>
      cases fragment with
      | var index =>
          simp only [ElaboratesFuel] at derivation
          obtain ⟨scheme, lookup, rfl, rfl⟩ := derivation
          exact .var lookup
      | lit value =>
          simp only [ElaboratesFuel] at derivation
          obtain ⟨rfl, rfl⟩ := derivation
          exact .lit
      | something =>
          simp only [ElaboratesFuel] at derivation
          obtain ⟨rfl, rfl⟩ := derivation
          exact .something
      | lam bodyFragment =>
          simp only [ElaboratesFuel] at derivation
          obtain ⟨generatedBody, bodyDerivation, rfl⟩ := derivation
          exact .lam (induction bodyFragment bodyDerivation)
      | app functionFragment argumentFragment =>
          simp only [ElaboratesFuel] at derivation
          obtain ⟨generatedFunction, afterFunction, generatedArgument,
            afterArgument, functionDerivation, argumentDerivation, rfl, rfl⟩ :=
            derivation
          exact .app (induction functionFragment functionDerivation)
            (induction argumentFragment argumentDerivation)
      | tuple itemsFragment =>
          simp only [ElaboratesFuel] at derivation
          obtain ⟨generatedItems, itemsDerivation, rfl⟩ := derivation
          exact .tuple (itemsElaborateUsing_toM2
            (fun childFragment childDerivation =>
              induction childFragment childDerivation)
            itemsFragment itemsDerivation)
      | letE valueFragment bodyFragment =>
          simp only [ElaboratesFuel] at derivation
          obtain ⟨generatedValue, afterValue, valueDerivation, closure,
            generatedBody, absorbing, bodyDerivation, rfl⟩ := derivation
          exact .letE (induction valueFragment valueDerivation) closure absorbing
            (induction bodyFragment bodyDerivation)
      | @ctor constructor arguments argumentsFragment =>
          simp only [ElaboratesFuel] at derivation
          obtain ⟨scheme, lookup, arity, closed, callDerivation⟩ := derivation
          exact .ctor lookup arity closed (callElaboratesUsing_toM2
            (fun childFragment childDerivation =>
              induction childFragment childDerivation)
            argumentsFragment callDerivation)
      | @prim operation arguments argumentsFragment =>
          simp only [ElaboratesFuel] at derivation
          obtain ⟨scheme, lookup, arity, closed, callDerivation⟩ := derivation
          exact .prim lookup arity closed (callElaboratesUsing_toM2
            (fun childFragment childDerivation =>
              induction childFragment childDerivation)
            argumentsFragment callDerivation)
      | ifE conditionFragment thenFragment elseFragment =>
          simp only [ElaboratesFuel] at derivation
          exact .ifE (callElaboratesUsing_toM2
            (fun childFragment childDerivation =>
              induction childFragment childDerivation)
            (.cons conditionFragment
              (.cons thenFragment (.cons elseFragment .nil))) derivation)

/-- Public M4 elaboration in the M2--M3 fragment can be viewed through the
completed old relation. -/
theorem Elaborates.toM2_of_m2Fragment
    {signature : FrozenSignature} {context : Context} {expression : Expr}
    {supply : Supply} {generated : Generated} {next : Supply}
    (fragment : M2Fragment expression)
    (derivation : M4.Elaborates signature context expression supply generated next) :
    Source.Elaborates signature.base context expression supply generated next := by
  obtain ⟨fuel, fuelDerivation⟩ := derivation
  exact elaboratesFuel_toM2_of_m2Fragment fragment fuelDerivation

/-- The old supply-monotonicity and generated-variable provenance theorems
also transfer unchanged on the embedded M2--M3 fragment. -/
theorem elaboratesFuel_supplyAndSupport_of_m2Fragment
    {signature : FrozenSignature} {fuel : Nat} {context : Context}
    {expression : Expr} {start finish : Supply} {generated : Generated}
    (fragment : M2Fragment expression)
    (derivation : ElaboratesFuel signature fuel context expression start
      generated finish) :
    start.Le finish ∧
      GeneratedSupportProvenance context start finish generated := by
  let oldDerivation :=
    elaboratesFuel_toM2_of_m2Fragment fragment derivation
  exact ⟨oldDerivation.supply_le_next, oldDerivation.supportProvenance⟩

/-- Coherence of two arbitrary-fuel M4 derivations.  Quantifying over both
fuel values is necessary because public `M4.Elaborates` hides its fuel
witness, and the two witnesses need not be numerically equal. -/
def FullM4FuelPairProperty (expression : Expr) : Prop :=
  ∀ {signature : FrozenSignature} {context : Context} {start : Supply}
      {leftGenerated rightGenerated : Generated}
      {leftNext rightNext : Supply} {leftFuel rightFuel : Nat},
    signature.WellFormed → start.WellFormedFor context →
      ElaboratesFuel signature leftFuel context expression start
          leftGenerated leftNext →
        ElaboratesFuel signature rightFuel context expression start
            rightGenerated rightNext →
          Nonempty (FullM2PairCoherence start leftNext rightNext
            leftGenerated rightGenerated context)

/-- The completed M2 graph proof applies unchanged to the full recursive
M2--M3 fragment of M4, including nested `let`. -/
theorem fullM4FuelPairProperty_of_m2Fragment
    {expression : Expr} (fragment : M2Fragment expression) :
    FullM4FuelPairProperty expression := by
  intro signature context start leftGenerated rightGenerated leftNext rightNext
    leftFuel rightFuel _signatureWellFormed wellFormed leftDerivation
    rightDerivation
  exact fullM2CoherenceComplete expression wellFormed
    (elaboratesFuel_toM2_of_m2Fragment fragment leftDerivation)
    (elaboratesFuel_toM2_of_m2Fragment fragment rightDerivation)

/-- Public pair coherence after hiding both fuel witnesses. -/
def FullM4PairProperty (expression : Expr) : Prop :=
  ∀ {signature : FrozenSignature} {context : Context} {start : Supply}
      {leftGenerated rightGenerated : Generated}
      {leftNext rightNext : Supply},
    signature.WellFormed → start.WellFormedFor context →
      M4.Elaborates signature context expression start leftGenerated leftNext →
        M4.Elaborates signature context expression start rightGenerated rightNext →
          Nonempty (FullM2PairCoherence start leftNext rightNext
            leftGenerated rightGenerated context)

/-- Fuel-level coherence immediately implies public coherence. -/
theorem FullM4FuelPairProperty.toPublic
    {expression : Expr} (coherent : FullM4FuelPairProperty expression) :
    FullM4PairProperty expression := by
  intro signature context start leftGenerated rightGenerated leftNext rightNext
    signatureWellFormed wellFormed leftDerivation rightDerivation
  obtain ⟨leftFuel, leftFuelDerivation⟩ := leftDerivation
  obtain ⟨rightFuel, rightFuelDerivation⟩ := rightDerivation
  exact coherent signatureWellFormed wellFormed leftFuelDerivation
    rightFuelDerivation

/-- Public coherence for the embedded M2--M3 fragment. -/
theorem fullM4PairProperty_of_m2Fragment
    {expression : Expr} (fragment : M2Fragment expression) :
    FullM4PairProperty expression :=
  FullM4FuelPairProperty.toPublic
    (fullM4FuelPairProperty_of_m2Fragment fragment)

/-- Coherence for every M4 source expression. -/
def FullM4Coherence : Prop :=
  ∀ expression, FullM4PairProperty expression

/-- A public executable run paired with a relational derivation of exactly
the generated block and supply returned by that run.  **Replay** means
reconstructing this exact executable run from an independently chosen
relational derivation. -/
def ExecutableElaborationReplay
    (signature : FrozenSignature) (context : Context) (expression : Expr)
    (supply : Supply) : Prop :=
  ∃ generated next,
    M4.elaborate signature context expression supply = some (generated, next) ∧
      M4.Elaborates signature context expression supply generated next

/-- The final replay consequence consumed by the principality proof.  The
component boundary below exposes fuel normalization, ordinary structural
replay, and the representative-changing `let` case separately. -/
def FullM4ExecutableReplay : Prop :=
  ∀ {signature : FrozenSignature} {context : Context} {expression : Expr}
      {supply : Supply} {generated : Generated} {next : Supply},
    M4.Elaborates signature context expression supply generated next →
      signature.WellFormed → supply.WellFormedFor context →
        ExecutableElaborationReplay signature context expression supply

/-- Normalize an arbitrary relational fuel witness to the fuel chosen by the
public elaborator.  Fuel is only a recursion counter; it must not change which
derivations are expressible once it is large enough. -/
def M4FuelNormalization : Prop :=
  ∀ {signature : FrozenSignature} {context : Context} {expression : Expr}
      {supply : Supply} {generated : Generated} {next : Supply} {fuel : Nat},
    ElaboratesFuel signature fuel context expression supply generated next →
      ElaboratesFuel signature (expression.complexity + 1) context expression
        supply generated next

/-- The structural fuel theorem discharges the architecture's normalization
interface without any well-formedness or acceptance hypothesis. -/
theorem m4FuelNormalization : M4FuelNormalization := by
  intro signature context expression supply generated next fuel derivation
  exact derivation.normalize

/-- Replay at a `let` root after changing from the independently selected
principal closure of the value derivation to the representative returned by
the public solver.  This is where the two generalized body contexts must be
aligned; it is deliberately separate from fuel normalization. -/
def M4LetClosureRepresentativeAgreement : Prop :=
  ∀ {signature : FrozenSignature} {context : Context} {value body : Expr}
      {supply : Supply} {generated : Generated} {next : Supply},
    ElaboratesFuel signature ((Expr.letE value body).complexity + 1) context
        (Expr.letE value body) supply generated next →
      signature.WellFormed → supply.WellFormedFor context →
        ExecutableElaborationReplay signature context (Expr.letE value body) supply

/-- Replay for every non-`let` root once recursive derivations use the public
complexity fuel.  The premise excludes `let` so that closure representative
alignment cannot disappear into this structural obligation. -/
def M4StructuralReplay : Prop :=
  ∀ {signature : FrozenSignature} {context : Context} {expression : Expr}
      {supply : Supply} {generated : Generated} {next : Supply},
    (∀ value body, expression ≠ .letE value body) →
      ElaboratesFuel signature (expression.complexity + 1) context expression
          supply generated next →
        signature.WellFormed → supply.WellFormedFor context →
          ExecutableElaborationReplay signature context expression supply

/-- Fuel normalization, `let` representative agreement, and non-`let`
structural replay imply the final public replay interface. -/
theorem fullM4ExecutableReplay_of_components
    (normalization : M4FuelNormalization)
    (letAgreement : M4LetClosureRepresentativeAgreement)
    (structural : M4StructuralReplay) :
    FullM4ExecutableReplay := by
  intro signature context expression supply generated next derivation
    signatureWellFormed wellFormed
  obtain ⟨fuel, fuelDerivation⟩ := derivation
  have normalized := normalization fuelDerivation
  cases expression with
  | letE value body =>
      exact letAgreement normalized signatureWellFormed wellFormed
  | var index =>
      exact structural (by simp) normalized signatureWellFormed wellFormed
  | lit value =>
      exact structural (by simp) normalized signatureWellFormed wellFormed
  | something =>
      exact structural (by simp) normalized signatureWellFormed wellFormed
  | lam body =>
      exact structural (by simp) normalized signatureWellFormed wellFormed
  | app function argument =>
      exact structural (by simp) normalized signatureWellFormed wellFormed
  | tuple items =>
      exact structural (by simp) normalized signatureWellFormed wellFormed
  | ctor constructor arguments =>
      exact structural (by simp) normalized signatureWellFormed wellFormed
  | prim operation arguments =>
      exact structural (by simp) normalized signatureWellFormed wellFormed
  | ifE condition thenBranch elseBranch =>
      exact structural (by simp) normalized signatureWellFormed wellFormed
  | fixE body =>
      exact structural (by simp) normalized signatureWellFormed wellFormed
  | matcher clauses =>
      exact structural (by simp) normalized signatureWellFormed wellFormed
  | matchAll target matcher pattern body =>
      exact structural (by simp) normalized signatureWellFormed wellFormed
  | matchFirst target matcher arms =>
      exact structural (by simp) normalized signatureWellFormed wellFormed

/-- Per-derivation target correspondence needed for M4 principality.  Two
types are mutual instances when each can be obtained from the other by a
substitution; this permits only harmless choices of fresh variable names. -/
def WellFormedM4ElaborationPrincipalityComplete : Prop :=
  ∀ {signature : FrozenSignature} {context : Context} {expression : Expr}
      {supply next : Supply} {generated : Generated},
    M4.Elaborates signature context expression supply generated next →
      ∀ (closure : PrincipalBlockClosure generated),
        signature.WellFormed → supply.WellFormedFor context → closure.Absorbing →
          ∃ computed computedNext,
            M4.elaborate signature context expression supply =
                some (computed, computedNext) ∧
              ∃ computedClosure : PrincipalBlockClosure computed,
                IsInstance computedClosure.target closure.target ∧
                  IsInstance closure.target computedClosure.target

private theorem blockAccepts_of_principal
    {generated : Generated} (closure : PrincipalBlockClosure generated) :
    BlockAccepts generated :=
  ⟨closure.finalHard, closure.finalPending, closure.hardSubstitution,
    closure.residualSubstitution, closure.saturation,
    closure.residualPrincipal.1⟩

/-- Coherence plus exact executable replay is sufficient for the final M4
principality correspondence.  No M4-specific solver theorem is left here;
all remaining work is source-derivation coherence and replay. -/
theorem wellFormedM4ElaborationPrincipalityComplete_of_coherence_and_replay
    (coherent : FullM4Coherence) (replay : FullM4ExecutableReplay) :
    WellFormedM4ElaborationPrincipalityComplete := by
  intro signature context expression supply next generated derivation closure
    signatureWellFormed wellFormed absorbing
  obtain ⟨computed, computedNext, executable, computedDerivation⟩ :=
    replay derivation signatureWellFormed wellFormed
  obtain ⟨pair⟩ := coherent expression signatureWellFormed wellFormed
    derivation computedDerivation
  have computedAccepts : BlockAccepts computed := by
    exact (pair.blockAccepts_iff .hole trivial).mp
      (blockAccepts_of_principal closure)
  have closes :=
    computedAccepts.inferGeneratedUsing_isSome unify_completeMGUSolver
  cases closureResult : inferGeneratedUsing unify computed with
  | none => exact (closes closureResult).elim
  | some result =>
      obtain ⟨computedClosure, _, _, computedAbsorbing⟩ :=
        inferGeneratedUsing_absorbingPrincipalBlockClosure
          unify_absorbingMGUSolver closureResult
      obtain ⟨computedToOriginal, originalToComputed⟩ :=
        pair.closureTargets_mutualInstances closure computedClosure absorbing
          computedAbsorbing
      exact ⟨computed, computedNext, executable, computedClosure,
        originalToComputed, computedToOriginal⟩

/-- The principality correspondence already implies acceptance of every M4
`Typing` witness by public inference. -/
theorem Typing.infer_isSome_of_principalityComplete
    (complete : WellFormedM4ElaborationPrincipalityComplete)
    {signature : FrozenSignature} {context : Context} {expression : Expr}
    {target : Ty} (wellFormed : signature.WellFormed)
    (typing : M4.Typing signature context expression target) :
    M4.infer signature context expression ≠ none := by
  obtain ⟨principal, ⟨derivation⟩, _instance⟩ := typing
  obtain ⟨computed, computedNext, executable, computedClosure, _⟩ :=
    complete derivation.elaboration derivation.closure
      wellFormed (Supply.wellFormedFor_initialSupply context)
      derivation.absorbing
  have closes :=
    computedClosure.inferGeneratedUsing_isSome unify_completeMGUSolver
  cases closureResult : inferGeneratedUsing unify computed with
  | none => exact (closes closureResult).elim
  | some result =>
      simp [M4.infer, executable, closureResult]

/-! ## Interfaces for the genuinely new M4 cases

The following propositions are deliberate proof obligations rather than
assumptions used by public code.  They state the exact constructor-local
results required by a later well-founded induction.  Keeping them here makes
the unproved boundary explicit without adding unproved assumptions or proof
placeholders.
-/

/-- Coherence step for recursive functions.  The premise covers every
strictly smaller expression because the direct-self-reference check changes
the context used for the body. -/
def FixCoherenceStep : Prop :=
  ∀ (body : Expr),
    (∀ smaller : Expr,
      smaller.complexity < (Expr.fixE body).complexity →
      FullM4FuelPairProperty smaller) →
    FullM4FuelPairProperty (.fixE body)

/-- Coherence step for matcher literals.  Its implementation must include
the expression positions inside matcher clauses as well as the executable
coverage checks on pattern-pattern and data-pattern headers. -/
def MatcherCoherenceStep : Prop :=
  ∀ (clauses : List MatcherClause),
    (∀ smaller : Expr,
      smaller.complexity < (Expr.matcher clauses).complexity →
      FullM4FuelPairProperty smaller) →
    FullM4FuelPairProperty (.matcher clauses)

/-- Coherence step for multi-result matching, including target, matcher,
value-pattern expressions, and body elaboration. -/
def MatchAllCoherenceStep : Prop :=
  ∀ (target matcher : Expr) (pattern : Pattern) (body : Expr),
    (∀ smaller : Expr,
      smaller.complexity <
        (Expr.matchAll target matcher pattern body).complexity →
        FullM4FuelPairProperty smaller) →
    FullM4FuelPairProperty (.matchAll target matcher pattern body)

/-- Coherence step for ordered single-result matching, including every arm
body and every expression stored in an arm pattern. -/
def MatchFirstCoherenceStep : Prop :=
  ∀ (target matcher : Expr) (arms : List MatchFirstArm),
    (∀ smaller : Expr,
      smaller.complexity < (Expr.matchFirst target matcher arms).complexity →
        FullM4FuelPairProperty smaller) →
    FullM4FuelPairProperty (.matchFirst target matcher arms)

/-- Every M4 derivation must retain the two structural facts used throughout
the M2 `let` proof: supplies only increase, and every generated variable comes
from the input context or from the fresh interval allocated by this
derivation.  Support requires a well-formed frozen signature because pattern
constructor and pattern-function schemes are closed at that boundary rather
than carrying closedness evidence in each relational rule. -/
def M4SupplyAndSupport : Prop :=
  ∀ {signature : FrozenSignature} {fuel : Nat} {context : Context}
      {expression : Expr} {start finish : Supply} {generated : Generated},
    signature.WellFormed →
      ElaboratesFuel signature fuel context expression start generated finish →
        start.Le finish ∧
          GeneratedSupportProvenance context start finish generated

/-- Renaming transport required for the body of a representative-changing
`let`.  `FixesAtOrAbove start` means that the renaming leaves every variable
that can be freshly allocated from `start` onward unchanged. -/
def M4FreshRenamingTransport : Prop :=
  ∀ {rho : VariableRenaming} {signature : FrozenSignature} {fuel : Nat}
      {context : Context} {expression : Expr} {start finish : Supply}
      {generated : Generated},
    signature.WellFormed →
      ElaboratesFuel signature fuel context expression start generated finish →
      start.WellFormedFor context → rho.FixesAtOrAbove start →
        ElaboratesFuel signature fuel
          (ElaborationRenaming.renameContext rho context) expression start
          (ElaborationRenaming.renameGenerated rho generated) finish

/-- Support and renaming transport needed when an M4 constructor occurs
inside either child of `let`.  "Support" is the finite set of type and
capability variables occurring in a generated block.  The completed M2
assembly theorem can be reused after this bridge produces the same
`FullM2PairCoherence` input expected by its generated-block part. -/
def M4LetTransportAndAssembly : Prop :=
  ∀ (value body : Expr),
    FullM4FuelPairProperty value →
    FullM4FuelPairProperty body →
    FullM4FuelPairProperty (.letE value body)

/-- A constructor is old at its root and is not `let`; its children may
still contain M4 constructs.  These mixed cases require the existing M2
lambda/application/tuple/call composition lemmas to be lifted to arbitrary
M4 fuel witnesses. -/
inductive M2NonLetRoot : Expr → Prop where
  | var (index : Nat) : M2NonLetRoot (.var index)
  | lit (value : Int) : M2NonLetRoot (.lit value)
  | something : M2NonLetRoot .something
  | lam (body : Expr) : M2NonLetRoot (.lam body)
  | app (function argument : Expr) : M2NonLetRoot (.app function argument)
  | tuple (items : List Expr) : M2NonLetRoot (.tuple items)
  | ctor (constructor : DataCtor) (arguments : List Expr) :
      M2NonLetRoot (.ctor constructor arguments)
  | prim (operation : PrimOp) (arguments : List Expr) :
      M2NonLetRoot (.prim operation arguments)
  | ifE (condition thenBranch elseBranch : Expr) :
      M2NonLetRoot (.ifE condition thenBranch elseBranch)

/-- Ordinary-root coherence for mixed trees, for example a lambda whose body
is a matcher literal.  This is separate from the fragment reuse theorem,
which applies only when the whole tree is in the old fragment. -/
def OrdinaryM4CoherenceStep : Prop :=
  ∀ (expression : Expr), M2NonLetRoot expression →
    (∀ smaller : Expr, smaller.complexity < expression.complexity →
      FullM4FuelPairProperty smaller) →
    FullM4FuelPairProperty expression

/-- Exact conjunction of the constructor-local obligations left after the
checked M2--M3 reuse theorem above.  Supply and generated-support provenance
are already established by `M4.supplyAndSupport`, so they are no longer an
open item in this boundary. -/
def M4CoherenceExtensionBoundary : Prop :=
  M4FreshRenamingTransport ∧ OrdinaryM4CoherenceStep ∧ FixCoherenceStep ∧
    MatcherCoherenceStep ∧ MatchAllCoherenceStep ∧ MatchFirstCoherenceStep ∧
      M4LetTransportAndAssembly

/-- Assemble the constructor-local fuel pair theorems by structural
complexity.  Using the same `Expr.complexity` measure as public elaboration
keeps list- and pattern-contained expression bounds reusable. -/
theorem fullM4FuelCoherence_of_steps
    (ordinary : OrdinaryM4CoherenceStep)
    (fix : FixCoherenceStep)
    (matcher : MatcherCoherenceStep)
    (matchAll : MatchAllCoherenceStep)
    (matchFirst : MatchFirstCoherenceStep)
    (letE : M4LetTransportAndAssembly) :
    ∀ expression, FullM4FuelPairProperty expression := by
  intro expression
  apply (measure Expr.complexity).wf.induction expression
  intro current induction
  cases current with
  | var index => exact ordinary _ (.var index) induction
  | lit value => exact ordinary _ (.lit value) induction
  | something => exact ordinary _ .something induction
  | lam body => exact ordinary _ (.lam body) induction
  | app function argument => exact ordinary _ (.app function argument) induction
  | tuple items => exact ordinary _ (.tuple items) induction
  | letE value body =>
      exact letE value body
        (induction value (by
          show value.complexity <
            value.complexity + body.complexity + 1
          omega))
        (induction body (by
          show body.complexity <
            value.complexity + body.complexity + 1
          omega))
  | ctor constructor arguments =>
      exact ordinary _ (.ctor constructor arguments) induction
  | prim operation arguments =>
      exact ordinary _ (.prim operation arguments) induction
  | ifE condition thenBranch elseBranch =>
      exact ordinary _ (.ifE condition thenBranch elseBranch) induction
  | fixE body => exact fix body induction
  | matcher clauses => exact matcher clauses induction
  | matchAll target matcherExpression pattern body =>
      exact matchAll target matcherExpression pattern body induction
  | matchFirst target matcherExpression arms =>
      exact matchFirst target matcherExpression arms induction

/-- Fuel coherence immediately yields the public, fuel-hidden theorem. -/
theorem fullM4Coherence_of_steps
    (ordinary : OrdinaryM4CoherenceStep)
    (fix : FixCoherenceStep)
    (matcher : MatcherCoherenceStep)
    (matchAll : MatchAllCoherenceStep)
    (matchFirst : MatchFirstCoherenceStep)
    (letE : M4LetTransportAndAssembly) : FullM4Coherence := by
  intro expression
  exact FullM4FuelPairProperty.toPublic
    (fullM4FuelCoherence_of_steps ordinary fix matcher matchAll matchFirst
      letE expression)

/-- Final proof boundary for results 5.2--5.5 at M4.  The local coherence
steps must first be assembled into `FullM4Coherence`; the parallel recursive
replay proof must establish `FullM4ExecutableReplay`.  The theorem
`wellFormedM4ElaborationPrincipalityComplete_of_coherence_and_replay` then
discharges the solver-facing remainder. -/
def M4PrincipalityCompletionBoundary : Prop :=
  M4FuelNormalization ∧ M4LetClosureRepresentativeAgreement ∧
    M4StructuralReplay ∧ FullM4Coherence

end TypePM.Source.M4.CompletenessArchitecture
