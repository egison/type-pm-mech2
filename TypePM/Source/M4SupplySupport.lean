import TypePM.Source.M4CompletenessArchitecture

/-!
# Supply monotonicity and generated support for M4

This module proves the structural facts needed by the M4 `let` coherence
argument.  A supply is the pair of counters from which fresh ordinary type
variables and fresh capability variables are allocated.  Supply monotonicity
means that neither counter decreases during elaboration.

Generated support is the stronger statement that every variable occurring in
the generated constraint block either already occurs freely in the input
context or was allocated in the half-open interval between the starting and
finishing supplies.
-/

namespace TypePM.Source

/-! ## Supply monotonicity of callback-parametric components -/

/-- `fix` preserves supply monotonicity whenever its recursive expression
callback does. -/
theorem FixElaboratesUsing.supply_le_next
    {BodyElaborates : Context → Expr → Supply → Generated → Supply → Prop}
    (bodyIncreases : ∀ {context expression start generated finish},
      BodyElaborates context expression start generated finish → start.Le finish)
    {context expression start generated finish}
    (derivation : FixElaboratesUsing BodyElaborates context expression start
      generated finish) :
    start.Le finish := by
  cases derivation with
  | @fixE body start generatedBody finish direct bodyElaboration =>
      exact Supply.le_trans (by
        cases body <;> simp [Fix.bodySupply, Supply.Le, Supply.nextTy])
        (bodyIncreases bodyElaboration)

mutual

/-- User-pattern synthesis preserves supply monotonicity whenever embedded
value expressions do. -/
theorem PatternElaboratesUsing.supply_le_next
    {ExpressionElaborates : M4ExpressionElaborationRelation}
    (expressionIncreases : ∀ {context expression start generated finish},
      ExpressionElaborates context expression start generated finish →
        start.Le finish)
    {signature context arguments pattern bindings start generated finish}
    (derivation : PatternElaboratesUsing ExpressionElaborates signature context
      arguments pattern bindings start generated finish) :
    start.Le finish := by
  cases derivation with
  | var => simp [Supply.Le]
  | wild => simp [Supply.Le]
  | value expressionDerivation =>
      exact Supply.le_trans (expressionIncreases expressionDerivation)
        (by simp [Supply.Le])
  | ctor lookup arity fieldsDerivation =>
      exact Supply.le_trans (by simp [Supply.Le, DualScheme.instantiate])
        (PatternsElaborateUsing.supply_le_next expressionIncreases
          fieldsDerivation)
  | tuple itemsDerivation =>
      exact PatternsElaborateUsing.supply_le_next expressionIncreases
        itemsDerivation
  | embed lookup => exact Supply.le_refl _
  | app lookup arity fieldsDerivation =>
      exact Supply.le_trans (by simp [Supply.Le, DualScheme.instantiate])
        (PatternsElaborateUsing.supply_le_next expressionIncreases
          fieldsDerivation)

/-- Left-to-right pattern-list synthesis preserves supply monotonicity. -/
theorem PatternsElaborateUsing.supply_le_next
    {ExpressionElaborates : M4ExpressionElaborationRelation}
    (expressionIncreases : ∀ {context expression start generated finish},
      ExpressionElaborates context expression start generated finish →
        start.Le finish)
    {signature context arguments patterns bindings start generated finish}
    (derivation : PatternsElaborateUsing ExpressionElaborates signature context
      arguments patterns bindings start generated finish) :
    start.Le finish := by
  cases derivation with
  | nil => exact Supply.le_refl _
  | cons head tail =>
      exact Supply.le_trans
        (PatternElaboratesUsing.supply_le_next expressionIncreases head)
        (PatternsElaborateUsing.supply_le_next expressionIncreases tail)

end

/-- `matchAll` preserves supply monotonicity whenever its recursive
expression callback does. -/
theorem MatchAllElaboratesUsing.supply_le_next
    {ExpressionElaborates : M4ExpressionElaborationRelation}
    (expressionIncreases : ∀ {context expression start generated finish},
      ExpressionElaborates context expression start generated finish →
        start.Le finish)
    {signature context target matcher pattern body start generated finish}
    (derivation : MatchAllElaboratesUsing ExpressionElaborates signature context
      target matcher pattern body start generated finish) :
    start.Le finish := by
  cases derivation with
  | mk targetDerivation patternDerivation matcherDerivation bodyDerivation =>
      exact Supply.le_trans (expressionIncreases targetDerivation)
        (Supply.le_trans
          (PatternElaboratesUsing.supply_le_next expressionIncreases
            patternDerivation)
          (Supply.le_trans (expressionIncreases matcherDerivation)
            (expressionIncreases bodyDerivation)))

namespace MatcherTyping

mutual

/-- Primitive pattern-pattern header elaboration preserves supply
monotonicity. -/
theorem PPatElaborates.supply_le_next
    {signature pattern expectedTarget expectedCapability start generated finish}
    (derivation : PPatElaborates signature pattern expectedTarget
      expectedCapability start generated finish) :
    start.Le finish := by
  cases derivation with
  | hole => simp [Supply.Le]
  | wild => exact Supply.le_refl _
  | capture => exact Supply.le_refl _
  | ctor lookup arity fields =>
      exact Supply.le_trans (by simp [Supply.Le, DualScheme.instantiate])
        (PPatsElaborate.supply_le_next fields)

/-- Pattern-pattern field lists preserve supply monotonicity. -/
theorem PPatsElaborate.supply_le_next
    {signature patterns expected start generated finish}
    (derivation : PPatsElaborate signature patterns expected start generated
      finish) :
    start.Le finish := by
  cases derivation with
  | nil => exact Supply.le_refl _
  | cons head tail =>
      exact Supply.le_trans head.supply_le_next tail.supply_le_next

end

mutual

/-- Data-pattern header elaboration preserves supply monotonicity. -/
theorem DPatElaborates.supply_le_next
    {signature pattern expected start generated finish}
    (derivation : DPatElaborates signature pattern expected start generated
      finish) :
    start.Le finish := by
  cases derivation with
  | var => exact Supply.le_refl _
  | wild => exact Supply.le_refl _
  | ctor lookup arity peel fields =>
      exact Supply.le_trans (by simp [Supply.Le, Scheme.instantiate])
        (DPatsElaborate.supply_le_next fields)
  | tuple fieldsEquality items =>
      exact Supply.le_trans (Supply.le_nextTy _ _) items.supply_le_next

/-- Data-pattern field lists preserve supply monotonicity. -/
theorem DPatsElaborate.supply_le_next
    {signature patterns expected start generated finish}
    (derivation : DPatsElaborate signature patterns expected start generated
      finish) :
    start.Le finish := by
  cases derivation with
  | nil => exact Supply.le_refl _
  | cons head tail =>
      exact Supply.le_trans head.supply_le_next tail.supply_le_next

end

/-- An expression checked at an expected type has the supply behavior of its
expression derivation. -/
theorem CheckedExpressionElaboratesUsing.supply_le_next
    {expressionRelation : ExpressionElaborationRelation}
    (expressionIncreases : ∀ {context expression start generated finish},
      expressionRelation context expression start generated finish →
        start.Le finish)
    {context expression expected start generated finish}
    (derivation : CheckedExpressionElaboratesUsing expressionRelation context
      expression expected start generated finish) :
    start.Le finish := by
  cases derivation with
  | mk expressionDerivation => exact expressionIncreases expressionDerivation

/-- A list of separately checked next matchers preserves supply monotonicity. -/
theorem NextMatcherItemsElaborateUsing.supply_le_next
    {expressionRelation : ExpressionElaborationRelation}
    (expressionIncreases : ∀ {context expression start generated finish},
      expressionRelation context expression start generated finish →
        start.Le finish)
    {context items holes start generated finish}
    (derivation : NextMatcherItemsElaborateUsing expressionRelation context
      items holes start generated finish) :
    start.Le finish := by
  induction derivation with
  | nil => exact Supply.le_refl _
  | cons head tail induction =>
      exact Supply.le_trans
        (head.supply_le_next expressionIncreases) induction

/-- The zero/one/many next-matcher convention preserves supply monotonicity. -/
theorem NextMatchersElaborateUsing.supply_le_next
    {expressionRelation : ExpressionElaborationRelation}
    (expressionIncreases : ∀ {context expression start generated finish},
      expressionRelation context expression start generated finish →
        start.Le finish)
    {context expression holes start generated finish}
    (derivation : NextMatchersElaborateUsing expressionRelation context
      expression holes start generated finish) :
    start.Le finish := by
  cases derivation with
  | zero checked | one checked =>
      exact checked.supply_le_next expressionIncreases
  | many components => exact components.supply_le_next expressionIncreases

/-- One matcher data arm preserves supply monotonicity. -/
theorem MatcherArmElaboratesUsing.supply_le_next
    {expressionRelation : ExpressionElaborationRelation}
    {dpatRelation : DPatElaborationRelation}
    (expressionIncreases : ∀ {context expression start generated finish},
      expressionRelation context expression start generated finish →
        start.Le finish)
    (dpatIncreases : ∀ {signature pattern expected start generated finish},
      dpatRelation signature pattern expected start generated finish →
        start.Le finish)
    {signature context captures matcherTarget holes arm start generated finish}
    (derivation : MatcherArmElaboratesUsing expressionRelation dpatRelation
      signature context captures matcherTarget holes arm start generated finish) :
    start.Le finish := by
  cases derivation with
  | mk header body =>
      exact Supply.le_trans (dpatIncreases header)
        (body.supply_le_next expressionIncreases)

/-- Matcher data-arm lists preserve supply monotonicity. -/
theorem MatcherArmsElaborateUsing.supply_le_next
    {expressionRelation : ExpressionElaborationRelation}
    {dpatRelation : DPatElaborationRelation}
    (expressionIncreases : ∀ {context expression start generated finish},
      expressionRelation context expression start generated finish →
        start.Le finish)
    (dpatIncreases : ∀ {signature pattern expected start generated finish},
      dpatRelation signature pattern expected start generated finish →
        start.Le finish)
    {signature context captures matcherTarget holes arms start generated finish}
    (derivation : MatcherArmsElaborateUsing expressionRelation dpatRelation
      signature context captures matcherTarget holes arms start generated finish) :
    start.Le finish := by
  induction derivation with
  | nil => exact Supply.le_refl _
  | cons head tail induction =>
      exact Supply.le_trans
        (head.supply_le_next expressionIncreases dpatIncreases) induction

/-- One matcher clause preserves supply monotonicity. -/
theorem MatcherClauseElaboratesUsing.supply_le_next
    {expressionRelation : ExpressionElaborationRelation}
    {ppatRelation : PPatElaborationRelation}
    {dpatRelation : DPatElaborationRelation}
    (expressionIncreases : ∀ {context expression start generated finish},
      expressionRelation context expression start generated finish →
        start.Le finish)
    (ppatIncreases : ∀ {signature pattern target capability start generated finish},
      ppatRelation signature pattern target capability start generated finish →
        start.Le finish)
    (dpatIncreases : ∀ {signature pattern expected start generated finish},
      dpatRelation signature pattern expected start generated finish →
        start.Le finish)
    {signature context matcherTarget clause start generated finish}
    (derivation : MatcherClauseElaboratesUsing expressionRelation ppatRelation
      dpatRelation signature context matcherTarget clause start generated finish) :
    start.Le finish := by
  cases derivation with
  | mk shape header next arms =>
      exact Supply.le_trans (ppatIncreases header)
        (Supply.le_trans (next.supply_le_next expressionIncreases)
          (arms.supply_le_next expressionIncreases dpatIncreases))

/-- Matcher clause lists preserve supply monotonicity. -/
theorem MatcherClausesElaborateUsing.supply_le_next
    {expressionRelation : ExpressionElaborationRelation}
    {ppatRelation : PPatElaborationRelation}
    {dpatRelation : DPatElaborationRelation}
    (expressionIncreases : ∀ {context expression start generated finish},
      expressionRelation context expression start generated finish →
        start.Le finish)
    (ppatIncreases : ∀ {signature pattern target capability start generated finish},
      ppatRelation signature pattern target capability start generated finish →
        start.Le finish)
    (dpatIncreases : ∀ {signature pattern expected start generated finish},
      dpatRelation signature pattern expected start generated finish →
        start.Le finish)
    {signature context matcherTarget clauses start generated finish}
    (derivation : MatcherClausesElaborateUsing expressionRelation ppatRelation
      dpatRelation signature context matcherTarget clauses start generated finish) :
    start.Le finish := by
  induction derivation with
  | nil => exact Supply.le_refl _
  | cons head tail induction =>
      exact Supply.le_trans
        (head.supply_le_next expressionIncreases ppatIncreases dpatIncreases)
        induction

/-- Matcher literals preserve supply monotonicity. -/
theorem MatcherLiteralElaboratesUsing.supply_le_next
    {expressionRelation : ExpressionElaborationRelation}
    {ppatRelation : PPatElaborationRelation}
    {dpatRelation : DPatElaborationRelation}
    (expressionIncreases : ∀ {context expression start generated finish},
      expressionRelation context expression start generated finish →
        start.Le finish)
    (ppatIncreases : ∀ {signature pattern target capability start generated finish},
      ppatRelation signature pattern target capability start generated finish →
        start.Le finish)
    (dpatIncreases : ∀ {signature pattern expected start generated finish},
      dpatRelation signature pattern expected start generated finish →
        start.Le finish)
    {signature context clauses start generated finish}
    (derivation : MatcherLiteralElaboratesUsing expressionRelation ppatRelation
      dpatRelation signature context clauses start generated finish) :
    start.Le finish := by
  cases derivation with
  | mk checked clauses =>
      exact Supply.le_trans (by simp [Supply.Le])
        (clauses.supply_le_next expressionIncreases ppatIncreases dpatIncreases)

end MatcherTyping

namespace MatchFirstTyping

/-- Later `matchFirst` arms preserve supply monotonicity. -/
theorem TailElaboratesUsing.supply_le_next
    {ExpressionElaborates :
      Context → Expr → Supply → Generated → Supply → Prop}
    (expressionIncreases : ∀ {context expression start generated finish},
      ExpressionElaborates context expression start generated finish →
        start.Le finish)
    {signature context targetType matcherType expectedResult arms start generated
      finish}
    (derivation : TailElaboratesUsing ExpressionElaborates signature context
      targetType matcherType expectedResult arms start generated finish) :
    start.Le finish := by
  induction derivation with
  | nil => exact Supply.le_refl _
  | cons pattern body tail induction =>
      exact Supply.le_trans
        (pattern.supply_le_next expressionIncreases)
        (Supply.le_trans (expressionIncreases body) induction)

/-- A nonempty `matchFirst` arm list preserves supply monotonicity. -/
theorem ArmsElaborateUsing.supply_le_next
    {ExpressionElaborates :
      Context → Expr → Supply → Generated → Supply → Prop}
    (expressionIncreases : ∀ {context expression start generated finish},
      ExpressionElaborates context expression start generated finish →
        start.Le finish)
    {signature context targetType matcherType arms start generated finish}
    (derivation : ArmsElaborateUsing ExpressionElaborates signature context
      targetType matcherType arms start generated finish) :
    start.Le finish := by
  cases derivation with
  | cons pattern body tail =>
      exact Supply.le_trans
        (pattern.supply_le_next expressionIncreases)
        (Supply.le_trans (expressionIncreases body)
          (tail.supply_le_next expressionIncreases))

/-- `matchFirst` preserves supply monotonicity. -/
theorem ElaboratesUsing.supply_le_next
    {ExpressionElaborates :
      Context → Expr → Supply → Generated → Supply → Prop}
    (expressionIncreases : ∀ {context expression start generated finish},
      ExpressionElaborates context expression start generated finish →
        start.Le finish)
    {signature context expression start generated finish}
    (derivation : ElaboratesUsing ExpressionElaborates signature context
      expression start generated finish) :
    start.Le finish := by
  cases derivation with
  | matchFirst exhaustive target matcher arms =>
      exact Supply.le_trans (expressionIncreases target)
        (Supply.le_trans (expressionIncreases matcher)
          (arms.supply_le_next expressionIncreases))

end MatchFirstTyping

namespace M4

/-- Sibling-expression elaboration preserves supply monotonicity. -/
theorem ItemsElaborateUsing.supply_le_next
    {ExpressionElaborates : Context → Expr → Supply → Generated → Supply → Prop}
    (expressionIncreases : ∀ {context expression start generated finish},
      ExpressionElaborates context expression start generated finish →
        start.Le finish)
    {context items start generated finish}
    (derivation : ItemsElaborateUsing ExpressionElaborates context items start
      generated finish) :
    start.Le finish := by
  induction derivation with
  | nil => exact Supply.le_refl _
  | cons head tail induction =>
      exact Supply.le_trans (expressionIncreases head) induction

/-- Fixed-arity call elaboration preserves supply monotonicity. -/
theorem CallElaboratesUsing.supply_le_next
    {ExpressionElaborates : Context → Expr → Supply → Generated → Supply → Prop}
    (expressionIncreases : ∀ {context expression start generated finish},
      ExpressionElaborates context expression start generated finish →
        start.Le finish)
    {context accumulated arguments start generated finish}
    (derivation : CallElaboratesUsing ExpressionElaborates context accumulated
      arguments start generated finish) :
    start.Le finish := by
  induction derivation with
  | nil => exact Supply.le_refl _
  | cons head tail induction =>
      exact Supply.le_trans (expressionIncreases head)
        (Supply.le_trans (Supply.le_nextTy _ _) induction)

/-- Every fuel-indexed M4 derivation moves both fresh-name counters only
forward. -/
theorem ElaboratesFuel.supply_le_next
    {signature : FrozenSignature} {fuel : Nat} {context : Context}
    {expression : Expr} {start finish : Supply} {generated : Generated}
    (derivation : ElaboratesFuel signature fuel context expression start
      generated finish) :
    start.Le finish := by
  induction fuel generalizing context expression start generated finish with
  | zero => simp [ElaboratesFuel] at derivation
  | succ fuel induction =>
      cases expression <;> simp only [ElaboratesFuel] at derivation
      · obtain ⟨scheme, lookup, rfl, rfl⟩ := derivation
        simp [Supply.Le, Scheme.instantiate]
      · exact derivation.2 ▸ Supply.le_refl _
      · exact derivation.2 ▸ Supply.le_nextTy _ _
      · obtain ⟨body, bodyDerivation, rfl⟩ := derivation
        exact Supply.le_trans (Supply.le_nextTy _ _)
          (induction bodyDerivation)
      · obtain ⟨function, afterFunction, argument, afterArgument,
          functionDerivation, argumentDerivation, rfl, rfl⟩ := derivation
        exact Supply.le_trans (induction functionDerivation)
          (Supply.le_trans (induction argumentDerivation)
            (Supply.le_nextTy _ _))
      · obtain ⟨items, itemsDerivation, rfl⟩ := derivation
        exact itemsDerivation.supply_le_next
          (fun child => induction child)
      · obtain ⟨value, afterValue, valueDerivation, closure, body, absorbing,
          bodyDerivation, rfl⟩ := derivation
        exact Supply.le_trans (induction valueDerivation)
          (Supply.le_trans (Supply.le_join_left _ _)
            (induction bodyDerivation))
      · obtain ⟨scheme, lookup, arity, closed, call⟩ := derivation
        exact Supply.le_trans (by simp [Supply.Le, Scheme.instantiate])
          (call.supply_le_next (fun child => induction child))
      · obtain ⟨scheme, lookup, arity, closed, call⟩ := derivation
        exact Supply.le_trans (by simp [Supply.Le, Scheme.instantiate])
          (call.supply_le_next (fun child => induction child))
      · exact Supply.le_trans (by simp [Supply.Le, Scheme.instantiate])
          (derivation.supply_le_next (fun child => induction child))
      · exact derivation.supply_le_next (fun child => induction child)
      · exact derivation.supply_le_next (fun child => induction child)
          MatcherTyping.PPatElaborates.supply_le_next
          MatcherTyping.DPatElaborates.supply_le_next
      · exact derivation.supply_le_next (fun child => induction child)
      · exact derivation.supply_le_next (fun child => induction child)

end M4

/-! ## Common support vocabulary -/

/-- Every variable in `variables` either belongs to the original context or
was freshly allocated between `start` and `finish`. -/
def VariablesSupportProvenance
    (context : Context) (start finish : Supply)
    (variables : List UnificationVar) : Prop :=
  ∀ candidate, candidate ∈ variables →
    candidate ∈ context.unificationVars ∨ candidate.FreshIn start finish

namespace VariablesSupportProvenance

theorem nil (context : Context) (start finish : Supply) :
    VariablesSupportProvenance context start finish [] := by
  intro candidate member
  simp at member

theorem append {context : Context} {start finish : Supply} {left right}
    (leftSupport : VariablesSupportProvenance context start finish left)
    (rightSupport : VariablesSupportProvenance context start finish right) :
    VariablesSupportProvenance context start finish (left ++ right) := by
  intro candidate member
  rcases List.mem_append.mp member with member | member
  · exact leftSupport candidate member
  · exact rightSupport candidate member

theorem mono_finish {context : Context} {start middle finish : Supply} {variables}
    (support : VariablesSupportProvenance context start middle variables)
    (increases : middle.Le finish) :
    VariablesSupportProvenance context start finish variables := by
  intro candidate member
  rcases support candidate member with outer | fresh
  · exact Or.inl outer
  · exact Or.inr (fresh.extend_finish increases)

theorem lower_start {context : Context} {start middle finish : Supply} {variables}
    (increases : start.Le middle)
    (support : VariablesSupportProvenance context middle finish variables) :
    VariablesSupportProvenance context start finish variables := by
  intro candidate member
  rcases support candidate member with outer | fresh
  · exact Or.inl outer
  · exact Or.inr (fresh.lower_start increases)

theorem trans_interval {context : Context} {start middle finish : Supply}
    {variables}
    (support : VariablesSupportProvenance context start middle variables)
    (increases : middle.Le finish) :
    VariablesSupportProvenance context start finish variables :=
  support.mono_finish increases

end VariablesSupportProvenance

/-- Variables occurring in both halves of a target/capability pair. -/
def dualVariables (dual : Dual) : List UnificationVar :=
  dual.capability.unificationVars ++ dual.target.unificationVars

/-- Variables occurring in a list of target/capability pairs. -/
def dualUnificationVars (duals : List Dual) : List UnificationVar :=
  duals.flatMap dualVariables

namespace MatcherTyping.GeneratedChecks

def unificationVars (checks : GeneratedChecks) : List UnificationVar :=
  TypePM.unificationVars checks.hard ++
    pendingUnificationVars checks.pending

end MatcherTyping.GeneratedChecks

namespace GeneratedPattern

def unificationVars (generated : GeneratedPattern) : List UnificationVar :=
  dualVariables generated.dual ++
    Ty.unificationVarsList generated.bindings ++
      TypePM.unificationVars generated.hard ++
        pendingUnificationVars generated.pending

end GeneratedPattern

namespace GeneratedPatterns

def unificationVars (generated : GeneratedPatterns) : List UnificationVar :=
  dualUnificationVars generated.duals ++
    Ty.unificationVarsList generated.bindings ++
      TypePM.unificationVars generated.hard ++
        pendingUnificationVars generated.pending

end GeneratedPatterns

namespace MatcherTyping.GeneratedPPat

def unificationVars (generated : GeneratedPPat) : List UnificationVar :=
  dualUnificationVars generated.holes ++
    Ty.unificationVarsList generated.captures ++
      (match generated.evidence with
        | none => []
        | some evidence => evidence.unificationVars) ++
        TypePM.unificationVars generated.hard

end MatcherTyping.GeneratedPPat

namespace MatcherTyping.GeneratedPPats

def unificationVars (generated : GeneratedPPats) : List UnificationVar :=
  dualUnificationVars generated.holes ++
    Ty.unificationVarsList generated.captures ++
      TypePM.unificationVars generated.hard

end MatcherTyping.GeneratedPPats

namespace MatcherTyping.GeneratedDPat

def unificationVars (generated : GeneratedDPat) : List UnificationVar :=
  Ty.unificationVarsList generated.bindings ++
    TypePM.unificationVars generated.hard

end MatcherTyping.GeneratedDPat

namespace MatcherTyping.GeneratedDPats

def unificationVars (generated : GeneratedDPats) : List UnificationVar :=
  Ty.unificationVarsList generated.bindings ++
    TypePM.unificationVars generated.hard

end MatcherTyping.GeneratedDPats

/-- A closed instantiated dual scheme mentions only variables allocated by
that instantiation. -/
theorem DualScheme.instantiate_support
    {scheme : DualScheme} (closed : scheme.Closed) (supply : Supply) :
    VariablesSupportProvenance [] supply (scheme.instantiate supply).2
      (dualUnificationVars (scheme.instantiate supply).1.fields ++
        dualVariables (scheme.instantiate supply).1.result) := by
  intro candidate member
  right
  simp only [List.mem_append] at member
  have freshTy {target : PolyTy}
      (wellScoped : target.WellScoped scheme.tyArity scheme.capArity)
      (freeAbsent : target.freeTyVars = []) {index : TyVar}
      (membership : .ty index ∈
        (target.openBound
          (fun position => .var (Scheme.boundTyInstance supply position))
          (fun position => .var
            (Scheme.boundCapInstance supply position))).unificationVars) :
      UnificationVar.FreshIn supply (scheme.instantiate supply).2 (.ty index) := by
    have inTy := (Ty.mem_tyVars_iff_unificationVars index _).mpr membership
    rcases PolyTy.openBound_supply_ty_origin target scheme.tyArity
        scheme.capArity supply wellScoped inTy with free | bound
    · rw [freeAbsent] at free
      simp at free
    · obtain ⟨position, valid, rfl⟩ := bound
      simp only [UnificationVar.FreshIn]
      constructor
      · exact Scheme.boundTyInstance_ge_start supply position
      · simp [DualScheme.instantiate]
        omega
  have freshCapFromTy {target : PolyTy}
      (wellScoped : target.WellScoped scheme.tyArity scheme.capArity)
      (freeAbsent : target.freeCapVars = []) {index : CapVar}
      (membership : .cap index ∈
        (target.openBound
          (fun position => .var (Scheme.boundTyInstance supply position))
          (fun position => .var
            (Scheme.boundCapInstance supply position))).unificationVars) :
      UnificationVar.FreshIn supply (scheme.instantiate supply).2 (.cap index) := by
    have inCap := (Ty.mem_capVars_iff_unificationVars index _).mpr membership
    rcases PolyTy.openBound_supply_cap_origin target scheme.tyArity
        scheme.capArity supply wellScoped inCap with free | bound
    · rw [freeAbsent] at free
      simp at free
    · obtain ⟨position, valid, rfl⟩ := bound
      simp only [UnificationVar.FreshIn]
      constructor
      · exact Scheme.boundCapInstance_ge_start supply position
      · simp [DualScheme.instantiate]
        omega
  have freshCap {capability : PolyCap}
      (wellScoped : capability.WellScoped scheme.capArity)
      (freeAbsent : capability.freeCapVars = []) {index : CapVar}
      (membership : .cap index ∈
        (capability.openBound
          (fun position => .var
            (Scheme.boundCapInstance supply position))).unificationVars) :
      UnificationVar.FreshIn supply (scheme.instantiate supply).2 (.cap index) := by
    have inCap := (Cap.mem_capVars_iff_unificationVars index _).mpr membership
    rcases PolyCap.openBound_supply_cap_origin capability scheme.capArity supply
        wellScoped inCap with free | bound
    · rw [freeAbsent] at free
      simp at free
    · obtain ⟨position, valid, rfl⟩ := bound
      simp only [UnificationVar.FreshIn]
      constructor
      · exact Scheme.boundCapInstance_ge_start supply position
      · simp [DualScheme.instantiate]
        omega
  have fieldTargetFreeTy (field : PolyDual) (fieldMember : field ∈ scheme.fields) :
      field.target.freeTyVars = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro index indexMember
    have : index ∈ scheme.freeTyVars := by
      simp only [DualScheme.freeTyVars, mem_dedupFirst, List.mem_append,
        List.mem_flatMap]
      exact Or.inl ⟨field, fieldMember, indexMember⟩
    rw [closed.1] at this
    simp at this
  have resultTargetFreeTy : scheme.result.target.freeTyVars = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro index indexMember
    have : index ∈ scheme.freeTyVars := by
      simp only [DualScheme.freeTyVars, mem_dedupFirst, List.mem_append,
        List.mem_flatMap]
      exact Or.inr indexMember
    rw [closed.1] at this
    simp at this
  have fieldCapabilityFreeCap (field : PolyDual)
      (fieldMember : field ∈ scheme.fields) :
      field.capability.freeCapVars = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro index indexMember
    have : index ∈ scheme.freeCapVars := by
      simp only [DualScheme.freeCapVars, mem_dedupFirst, List.mem_append,
        List.mem_flatMap]
      exact Or.inl (Or.inl ⟨field, fieldMember, Or.inl indexMember⟩)
    rw [closed.2] at this
    simp at this
  have fieldTargetFreeCap (field : PolyDual) (fieldMember : field ∈ scheme.fields) :
      field.target.freeCapVars = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro index indexMember
    have : index ∈ scheme.freeCapVars := by
      simp only [DualScheme.freeCapVars, mem_dedupFirst, List.mem_append,
        List.mem_flatMap]
      exact Or.inl (Or.inl ⟨field, fieldMember, Or.inr indexMember⟩)
    rw [closed.2] at this
    simp at this
  have resultCapabilityFreeCap : scheme.result.capability.freeCapVars = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro index indexMember
    have : index ∈ scheme.freeCapVars := by
      simp only [DualScheme.freeCapVars, mem_dedupFirst, List.mem_append,
        List.mem_flatMap]
      exact Or.inl (Or.inr indexMember)
    rw [closed.2] at this
    simp at this
  have resultTargetFreeCap : scheme.result.target.freeCapVars = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro index indexMember
    have : index ∈ scheme.freeCapVars := by
      simp only [DualScheme.freeCapVars, mem_dedupFirst, List.mem_append,
        List.mem_flatMap]
      exact Or.inr indexMember
    rw [closed.2] at this
    simp at this
  -- Field and result membership is reduced to the origin lemmas above.
  rcases member with fieldsMember | resultMember
  · rw [dualUnificationVars, List.mem_flatMap] at fieldsMember
    obtain ⟨dual, dualMember, dualVariable⟩ := fieldsMember
    rw [DualScheme.instantiate] at dualMember
    simp only at dualMember
    obtain ⟨field, fieldMember, rfl⟩ := List.mem_map.mp dualMember
    simp only [dualVariables, List.mem_append] at dualVariable
    rcases candidate with index | index
    · rcases dualVariable with capabilityMember | targetMember
      · exact freshCap (scheme.fieldsWellScoped field fieldMember).1
          (fieldCapabilityFreeCap field fieldMember) capabilityMember
      · exact freshCapFromTy (scheme.fieldsWellScoped field fieldMember).2
          (fieldTargetFreeCap field fieldMember) targetMember
    · rcases dualVariable with capabilityMember | targetMember
      · simp at capabilityMember
      · exact freshTy (scheme.fieldsWellScoped field fieldMember).2
          (fieldTargetFreeTy field fieldMember) targetMember
  · simp only [dualVariables, List.mem_append] at resultMember
    rcases candidate with index | index
    · rcases resultMember with capabilityMember | targetMember
      · exact freshCap scheme.resultWellScoped.1 resultCapabilityFreeCap
          capabilityMember
      · exact freshCapFromTy scheme.resultWellScoped.2 resultTargetFreeCap
          targetMember
    · rcases resultMember with capabilityMember | targetMember
      · simp at capabilityMember
      · exact freshTy scheme.resultWellScoped.2 resultTargetFreeTy targetMember

/-- Pattern-constructor lookup returns a closed dual scheme in a well-formed
base signature. -/
theorem Signature.WellFormed.patternConstructorClosed_of_lookup
    {signature : Signature} (wellFormed : signature.WellFormed)
    {constructor : PatternCtor} {scheme : DualScheme}
    (lookup : signature.lookupPatternConstructor constructor = some scheme) :
    scheme.Closed := by
  unfold Signature.lookupPatternConstructor at lookup
  split at lookup
  next declaration found =>
    simp only [Option.some.injEq] at lookup
    subst scheme
    exact wellFormed.patternConstructorClosed declaration
      (List.mem_of_find?_eq_some found)
  next => simp at lookup

/-- A monomorphic context entry contributes exactly the variables of its
stored type. -/
theorem Context.mono_cons_unificationVars_origin
    (context : Context) (target : Ty) {candidate : UnificationVar}
    (member : candidate ∈
      Context.unificationVars (Scheme.mono target :: context)) :
    candidate ∈ target.unificationVars ∨
      candidate ∈ context.unificationVars := by
  cases candidate with
  | cap index =>
      simp only [Context.unificationVars, List.mem_append, List.mem_map] at member ⊢
      rcases member with tyMember | capMember
      · obtain ⟨candidateIndex, candidateMember, equality⟩ := tyMember
        cases equality
      · obtain ⟨candidateIndex, candidateMember, equality⟩ := capMember
        cases equality
        rw [Context.freeCapVars, mem_dedupFirst, List.mem_flatMap]
          at candidateMember
        obtain ⟨scheme, schemeMember, freeMember⟩ := candidateMember
        simp only [List.mem_cons] at schemeMember
        rcases schemeMember with rfl | schemeMember
        · left
          apply (Ty.mem_capVars_iff_unificationVars index target).mp
          apply mem_dedupFirst.mp
          simpa [Scheme.mono, Scheme.freeCapVars, PolyTy.ofTy,
            PolyTy.freeCapVars] using freeMember
        · right
          apply Or.inr
          refine ⟨index, ?_, rfl⟩
          rw [Context.freeCapVars, mem_dedupFirst, List.mem_flatMap]
          exact ⟨scheme, schemeMember, freeMember⟩
  | ty index =>
      simp only [Context.unificationVars, List.mem_append, List.mem_map] at member ⊢
      rcases member with tyMember | capMember
      · obtain ⟨candidateIndex, candidateMember, equality⟩ := tyMember
        cases equality
        rw [Context.freeTyVars, mem_dedupFirst, List.mem_flatMap]
          at candidateMember
        obtain ⟨scheme, schemeMember, freeMember⟩ := candidateMember
        simp only [List.mem_cons] at schemeMember
        rcases schemeMember with rfl | schemeMember
        · left
          apply (Ty.mem_tyVars_iff_unificationVars index target).mp
          apply mem_dedupFirst.mp
          simpa [Scheme.mono, Scheme.freeTyVars, PolyTy.ofTy,
            PolyTy.freeTyVars] using freeMember
        · right
          apply Or.inl
          refine ⟨index, ?_, rfl⟩
          rw [Context.freeTyVars, mem_dedupFirst, List.mem_flatMap]
          exact ⟨scheme, schemeMember, freeMember⟩
      · obtain ⟨candidateIndex, candidateMember, equality⟩ := capMember
        cases equality

/-- Support of the types prepended by `Pattern.extendContext`. -/
theorem Pattern.extendContext_support
    {outerContext : Context} {outerStart finish : Supply}
    {bindings : List Ty}
    (bindingsSupport : VariablesSupportProvenance outerContext outerStart finish
      (Ty.unificationVarsList bindings)) :
    VariablesSupportProvenance outerContext outerStart finish
      (Pattern.extendContext bindings outerContext).unificationVars := by
  induction bindings with
  | nil =>
      intro candidate member
      exact Or.inl (by simpa [Pattern.extendContext] using member)
  | cons binding bindings induction =>
      intro candidate member
      have origin := Context.mono_cons_unificationVars_origin
        (bindings.map Scheme.mono ++ outerContext) binding member
      rcases origin with bindingMember | tailMember
      · exact bindingsSupport candidate (by
          simpa [Ty.unificationVarsList] using Or.inl bindingMember)
      · apply induction
        · intro item itemMember
          exact bindingsSupport item (by
            simpa [Ty.unificationVarsList] using Or.inr itemMember)
        · simpa [Pattern.extendContext] using tailMember

/-- Field-equation generation introduces no variables beyond the actual and
expected dual lists. -/
theorem Pattern.fieldEquations_support
    {context : Context} {start finish : Supply} {actual expected : List Dual}
    (actualSupport : VariablesSupportProvenance context start finish
      (dualUnificationVars actual))
    (expectedSupport : VariablesSupportProvenance context start finish
      (dualUnificationVars expected)) :
    VariablesSupportProvenance context start finish
      (TypePM.unificationVars (Pattern.fieldEquations actual expected)) := by
  induction actual generalizing expected with
  | nil =>
      intro candidate member
      simp [Pattern.fieldEquations, TypePM.unificationVars] at member
  | cons actual actuals induction =>
      cases expected with
      | nil =>
          intro candidate member
          simp [Pattern.fieldEquations, TypePM.unificationVars] at member
      | cons expected expecteds =>
          intro candidate member
          have origin :
              candidate ∈ actual.target.unificationVars ∨
              candidate ∈ expected.target.unificationVars ∨
              candidate ∈ actual.capability.unificationVars ∨
              candidate ∈ expected.capability.unificationVars ∨
              candidate ∈ TypePM.unificationVars
                (Pattern.fieldEquations actuals expecteds) := by
            simpa [Pattern.fieldEquations, TypePM.unificationVars,
              Equation.unificationVars, dualVariables] using member
          rcases origin with actualTarget | expectedTarget | actualCapability |
              expectedCapability | tailMember
          · exact actualSupport candidate (by
              simp [dualUnificationVars, dualVariables, actualTarget])
          · exact expectedSupport candidate (by
              simp [dualUnificationVars, dualVariables, expectedTarget])
          · exact actualSupport candidate (by
              simp [dualUnificationVars, dualVariables, actualCapability])
          · exact expectedSupport candidate (by
              simp [dualUnificationVars, dualVariables, expectedCapability])
          · apply induction
              (fun item itemMember => actualSupport item (by
                simp only [dualUnificationVars, List.flatMap_cons,
                  List.mem_append]
                exact Or.inr itemMember))
              (fun item itemMember => expectedSupport item (by
                simp only [dualUnificationVars, List.flatMap_cons,
                  List.mem_append]
                exact Or.inr itemMember))
              candidate
              tailMember

/-- Rebase child generated support from an extended context to an outer
context whose added variables are themselves already supported. -/
theorem GeneratedSupportProvenance.rebase_context
    {outerContext childContext : Context} {outerStart childStart finish : Supply}
    {generated : Generated}
    (outerToChild : outerStart.Le childStart)
    (childIncreases : childStart.Le finish)
    (contextSupport : VariablesSupportProvenance outerContext outerStart
      childStart childContext.unificationVars)
    (childSupport : GeneratedSupportProvenance childContext childStart finish
      generated) :
    GeneratedSupportProvenance outerContext outerStart finish generated := by
  intro candidate member
  rcases childSupport candidate member with childContextMember | fresh
  · rcases contextSupport candidate childContextMember with outer | allocated
    · exact Or.inl outer
    · exact Or.inr (allocated.extend_finish childIncreases)
  · exact Or.inr (fresh.lower_start outerToChild)

/-! ## Support of individual M4 components -/

/-- `fix` preserves generated support whenever its recursive callback does. -/
theorem FixElaboratesUsing.supportProvenance
    {BodyElaborates : Context → Expr → Supply → Generated → Supply → Prop}
    (bodyIncreases : ∀ {context expression start generated finish},
      BodyElaborates context expression start generated finish → start.Le finish)
    (bodySupport : ∀ {context expression start generated finish},
      BodyElaborates context expression start generated finish →
        GeneratedSupportProvenance context start finish generated)
    {context expression start generated finish}
    (derivation : FixElaboratesUsing BodyElaborates context expression start
      generated finish) :
    GeneratedSupportProvenance context start finish generated := by
  cases derivation with
  | @fixE body start generatedBody finish direct bodyDerivation =>
      have startToBody : start.Le (Fix.bodySupply body start) := by
        cases body <;> simp [Fix.bodySupply, Supply.Le, Supply.nextTy]
      have bodyToFinish := bodyIncreases bodyDerivation
      have typeSupport (target : Ty)
          (member : ∀ candidate, candidate ∈ target.unificationVars →
            candidate.FreshIn start (Fix.bodySupply body start)) :
          VariablesSupportProvenance context start (Fix.bodySupply body start)
            target.unificationVars := by
        intro candidate candidateMember
        exact Or.inr (member candidate candidateMember)
      have domainSupport : VariablesSupportProvenance context start
          (Fix.bodySupply body start) (Fix.domain body start).unificationVars := by
        apply typeSupport
        intro candidate member
        cases candidate <;> cases body <;>
          simp_all [Fix.domain, Fix.bodySupply, Ty.unificationVars,
            Cap.unificationVars, UnificationVar.FreshIn, Supply.nextTy] <;>
          omega
      have codomainSupport : VariablesSupportProvenance context start
          (Fix.bodySupply body start) (Fix.codomain body start).unificationVars := by
        apply typeSupport
        intro candidate member
        cases candidate <;> cases body <;>
          simp_all [Fix.codomain, Fix.bodySupply, Ty.unificationVars,
            Cap.unificationVars, UnificationVar.FreshIn, Supply.nextTy] <;>
          omega
      have bodyContextSupport : VariablesSupportProvenance context start
          (Fix.bodySupply body start)
          (Fix.bodyContext (Fix.domain body start) (Fix.codomain body start)
            context).unificationVars := by
        intro candidate member
        have first := Context.mono_cons_unificationVars_origin
          (Scheme.mono (.fn (Fix.domain body start) (Fix.codomain body start)) ::
            context) (Fix.domain body start) member
        rcases first with domainMember | restMember
        · exact domainSupport candidate domainMember
        · have second := Context.mono_cons_unificationVars_origin context
            (.fn (Fix.domain body start) (Fix.codomain body start)) restMember
          rcases second with selfMember | outerMember
          · simp only [Ty.unificationVars, List.mem_append] at selfMember
            rcases selfMember with domainMember | codomainMember
            · exact domainSupport candidate domainMember
            · exact codomainSupport candidate codomainMember
          · exact Or.inl outerMember
      have rebasedBody : GeneratedSupportProvenance context start finish
          generatedBody :=
        (bodySupport bodyDerivation).rebase_context startToBody bodyToFinish
          bodyContextSupport
      intro candidate member
      by_cases bodyMember : candidate ∈ generatedBody.unificationVars
      · exact rebasedBody candidate bodyMember
      · have outside :
            candidate ∈ (Fix.domain body start).unificationVars ∨
              candidate ∈ (Fix.codomain body start).unificationVars := by
          simp [Generated.fromFix, Generated.unificationVars,
            TypePM.unificationVars, Equation.unificationVars]
            at member bodyMember ⊢
          simp_all [Ty.unificationVars]
        rcases outside with domainMember | codomainMember
        · rcases domainSupport candidate domainMember with outer | fresh
          · exact Or.inl outer
          · exact Or.inr (fresh.extend_finish bodyToFinish)
        · rcases codomainSupport candidate codomainMember with outer | fresh
          · exact Or.inl outer
          · exact Or.inr (fresh.extend_finish bodyToFinish)

end TypePM.Source
