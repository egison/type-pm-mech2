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
        simp only [Fix.bodySupply]
        split <;> simp [Supply.Le, Supply.nextTy])
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
  | and left right =>
      exact Supply.le_trans
        (PatternElaboratesUsing.supply_le_next expressionIncreases left)
        (PatternElaboratesUsing.supply_le_next expressionIncreases right)
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
        simp only [Fix.bodySupply]
        split <;> simp [Supply.Le, Supply.nextTy]
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
        cases candidate <;> simp only [Fix.domain] at member <;>
          split at member <;>
          simp_all [Fix.bodySupply, Ty.unificationVars, Cap.unificationVars,
            UnificationVar.FreshIn, Supply.nextTy] <;> omega
      have codomainSupport : VariablesSupportProvenance context start
          (Fix.bodySupply body start) (Fix.codomain body start).unificationVars := by
        apply typeSupport
        intro candidate member
        cases candidate <;> simp only [Fix.codomain] at member <;>
          split at member <;>
          simp_all [Fix.bodySupply, Ty.unificationVars, Cap.unificationVars,
            UnificationVar.FreshIn, Supply.nextTy] <;> omega
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

/-! ## Support of matcher headers

The component relations below accept types synthesized by an earlier
component.  Their support hypotheses say that those input types either came
from the original context or were allocated before the component started.
This explicit input condition is what lets the component lemmas compose in
source order.
-/

/-- Lift support across a later finishing supply. -/
theorem VariablesSupportProvenance.extend_finish
    {context : Context} {start middle finish : Supply} {variables}
    (increases : middle.Le finish)
    (support : VariablesSupportProvenance context start middle variables) :
    VariablesSupportProvenance context start finish variables := by
  intro candidate member
  rcases support candidate member with outer | fresh
  · exact Or.inl outer
  · exact Or.inr (fresh.extend_finish increases)

/-- Generated support can be moved to an earlier starting supply. -/
theorem GeneratedSupportProvenance.lower_start
    {context : Context} {outerStart start finish : Supply} {generated}
    (increases : outerStart.Le start)
    (support : GeneratedSupportProvenance context start finish generated) :
    GeneratedSupportProvenance context outerStart finish generated := by
  intro candidate member
  rcases support candidate member with outer | fresh
  · exact Or.inl outer
  · exact Or.inr (fresh.lower_start increases)

/-- Generated support can be moved to a later finishing supply. -/
theorem GeneratedSupportProvenance.extend_finish
    {context : Context} {start middle finish : Supply} {generated}
    (increases : middle.Le finish)
    (support : GeneratedSupportProvenance context start middle generated) :
    GeneratedSupportProvenance context start finish generated := by
  intro candidate member
  rcases support candidate member with outer | fresh
  · exact Or.inl outer
  · exact Or.inr (fresh.extend_finish increases)

/-- One freshly allocated ordinary type variable has the expected support. -/
theorem freshTy_support (context : Context) (start : Supply) :
    VariablesSupportProvenance context start (start.nextTy 1)
      (Ty.unificationVars (.var ⟨start.ty⟩)) := by
  intro candidate member
  have : candidate = .ty ⟨start.ty⟩ := by
    simpa [Ty.unificationVars] using member
  subst candidate
  exact Or.inr (by simp [UnificationVar.FreshIn, Supply.nextTy])

/-- One freshly allocated capability variable has the expected support. -/
theorem freshCap_support (context : Context) (start : Supply) :
    VariablesSupportProvenance context start
      ⟨start.ty, start.cap + 1⟩ (Cap.unificationVars (.var ⟨start.cap⟩)) := by
  intro candidate member
  have : candidate = .cap ⟨start.cap⟩ := by
    simpa [Cap.unificationVars] using member
  subst candidate
  exact Or.inr (by simp [UnificationVar.FreshIn])

/-- Variables of a closed ordinary scheme instance are allocated by that
instance. -/
theorem Scheme.instantiate_variables_support
    {context : Context} {start : Supply} {scheme : Scheme}
    (closed : scheme.Closed) :
    VariablesSupportProvenance context start (scheme.instantiate start).2
      (scheme.instantiate start).1.unificationVars := by
  intro candidate member
  exact supportProvenance_closed_instantiate (context := context) closed candidate
    (by simpa [Generated.unificationVars, TypePM.unificationVars,
      pendingUnificationVars] using member)

/-- Variable collection distributes over concatenation of type lists. -/
theorem Ty.unificationVarsList_append (left right : List Ty) :
    Ty.unificationVarsList (left ++ right) =
      Ty.unificationVarsList left ++ Ty.unificationVarsList right := by
  induction left with
  | nil => rfl
  | cons head tail induction =>
      simp only [List.cons_append, Ty.unificationVarsList]
      rw [induction, List.append_assoc]

/-- Variables in a type found by peeling a curried function occur in the
original function type. -/
theorem MatcherTyping.peelFunctionExact_variables
    {count : Nat} {source : Ty} {fields : List Ty} {result : Ty}
    (peel : peelFunctionExact count source = some (fields, result)) :
    ∀ candidate, candidate ∈
        Ty.unificationVarsList fields ++ result.unificationVars →
      candidate ∈ source.unificationVars := by
  induction count generalizing source fields with
  | zero =>
      simp [peelFunctionExact] at peel
      rcases peel with ⟨rfl, rfl⟩
      intro candidate member
      simpa [Ty.unificationVarsList] using member
  | succ count induction =>
      cases source with
      | fn domain codomain =>
          cases equation : peelFunctionExact count codomain with
          | none => simp [peelFunctionExact, equation] at peel
          | some output =>
            rcases output with ⟨tailFields, finalResult⟩
            simp [peelFunctionExact, equation] at peel
            rcases peel with ⟨rfl, rfl⟩
            intro candidate member
            simp only [Ty.unificationVarsList, List.mem_append] at member
            rcases member with (domainMember | tailMember) | resultMember
            · simpa [Ty.unificationVars] using
                (Or.inl domainMember : candidate ∈ domain.unificationVars ∨
                  candidate ∈ codomain.unificationVars)
            · have codomainMember := induction equation candidate (by
                simpa [Ty.unificationVarsList] using
                  (Or.inl tailMember : candidate ∈
                    Ty.unificationVarsList tailFields ∨
                    candidate ∈ finalResult.unificationVars))
              simpa [Ty.unificationVars] using
                (Or.inr codomainMember : candidate ∈ domain.unificationVars ∨
                  candidate ∈ codomain.unificationVars)
            · have codomainMember := induction equation candidate (by
                simpa [Ty.unificationVarsList] using
                  (Or.inr resultMember : candidate ∈
                    Ty.unificationVarsList tailFields ∨
                    candidate ∈ finalResult.unificationVars))
              simpa [Ty.unificationVars] using
                (Or.inr codomainMember : candidate ∈ domain.unificationVars ∨
                  candidate ∈ codomain.unificationVars)
      | _ => simp [peelFunctionExact] at peel

namespace MatcherTyping

abbrev GeneratedPPatSupportProvenance
    (context : Context) (start finish : Supply) (generated : GeneratedPPat) :=
  VariablesSupportProvenance context start finish generated.unificationVars

abbrev GeneratedPPatsSupportProvenance
    (context : Context) (start finish : Supply) (generated : GeneratedPPats) :=
  VariablesSupportProvenance context start finish generated.unificationVars

/-- Support of one type equality follows from support of both sides. -/
theorem tyEquation_support
    {left right : Ty}
    (leftSupport : VariablesSupportProvenance context start finish
      left.unificationVars)
    (rightSupport : VariablesSupportProvenance context start finish
      right.unificationVars) :
    VariablesSupportProvenance context start finish
      (TypePM.unificationVars [.ty left right]) := by
  intro candidate member
  simp only [TypePM.unificationVars, Equation.unificationVars,
    List.mem_append, List.not_mem_nil, or_false] at member
  rcases member with leftMember | rightMember
  · exact leftSupport candidate leftMember
  · exact rightSupport candidate rightMember

/-- Support of one capability equality follows from support of both sides. -/
theorem capEquation_support
    {left right : Cap}
    (leftSupport : VariablesSupportProvenance context start finish
      left.unificationVars)
    (rightSupport : VariablesSupportProvenance context start finish
      right.unificationVars) :
    VariablesSupportProvenance context start finish
      (TypePM.unificationVars [.cap left right]) := by
  intro candidate member
  simp only [TypePM.unificationVars, Equation.unificationVars,
    List.mem_append, List.not_mem_nil, or_false] at member
  rcases member with leftMember | rightMember
  · exact leftSupport candidate leftMember
  · exact rightSupport candidate rightMember

mutual

/-- Support of a pattern-pattern header and its synthesized holes, captures,
evidence, and equations. -/
theorem PPatElaborates.supportProvenance
    {signature : FrozenSignature} (wellFormed : signature.WellFormed)
    {pattern expectedTarget expectedCapability start generated finish}
    (targetSupport : VariablesSupportProvenance context outerStart start
      expectedTarget.unificationVars)
    (capabilitySupport : VariablesSupportProvenance context outerStart start
      (match expectedCapability with
       | none => []
       | some capability => capability.unificationVars))
    (outerToStart : outerStart.Le start)
    (derivation : PPatElaborates signature pattern expectedTarget
      expectedCapability start generated finish) :
    GeneratedPPatSupportProvenance context outerStart finish generated := by
  cases derivation with
  | hole =>
      intro candidate member
      cases expectedCapability with
      | none =>
        simp [GeneratedPPat.unificationVars, dualUnificationVars,
          dualVariables, Ty.unificationVarsList,
          TypePM.unificationVars] at member
        rcases member with freshMember | targetMember
        · have equality : candidate = .cap ⟨start.cap⟩ := by
            simpa [Cap.unificationVars] using freshMember
          subst candidate
          exact Or.inr ⟨outerToStart.2, Nat.lt_succ_self start.cap⟩
        · exact (targetSupport.extend_finish (by simp [Supply.Le])) candidate
            targetMember
      | some expected =>
        simp [GeneratedPPat.unificationVars, dualUnificationVars,
          dualVariables, Ty.unificationVarsList, TypePM.unificationVars,
          Equation.unificationVars] at member
        rcases member with freshMember | targetMember | freshMember | expectedMember
        · have equality : candidate = .cap ⟨start.cap⟩ := by
            simpa [Cap.unificationVars] using freshMember
          subst candidate
          exact Or.inr ⟨outerToStart.2, Nat.lt_succ_self start.cap⟩
        · exact (targetSupport.extend_finish (by simp [Supply.Le])) candidate
            targetMember
        · have equality : candidate = .cap ⟨start.cap⟩ := by
            simpa [Cap.unificationVars] using freshMember
          subst candidate
          exact Or.inr ⟨outerToStart.2, Nat.lt_succ_self start.cap⟩
        · exact (capabilitySupport.extend_finish
            (by simp [Supply.Le])) candidate expectedMember
  | wild =>
      intro candidate member
      simp [GeneratedPPat.unificationVars, dualUnificationVars,
        Ty.unificationVarsList, TypePM.unificationVars] at member
  | capture =>
      intro candidate member
      apply targetSupport candidate
      simpa [GeneratedPPat.unificationVars, dualUnificationVars,
        Ty.unificationVarsList, TypePM.unificationVars] using member
  | @ctor constructor fields expectedTarget expectedCapability start scheme
      generatedFields finish lookup arity fieldsDerivation =>
      have closed := wellFormed.baseWellFormed.patternConstructorClosed_of_lookup
        lookup
      have instantiatedFresh := DualScheme.instantiate_support closed start
      have instantiatedSupport : VariablesSupportProvenance context start
          (scheme.instantiate start).2
          (dualUnificationVars (scheme.instantiate start).1.fields ++
            dualVariables (scheme.instantiate start).1.result) := by
        intro candidate member
        rcases instantiatedFresh candidate member with impossible | fresh
        · exfalso
          rcases impossible with ⟨index, indexMember, equality⟩ |
              ⟨index, indexMember, equality⟩ <;>
            simpa [Context.freeTyVars, Context.freeCapVars,
              mem_dedupFirst] using indexMember
        · exact Or.inr fresh
      have outerInstantiatedSupport : VariablesSupportProvenance context
          outerStart (scheme.instantiate start).2
          (dualUnificationVars (scheme.instantiate start).1.fields ++
            dualVariables (scheme.instantiate start).1.result) :=
        instantiatedSupport.lower_start outerToStart
      have fieldsSupport := PPatsElaborate.supportProvenance wellFormed
        (fun candidate member => outerInstantiatedSupport candidate
          (by exact List.mem_append_left _ member))
        (Supply.le_trans outerToStart (by
          simp [Supply.Le, DualScheme.instantiate])) fieldsDerivation
      have instantiatedToFinish := fieldsDerivation.supply_le_next
      have instantiatedFinal :=
        outerInstantiatedSupport.extend_finish instantiatedToFinish
      have fieldsFinal := fieldsSupport
      have holesSupport : VariablesSupportProvenance context outerStart finish
          (dualUnificationVars generatedFields.holes) := by
        intro candidate member
        exact fieldsFinal candidate (by
          simp [GeneratedPPats.unificationVars, member])
      have capturesSupport : VariablesSupportProvenance context outerStart finish
          (Ty.unificationVarsList generatedFields.captures) := by
        intro candidate member
        exact fieldsFinal candidate (by
          simp [GeneratedPPats.unificationVars, member])
      have resultTargetSupport : VariablesSupportProvenance context outerStart finish
          (scheme.instantiate start).1.result.target.unificationVars := by
        intro candidate member
        exact instantiatedFinal candidate (by
          exact List.mem_append_right _ (by simp [dualVariables, member]))
      have resultCapabilitySupport : VariablesSupportProvenance context outerStart
          finish (scheme.instantiate start).1.result.capability.unificationVars := by
        intro candidate member
        exact instantiatedFinal candidate (by
          exact List.mem_append_right _ (by simp [dualVariables, member]))
      have targetFinal := targetSupport.extend_finish
        (Supply.le_trans (by simp [Supply.Le, DualScheme.instantiate])
          instantiatedToFinish)
      have outerTargetEquation := tyEquation_support resultTargetSupport targetFinal
      have fieldsHardSupport : VariablesSupportProvenance context outerStart finish
          (TypePM.unificationVars generatedFields.hard) := by
        intro candidate member
        exact fieldsFinal candidate (by
          simp [GeneratedPPats.unificationVars, member])
      have hardSupport : VariablesSupportProvenance context outerStart finish
          (TypePM.unificationVars
            (([.ty (scheme.instantiate start).1.result.target expectedTarget] ++
              (match expectedCapability with
               | some expected =>
                   [.cap (scheme.instantiate start).1.result.capability expected]
               | none => [])) ++ generatedFields.hard)) := by
        intro candidate member
        have targetDirect : VariablesSupportProvenance context outerStart finish
            (Equation.ty (scheme.instantiate start).1.result.target
              expectedTarget).unificationVars := by
          intro item itemMember
          exact outerTargetEquation item (by
            simpa [TypePM.unificationVars] using itemMember)
        cases expectedCapability with
        | none =>
            change candidate ∈
              (Equation.ty (scheme.instantiate start).1.result.target
                expectedTarget).unificationVars ++
              TypePM.unificationVars generatedFields.hard at member
            exact (targetDirect.append fieldsHardSupport) candidate member
        | some expected =>
            have expectedFinal :=
              capabilitySupport.extend_finish
                (Supply.le_trans
                  (by simp [Supply.Le, DualScheme.instantiate])
                  instantiatedToFinish)
            have capabilityEquation :=
              capEquation_support resultCapabilitySupport expectedFinal
            have capabilityDirect : VariablesSupportProvenance context outerStart
                finish (Equation.cap
                  (scheme.instantiate start).1.result.capability
                  expected).unificationVars := by
              intro item itemMember
              exact capabilityEquation item (by
                simpa [TypePM.unificationVars] using itemMember)
            change candidate ∈
              (Equation.ty (scheme.instantiate start).1.result.target
                expectedTarget).unificationVars ++
              ((Equation.cap (scheme.instantiate start).1.result.capability
                expected).unificationVars ++
                TypePM.unificationVars generatedFields.hard) at member
            exact (targetDirect.append
              (capabilityDirect.append fieldsHardSupport)) candidate member
      intro candidate member
      exact (((holesSupport.append capturesSupport).append
        resultCapabilitySupport).append hardSupport) candidate member

/-- Support of a left-to-right list of pattern-pattern headers. -/
theorem PPatsElaborate.supportProvenance
    {signature : FrozenSignature} (wellFormed : signature.WellFormed)
    {patterns expected start generated finish}
    (expectedSupport : VariablesSupportProvenance context outerStart start
      (dualUnificationVars expected))
    (outerToStart : outerStart.Le start)
    (derivation : PPatsElaborate signature patterns expected start generated
      finish) :
    GeneratedPPatsSupportProvenance context outerStart finish generated := by
  cases derivation with
  | nil =>
      intro candidate member
      simp [GeneratedPPats.unificationVars, dualUnificationVars,
        Ty.unificationVarsList, TypePM.unificationVars] at member
  | @cons pattern patterns expected expecteds start generatedPattern afterPattern
      generatedPatterns finish head tail =>
      have headExpected : VariablesSupportProvenance context outerStart start
          (dualVariables expected) := by
        intro candidate member
        exact expectedSupport candidate (by
          simp [dualUnificationVars, member])
      have headSupport := PPatElaborates.supportProvenance wellFormed
        (fun candidate member => headExpected candidate (by
          simp [dualVariables, member]))
        (fun candidate member => headExpected candidate (by
          simp [dualVariables, member])) outerToStart head
      have startToAfter := head.supply_le_next
      have tailExpectedAtStart : VariablesSupportProvenance context outerStart start
          (dualUnificationVars expecteds) := by
        intro candidate member
        exact expectedSupport candidate (by
          simp only [dualUnificationVars, List.flatMap_cons, List.mem_append]
          exact Or.inr member)
      have tailExpected : VariablesSupportProvenance context outerStart afterPattern
          (dualUnificationVars expecteds) :=
        tailExpectedAtStart.extend_finish startToAfter
      have tailSupport := PPatsElaborate.supportProvenance
        (context := context) (outerStart := outerStart) wellFormed tailExpected
        (Supply.le_trans outerToStart startToAfter) tail
      intro candidate member
      have headHoles : VariablesSupportProvenance context outerStart finish
          (dualUnificationVars generatedPattern.holes) := by
        intro item itemMember
        exact (headSupport.extend_finish tail.supply_le_next) item (by
          simp [GeneratedPPat.unificationVars, itemMember])
      have tailHoles : VariablesSupportProvenance context outerStart finish
          (dualUnificationVars generatedPatterns.holes) := by
        intro item itemMember
        exact tailSupport item (by
          simp [GeneratedPPats.unificationVars, itemMember])
      have headCaptures : VariablesSupportProvenance context outerStart finish
          (Ty.unificationVarsList generatedPattern.captures) := by
        intro item itemMember
        exact (headSupport.extend_finish tail.supply_le_next) item (by
          simp [GeneratedPPat.unificationVars, itemMember])
      have tailCaptures : VariablesSupportProvenance context outerStart finish
          (Ty.unificationVarsList generatedPatterns.captures) := by
        intro item itemMember
        exact tailSupport item (by
          simp [GeneratedPPats.unificationVars, itemMember])
      have headHard : VariablesSupportProvenance context outerStart finish
          (TypePM.unificationVars generatedPattern.hard) := by
        intro item itemMember
        exact (headSupport.extend_finish tail.supply_le_next) item (by
          simp [GeneratedPPat.unificationVars, itemMember])
      have tailHard : VariablesSupportProvenance context outerStart finish
          (TypePM.unificationVars generatedPatterns.hard) := by
        intro item itemMember
        exact tailSupport item (by
          simp [GeneratedPPats.unificationVars, itemMember])
      exact (headHoles.append tailHoles).append
        ((headCaptures.append tailCaptures).append
          (headHard.append tailHard)) candidate (by
            simpa [GeneratedPPats.unificationVars, dualUnificationVars,
              Ty.unificationVarsList_append, List.flatMap_append,
              List.append_assoc,
              unificationVars_append] using member)

end

abbrev GeneratedDPatSupportProvenance
    (context : Context) (start finish : Supply) (generated : GeneratedDPat) :=
  VariablesSupportProvenance context start finish generated.unificationVars

abbrev GeneratedDPatsSupportProvenance
    (context : Context) (start finish : Supply) (generated : GeneratedDPats) :=
  VariablesSupportProvenance context start finish generated.unificationVars

/-- Tuple fields reserved consecutively from the ordinary type-variable
counter are supported by exactly that reservation interval. -/
theorem freshTargets_support (context : Context) (start : Supply) (count : Nat) :
    VariablesSupportProvenance context start (start.nextTy count)
      (Ty.unificationVarsList (freshTargets start count)) := by
  induction count with
  | zero =>
      intro candidate member
      simp [freshTargets, Ty.unificationVarsList] at member
  | succ count induction =>
      have step : (start.nextTy count).Le (start.nextTy (count + 1)) := by
        simp [Supply.Le, Supply.nextTy]
      have previous := induction.extend_finish step
      have last : VariablesSupportProvenance context start
          (start.nextTy (count + 1))
          (Ty.unificationVars (.var ⟨start.ty + count⟩)) := by
        intro candidate member
        have equality : candidate = .ty ⟨start.ty + count⟩ := by
          simpa [Ty.unificationVars] using member
        subst candidate
        exact Or.inr (by
          simp only [UnificationVar.FreshIn, Supply.nextTy]
          omega)
      intro candidate member
      apply previous.append last candidate
      simpa [freshTargets, List.range_succ, List.map_append,
        Ty.unificationVarsList_append, Ty.unificationVarsList] using member

mutual

/-- Support of one matcher data pattern. -/
theorem DPatElaborates.supportProvenance
    {signature : FrozenSignature} (wellFormed : signature.WellFormed)
    {pattern expected start generated finish}
    (expectedSupport : VariablesSupportProvenance context outerStart start
      expected.unificationVars)
    (outerToStart : outerStart.Le start)
    (derivation : DPatElaborates signature pattern expected start generated
      finish) :
    GeneratedDPatSupportProvenance context outerStart finish generated := by
  cases derivation with
  | var =>
      intro candidate member
      apply expectedSupport candidate
      simpa [GeneratedDPat.unificationVars, Ty.unificationVarsList,
        TypePM.unificationVars] using member
  | wild =>
      intro candidate member
      simp [GeneratedDPat.unificationVars, Ty.unificationVarsList,
        TypePM.unificationVars] at member
  | @ctor constructor fields expected start scheme fieldTypes resultType
      generatedFields finish lookup arity peel fieldsDerivation =>
      have closed := wellFormed.baseWellFormed.dataConstructorClosed_of_lookup
        lookup
      have instantiated := Scheme.instantiate_variables_support
        (context := context) (start := start) closed
      have outerInstantiated := instantiated.lower_start outerToStart
      have instantiatedToFields : start.Le (scheme.instantiate start).2 := by
        simp [Supply.Le, Scheme.instantiate]
      have peeledSupport : VariablesSupportProvenance context outerStart
          (scheme.instantiate start).2
          (Ty.unificationVarsList fieldTypes ++ resultType.unificationVars) := by
        intro candidate member
        exact outerInstantiated candidate
          (MatcherTyping.peelFunctionExact_variables peel candidate member)
      have fieldTypesSupport : VariablesSupportProvenance context outerStart
          (scheme.instantiate start).2 (Ty.unificationVarsList fieldTypes) := by
        intro candidate member
        exact peeledSupport candidate (List.mem_append_left _ member)
      have fieldsSupport := DPatsElaborate.supportProvenance wellFormed
        fieldTypesSupport (Supply.le_trans outerToStart instantiatedToFields)
        fieldsDerivation
      have instantiatedToFinish := fieldsDerivation.supply_le_next
      have resultSupport : VariablesSupportProvenance context outerStart finish
          resultType.unificationVars := by
        intro candidate member
        exact (peeledSupport.extend_finish instantiatedToFinish) candidate
          (List.mem_append_right _ member)
      have expectedFinal := expectedSupport.extend_finish
        (Supply.le_trans instantiatedToFields instantiatedToFinish)
      have equationSupport := tyEquation_support resultSupport expectedFinal
      have bindingsSupport : VariablesSupportProvenance context outerStart finish
          (Ty.unificationVarsList generatedFields.bindings) := by
        intro candidate member
        exact fieldsSupport candidate (by
          simp [GeneratedDPats.unificationVars, member])
      have fieldsHardSupport : VariablesSupportProvenance context outerStart finish
          (TypePM.unificationVars generatedFields.hard) := by
        intro candidate member
        exact fieldsSupport candidate (by
          simp [GeneratedDPats.unificationVars, member])
      intro candidate member
      exact bindingsSupport.append (equationSupport.append fieldsHardSupport)
        candidate (by
          simpa [GeneratedDPat.unificationVars, TypePM.unificationVars]
            using member)
  | @tuple items expected start fields generatedItems finish fieldsEquality
      itemsDerivation =>
      subst fields
      have reserved := freshTargets_support context start items.length
      have outerReserved := reserved.lower_start outerToStart
      have startToItems : start.Le (start.nextTy items.length) :=
        Supply.le_nextTy _ _
      have itemsSupport := DPatsElaborate.supportProvenance wellFormed
        outerReserved (Supply.le_trans outerToStart startToItems) itemsDerivation
      have itemsToFinish := itemsDerivation.supply_le_next
      have fieldsFinal := outerReserved.extend_finish itemsToFinish
      have expectedFinal := expectedSupport.extend_finish
        (Supply.le_trans startToItems itemsToFinish)
      have productSupport : VariablesSupportProvenance context outerStart finish
          (.prod (freshTargets start items.length) : Ty).unificationVars := by
        simpa [Ty.unificationVars] using fieldsFinal
      have equationSupport := tyEquation_support expectedFinal productSupport
      have bindingsSupport : VariablesSupportProvenance context outerStart finish
          (Ty.unificationVarsList generatedItems.bindings) := by
        intro candidate member
        exact itemsSupport candidate (by
          simp [GeneratedDPats.unificationVars, member])
      have itemsHardSupport : VariablesSupportProvenance context outerStart finish
          (TypePM.unificationVars generatedItems.hard) := by
        intro candidate member
        exact itemsSupport candidate (by
          simp [GeneratedDPats.unificationVars, member])
      intro candidate member
      exact bindingsSupport.append (equationSupport.append itemsHardSupport)
        candidate (by
          simpa [GeneratedDPat.unificationVars, TypePM.unificationVars]
            using member)

/-- Support of a source-ordered list of matcher data patterns. -/
theorem DPatsElaborate.supportProvenance
    {signature : FrozenSignature} (wellFormed : signature.WellFormed)
    {patterns expected start generated finish}
    (expectedSupport : VariablesSupportProvenance context outerStart start
      (Ty.unificationVarsList expected))
    (outerToStart : outerStart.Le start)
    (derivation : DPatsElaborate signature patterns expected start generated
      finish) :
    GeneratedDPatsSupportProvenance context outerStart finish generated := by
  cases derivation with
  | nil =>
      intro candidate member
      simp [GeneratedDPats.unificationVars, Ty.unificationVarsList,
        TypePM.unificationVars] at member
  | @cons pattern patterns expected expecteds start generatedPattern afterPattern
      generatedPatterns finish head tail =>
      have headExpected : VariablesSupportProvenance context outerStart start
          expected.unificationVars := by
        intro candidate member
        exact expectedSupport candidate (by
          simp [Ty.unificationVarsList, member])
      have headSupport := DPatElaborates.supportProvenance wellFormed headExpected
        outerToStart head
      have startToAfter := head.supply_le_next
      have tailExpectedAtStart : VariablesSupportProvenance context outerStart start
          (Ty.unificationVarsList expecteds) := by
        intro candidate member
        exact expectedSupport candidate (by
          simp [Ty.unificationVarsList, member])
      have tailSupport := DPatsElaborate.supportProvenance wellFormed
        (tailExpectedAtStart.extend_finish startToAfter)
        (Supply.le_trans outerToStart startToAfter) tail
      have afterToFinish := tail.supply_le_next
      have headFinal := headSupport.extend_finish afterToFinish
      have headBindings : VariablesSupportProvenance context outerStart finish
          (Ty.unificationVarsList generatedPattern.bindings) := by
        intro candidate member
        exact headFinal candidate (by
          simp [GeneratedDPat.unificationVars, member])
      have tailBindings : VariablesSupportProvenance context outerStart finish
          (Ty.unificationVarsList generatedPatterns.bindings) := by
        intro candidate member
        exact tailSupport candidate (by
          simp [GeneratedDPats.unificationVars, member])
      have headHard : VariablesSupportProvenance context outerStart finish
          (TypePM.unificationVars generatedPattern.hard) := by
        intro candidate member
        exact headFinal candidate (by
          simp [GeneratedDPat.unificationVars, member])
      have tailHard : VariablesSupportProvenance context outerStart finish
          (TypePM.unificationVars generatedPatterns.hard) := by
        intro candidate member
        exact tailSupport candidate (by
          simp [GeneratedDPats.unificationVars, member])
      intro candidate member
      exact (headBindings.append tailBindings).append
        (headHard.append tailHard) candidate (by
          simpa [GeneratedDPats.unificationVars, Ty.unificationVarsList_append,
            unificationVars_append] using member)

end

abbrev GeneratedChecksSupportProvenance
    (context : Context) (start finish : Supply)
    (generated : GeneratedChecks) :=
  VariablesSupportProvenance context start finish generated.unificationVars

/-- Checking an expression against a supported expected type preserves
generated-variable provenance. -/
theorem CheckedExpressionElaboratesUsing.supportProvenance
    {expressionRelation : ExpressionElaborationRelation}
    (expressionIncreases : ∀ {context expression start generated finish},
      expressionRelation context expression start generated finish →
        start.Le finish)
    (expressionSupport : ∀ {context expression start generated finish},
      expressionRelation context expression start generated finish →
        GeneratedSupportProvenance context start finish generated)
    {expression expected start generated finish}
    (expectedSupport : VariablesSupportProvenance context outerStart start
      expected.unificationVars)
    (outerToStart : outerStart.Le start)
    (derivation : CheckedExpressionElaboratesUsing expressionRelation context
      expression expected start generated finish) :
    GeneratedChecksSupportProvenance context outerStart finish generated := by
  cases derivation with
  | mk childDerivation =>
      have childSupport :=
        (expressionSupport childDerivation).lower_start outerToStart
      have childIncreases := expressionIncreases childDerivation
      have expectedFinal := expectedSupport.extend_finish childIncreases
      intro candidate member
      simp only [GeneratedChecks.unificationVars, GeneratedChecks.checked,
        pendingUnificationVars_append, pendingUnificationVars,
        CheckObligation.unificationVars, List.mem_append] at member
      rcases member with hardMember | pendingMember | obligationMember |
          impossible
      · exact childSupport candidate (by
          simp [Generated.unificationVars, hardMember])
      · exact childSupport candidate (by
          simp [Generated.unificationVars, pendingMember])
      · rcases obligationMember with sourceMember | expectedMember
        · exact childSupport candidate (by
            simp [Generated.unificationVars, sourceMember])
        · exact expectedFinal candidate expectedMember
      · simp at impossible

/-- Support of separately checked next-matcher tuple components. -/
theorem NextMatcherItemsElaborateUsing.supportProvenance
    {expressionRelation : ExpressionElaborationRelation}
    (expressionIncreases : ∀ {context expression start generated finish},
      expressionRelation context expression start generated finish →
        start.Le finish)
    (expressionSupport : ∀ {context expression start generated finish},
      expressionRelation context expression start generated finish →
        GeneratedSupportProvenance context start finish generated)
    {items holes start generated finish}
    (holesSupport : VariablesSupportProvenance context outerStart start
      (dualUnificationVars holes))
    (outerToStart : outerStart.Le start)
    (derivation : NextMatcherItemsElaborateUsing expressionRelation context
      items holes start generated finish) :
    GeneratedChecksSupportProvenance context outerStart finish generated := by
  induction derivation with
  | nil =>
      intro candidate member
      simp [GeneratedChecks.unificationVars, GeneratedChecks.empty,
        TypePM.unificationVars, pendingUnificationVars] at member
  | @cons item items hole holes start generatedItem afterItem generatedItems
      finish head tail induction =>
      have holeSupport : VariablesSupportProvenance context outerStart start
          (dualVariables hole) := by
        intro candidate member
        exact holesSupport candidate (by
          simp [dualUnificationVars, member])
      have slotSupport : VariablesSupportProvenance context outerStart start
          (.slot hole.capability hole.target : Ty).unificationVars := by
        simpa [dualVariables, Ty.unificationVars] using holeSupport
      have headSupport := head.supportProvenance expressionIncreases
        expressionSupport slotSupport outerToStart
      have startToAfter := head.supply_le_next expressionIncreases
      have tailHolesAtStart : VariablesSupportProvenance context outerStart start
          (dualUnificationVars holes) := by
        intro candidate member
        exact holesSupport candidate (by
          simp only [dualUnificationVars, List.flatMap_cons, List.mem_append]
          exact Or.inr member)
      have tailSupport := induction
        (tailHolesAtStart.extend_finish startToAfter)
        (Supply.le_trans outerToStart startToAfter)
      have headFinal := headSupport.extend_finish
        (tail.supply_le_next expressionIncreases)
      intro candidate member
      have headHardSupport : VariablesSupportProvenance context outerStart finish
          (TypePM.unificationVars generatedItem.hard) := by
        intro item itemMember
        exact headFinal item (by
          simp [GeneratedChecks.unificationVars, itemMember])
      have tailHardSupport : VariablesSupportProvenance context outerStart finish
          (TypePM.unificationVars generatedItems.hard) := by
        intro item itemMember
        exact tailSupport item (by
          simp [GeneratedChecks.unificationVars, itemMember])
      have headPendingSupport : VariablesSupportProvenance context outerStart finish
          (pendingUnificationVars generatedItem.pending) := by
        intro item itemMember
        exact headFinal item (by
          simp [GeneratedChecks.unificationVars, itemMember])
      have tailPendingSupport : VariablesSupportProvenance context outerStart finish
          (pendingUnificationVars generatedItems.pending) := by
        intro item itemMember
        exact tailSupport item (by
          simp [GeneratedChecks.unificationVars, itemMember])
      exact ((headHardSupport.append tailHardSupport).append
        (headPendingSupport.append tailPendingSupport)) candidate (by
          simpa [GeneratedChecks.unificationVars, GeneratedChecks.append,
            unificationVars_append, pendingUnificationVars_append]
            using member)

/-- Support for the zero/one/many next-matcher convention. -/
theorem NextMatchersElaborateUsing.supportProvenance
    {expressionRelation : ExpressionElaborationRelation}
    (expressionIncreases : ∀ {context expression start generated finish},
      expressionRelation context expression start generated finish →
        start.Le finish)
    (expressionSupport : ∀ {context expression start generated finish},
      expressionRelation context expression start generated finish →
        GeneratedSupportProvenance context start finish generated)
    {expression holes start generated finish}
    (holesSupport : VariablesSupportProvenance context outerStart start
      (dualUnificationVars holes))
    (outerToStart : outerStart.Le start)
    (derivation : NextMatchersElaborateUsing expressionRelation context expression
      holes start generated finish) :
    GeneratedChecksSupportProvenance context outerStart finish generated := by
  cases derivation with
  | zero checked =>
      exact checked.supportProvenance expressionIncreases expressionSupport (by
        intro candidate member
        simp [Ty.unificationVars, Ty.unificationVarsList] at member) outerToStart
  | @one expression hole start generated finish checked =>
      have holeSupport : VariablesSupportProvenance context outerStart start
          (dualVariables hole) := by
        simpa [dualUnificationVars] using holesSupport
      exact checked.supportProvenance expressionIncreases expressionSupport (by
        simpa [dualVariables, Ty.unificationVars] using holeSupport) outerToStart
  | many components =>
      exact components.supportProvenance expressionIncreases expressionSupport
        holesSupport outerToStart

/-- Adding local context entries preserves every variable already present in
the suffix context. -/
theorem Context.mem_unificationVars_append_left
    (added context : Context) {candidate : UnificationVar}
    (member : candidate ∈ context.unificationVars) :
    candidate ∈ (added ++ context).unificationVars := by
  cases candidate with
  | ty index =>
      simp only [Context.unificationVars, List.mem_append, List.mem_map]
        at member ⊢
      rcases member with tyMember | capMember
      · obtain ⟨candidateIndex, candidateMember, equality⟩ := tyMember
        cases equality
        left
        refine ⟨index, ?_, rfl⟩
        rw [Context.freeTyVars, mem_dedupFirst, List.mem_flatMap]
          at candidateMember ⊢
        obtain ⟨scheme, schemeMember, freeMember⟩ := candidateMember
        exact ⟨scheme, List.mem_append_right added schemeMember, freeMember⟩
      · obtain ⟨candidateIndex, candidateMember, equality⟩ := capMember
        cases equality
  | cap index =>
      simp only [Context.unificationVars, List.mem_append, List.mem_map]
        at member ⊢
      rcases member with tyMember | capMember
      · obtain ⟨candidateIndex, candidateMember, equality⟩ := tyMember
        cases equality
      · obtain ⟨candidateIndex, candidateMember, equality⟩ := capMember
        cases equality
        right
        refine ⟨index, ?_, rfl⟩
        rw [Context.freeCapVars, mem_dedupFirst, List.mem_flatMap]
          at candidateMember ⊢
        obtain ⟨scheme, schemeMember, freeMember⟩ := candidateMember
        exact ⟨scheme, List.mem_append_right added schemeMember, freeMember⟩

/-- Reinterpret supported variables after prepending pattern bindings to the
context. -/
theorem VariablesSupportProvenance.extend_context
    {context : Context} {start finish : Supply} {variables}
    (bindings : List Ty)
    (support : VariablesSupportProvenance context start finish variables) :
    VariablesSupportProvenance (Pattern.extendContext bindings context)
      start finish variables := by
  intro candidate member
  rcases support candidate member with outer | fresh
  · exact Or.inl (Context.mem_unificationVars_append_left
      (bindings.map Scheme.mono) context outer)
  · exact Or.inr fresh

/-- Rebase arbitrary variable support from a child context to an outer
context whose variables have already been accounted for. -/
theorem VariablesSupportProvenance.rebase_context
    {outerContext childContext : Context} {outerStart childStart finish : Supply}
    {variables}
    (outerToChild : outerStart.Le childStart)
    (childIncreases : childStart.Le finish)
    (contextSupport : VariablesSupportProvenance outerContext outerStart
      childStart childContext.unificationVars)
    (childSupport : VariablesSupportProvenance childContext childStart finish
      variables) :
    VariablesSupportProvenance outerContext outerStart finish variables := by
  intro candidate member
  rcases childSupport candidate member with childContextMember | fresh
  · rcases contextSupport candidate childContextMember with outer | allocated
    · exact Or.inl outer
    · exact Or.inr (allocated.extend_finish childIncreases)
  · exact Or.inr (fresh.lower_start outerToChild)

/-- Rebase child support that already uses the outer starting supply. -/
theorem VariablesSupportProvenance.rebase_context_wide
    {outerContext childContext : Context} {outerStart childStart finish : Supply}
    {variables}
    (childIncreases : childStart.Le finish)
    (contextSupport : VariablesSupportProvenance outerContext outerStart
      childStart childContext.unificationVars)
    (childSupport : VariablesSupportProvenance childContext outerStart finish
      variables) :
    VariablesSupportProvenance outerContext outerStart finish variables := by
  intro candidate member
  rcases childSupport candidate member with childContextMember | fresh
  · rcases contextSupport candidate childContextMember with outer | allocated
    · exact Or.inl outer
    · exact Or.inr (allocated.extend_finish childIncreases)
  · exact Or.inr fresh

/-- Support of the canonical decomposition product formed from matcher
holes. -/
theorem dualTargets_variables
    {duals : List Dual} {candidate : UnificationVar}
    (member : candidate ∈ Ty.unificationVarsList (Dual.targets duals)) :
    candidate ∈ dualUnificationVars duals := by
  induction duals with
  | nil => simp [Dual.targets, Ty.unificationVarsList] at member
  | cons head tail induction =>
      have origin : candidate ∈ head.target.unificationVars ∨
          candidate ∈ Ty.unificationVarsList (Dual.targets tail) := by
        simpa [Dual.targets, Ty.unificationVarsList] using member
      rcases origin with headMember | tailMember
      · apply List.mem_append_left
        simpa [dualVariables] using
          (Or.inr headMember : candidate ∈ head.capability.unificationVars ∨
            candidate ∈ head.target.unificationVars)
      · exact List.mem_append_right _ (induction tailMember)

theorem holeProductTarget_support
    {holes : List Dual}
    (support : VariablesSupportProvenance context start finish
      (dualUnificationVars holes)) :
    VariablesSupportProvenance context start finish
      (holeProductTarget holes).unificationVars := by
  cases holes with
  | nil =>
      intro candidate member
      simp [holeProductTarget, Ty.unificationVars,
        Ty.unificationVarsList] at member
  | cons first rest =>
      cases rest with
      | nil =>
          intro candidate member
          exact support candidate (by
            simp only [dualUnificationVars, List.flatMap_cons, List.flatMap_nil,
              List.append_nil, dualVariables, List.mem_append]
            exact Or.inr member)
      | cons second rest =>
          intro candidate member
          simp only [holeProductTarget, Ty.unificationVars] at member
          exact support candidate (dualTargets_variables member)

/-- Assemble support for the checking block added around an already
supported synthesized expression. -/
theorem GeneratedChecks.checked_support
    {generated : Generated} {expected : Ty}
    (generatedSupport : GeneratedSupportProvenance context start finish generated)
    (expectedSupport : VariablesSupportProvenance context start finish
      expected.unificationVars) :
    GeneratedChecksSupportProvenance context start finish
      (GeneratedChecks.checked generated expected) := by
  intro candidate member
  simp only [GeneratedChecks.unificationVars, GeneratedChecks.checked,
    pendingUnificationVars_append, pendingUnificationVars,
    CheckObligation.unificationVars, List.mem_append] at member
  rcases member with hardMember | pendingMember | obligationMember | impossible
  · exact generatedSupport candidate (by
      simp [Generated.unificationVars, hardMember])
  · exact generatedSupport candidate (by
      simp [Generated.unificationVars, pendingMember])
  · rcases obligationMember with sourceMember | expectedMember
    · exact generatedSupport candidate (by
        simp [Generated.unificationVars, sourceMember])
    · exact expectedSupport candidate expectedMember
  · simp at impossible

/-- Support composes across concatenated checking blocks. -/
theorem GeneratedChecks.append_support
    {left right : GeneratedChecks}
    (leftSupport : GeneratedChecksSupportProvenance context start finish left)
    (rightSupport : GeneratedChecksSupportProvenance context start finish right) :
    GeneratedChecksSupportProvenance context start finish (left.append right) := by
  intro candidate member
  have leftHard : VariablesSupportProvenance context start finish
      (TypePM.unificationVars left.hard) := by
    intro item itemMember
    exact leftSupport item (by
      simp [GeneratedChecks.unificationVars, itemMember])
  have rightHard : VariablesSupportProvenance context start finish
      (TypePM.unificationVars right.hard) := by
    intro item itemMember
    exact rightSupport item (by
      simp [GeneratedChecks.unificationVars, itemMember])
  have leftPending : VariablesSupportProvenance context start finish
      (pendingUnificationVars left.pending) := by
    intro item itemMember
    exact leftSupport item (by
      simp [GeneratedChecks.unificationVars, itemMember])
  have rightPending : VariablesSupportProvenance context start finish
      (pendingUnificationVars right.pending) := by
    intro item itemMember
    exact rightSupport item (by
      simp [GeneratedChecks.unificationVars, itemMember])
  exact ((leftHard.append rightHard).append
    (leftPending.append rightPending)) candidate (by
      simpa [GeneratedChecks.unificationVars, GeneratedChecks.append,
        unificationVars_append, pendingUnificationVars_append] using member)

/-- Support of one matcher decomposition arm. -/
theorem MatcherArmElaboratesUsing.supportProvenance
    {expressionRelation : ExpressionElaborationRelation}
    {dpatRelation : DPatElaborationRelation}
    (wellFormed : signature.WellFormed)
    (expressionIncreases : ∀ {context expression start generated finish},
      expressionRelation context expression start generated finish →
        start.Le finish)
    (expressionSupport : ∀ {context expression start generated finish},
      expressionRelation context expression start generated finish →
        GeneratedSupportProvenance context start finish generated)
    (dpatIncreases : ∀ {signature pattern expected start generated finish},
      dpatRelation signature pattern expected start generated finish →
        start.Le finish)
    (dpatSupport : ∀ {signature pattern expected start generated finish}
        {context outerStart},
      signature.WellFormed →
      VariablesSupportProvenance context outerStart start
        expected.unificationVars →
      outerStart.Le start →
      dpatRelation signature pattern expected start generated finish →
      GeneratedDPatSupportProvenance context outerStart finish generated)
    {captures matcherTarget holes arm start generated finish}
    (capturesSupport : VariablesSupportProvenance context outerStart start
      (Ty.unificationVarsList captures))
    (targetSupport : VariablesSupportProvenance context outerStart start
      matcherTarget.unificationVars)
    (holesSupport : VariablesSupportProvenance context outerStart start
      (dualUnificationVars holes))
    (outerToStart : outerStart.Le start)
    (derivation : MatcherArmElaboratesUsing expressionRelation dpatRelation
      signature context captures matcherTarget holes arm start generated finish) :
    GeneratedChecksSupportProvenance context outerStart finish generated := by
  cases derivation with
  | @mk header body start generatedHeader afterHeader generatedBody finish
      headerElaboration bodyElaboration =>
      have headerSupport := dpatSupport wellFormed targetSupport outerToStart
        headerElaboration
      have startToHeader := dpatIncreases headerElaboration
      have headerToFinish := bodyElaboration.supply_le_next expressionIncreases
      have bindingsSupport : VariablesSupportProvenance context outerStart
          afterHeader (Ty.unificationVarsList generatedHeader.bindings) := by
        intro candidate member
        exact headerSupport candidate (by
          simp [GeneratedDPat.unificationVars, member])
      have capturesContextSupport := Pattern.extendContext_support capturesSupport
      have capturesContextFinal :=
        capturesContextSupport.extend_finish startToHeader
      have bindingsInCapturedContext :=
        VariablesSupportProvenance.extend_context captures bindingsSupport
      have localBodyContextSupport :=
        Pattern.extendContext_support bindingsInCapturedContext
      have bodyContextSupport : VariablesSupportProvenance context outerStart
          afterHeader
          (Pattern.extendContext generatedHeader.bindings
            (Pattern.extendContext captures context)).unificationVars := by
        intro candidate member
        rcases localBodyContextSupport candidate member with captured | fresh
        · exact capturesContextFinal candidate captured
        · exact Or.inr fresh
      cases bodyElaboration with
      | @mk inferred _ expressionElaboration =>
          have expressionGeneratedSupport := expressionSupport expressionElaboration
          have expressionIncrease := expressionIncreases expressionElaboration
          have rebasedExpression := expressionGeneratedSupport.rebase_context
            (Supply.le_trans outerToStart startToHeader) expressionIncrease
            bodyContextSupport
          have holesAtHeader := holesSupport.extend_finish startToHeader
          have productSupport := holeProductTarget_support holesAtHeader
          have expectedSupport : VariablesSupportProvenance context outerStart
              afterHeader
              (DataTypes.list (holeProductTarget holes)).unificationVars := by
            simpa [DataTypes.list, Ty.unificationVars,
              Ty.unificationVarsList] using productSupport
          have expectedFinal := expectedSupport.extend_finish expressionIncrease
          have bodyChecks := GeneratedChecks.checked_support rebasedExpression
            expectedFinal
          have headerHard : VariablesSupportProvenance context outerStart finish
              (TypePM.unificationVars generatedHeader.hard) := by
            intro candidate member
            exact (headerSupport.extend_finish headerToFinish) candidate (by
              simp [GeneratedDPat.unificationVars, member])
          have bodyHard : VariablesSupportProvenance context outerStart finish
              (TypePM.unificationVars
                (GeneratedChecks.checked inferred
                  (DataTypes.list (holeProductTarget holes))).hard) := by
            intro candidate member
            exact bodyChecks candidate (by
              simp [GeneratedChecks.unificationVars, member])
          have bodyPending : VariablesSupportProvenance context outerStart finish
              (pendingUnificationVars
                (GeneratedChecks.checked inferred
                  (DataTypes.list (holeProductTarget holes))).pending) := by
            intro candidate member
            exact bodyChecks candidate (by
              simp [GeneratedChecks.unificationVars, member])
          intro candidate member
          exact ((headerHard.append bodyHard).append bodyPending) candidate (by
            simpa [GeneratedChecks.unificationVars, unificationVars_append]
              using member)

/-- Support of matcher decomposition arms elaborated in source order. -/
theorem MatcherArmsElaborateUsing.supportProvenance
    {expressionRelation : ExpressionElaborationRelation}
    {dpatRelation : DPatElaborationRelation}
    (wellFormed : signature.WellFormed)
    (expressionIncreases : ∀ {context expression start generated finish},
      expressionRelation context expression start generated finish →
        start.Le finish)
    (expressionSupport : ∀ {context expression start generated finish},
      expressionRelation context expression start generated finish →
        GeneratedSupportProvenance context start finish generated)
    (dpatIncreases : ∀ {signature pattern expected start generated finish},
      dpatRelation signature pattern expected start generated finish →
        start.Le finish)
    (dpatSupport : ∀ {signature pattern expected start generated finish}
        {context outerStart},
      signature.WellFormed →
      VariablesSupportProvenance context outerStart start
        expected.unificationVars →
      outerStart.Le start →
      dpatRelation signature pattern expected start generated finish →
      GeneratedDPatSupportProvenance context outerStart finish generated)
    {captures matcherTarget holes arms start generated finish}
    (capturesSupport : VariablesSupportProvenance context outerStart start
      (Ty.unificationVarsList captures))
    (targetSupport : VariablesSupportProvenance context outerStart start
      matcherTarget.unificationVars)
    (holesSupport : VariablesSupportProvenance context outerStart start
      (dualUnificationVars holes))
    (outerToStart : outerStart.Le start)
    (derivation : MatcherArmsElaborateUsing expressionRelation dpatRelation
      signature context captures matcherTarget holes arms start generated finish) :
    GeneratedChecksSupportProvenance context outerStart finish
      generated.checks := by
  induction derivation with
  | nil =>
      intro candidate member
      simp [GeneratedChecks.unificationVars, GeneratedChecks.empty,
        TypePM.unificationVars, pendingUnificationVars] at member
  | @cons arm arms start generatedArm afterArm generatedArms finish head tail
      induction =>
      have headSupport := head.supportProvenance wellFormed expressionIncreases
        expressionSupport dpatIncreases dpatSupport capturesSupport targetSupport
        holesSupport outerToStart
      have startToAfter := head.supply_le_next expressionIncreases dpatIncreases
      have tailSupport := induction
        (capturesSupport.extend_finish startToAfter)
        (targetSupport.extend_finish startToAfter)
        (holesSupport.extend_finish startToAfter)
        (Supply.le_trans outerToStart startToAfter)
      exact GeneratedChecks.append_support
        (headSupport.extend_finish
          (tail.supply_le_next expressionIncreases dpatIncreases))
        tailSupport

namespace GeneratedMatcherClause

def unificationVars (generated : GeneratedMatcherClause) : List UnificationVar :=
  dualUnificationVars generated.holes ++
    (match generated.evidence with
     | none => []
     | some evidence => evidence.unificationVars) ++
    generated.checks.unificationVars

end GeneratedMatcherClause

namespace GeneratedMatcherClauses

def unificationVars (generated : GeneratedMatcherClauses) : List UnificationVar :=
  Cap.unificationVarsList generated.evidences ++
    generated.checks.unificationVars

end GeneratedMatcherClauses

abbrev GeneratedMatcherClauseSupportProvenance
    (context : Context) (start finish : Supply)
    (generated : GeneratedMatcherClause) :=
  VariablesSupportProvenance context start finish generated.unificationVars

abbrev GeneratedMatcherClausesSupportProvenance
    (context : Context) (start finish : Supply)
    (generated : GeneratedMatcherClauses) :=
  VariablesSupportProvenance context start finish generated.unificationVars

/-- Support of one complete matcher clause. -/
theorem MatcherClauseElaboratesUsing.supportProvenance
    {expressionRelation : ExpressionElaborationRelation}
    {ppatRelation : PPatElaborationRelation}
    {dpatRelation : DPatElaborationRelation}
    (wellFormed : signature.WellFormed)
    (expressionIncreases : ∀ {context expression start generated finish},
      expressionRelation context expression start generated finish →
        start.Le finish)
    (expressionSupport : ∀ {context expression start generated finish},
      expressionRelation context expression start generated finish →
        GeneratedSupportProvenance context start finish generated)
    (ppatIncreases : ∀ {signature pattern target capability start generated finish},
      ppatRelation signature pattern target capability start generated finish →
        start.Le finish)
    (ppatSupport : ∀ {signature pattern target capability start generated finish}
        {context outerStart},
      signature.WellFormed →
      VariablesSupportProvenance context outerStart start target.unificationVars →
      VariablesSupportProvenance context outerStart start
        (match capability with
         | none => []
         | some expected => expected.unificationVars) →
      outerStart.Le start →
      ppatRelation signature pattern target capability start generated finish →
      GeneratedPPatSupportProvenance context outerStart finish generated)
    (dpatIncreases : ∀ {signature pattern expected start generated finish},
      dpatRelation signature pattern expected start generated finish →
        start.Le finish)
    (dpatSupport : ∀ {signature pattern expected start generated finish}
        {context outerStart},
      signature.WellFormed →
      VariablesSupportProvenance context outerStart start
        expected.unificationVars →
      outerStart.Le start →
      dpatRelation signature pattern expected start generated finish →
      GeneratedDPatSupportProvenance context outerStart finish generated)
    {matcherTarget clause start generated finish}
    (targetSupport : VariablesSupportProvenance context outerStart start
      matcherTarget.unificationVars)
    (outerToStart : outerStart.Le start)
    (derivation : MatcherClauseElaboratesUsing expressionRelation ppatRelation
      dpatRelation signature context matcherTarget clause start generated finish) :
    GeneratedMatcherClauseSupportProvenance context outerStart finish generated := by
  cases derivation with
  | @mk header nextMatchers arms start generatedHeader afterHeader generatedNext
      afterNext generatedArms finish shape headerElaboration nextElaboration
      armsElaboration =>
      have emptyCapability : VariablesSupportProvenance context outerStart start
          ([] : List UnificationVar) := by
        intro candidate member
        simp at member
      have headerSupport := ppatSupport (capability := none) wellFormed
        targetSupport emptyCapability outerToStart headerElaboration
      have startToHeader := ppatIncreases headerElaboration
      have headerToNext := nextElaboration.supply_le_next expressionIncreases
      have nextToFinish := armsElaboration.supply_le_next expressionIncreases
        dpatIncreases
      have holesSupport : VariablesSupportProvenance context outerStart afterHeader
          (dualUnificationVars generatedHeader.holes) := by
        intro candidate member
        exact headerSupport candidate (by
          simp [GeneratedPPat.unificationVars, member])
      have capturesSupport : VariablesSupportProvenance context outerStart afterHeader
          (Ty.unificationVarsList generatedHeader.captures) := by
        intro candidate member
        exact headerSupport candidate (by
          simp [GeneratedPPat.unificationVars, member])
      have capturedContextSupport := Pattern.extendContext_support capturesSupport
      have holesInCapturedContext :=
        VariablesSupportProvenance.extend_context generatedHeader.captures
          holesSupport
      have nextSupportInCaptured := nextElaboration.supportProvenance
        expressionIncreases expressionSupport holesInCapturedContext
        (Supply.le_trans outerToStart startToHeader)
      have nextSupport := VariablesSupportProvenance.rebase_context_wide
        headerToNext capturedContextSupport nextSupportInCaptured
      have armsSupport := armsElaboration.supportProvenance wellFormed
        expressionIncreases expressionSupport dpatIncreases dpatSupport
        (capturesSupport.extend_finish headerToNext)
        (targetSupport.extend_finish
          (Supply.le_trans startToHeader headerToNext))
        (holesSupport.extend_finish headerToNext)
        (Supply.le_trans outerToStart
          (Supply.le_trans startToHeader headerToNext))
      have headerFinal := headerSupport.extend_finish
        (Supply.le_trans headerToNext nextToFinish)
      have nextFinal := nextSupport.extend_finish nextToFinish
      have holesFinal : VariablesSupportProvenance context outerStart finish
          (dualUnificationVars generatedHeader.holes) := by
        intro candidate member
        exact headerFinal candidate (by
          simp [GeneratedPPat.unificationVars, member])
      have evidenceFinal : VariablesSupportProvenance context outerStart finish
          (match generatedHeader.evidence with
           | none => []
           | some evidence => evidence.unificationVars) := by
        intro candidate member
        exact headerFinal candidate (by
          simp [GeneratedPPat.unificationVars, member])
      have headerHard : VariablesSupportProvenance context outerStart finish
          (TypePM.unificationVars generatedHeader.hard) := by
        intro candidate member
        exact headerFinal candidate (by
          simp [GeneratedPPat.unificationVars, member])
      have nextHard : VariablesSupportProvenance context outerStart finish
          (TypePM.unificationVars generatedNext.hard) := by
        intro candidate member
        exact nextFinal candidate (by
          simp [GeneratedChecks.unificationVars, member])
      have armsHard : VariablesSupportProvenance context outerStart finish
          (TypePM.unificationVars generatedArms.checks.hard) := by
        intro candidate member
        exact armsSupport candidate (by
          simp [GeneratedChecks.unificationVars, member])
      have nextPending : VariablesSupportProvenance context outerStart finish
          (pendingUnificationVars generatedNext.pending) := by
        intro candidate member
        exact nextFinal candidate (by
          simp [GeneratedChecks.unificationVars, member])
      have armsPending : VariablesSupportProvenance context outerStart finish
          (pendingUnificationVars generatedArms.checks.pending) := by
        intro candidate member
        exact armsSupport candidate (by
          simp [GeneratedChecks.unificationVars, member])
      intro candidate member
      exact ((holesFinal.append evidenceFinal).append
        (((headerHard.append nextHard).append armsHard).append
          (nextPending.append armsPending))) candidate (by
            simpa [GeneratedMatcherClause.unificationVars,
              GeneratedChecks.unificationVars, unificationVars_append,
              pendingUnificationVars_append, List.append_assoc] using member)

/-- Support of matcher clauses elaborated at one shared target. -/
theorem MatcherClausesElaborateUsing.supportProvenance
    {expressionRelation : ExpressionElaborationRelation}
    {ppatRelation : PPatElaborationRelation}
    {dpatRelation : DPatElaborationRelation}
    (wellFormed : signature.WellFormed)
    (expressionIncreases : ∀ {context expression start generated finish},
      expressionRelation context expression start generated finish →
        start.Le finish)
    (expressionSupport : ∀ {context expression start generated finish},
      expressionRelation context expression start generated finish →
        GeneratedSupportProvenance context start finish generated)
    (ppatIncreases : ∀ {signature pattern target capability start generated finish},
      ppatRelation signature pattern target capability start generated finish →
        start.Le finish)
    (ppatSupport : ∀ {signature pattern target capability start generated finish}
        {context outerStart},
      signature.WellFormed →
      VariablesSupportProvenance context outerStart start target.unificationVars →
      VariablesSupportProvenance context outerStart start
        (match capability with
         | none => []
         | some expected => expected.unificationVars) →
      outerStart.Le start →
      ppatRelation signature pattern target capability start generated finish →
      GeneratedPPatSupportProvenance context outerStart finish generated)
    (dpatIncreases : ∀ {signature pattern expected start generated finish},
      dpatRelation signature pattern expected start generated finish →
        start.Le finish)
    (dpatSupport : ∀ {signature pattern expected start generated finish}
        {context outerStart},
      signature.WellFormed →
      VariablesSupportProvenance context outerStart start
        expected.unificationVars →
      outerStart.Le start →
      dpatRelation signature pattern expected start generated finish →
      GeneratedDPatSupportProvenance context outerStart finish generated)
    {matcherTarget clauses start generated finish}
    (targetSupport : VariablesSupportProvenance context outerStart start
      matcherTarget.unificationVars)
    (outerToStart : outerStart.Le start)
    (derivation : MatcherClausesElaborateUsing expressionRelation ppatRelation
      dpatRelation signature context matcherTarget clauses start generated finish) :
    GeneratedMatcherClausesSupportProvenance context outerStart finish generated := by
  induction derivation with
  | nil =>
      intro candidate member
      simp [GeneratedMatcherClauses.unificationVars,
        GeneratedChecks.unificationVars, GeneratedChecks.empty,
        Cap.unificationVarsList, TypePM.unificationVars,
        pendingUnificationVars] at member
  | @cons clause clauses start generatedClause afterClause generatedClauses finish
      head tail induction =>
      have headSupport := head.supportProvenance wellFormed expressionIncreases
        expressionSupport ppatIncreases ppatSupport dpatIncreases dpatSupport
        targetSupport outerToStart
      have startToAfter := head.supply_le_next expressionIncreases ppatIncreases
        dpatIncreases
      have tailSupport := induction
        (targetSupport.extend_finish startToAfter)
        (Supply.le_trans outerToStart startToAfter)
      have headFinal := headSupport.extend_finish
        (tail.supply_le_next expressionIncreases ppatIncreases dpatIncreases)
      have headEvidence : VariablesSupportProvenance context outerStart finish
          (match generatedClause.evidence with
           | none => []
           | some evidence => evidence.unificationVars) := by
        intro candidate member
        exact headFinal candidate (by
          simp [GeneratedMatcherClause.unificationVars, member])
      have tailEvidence : VariablesSupportProvenance context outerStart finish
          (Cap.unificationVarsList generatedClauses.evidences) := by
        intro candidate member
        exact tailSupport candidate (by
          simp [GeneratedMatcherClauses.unificationVars, member])
      have evidenceSupport : VariablesSupportProvenance context outerStart finish
          (Cap.unificationVarsList
            (match generatedClause.evidence with
             | some evidence => evidence :: generatedClauses.evidences
             | none => generatedClauses.evidences)) := by
        cases evidenceCase : generatedClause.evidence with
        | none =>
            simpa [evidenceCase, Cap.unificationVarsList] using tailEvidence
        | some evidence =>
            have evidenceHead : VariablesSupportProvenance context outerStart finish
                evidence.unificationVars := by
              simpa [evidenceCase] using headEvidence
            simpa [evidenceCase, Cap.unificationVarsList] using
              evidenceHead.append tailEvidence
      have headChecks : GeneratedChecksSupportProvenance context outerStart finish
          generatedClause.checks := by
        intro candidate member
        exact headFinal candidate (by
          simp [GeneratedMatcherClause.unificationVars, member])
      have tailChecks : GeneratedChecksSupportProvenance context outerStart finish
          generatedClauses.checks := by
        intro candidate member
        exact tailSupport candidate (by
          simp [GeneratedMatcherClauses.unificationVars, member])
      exact evidenceSupport.append
        (GeneratedChecks.append_support headChecks tailChecks)

/-- Every variable in the capability equations for a nonempty evidence list
comes from either the shared producer or one of the evidence capabilities. -/
private theorem evidenceMap_support
    {context : Context} {start finish : Supply} {producer : Cap}
    (producerSupport : VariablesSupportProvenance context start finish
      producer.unificationVars)
    {evidences : List Cap}
    (evidenceSupport : VariablesSupportProvenance context start finish
      (Cap.unificationVarsList evidences)) :
    VariablesSupportProvenance context start finish
      (TypePM.unificationVars
        (evidences.map (fun evidence => .cap producer evidence))) := by
  induction evidences with
  | nil => exact VariablesSupportProvenance.nil context start finish
  | cons evidence evidences induction =>
      have headEvidence : VariablesSupportProvenance context start finish
          evidence.unificationVars := by
        intro candidate member
        exact evidenceSupport candidate (by
          simp [Cap.unificationVarsList, member])
      have tailEvidence : VariablesSupportProvenance context start finish
          (Cap.unificationVarsList evidences) := by
        intro candidate member
        exact evidenceSupport candidate (by
          simp [Cap.unificationVarsList, member])
      have tailEquations := induction tailEvidence
      intro candidate member
      exact ((producerSupport.append headEvidence).append tailEquations)
        candidate (by
          simpa [TypePM.unificationVars, Equation.unificationVars] using member)

/-- The equations joining a matcher producer to clause evidence do not invent
variables.  With no evidence the equation uses the closed capability `any`. -/
theorem evidenceEquations_support
    {context : Context} {start finish : Supply} {producer : Cap}
    (producerSupport : VariablesSupportProvenance context start finish
      producer.unificationVars)
    {evidences : List Cap}
    (evidenceSupport : VariablesSupportProvenance context start finish
      (Cap.unificationVarsList evidences)) :
    VariablesSupportProvenance context start finish
      (TypePM.unificationVars (evidenceEquations producer evidences)) := by
  cases evidences with
  | nil =>
      intro candidate member
      exact producerSupport candidate (by
        simpa [evidenceEquations, TypePM.unificationVars,
          Equation.unificationVars, Cap.unificationVars] using member)
  | cons evidence evidences =>
      exact evidenceMap_support producerSupport evidenceSupport

/-- Support of a complete matcher literal.  Its result target and producer are
the two fresh variables allocated immediately before its clauses. -/
theorem MatcherLiteralElaboratesUsing.supportProvenance
    {expressionRelation : ExpressionElaborationRelation}
    {ppatRelation : PPatElaborationRelation}
    {dpatRelation : DPatElaborationRelation}
    (wellFormed : signature.WellFormed)
    (expressionIncreases : ∀ {context expression start generated finish},
      expressionRelation context expression start generated finish →
        start.Le finish)
    (expressionSupport : ∀ {context expression start generated finish},
      expressionRelation context expression start generated finish →
        GeneratedSupportProvenance context start finish generated)
    (ppatIncreases : ∀ {signature pattern target capability start generated finish},
      ppatRelation signature pattern target capability start generated finish →
        start.Le finish)
    (ppatSupport : ∀ {signature pattern target capability start generated finish}
        {context outerStart},
      signature.WellFormed →
      VariablesSupportProvenance context outerStart start
        target.unificationVars →
      VariablesSupportProvenance context outerStart start
        (match capability with
         | none => []
         | some expected => expected.unificationVars) →
      outerStart.Le start →
      ppatRelation signature pattern target capability start generated finish →
      GeneratedPPatSupportProvenance context outerStart finish generated)
    (dpatIncreases : ∀ {signature pattern expected start generated finish},
      dpatRelation signature pattern expected start generated finish →
        start.Le finish)
    (dpatSupport : ∀ {signature pattern expected start generated finish}
        {context outerStart},
      signature.WellFormed →
      VariablesSupportProvenance context outerStart start
        expected.unificationVars →
      outerStart.Le start →
      dpatRelation signature pattern expected start generated finish →
      GeneratedDPatSupportProvenance context outerStart finish generated)
    {clauses start generated finish}
    (derivation : MatcherLiteralElaboratesUsing expressionRelation ppatRelation
      dpatRelation signature context clauses start generated finish) :
    GeneratedSupportProvenance context start finish generated := by
  cases derivation with
  | @mk generatedClauses _ checked clausesElaboration =>
      let afterRoot : Supply := ⟨start.ty + 1, start.cap + 1⟩
      have startToRoot : start.Le afterRoot := by
        simp [afterRoot, Supply.Le]
      have rootToFinish := clausesElaboration.supply_le_next
        expressionIncreases ppatIncreases dpatIncreases
      have targetAtRoot : VariablesSupportProvenance context start afterRoot
          (Ty.unificationVars (.var ⟨start.ty⟩)) := by
        exact (freshTy_support context start).extend_finish (by
          simp [afterRoot, Supply.Le, Supply.nextTy])
      have producerAtRoot : VariablesSupportProvenance context start afterRoot
          (Cap.unificationVars (.var ⟨start.cap⟩)) := by
        exact (freshCap_support context start).extend_finish (by
          simp [afterRoot, Supply.Le])
      have clausesSupport := clausesElaboration.supportProvenance wellFormed
        expressionIncreases expressionSupport ppatIncreases ppatSupport
        dpatIncreases dpatSupport targetAtRoot startToRoot
      have targetFinal := targetAtRoot.extend_finish rootToFinish
      have producerFinal := producerAtRoot.extend_finish rootToFinish
      have evidencesSupport : VariablesSupportProvenance context start finish
          (Cap.unificationVarsList generatedClauses.evidences) := by
        intro candidate member
        exact clausesSupport candidate (by
          simp [GeneratedMatcherClauses.unificationVars, member])
      have checksSupport : GeneratedChecksSupportProvenance context start finish
          generatedClauses.checks := by
        intro candidate member
        exact clausesSupport candidate (by
          simp [GeneratedMatcherClauses.unificationVars, member])
      have equationsSupport := evidenceEquations_support producerFinal
        evidencesSupport
      have resultSupport : VariablesSupportProvenance context start finish
          (Ty.unificationVars
            (.matcher (.var ⟨start.cap⟩) (.var ⟨start.ty⟩))) := by
        simpa [Ty.unificationVars] using producerFinal.append targetFinal
      have checksHard : VariablesSupportProvenance context start finish
          (TypePM.unificationVars generatedClauses.checks.hard) := by
        intro candidate member
        exact checksSupport candidate (by
          simp [GeneratedChecks.unificationVars, member])
      have checksPending : VariablesSupportProvenance context start finish
          (pendingUnificationVars generatedClauses.checks.pending) := by
        intro candidate member
        exact checksSupport candidate (by
          simp [GeneratedChecks.unificationVars, member])
      intro candidate member
      exact ((resultSupport.append (equationsSupport.append checksHard)).append
        checksPending) candidate (by
          simpa [Generated.unificationVars, unificationVars_append,
            List.append_assoc] using member)

end MatcherTyping

abbrev GeneratedPatternSupportProvenance
    (context : Context) (start finish : Supply) (generated : GeneratedPattern) :=
  VariablesSupportProvenance context start finish generated.unificationVars

abbrev GeneratedPatternsSupportProvenance
    (context : Context) (start finish : Supply) (generated : GeneratedPatterns) :=
  VariablesSupportProvenance context start finish generated.unificationVars

/-- The two equalities joining conjunctive patterns use only variables from
the two input target/capability pairs. -/
theorem Pattern.dualEquations_support
    {context : Context} {start finish : Supply} {left right : Dual}
    (leftSupport : VariablesSupportProvenance context start finish
      (dualVariables left))
    (rightSupport : VariablesSupportProvenance context start finish
      (dualVariables right)) :
    VariablesSupportProvenance context start finish
      (TypePM.unificationVars (Pattern.dualEquations left right)) := by
  intro candidate member
  have origin :
      candidate ∈ left.target.unificationVars ∨
      candidate ∈ right.target.unificationVars ∨
      candidate ∈ left.capability.unificationVars ∨
      candidate ∈ right.capability.unificationVars := by
    simpa [Pattern.dualEquations, TypePM.unificationVars,
      Equation.unificationVars] using member
  rcases origin with leftTarget | rightTarget | leftCapability | rightCapability
  · exact leftSupport candidate (by simp [dualVariables, leftTarget])
  · exact rightSupport candidate (by simp [dualVariables, rightTarget])
  · exact leftSupport candidate (by simp [dualVariables, leftCapability])
  · exact rightSupport candidate (by simp [dualVariables, rightCapability])

/-- A target/capability pair selected from a pattern argument list inherits
the support of that list. -/
theorem dualSupport_of_getElem
    {context : Context} {start finish : Supply} {arguments : List Dual}
    (argumentsSupport : VariablesSupportProvenance context start finish
      (dualUnificationVars arguments))
    {index : Nat} {dual : Dual}
    (lookup : arguments[index]? = some dual) :
    VariablesSupportProvenance context start finish (dualVariables dual) := by
  intro candidate member
  apply argumentsSupport candidate
  rw [dualUnificationVars, List.mem_flatMap]
  have dualMember : dual ∈ arguments := by
    obtain ⟨bound, equality⟩ := List.getElem?_eq_some_iff.mp lookup
    rw [← equality]
    exact List.getElem_mem bound
  exact ⟨dual, dualMember, member⟩

/-- Packing a list of target/capability pairs into one product pair only
reorders their variables. -/
theorem tupleDual_support
    {context : Context} {start finish : Supply} {duals : List Dual}
    (support : VariablesSupportProvenance context start finish
      (dualUnificationVars duals)) :
    VariablesSupportProvenance context start finish
      (dualVariables
        (⟨.prod (Dual.capabilities duals),
          .prod (Dual.targets duals)⟩ : Dual)) := by
  induction duals with
  | nil =>
      intro candidate member
      simp [dualVariables, Dual.capabilities, Dual.targets,
        Cap.unificationVars, Ty.unificationVars, Cap.unificationVarsList,
        Ty.unificationVarsList] at member
  | cons dual duals induction =>
      have headSupport : VariablesSupportProvenance context start finish
          (dualVariables dual) := by
        intro candidate member
        exact support candidate (by
          simp only [dualUnificationVars, List.flatMap_cons, List.mem_append]
          exact Or.inl member)
      have tailSupport : VariablesSupportProvenance context start finish
          (dualUnificationVars duals) := by
        intro candidate member
        exact support candidate (by
          simp only [dualUnificationVars, List.flatMap_cons, List.mem_append]
          exact Or.inr member)
      have packedTail := induction tailSupport
      intro candidate member
      have origin :
          candidate ∈ dual.capability.unificationVars ∨
          candidate ∈ Cap.unificationVarsList (Dual.capabilities duals) ∨
          candidate ∈ dual.target.unificationVars ∨
          candidate ∈ Ty.unificationVarsList (Dual.targets duals) := by
        simpa [dualVariables, Dual.capabilities, Dual.targets,
          Cap.unificationVars, Ty.unificationVars, Cap.unificationVarsList,
          Ty.unificationVarsList] using member
      rcases origin with headCapability | tailCapability | headTarget | tailTarget
      · exact headSupport candidate (by simp [dualVariables, headCapability])
      · exact packedTail candidate (by
          simp [dualVariables, Cap.unificationVars, Ty.unificationVars,
            tailCapability])
      · exact headSupport candidate (by simp [dualVariables, headTarget])
      · exact packedTail candidate (by
          simp [dualVariables, Cap.unificationVars, Ty.unificationVars,
            tailTarget])

mutual

/-- User-pattern synthesis preserves generated-variable provenance.  The
argument and binding hypotheses account for types supplied by the enclosing
match site before this pattern begins. -/
theorem PatternElaboratesUsing.supportProvenance
    {ExpressionElaborates : M4ExpressionElaborationRelation}
    (wellFormed : signature.WellFormed)
    (expressionIncreases : ∀ {context expression start generated finish},
      ExpressionElaborates context expression start generated finish →
        start.Le finish)
    (expressionSupport : ∀ {context expression start generated finish},
      ExpressionElaborates context expression start generated finish →
        GeneratedSupportProvenance context start finish generated)
    {context outerStart arguments pattern bindings start generated finish}
    (argumentsSupport : VariablesSupportProvenance context outerStart start
      (dualUnificationVars arguments))
    (bindingsSupport : VariablesSupportProvenance context outerStart start
      (Ty.unificationVarsList bindings))
    (outerToStart : outerStart.Le start)
    (derivation : PatternElaboratesUsing ExpressionElaborates signature context
      arguments pattern bindings start generated finish) :
    GeneratedPatternSupportProvenance context outerStart finish generated := by
  cases derivation with
  | var =>
      have startToFinish : start.Le ⟨start.ty + 1, start.cap + 1⟩ := by
        simp [Supply.Le]
      have targetLocal : VariablesSupportProvenance context start
          ⟨start.ty + 1, start.cap + 1⟩
          (Ty.unificationVars (.var ⟨start.ty⟩)) :=
        (freshTy_support context start).extend_finish (by
          simp [Supply.Le, Supply.nextTy])
      have capabilityLocal : VariablesSupportProvenance context start
          ⟨start.ty + 1, start.cap + 1⟩
          (Cap.unificationVars (.var ⟨start.cap⟩)) :=
        (freshCap_support context start).extend_finish (by simp [Supply.Le])
      have targetSupport := VariablesSupportProvenance.lower_start outerToStart
        targetLocal
      have capabilitySupport := VariablesSupportProvenance.lower_start
        outerToStart capabilityLocal
      have dualSupport := capabilitySupport.append targetSupport
      have bindingsFinal := bindingsSupport.extend_finish startToFinish
      have outputBindings := bindingsFinal.append targetSupport
      intro candidate member
      exact (dualSupport.append outputBindings) candidate (by
        simpa [GeneratedPattern.unificationVars, dualVariables,
          Ty.unificationVarsList, Ty.unificationVarsList_append,
          TypePM.unificationVars,
          pendingUnificationVars] using member)
  | wild =>
      have startToFinish : start.Le ⟨start.ty + 1, start.cap + 1⟩ := by
        simp [Supply.Le]
      have targetLocal : VariablesSupportProvenance context start
          ⟨start.ty + 1, start.cap + 1⟩
          (Ty.unificationVars (.var ⟨start.ty⟩)) :=
        (freshTy_support context start).extend_finish (by
          simp [Supply.Le, Supply.nextTy])
      have capabilityLocal : VariablesSupportProvenance context start
          ⟨start.ty + 1, start.cap + 1⟩
          (Cap.unificationVars (.var ⟨start.cap⟩)) :=
        (freshCap_support context start).extend_finish (by simp [Supply.Le])
      have targetSupport := VariablesSupportProvenance.lower_start outerToStart
        targetLocal
      have capabilitySupport := VariablesSupportProvenance.lower_start
        outerToStart capabilityLocal
      have bindingsFinal := bindingsSupport.extend_finish startToFinish
      intro candidate member
      exact ((capabilitySupport.append targetSupport).append bindingsFinal)
        candidate (by
          simpa [GeneratedPattern.unificationVars, dualVariables,
            TypePM.unificationVars, pendingUnificationVars] using member)
  | @value expression bindings start inferred afterExpression
      expressionDerivation =>
      have expressionIncrease := expressionIncreases expressionDerivation
      have localContextSupport := Pattern.extendContext_support bindingsSupport
      have expressionWide := (expressionSupport expressionDerivation).rebase_context
        outerToStart expressionIncrease localContextSupport
      have afterToFinish : afterExpression.Le
          ⟨afterExpression.ty, afterExpression.cap + 1⟩ := by
        simp [Supply.Le]
      have outerToAfter := Supply.le_trans outerToStart expressionIncrease
      have capabilityWide : VariablesSupportProvenance context outerStart
          ⟨afterExpression.ty, afterExpression.cap + 1⟩
          (Cap.unificationVars (.var ⟨afterExpression.cap⟩)) := by
        exact VariablesSupportProvenance.lower_start outerToAfter
          (freshCap_support context afterExpression)
      have expressionFinal := expressionWide.extend_finish afterToFinish
      have bindingsFinal := bindingsSupport.extend_finish
        (Supply.le_trans expressionIncrease afterToFinish)
      have targetSupport : VariablesSupportProvenance context outerStart
          ⟨afterExpression.ty, afterExpression.cap + 1⟩
          inferred.target.unificationVars := by
        intro candidate member
        exact expressionFinal candidate (by
          simp [Generated.unificationVars, member])
      have hardSupport : VariablesSupportProvenance context outerStart
          ⟨afterExpression.ty, afterExpression.cap + 1⟩
          (TypePM.unificationVars inferred.hard) := by
        intro candidate member
        exact expressionFinal candidate (by
          simp [Generated.unificationVars, member])
      have pendingSupport : VariablesSupportProvenance context outerStart
          ⟨afterExpression.ty, afterExpression.cap + 1⟩
          (pendingUnificationVars inferred.pending) := by
        intro candidate member
        exact expressionFinal candidate (by
          simp [Generated.unificationVars, member])
      intro candidate member
      exact ((((capabilityWide.append targetSupport).append bindingsFinal).append
        hardSupport).append pendingSupport) candidate (by
          simpa [GeneratedPattern.unificationVars, dualVariables] using member)
  | @ctor constructor fields bindings start scheme generatedFields
      finish lookup arity fieldsElaboration =>
      have closed := wellFormed.baseWellFormed.patternConstructorClosed_of_lookup
        lookup
      have instantiated := DualScheme.instantiate_support closed start
      have instantiationIncrease : start.Le (scheme.instantiate start).2 := by
        simp [Supply.Le, DualScheme.instantiate]
      have instantiatedWide : VariablesSupportProvenance context outerStart
          (scheme.instantiate start).2
          (dualUnificationVars (scheme.instantiate start).1.fields ++
            dualVariables (scheme.instantiate start).1.result) := by
        intro candidate member
        rcases instantiated candidate member with impossible | fresh
        · simp [Context.unificationVars, Context.freeTyVars,
            Context.freeCapVars, dedupFirst, dedup] at impossible
        · exact Or.inr (fresh.lower_start outerToStart)
      have fieldsSupport := fieldsElaboration.supportProvenance wellFormed
        expressionIncreases expressionSupport
        (argumentsSupport.extend_finish instantiationIncrease)
        (bindingsSupport.extend_finish instantiationIncrease)
        (Supply.le_trans outerToStart instantiationIncrease)
      have instantiationFinal := instantiatedWide.extend_finish
        (fieldsElaboration.supply_le_next expressionIncreases)
      have resultSupport : VariablesSupportProvenance context outerStart finish
          (dualVariables (scheme.instantiate start).1.result) := by
        intro candidate member
        exact instantiationFinal candidate (by simp [member])
      have expectedFields : VariablesSupportProvenance context outerStart finish
          (dualUnificationVars (scheme.instantiate start).1.fields) := by
        intro candidate member
        exact instantiationFinal candidate (by simp [member])
      have actualFields : VariablesSupportProvenance context outerStart finish
          (dualUnificationVars generatedFields.duals) := by
        intro candidate member
        exact fieldsSupport candidate (by
          simp [GeneratedPatterns.unificationVars, member])
      have fieldChecks := Pattern.fieldEquations_support actualFields expectedFields
      have fieldBindings : VariablesSupportProvenance context outerStart finish
          (Ty.unificationVarsList generatedFields.bindings) := by
        intro candidate member
        exact fieldsSupport candidate (by
          simp [GeneratedPatterns.unificationVars, member])
      have fieldHard : VariablesSupportProvenance context outerStart finish
          (TypePM.unificationVars generatedFields.hard) := by
        intro candidate member
        exact fieldsSupport candidate (by
          simp [GeneratedPatterns.unificationVars, member])
      have fieldPending : VariablesSupportProvenance context outerStart finish
          (pendingUnificationVars generatedFields.pending) := by
        intro candidate member
        exact fieldsSupport candidate (by
          simp [GeneratedPatterns.unificationVars, member])
      intro candidate member
      exact (((resultSupport.append fieldBindings).append
        (fieldHard.append fieldChecks)).append fieldPending) candidate (by
          simpa [GeneratedPattern.unificationVars, unificationVars_append,
            List.append_assoc] using member)
  | tuple itemsElaboration =>
      rename_i generatedItems
      have itemsSupport := PatternsElaborateUsing.supportProvenance wellFormed
        expressionIncreases expressionSupport argumentsSupport bindingsSupport
        outerToStart itemsElaboration
      have itemDuals : VariablesSupportProvenance context outerStart finish
          (dualUnificationVars generatedItems.duals) := by
        intro candidate member
        exact itemsSupport candidate (by
          simp [GeneratedPatterns.unificationVars, member])
      have packed := tupleDual_support itemDuals
      have itemBindings : VariablesSupportProvenance context outerStart finish
          (Ty.unificationVarsList generatedItems.bindings) := by
        intro candidate member
        exact itemsSupport candidate (by
          simp [GeneratedPatterns.unificationVars, member])
      have itemHard : VariablesSupportProvenance context outerStart finish
          (TypePM.unificationVars generatedItems.hard) := by
        intro candidate member
        exact itemsSupport candidate (by
          simp [GeneratedPatterns.unificationVars, member])
      have itemPending : VariablesSupportProvenance context outerStart finish
          (pendingUnificationVars generatedItems.pending) := by
        intro candidate member
        exact itemsSupport candidate (by
          simp [GeneratedPatterns.unificationVars, member])
      exact (((packed.append itemBindings).append itemHard).append itemPending)
  | @and left right bindings start generatedLeft afterLeft
      generatedRight finish leftElaboration rightElaboration =>
      have leftSupport := leftElaboration.supportProvenance wellFormed
        expressionIncreases expressionSupport argumentsSupport bindingsSupport
        outerToStart
      have startToLeft := leftElaboration.supply_le_next expressionIncreases
      have leftToFinish := rightElaboration.supply_le_next expressionIncreases
      have argumentsAtLeft := argumentsSupport.extend_finish startToLeft
      have leftBindings : VariablesSupportProvenance context outerStart afterLeft
          (Ty.unificationVarsList generatedLeft.bindings) := by
        intro candidate member
        exact leftSupport candidate (by
          simp [GeneratedPattern.unificationVars, member])
      have rightSupport := rightElaboration.supportProvenance wellFormed
        expressionIncreases expressionSupport argumentsAtLeft leftBindings
        (Supply.le_trans outerToStart startToLeft)
      have leftFinal := leftSupport.extend_finish leftToFinish
      have leftDual : VariablesSupportProvenance context outerStart finish
          (dualVariables generatedLeft.dual) := by
        intro candidate member
        exact leftFinal candidate (by
          simp [GeneratedPattern.unificationVars, member])
      have rightDual : VariablesSupportProvenance context outerStart finish
          (dualVariables generatedRight.dual) := by
        intro candidate member
        exact rightSupport candidate (by
          simp [GeneratedPattern.unificationVars, member])
      have equationsSupport := Pattern.dualEquations_support leftDual rightDual
      have rightBindings : VariablesSupportProvenance context outerStart finish
          (Ty.unificationVarsList generatedRight.bindings) := by
        intro candidate member
        exact rightSupport candidate (by
          simp [GeneratedPattern.unificationVars, member])
      have leftHard : VariablesSupportProvenance context outerStart finish
          (TypePM.unificationVars generatedLeft.hard) := by
        intro candidate member
        exact leftFinal candidate (by
          simp [GeneratedPattern.unificationVars, member])
      have rightHard : VariablesSupportProvenance context outerStart finish
          (TypePM.unificationVars generatedRight.hard) := by
        intro candidate member
        exact rightSupport candidate (by
          simp [GeneratedPattern.unificationVars, member])
      have leftPending : VariablesSupportProvenance context outerStart finish
          (pendingUnificationVars generatedLeft.pending) := by
        intro candidate member
        exact leftFinal candidate (by
          simp [GeneratedPattern.unificationVars, member])
      have rightPending : VariablesSupportProvenance context outerStart finish
          (pendingUnificationVars generatedRight.pending) := by
        intro candidate member
        exact rightSupport candidate (by
          simp [GeneratedPattern.unificationVars, member])
      intro candidate member
      exact (((leftDual.append rightBindings).append
        ((leftHard.append rightHard).append equationsSupport)).append
        (leftPending.append rightPending)) candidate (by
          simpa [GeneratedPattern.unificationVars, unificationVars_append,
            pendingUnificationVars_append, List.append_assoc] using member)
  | embed lookup =>
      have selected := dualSupport_of_getElem argumentsSupport lookup
      intro candidate member
      exact (selected.append bindingsSupport) candidate (by
        simpa [GeneratedPattern.unificationVars, TypePM.unificationVars,
          pendingUnificationVars] using member)
  | @app function fields bindings start scheme generatedFields
      finish lookup arity fieldsElaboration =>
      have closed := FrozenSignature.lookupPatternFunction_closed wellFormed lookup
      have instantiated := DualScheme.instantiate_support closed start
      have instantiationIncrease : start.Le (scheme.instantiate start).2 := by
        simp [Supply.Le, DualScheme.instantiate]
      have instantiatedWide : VariablesSupportProvenance context outerStart
          (scheme.instantiate start).2
          (dualUnificationVars (scheme.instantiate start).1.fields ++
            dualVariables (scheme.instantiate start).1.result) := by
        intro candidate member
        rcases instantiated candidate member with impossible | fresh
        · simp [Context.unificationVars, Context.freeTyVars,
            Context.freeCapVars, dedupFirst, dedup] at impossible
        · exact Or.inr (fresh.lower_start outerToStart)
      have fieldsSupport := fieldsElaboration.supportProvenance wellFormed
        expressionIncreases expressionSupport
        (argumentsSupport.extend_finish instantiationIncrease)
        (bindingsSupport.extend_finish instantiationIncrease)
        (Supply.le_trans outerToStart instantiationIncrease)
      have instantiationFinal := instantiatedWide.extend_finish
        (fieldsElaboration.supply_le_next expressionIncreases)
      have resultSupport : VariablesSupportProvenance context outerStart finish
          (dualVariables (scheme.instantiate start).1.result) := by
        intro candidate member
        exact instantiationFinal candidate (by simp [member])
      have expectedFields : VariablesSupportProvenance context outerStart finish
          (dualUnificationVars (scheme.instantiate start).1.fields) := by
        intro candidate member
        exact instantiationFinal candidate (by simp [member])
      have actualFields : VariablesSupportProvenance context outerStart finish
          (dualUnificationVars generatedFields.duals) := by
        intro candidate member
        exact fieldsSupport candidate (by
          simp [GeneratedPatterns.unificationVars, member])
      have fieldChecks := Pattern.fieldEquations_support actualFields expectedFields
      have fieldBindings : VariablesSupportProvenance context outerStart finish
          (Ty.unificationVarsList generatedFields.bindings) := by
        intro candidate member
        exact fieldsSupport candidate (by
          simp [GeneratedPatterns.unificationVars, member])
      have fieldHard : VariablesSupportProvenance context outerStart finish
          (TypePM.unificationVars generatedFields.hard) := by
        intro candidate member
        exact fieldsSupport candidate (by
          simp [GeneratedPatterns.unificationVars, member])
      have fieldPending : VariablesSupportProvenance context outerStart finish
          (pendingUnificationVars generatedFields.pending) := by
        intro candidate member
        exact fieldsSupport candidate (by
          simp [GeneratedPatterns.unificationVars, member])
      intro candidate member
      exact (((resultSupport.append fieldBindings).append
        (fieldHard.append fieldChecks)).append fieldPending) candidate (by
          simpa [GeneratedPattern.unificationVars, unificationVars_append,
            List.append_assoc] using member)

/-- Left-to-right synthesis of a pattern list preserves provenance. -/
theorem PatternsElaborateUsing.supportProvenance
    {ExpressionElaborates : M4ExpressionElaborationRelation}
    (wellFormed : signature.WellFormed)
    (expressionIncreases : ∀ {context expression start generated finish},
      ExpressionElaborates context expression start generated finish →
        start.Le finish)
    (expressionSupport : ∀ {context expression start generated finish},
      ExpressionElaborates context expression start generated finish →
        GeneratedSupportProvenance context start finish generated)
    {context outerStart arguments patterns bindings start generated finish}
    (argumentsSupport : VariablesSupportProvenance context outerStart start
      (dualUnificationVars arguments))
    (bindingsSupport : VariablesSupportProvenance context outerStart start
      (Ty.unificationVarsList bindings))
    (outerToStart : outerStart.Le start)
    (derivation : PatternsElaborateUsing ExpressionElaborates signature context
      arguments patterns bindings start generated finish) :
    GeneratedPatternsSupportProvenance context outerStart finish generated := by
  cases derivation with
  | nil =>
      intro candidate member
      exact bindingsSupport candidate (by
        simpa [GeneratedPatterns.unificationVars, dualUnificationVars,
          TypePM.unificationVars, pendingUnificationVars] using member)
  | @cons pattern patterns bindings start generatedPattern
      afterPattern generatedPatterns finish head tail =>
      have headSupport := head.supportProvenance wellFormed expressionIncreases
        expressionSupport argumentsSupport bindingsSupport outerToStart
      have startToHead := head.supply_le_next expressionIncreases
      have tailBindings : VariablesSupportProvenance context outerStart afterPattern
          (Ty.unificationVarsList generatedPattern.bindings) := by
        intro candidate member
        exact headSupport candidate (by
          simp [GeneratedPattern.unificationVars, member])
      have tailSupport := tail.supportProvenance wellFormed expressionIncreases
        expressionSupport (argumentsSupport.extend_finish startToHead)
        tailBindings (Supply.le_trans outerToStart startToHead)
      have headFinal := headSupport.extend_finish
        (tail.supply_le_next expressionIncreases)
      have headDual : VariablesSupportProvenance context outerStart finish
          (dualVariables generatedPattern.dual) := by
        intro candidate member
        exact headFinal candidate (by
          simp [GeneratedPattern.unificationVars, member])
      have headHard : VariablesSupportProvenance context outerStart finish
          (TypePM.unificationVars generatedPattern.hard) := by
        intro candidate member
        exact headFinal candidate (by
          simp [GeneratedPattern.unificationVars, member])
      have headPending : VariablesSupportProvenance context outerStart finish
          (pendingUnificationVars generatedPattern.pending) := by
        intro candidate member
        exact headFinal candidate (by
          simp [GeneratedPattern.unificationVars, member])
      have tailDuals : VariablesSupportProvenance context outerStart finish
          (dualUnificationVars generatedPatterns.duals) := by
        intro candidate member
        exact tailSupport candidate (by
          simp [GeneratedPatterns.unificationVars, member])
      have tailBindings : VariablesSupportProvenance context outerStart finish
          (Ty.unificationVarsList generatedPatterns.bindings) := by
        intro candidate member
        exact tailSupport candidate (by
          simp [GeneratedPatterns.unificationVars, member])
      have tailHard : VariablesSupportProvenance context outerStart finish
          (TypePM.unificationVars generatedPatterns.hard) := by
        intro candidate member
        exact tailSupport candidate (by
          simp [GeneratedPatterns.unificationVars, member])
      have tailPending : VariablesSupportProvenance context outerStart finish
          (pendingUnificationVars generatedPatterns.pending) := by
        intro candidate member
        exact tailSupport candidate (by
          simp [GeneratedPatterns.unificationVars, member])
      intro candidate member
      exact (((headDual.append tailDuals).append tailBindings).append
        ((headHard.append tailHard).append
          (headPending.append tailPending))) candidate (by
        simpa [GeneratedPattern.unificationVars,
          GeneratedPatterns.unificationVars, dualUnificationVars,
          unificationVars_append, pendingUnificationVars_append,
          List.append_assoc] using member)

end

/-- A complete `matchAll` preserves provenance across target synthesis,
pattern synthesis, matcher checking, and the body's extended context. -/
theorem MatchAllElaboratesUsing.supportProvenance
    {ExpressionElaborates : M4ExpressionElaborationRelation}
    (wellFormed : signature.WellFormed)
    (expressionIncreases : ∀ {context expression start generated finish},
      ExpressionElaborates context expression start generated finish →
        start.Le finish)
    (expressionSupport : ∀ {context expression start generated finish},
      ExpressionElaborates context expression start generated finish →
        GeneratedSupportProvenance context start finish generated)
    {context target matcher pattern body start generated finish}
    (derivation : MatchAllElaboratesUsing ExpressionElaborates signature context
      target matcher pattern body start generated finish) :
    GeneratedSupportProvenance context start finish generated := by
  cases derivation with
  | @mk generatedTarget afterTarget
      generatedPattern afterPattern generatedMatcher afterMatcher generatedBody
      finish targetElaboration patternElaboration matcherElaboration
      bodyElaboration =>
      have targetSupport := expressionSupport targetElaboration
      have startToTarget := expressionIncreases targetElaboration
      have emptyArguments : VariablesSupportProvenance context start afterTarget
          (dualUnificationVars []) := by
        intro candidate member
        simp [dualUnificationVars] at member
      have emptyBindings : VariablesSupportProvenance context start afterTarget
          (Ty.unificationVarsList []) := by
        intro candidate member
        simp [Ty.unificationVarsList] at member
      have patternSupport := patternElaboration.supportProvenance wellFormed
        expressionIncreases expressionSupport emptyArguments emptyBindings
        startToTarget
      have targetToPattern := patternElaboration.supply_le_next
        expressionIncreases
      have patternToMatcher := expressionIncreases matcherElaboration
      have matcherToBody := expressionIncreases bodyElaboration
      have matcherSupport := (expressionSupport matcherElaboration).lower_start
        (Supply.le_trans startToTarget targetToPattern)
      have bindingSupport : VariablesSupportProvenance context start afterPattern
          (Ty.unificationVarsList generatedPattern.bindings) := by
        intro candidate member
        exact patternSupport candidate (by
          simp [GeneratedPattern.unificationVars, member])
      have bodyContextAtPattern := Pattern.extendContext_support bindingSupport
      have bodyContextAtMatcher := bodyContextAtPattern.extend_finish
        patternToMatcher
      have bodySupport := (expressionSupport bodyElaboration).rebase_context
        (Supply.le_trans startToTarget
          (Supply.le_trans targetToPattern patternToMatcher))
        matcherToBody bodyContextAtMatcher
      have targetFinal := targetSupport.extend_finish
        (Supply.le_trans targetToPattern
          (Supply.le_trans patternToMatcher matcherToBody))
      have patternFinal := patternSupport.extend_finish
        (Supply.le_trans patternToMatcher matcherToBody)
      have matcherFinal := matcherSupport.extend_finish matcherToBody
      intro candidate member
      have allSupport := VariablesSupportProvenance.append
        (VariablesSupportProvenance.append
          (VariablesSupportProvenance.append targetFinal patternFinal)
          matcherFinal)
        bodySupport
      have slotIncluded :
          candidate ∈ generatedPattern.dual.capability.unificationVars ∨
          candidate ∈ generatedTarget.target.unificationVars →
          candidate ∈
            (generatedTarget.unificationVars ++
              (generatedPattern.unificationVars ++
                (generatedMatcher.unificationVars ++
                  generatedBody.unificationVars))) := by
        intro origin
        exact Or.elim origin
          (fun matcherCapability => by
            simp [Generated.unificationVars,
              GeneratedPattern.unificationVars, dualVariables,
              matcherCapability])
          (fun checkedTarget => by
            simp [Generated.unificationVars, checkedTarget])
      exact allSupport candidate (by
          simp [Generated.fromMatchAll, Generated.unificationVars,
            GeneratedPattern.unificationVars, DataTypes.list,
            TypePM.unificationVars, Equation.unificationVars,
            pendingUnificationVars_append, pendingUnificationVars,
            CheckObligation.unificationVars, dualVariables,
            unificationVars_append] at member ⊢
          rcases member with bodyTarget | targetHard | patternTarget |
              targetTarget | patternHard | matcherHard | bodyHard |
              targetPending | patternPending | matcherPending | matcherTarget |
              matcherSlot | bodyPending
          all_goals try simp_all [Ty.unificationVars, Ty.unificationVarsList]
          exact Or.elim matcherSlot
            (fun matcherCapability =>
              Or.inr (Or.inr (Or.inr (Or.inl matcherCapability))))
            (fun checkedTarget => Or.inl checkedTarget))

namespace MatchFirstTyping

namespace GeneratedTail

def unificationVars (generated : GeneratedTail) : List UnificationVar :=
  TypePM.unificationVars generated.hard ++
    pendingUnificationVars generated.pending

end GeneratedTail

namespace GeneratedArms

def unificationVars (generated : GeneratedArms) : List UnificationVar :=
  generated.target.unificationVars ++
    TypePM.unificationVars generated.hard ++
      pendingUnificationVars generated.pending

end GeneratedArms

abbrev GeneratedTailSupportProvenance
    (context : Context) (start finish : Supply) (generated : GeneratedTail) :=
  VariablesSupportProvenance context start finish generated.unificationVars

abbrev GeneratedArmsSupportProvenance
    (context : Context) (start finish : Supply) (generated : GeneratedArms) :=
  VariablesSupportProvenance context start finish generated.unificationVars

/-- One later match arm uses only its three surrounding types and the
variables generated by its pattern and body. -/
theorem GeneratedTail.fromArm_support
    {context : Context} {start finish : Supply}
    {targetType matcherType expectedResult : Ty}
    {pattern : GeneratedPattern} {body : Generated}
    (targetSupport : VariablesSupportProvenance context start finish
      targetType.unificationVars)
    (matcherSupport : VariablesSupportProvenance context start finish
      matcherType.unificationVars)
    (resultSupport : VariablesSupportProvenance context start finish
      expectedResult.unificationVars)
    (patternSupport : GeneratedPatternSupportProvenance context start finish
      pattern)
    (bodySupport : GeneratedSupportProvenance context start finish body) :
    GeneratedTailSupportProvenance context start finish
      (GeneratedTail.fromArm targetType matcherType expectedResult pattern body) := by
  have patternTarget : VariablesSupportProvenance context start finish
      pattern.dual.target.unificationVars := by
    intro candidate member
    exact patternSupport candidate (by
      simp [GeneratedPattern.unificationVars, dualVariables, member])
  have patternCapability : VariablesSupportProvenance context start finish
      pattern.dual.capability.unificationVars := by
    intro candidate member
    exact patternSupport candidate (by
      simp [GeneratedPattern.unificationVars, dualVariables, member])
  have patternHard : VariablesSupportProvenance context start finish
      (TypePM.unificationVars pattern.hard) := by
    intro candidate member
    exact patternSupport candidate (by
      simp [GeneratedPattern.unificationVars, member])
  have patternPending : VariablesSupportProvenance context start finish
      (pendingUnificationVars pattern.pending) := by
    intro candidate member
    exact patternSupport candidate (by
      simp [GeneratedPattern.unificationVars, member])
  have bodyTarget : VariablesSupportProvenance context start finish
      body.target.unificationVars := by
    intro candidate member
    exact bodySupport candidate (by simp [Generated.unificationVars, member])
  have bodyHard : VariablesSupportProvenance context start finish
      (TypePM.unificationVars body.hard) := by
    intro candidate member
    exact bodySupport candidate (by simp [Generated.unificationVars, member])
  have bodyPending : VariablesSupportProvenance context start finish
      (pendingUnificationVars body.pending) := by
    intro candidate member
    exact bodySupport candidate (by simp [Generated.unificationVars, member])
  have obligationSupport : VariablesSupportProvenance context start finish
      (CheckObligation.unificationVars
        ⟨matcherType, .slot pattern.dual.capability targetType⟩) := by
    intro candidate member
    have origin : candidate ∈ matcherType.unificationVars ∨
        candidate ∈ pattern.dual.capability.unificationVars ∨
        candidate ∈ targetType.unificationVars := by
      simpa [CheckObligation.unificationVars, Ty.unificationVars] using member
    exact Or.elim origin
      (fun matcherMember => matcherSupport candidate matcherMember)
      (fun rest => Or.elim rest
        (fun capabilityMember => patternCapability candidate capabilityMember)
        (fun targetMember => targetSupport candidate targetMember))
  intro candidate member
  exact (((((patternTarget.append targetSupport).append patternHard).append
    bodyHard).append (bodyTarget.append resultSupport)).append
    ((patternPending.append obligationSupport).append bodyPending)) candidate (by
      simpa [GeneratedTail.unificationVars, GeneratedTail.fromArm,
        TypePM.unificationVars, Equation.unificationVars,
        unificationVars_append, pendingUnificationVars_append,
        pendingUnificationVars] using member)

/-- Every later arm is checked left to right without introducing variables
outside the enclosing match interval. -/
theorem TailElaboratesUsing.supportProvenance
    {ExpressionElaborates : M4ExpressionElaborationRelation}
    (wellFormed : signature.WellFormed)
    (expressionIncreases : ∀ {context expression start generated finish},
      ExpressionElaborates context expression start generated finish →
        start.Le finish)
    (expressionSupport : ∀ {context expression start generated finish},
      ExpressionElaborates context expression start generated finish →
        GeneratedSupportProvenance context start finish generated)
    {context outerStart targetType matcherType expectedResult arms start generated
      finish}
    (targetSupport : VariablesSupportProvenance context outerStart start
      targetType.unificationVars)
    (matcherSupport : VariablesSupportProvenance context outerStart start
      matcherType.unificationVars)
    (resultSupport : VariablesSupportProvenance context outerStart start
      expectedResult.unificationVars)
    (outerToStart : outerStart.Le start)
    (derivation : TailElaboratesUsing ExpressionElaborates signature context
      targetType matcherType expectedResult arms start generated finish) :
    GeneratedTailSupportProvenance context outerStart finish generated := by
  induction derivation with
  | nil =>
      intro candidate member
      simp [GeneratedTail.unificationVars, TypePM.unificationVars,
        pendingUnificationVars] at member
  | @cons pattern body arms start generatedPattern afterPattern generatedBody
      afterBody generatedTail finish patternElaboration bodyElaboration
      tailElaboration induction =>
      have emptyArguments : VariablesSupportProvenance context outerStart start
          (dualUnificationVars []) := by
        intro candidate member
        simp [dualUnificationVars] at member
      have emptyBindings : VariablesSupportProvenance context outerStart start
          (Ty.unificationVarsList []) := by
        intro candidate member
        simp [Ty.unificationVarsList] at member
      have patternSupport := patternElaboration.supportProvenance wellFormed
        expressionIncreases expressionSupport emptyArguments emptyBindings
        outerToStart
      have startToPattern := patternElaboration.supply_le_next
        expressionIncreases
      have patternToBody := expressionIncreases bodyElaboration
      have bindingsSupport : VariablesSupportProvenance context outerStart
          afterPattern (Ty.unificationVarsList generatedPattern.bindings) := by
        intro candidate member
        exact patternSupport candidate (by
          simp [GeneratedPattern.unificationVars, member])
      have bodyContextSupport := Pattern.extendContext_support bindingsSupport
      have bodySupport := (expressionSupport bodyElaboration).rebase_context
        (Supply.le_trans outerToStart startToPattern) patternToBody
        bodyContextSupport
      have startToBody := Supply.le_trans startToPattern patternToBody
      have tailSupport := induction
        (targetSupport.extend_finish startToBody)
        (matcherSupport.extend_finish startToBody)
        (resultSupport.extend_finish startToBody)
        (Supply.le_trans outerToStart startToBody)
      have bodyToFinish := tailElaboration.supply_le_next expressionIncreases
      have currentSupport := GeneratedTail.fromArm_support
        (targetSupport.extend_finish
          (Supply.le_trans startToBody bodyToFinish))
        (matcherSupport.extend_finish
          (Supply.le_trans startToBody bodyToFinish))
        (resultSupport.extend_finish
          (Supply.le_trans startToBody bodyToFinish))
        (patternSupport.extend_finish
          (Supply.le_trans patternToBody bodyToFinish))
        (bodySupport.extend_finish bodyToFinish)
      have currentHard : VariablesSupportProvenance context outerStart finish
          (TypePM.unificationVars
            (GeneratedTail.fromArm targetType matcherType expectedResult
              generatedPattern generatedBody).hard) := by
        intro candidate member
        exact currentSupport candidate (by
          simp [GeneratedTail.unificationVars, member])
      have currentPending : VariablesSupportProvenance context outerStart finish
          (pendingUnificationVars
            (GeneratedTail.fromArm targetType matcherType expectedResult
              generatedPattern generatedBody).pending) := by
        intro candidate member
        exact currentSupport candidate (by
          simp [GeneratedTail.unificationVars, member])
      have tailHard : VariablesSupportProvenance context outerStart finish
          (TypePM.unificationVars generatedTail.hard) := by
        intro candidate member
        exact tailSupport candidate (by
          simp [GeneratedTail.unificationVars, member])
      have tailPending : VariablesSupportProvenance context outerStart finish
          (pendingUnificationVars generatedTail.pending) := by
        intro candidate member
        exact tailSupport candidate (by
          simp [GeneratedTail.unificationVars, member])
      intro candidate member
      exact ((currentHard.append tailHard).append
        (currentPending.append tailPending)) candidate (by
        simpa [GeneratedTail.unificationVars,
          unificationVars_append, pendingUnificationVars_append]
          using member)

/-- The first arm fixes the result type; later arms are checked against that
same supported type. -/
theorem ArmsElaborateUsing.supportProvenance
    {ExpressionElaborates : M4ExpressionElaborationRelation}
    (wellFormed : signature.WellFormed)
    (expressionIncreases : ∀ {context expression start generated finish},
      ExpressionElaborates context expression start generated finish →
        start.Le finish)
    (expressionSupport : ∀ {context expression start generated finish},
      ExpressionElaborates context expression start generated finish →
        GeneratedSupportProvenance context start finish generated)
    {context outerStart targetType matcherType arms start generated finish}
    (targetSupport : VariablesSupportProvenance context outerStart start
      targetType.unificationVars)
    (matcherSupport : VariablesSupportProvenance context outerStart start
      matcherType.unificationVars)
    (outerToStart : outerStart.Le start)
    (derivation : ArmsElaborateUsing ExpressionElaborates signature context
      targetType matcherType arms start generated finish) :
    GeneratedArmsSupportProvenance context outerStart finish generated := by
  cases derivation with
  | @cons pattern body arms start generatedPattern afterPattern generatedBody
      afterBody generatedTail finish patternElaboration bodyElaboration
      tailElaboration =>
      have emptyArguments : VariablesSupportProvenance context outerStart start
          (dualUnificationVars []) := by
        intro candidate member
        simp [dualUnificationVars] at member
      have emptyBindings : VariablesSupportProvenance context outerStart start
          (Ty.unificationVarsList []) := by
        intro candidate member
        simp [Ty.unificationVarsList] at member
      have patternSupport := patternElaboration.supportProvenance wellFormed
        expressionIncreases expressionSupport emptyArguments emptyBindings
        outerToStart
      have startToPattern := patternElaboration.supply_le_next
        expressionIncreases
      have patternToBody := expressionIncreases bodyElaboration
      have bindingsSupport : VariablesSupportProvenance context outerStart
          afterPattern (Ty.unificationVarsList generatedPattern.bindings) := by
        intro candidate member
        exact patternSupport candidate (by
          simp [GeneratedPattern.unificationVars, member])
      have bodySupport := (expressionSupport bodyElaboration).rebase_context
        (Supply.le_trans outerToStart startToPattern) patternToBody
        (Pattern.extendContext_support bindingsSupport)
      have startToBody := Supply.le_trans startToPattern patternToBody
      have bodyTargetAtBody : VariablesSupportProvenance context outerStart
          afterBody generatedBody.target.unificationVars := by
        intro candidate member
        exact bodySupport candidate (by simp [Generated.unificationVars, member])
      have tailSupport := tailElaboration.supportProvenance wellFormed
        expressionIncreases expressionSupport
        (targetSupport.extend_finish startToBody)
        (matcherSupport.extend_finish startToBody)
        bodyTargetAtBody (Supply.le_trans outerToStart startToBody)
      have bodyToFinish := tailElaboration.supply_le_next expressionIncreases
      have patternFinal := patternSupport.extend_finish
        (Supply.le_trans patternToBody bodyToFinish)
      have bodyFinal := bodySupport.extend_finish bodyToFinish
      have targetFinal := targetSupport.extend_finish
        (Supply.le_trans startToBody bodyToFinish)
      have matcherFinal := matcherSupport.extend_finish
        (Supply.le_trans startToBody bodyToFinish)
      have patternTarget : VariablesSupportProvenance context outerStart finish
          generatedPattern.dual.target.unificationVars := by
        intro candidate member
        exact patternFinal candidate (by
          simp [GeneratedPattern.unificationVars, dualVariables, member])
      have patternCapability : VariablesSupportProvenance context outerStart finish
          generatedPattern.dual.capability.unificationVars := by
        intro candidate member
        exact patternFinal candidate (by
          simp [GeneratedPattern.unificationVars, dualVariables, member])
      have obligationSupport : VariablesSupportProvenance context outerStart finish
          (CheckObligation.unificationVars
            ⟨matcherType, .slot generatedPattern.dual.capability targetType⟩) := by
        intro candidate member
        have origin : candidate ∈ matcherType.unificationVars ∨
            candidate ∈ generatedPattern.dual.capability.unificationVars ∨
            candidate ∈ targetType.unificationVars := by
          simpa [CheckObligation.unificationVars, Ty.unificationVars] using member
        exact Or.elim origin
          (fun item => matcherFinal candidate item)
          (fun rest => Or.elim rest
            (fun item => patternCapability candidate item)
            (fun item => targetFinal candidate item))
      have patternHard : VariablesSupportProvenance context outerStart finish
          (TypePM.unificationVars generatedPattern.hard) := by
        intro candidate member
        exact patternFinal candidate (by
          simp [GeneratedPattern.unificationVars, member])
      have patternPending : VariablesSupportProvenance context outerStart finish
          (pendingUnificationVars generatedPattern.pending) := by
        intro candidate member
        exact patternFinal candidate (by
          simp [GeneratedPattern.unificationVars, member])
      have tailHard : VariablesSupportProvenance context outerStart finish
          (TypePM.unificationVars generatedTail.hard) := by
        intro candidate member
        exact tailSupport candidate (by
          simp [GeneratedTail.unificationVars, member])
      have tailPending : VariablesSupportProvenance context outerStart finish
          (pendingUnificationVars generatedTail.pending) := by
        intro candidate member
        exact tailSupport candidate (by
          simp [GeneratedTail.unificationVars, member])
      have bodyTarget : VariablesSupportProvenance context outerStart finish
          generatedBody.target.unificationVars := by
        intro candidate member
        exact bodyFinal candidate (by simp [Generated.unificationVars, member])
      have bodyHard : VariablesSupportProvenance context outerStart finish
          (TypePM.unificationVars generatedBody.hard) := by
        intro candidate member
        exact bodyFinal candidate (by simp [Generated.unificationVars, member])
      have bodyPending : VariablesSupportProvenance context outerStart finish
          (pendingUnificationVars generatedBody.pending) := by
        intro candidate member
        exact bodyFinal candidate (by simp [Generated.unificationVars, member])
      intro candidate member
      exact ((((bodyTarget.append patternTarget).append targetFinal).append
        ((patternHard.append bodyHard).append tailHard)).append
        (((patternPending.append obligationSupport).append bodyPending).append
          tailPending)) candidate (by
            simpa [GeneratedArms.unificationVars, GeneratedArms.fromFirst,
              GeneratedTail.fromArm, TypePM.unificationVars,
              Equation.unificationVars, unificationVars_append,
              pendingUnificationVars_append, pendingUnificationVars]
              using member)

/-- A complete single-result match preserves generated-variable provenance. -/
theorem ElaboratesUsing.supportProvenance
    {ExpressionElaborates : M4ExpressionElaborationRelation}
    (wellFormed : signature.WellFormed)
    (expressionIncreases : ∀ {context expression start generated finish},
      ExpressionElaborates context expression start generated finish →
        start.Le finish)
    (expressionSupport : ∀ {context expression start generated finish},
      ExpressionElaborates context expression start generated finish →
        GeneratedSupportProvenance context start finish generated)
    {context expression start generated finish}
    (derivation : ElaboratesUsing ExpressionElaborates signature context
      expression start generated finish) :
    GeneratedSupportProvenance context start finish generated := by
  cases derivation with
  | @matchFirst target matcher arms start generatedTarget afterTarget
      generatedMatcher afterMatcher generatedArms finish exhaustive
      targetElaboration matcherElaboration armsElaboration =>
      have targetSupport := expressionSupport targetElaboration
      have startToTarget := expressionIncreases targetElaboration
      have matcherSupport := (expressionSupport matcherElaboration).lower_start
        startToTarget
      have targetToMatcher := expressionIncreases matcherElaboration
      have targetTypeSupport : VariablesSupportProvenance context start afterMatcher
          generatedTarget.target.unificationVars := by
        intro candidate member
        exact (targetSupport.extend_finish targetToMatcher) candidate (by
          simp [Generated.unificationVars, member])
      have matcherTypeSupport : VariablesSupportProvenance context start afterMatcher
          generatedMatcher.target.unificationVars := by
        intro candidate member
        exact matcherSupport candidate (by
          simp [Generated.unificationVars, member])
      have armsSupport := armsElaboration.supportProvenance wellFormed
        expressionIncreases expressionSupport targetTypeSupport matcherTypeSupport
        (Supply.le_trans startToTarget targetToMatcher)
      have matcherToFinish := armsElaboration.supply_le_next expressionIncreases
      have targetFinal := targetSupport.extend_finish
        (Supply.le_trans targetToMatcher matcherToFinish)
      have matcherFinal := matcherSupport.extend_finish matcherToFinish
      have armsTarget : VariablesSupportProvenance context start finish
          generatedArms.target.unificationVars := by
        intro candidate member
        exact armsSupport candidate (by
          simp [GeneratedArms.unificationVars, member])
      have targetHard : VariablesSupportProvenance context start finish
          (TypePM.unificationVars generatedTarget.hard) := by
        intro candidate member
        exact targetFinal candidate (by simp [Generated.unificationVars, member])
      have matcherHard : VariablesSupportProvenance context start finish
          (TypePM.unificationVars generatedMatcher.hard) := by
        intro candidate member
        exact matcherFinal candidate (by simp [Generated.unificationVars, member])
      have armsHard : VariablesSupportProvenance context start finish
          (TypePM.unificationVars generatedArms.hard) := by
        intro candidate member
        exact armsSupport candidate (by
          simp [GeneratedArms.unificationVars, member])
      have targetPending : VariablesSupportProvenance context start finish
          (pendingUnificationVars generatedTarget.pending) := by
        intro candidate member
        exact targetFinal candidate (by simp [Generated.unificationVars, member])
      have matcherPending : VariablesSupportProvenance context start finish
          (pendingUnificationVars generatedMatcher.pending) := by
        intro candidate member
        exact matcherFinal candidate (by simp [Generated.unificationVars, member])
      have armsPending : VariablesSupportProvenance context start finish
          (pendingUnificationVars generatedArms.pending) := by
        intro candidate member
        exact armsSupport candidate (by
          simp [GeneratedArms.unificationVars, member])
      intro candidate member
      exact (((armsTarget.append
        ((targetHard.append matcherHard).append armsHard)).append
        ((targetPending.append matcherPending).append armsPending))) candidate (by
          simpa [Generated.fromMatchFirst, Generated.unificationVars,
            unificationVars_append, pendingUnificationVars_append]
            using member)

end MatchFirstTyping

/-- Callback-independent form of the M2 `let` support argument.  The closure
transports the value's supported variables into the substituted and
generalized context used for the body. -/
theorem GeneratedSupportProvenance.fromLet_recursive
    {context : Context} {start afterValue finish : Supply}
    {generatedValue generatedBody : Generated}
    (valueIncrease : start.Le afterValue)
    (closure : PrincipalBlockClosure generatedValue)
    (absorbing : closure.Absorbing)
    (bodyIncrease :
      (afterValue.join
        (context.applyFree closure.substitution).initialSupply).Le finish)
    (valueSupport : GeneratedSupportProvenance context start afterValue
      generatedValue)
    (bodySupport : GeneratedSupportProvenance
      ((context.applyFree closure.substitution).generalize closure.target ::
        context.applyFree closure.substitution)
      (afterValue.join
        (context.applyFree closure.substitution).initialSupply)
      finish generatedBody) :
    GeneratedSupportProvenance context start finish
      (Generated.fromLet
        (context.interfaceEquations closure.substitution) generatedBody) := by
  intro candidate member
  simp only [Generated.fromLet, Generated.unificationVars,
    unificationVars_append, List.mem_append] at member
  have localized := closure.localized_of_absorbing absorbing
  have afterValueToFinish : afterValue.Le finish :=
    Supply.le_trans (Supply.le_join_left afterValue
      (context.applyFree closure.substitution).initialSupply) bodyIncrease
  have startToBodyStart : start.Le
      (afterValue.join
        (context.applyFree closure.substitution).initialSupply) :=
    Supply.le_trans valueIncrease (Supply.le_join_left afterValue
      (context.applyFree closure.substitution).initialSupply)
  have liftValue : ∀ {item},
      item ∈ context.unificationVars ∨ item.FreshIn start afterValue →
        item ∈ context.unificationVars ∨ item.FreshIn start finish := by
    intro item origin
    rcases origin with outer | fresh
    · exact Or.inl outer
    · exact Or.inr (fresh.extend_finish afterValueToFinish)
  have closedSupport := Context.applyFree_supportProvenance localized valueSupport
  have liftBody : ∀ {item}, item ∈ generatedBody.unificationVars →
      item ∈ context.unificationVars ∨ item.FreshIn start finish := by
    intro item bodyMember
    rcases bodySupport item bodyMember with bodyContext | fresh
    · have closedMember := Context.generalized_cons_support_subset
        (context.applyFree closure.substitution) closure.target item bodyContext
      exact liftValue (closedSupport item closedMember)
    · exact Or.inr (fresh.lower_start startToBodyStart)
  rcases member with targetOrHard | pending
  · rcases targetOrHard with target | effectsOrHard
    · exact liftBody (by
        simp only [Generated.unificationVars, List.mem_append]
        exact Or.inl (Or.inl target))
    · rcases effectsOrHard with effects | hard
      · exact liftValue (Context.interface_supportProvenance
          localized valueSupport candidate effects)
      · exact liftBody (by
          simp only [Generated.unificationVars, List.mem_append]
          exact Or.inl (Or.inr hard))
  · exact liftBody (by
      simp only [Generated.unificationVars, List.mem_append]
      exact Or.inr pending)

/-- Callback-independent application assembly. -/
theorem GeneratedSupportProvenance.fromApp_recursive
    {context : Context} {start afterFunction afterArgument : Supply}
    {generatedFunction generatedArgument : Generated}
    (functionIncrease : start.Le afterFunction)
    (argumentIncrease : afterFunction.Le afterArgument)
    (functionSupport : GeneratedSupportProvenance context start afterFunction
      generatedFunction)
    (argumentSupport : GeneratedSupportProvenance context afterFunction
      afterArgument generatedArgument) :
    GeneratedSupportProvenance context start (afterArgument.nextTy 2)
      (Generated.fromApp generatedFunction generatedArgument
        (.var ⟨afterArgument.ty⟩) (.var ⟨afterArgument.ty + 1⟩)) := by
  intro candidate member
  simp only [Generated.fromApp, Generated.unificationVars, Ty.unificationVars,
    TypePM.unificationVars, pendingUnificationVars,
    CheckObligation.unificationVars, List.mem_append,
    unificationVars_append, pendingUnificationVars_append,
    Equation.unificationVars, List.mem_cons, List.not_mem_nil, or_false]
    at member
  have startToArgument := Supply.le_trans functionIncrease argumentIncrease
  have argumentToFinish := Supply.le_nextTy afterArgument 2
  have liftFunction : ∀ {item},
      item ∈ context.unificationVars ∨ item.FreshIn start afterFunction →
        item ∈ context.unificationVars ∨
          item.FreshIn start (afterArgument.nextTy 2) := by
    intro item origin
    rcases origin with outer | fresh
    · exact Or.inl outer
    · exact Or.inr (fresh.extend_finish
        (Supply.le_trans argumentIncrease argumentToFinish))
  have liftArgument : ∀ {item},
      item ∈ context.unificationVars ∨ item.FreshIn afterFunction afterArgument →
        item ∈ context.unificationVars ∨
          item.FreshIn start (afterArgument.nextTy 2) := by
    intro item origin
    rcases origin with outer | fresh
    · exact Or.inl outer
    · exact Or.inr ((fresh.lower_start functionIncrease).extend_finish
        argumentToFinish)
  have freshAt (offset : Nat) (offsetLt : offset < 2) :
      UnificationVar.FreshIn start (afterArgument.nextTy 2)
        (.ty ⟨afterArgument.ty + offset⟩) := by
    simp only [UnificationVar.FreshIn, Supply.nextTy]
    exact ⟨Nat.le_trans startToArgument.1 (Nat.le_add_right _ _),
      Nat.add_lt_add_left offsetLt _⟩
  rcases member with (rfl | (functionHard | argumentHard) | functionTarget |
      rfl | rfl) | (functionPending | argumentPending) | argumentTarget | rfl
  · exact Or.inr (freshAt 1 (by omega))
  · exact liftFunction (functionSupport candidate (by
      simp only [Generated.unificationVars, List.mem_append]
      exact Or.inl (Or.inr functionHard)))
  · exact liftArgument (argumentSupport candidate (by
      simp only [Generated.unificationVars, List.mem_append]
      exact Or.inl (Or.inr argumentHard)))
  · exact liftFunction (functionSupport candidate (by
      simp only [Generated.unificationVars, List.mem_append]
      exact Or.inl (Or.inl functionTarget)))
  · simpa using Or.inr (freshAt 0 (by omega))
  · exact Or.inr (freshAt 1 (by omega))
  · exact liftFunction (functionSupport candidate (by
      simp only [Generated.unificationVars, List.mem_append]
      exact Or.inr functionPending))
  · exact liftArgument (argumentSupport candidate (by
      simp only [Generated.unificationVars, List.mem_append]
      exact Or.inr argumentPending))
  · exact liftArgument (argumentSupport candidate (by
      simp only [Generated.unificationVars, List.mem_append]
      exact Or.inl (Or.inl argumentTarget)))
  · simpa using Or.inr (freshAt 0 (by omega))

/-- Callback-independent lambda assembly. -/
theorem GeneratedSupportProvenance.fromLam_recursive
    {context : Context} {start finish : Supply} {body : Generated}
    (bodyIncrease : (start.nextTy 1).Le finish)
    (bodySupport : GeneratedSupportProvenance
      (.mono (.var ⟨start.ty⟩) :: context) (start.nextTy 1) finish body) :
    GeneratedSupportProvenance context start finish
      (Generated.fromLam (.var ⟨start.ty⟩) body) := by
  have bindingSupport := freshTy_support context start
  have bodyContextSupport : VariablesSupportProvenance context start
      (start.nextTy 1)
      (Context.unificationVars (.mono (.var ⟨start.ty⟩) :: context)) := by
    simpa [Pattern.extendContext] using
      Pattern.extendContext_support (bindings := [.var ⟨start.ty⟩])
        (by simpa [Ty.unificationVarsList] using bindingSupport)
  have bodyWide := bodySupport.rebase_context (Supply.le_nextTy start 1)
    bodyIncrease bodyContextSupport
  have domainFinal := bindingSupport.extend_finish bodyIncrease
  intro candidate member
  exact (domainFinal.append bodyWide) candidate (by
    simpa [Generated.fromLam, Generated.unificationVars, Ty.unificationVars]
      using member)

namespace M4

/-- Source-ordered sibling expressions preserve generated-item provenance. -/
theorem ItemsElaborateUsing.supportProvenance
    {ExpressionElaborates : M4ExpressionElaborationRelation}
    (expressionIncreases : ∀ {context expression start generated finish},
      ExpressionElaborates context expression start generated finish →
        start.Le finish)
    (expressionSupport : ∀ {context expression start generated finish},
      ExpressionElaborates context expression start generated finish →
        GeneratedSupportProvenance context start finish generated)
    {context items start generated finish}
    (derivation : ItemsElaborateUsing ExpressionElaborates context items start
      generated finish) :
    GeneratedItemsSupportProvenance context start finish generated := by
  induction derivation with
  | nil =>
      intro candidate member
      simp [GeneratedItems.unificationVars, Ty.unificationVarsList,
        TypePM.unificationVars, pendingUnificationVars] at member
  | @cons item items start generatedItem afterItem generatedItems finish
      head tail induction =>
      have headIncrease := expressionIncreases head
      have tailIncrease := tail.supply_le_next expressionIncreases
      have headFinal := (expressionSupport head).extend_finish tailIncrease
      have tailWide : GeneratedItemsSupportProvenance context start finish
          generatedItems := by
        intro candidate member
        rcases induction candidate member with outer | fresh
        · exact Or.inl outer
        · exact Or.inr (fresh.lower_start headIncrease)
      have headTarget : VariablesSupportProvenance context start finish
          generatedItem.target.unificationVars := by
        intro candidate member
        exact headFinal candidate (by simp [Generated.unificationVars, member])
      have headHard : VariablesSupportProvenance context start finish
          (TypePM.unificationVars generatedItem.hard) := by
        intro candidate member
        exact headFinal candidate (by simp [Generated.unificationVars, member])
      have headPending : VariablesSupportProvenance context start finish
          (pendingUnificationVars generatedItem.pending) := by
        intro candidate member
        exact headFinal candidate (by simp [Generated.unificationVars, member])
      have tailTargets : VariablesSupportProvenance context start finish
          (Ty.unificationVarsList generatedItems.targets) := by
        intro candidate member
        exact tailWide candidate (by
          simp [GeneratedItems.unificationVars, member])
      have tailHard : VariablesSupportProvenance context start finish
          (TypePM.unificationVars generatedItems.hard) := by
        intro candidate member
        exact tailWide candidate (by
          simp [GeneratedItems.unificationVars, member])
      have tailPending : VariablesSupportProvenance context start finish
          (pendingUnificationVars generatedItems.pending) := by
        intro candidate member
        exact tailWide candidate (by
          simp [GeneratedItems.unificationVars, member])
      intro candidate member
      exact (((headTarget.append tailTargets).append
        (headHard.append tailHard)).append
        (headPending.append tailPending)) candidate (by
          simpa [GeneratedItems.unificationVars, Ty.unificationVarsList,
            unificationVars_append, pendingUnificationVars_append]
            using member)

/-- A fixed-arity call fold preserves an already supported accumulated
function block while elaborating its arguments. -/
theorem CallElaboratesUsing.supportProvenance
    {ExpressionElaborates : M4ExpressionElaborationRelation}
    (expressionIncreases : ∀ {context expression start generated finish},
      ExpressionElaborates context expression start generated finish →
        start.Le finish)
    (expressionSupport : ∀ {context expression start generated finish},
      ExpressionElaborates context expression start generated finish →
        GeneratedSupportProvenance context start finish generated)
    {context accumulated arguments start generated finish outerStart}
    (outerToStart : outerStart.Le start)
    (accumulatedSupport : GeneratedSupportProvenance context outerStart start
      accumulated)
    (derivation : CallElaboratesUsing ExpressionElaborates context accumulated
      arguments start generated finish) :
    GeneratedSupportProvenance context outerStart finish generated := by
  induction derivation generalizing outerStart with
  | nil => exact accumulatedSupport
  | @cons accumulated argument arguments start generatedArgument afterArgument
      applied finish head tail induction =>
      have headIncrease := expressionIncreases head
      have argumentSupport := expressionSupport head
      have appliedSupport := GeneratedSupportProvenance.fromApp_recursive
        outerToStart headIncrease accumulatedSupport argumentSupport
      apply induction
        (Supply.le_trans outerToStart
          (Supply.le_trans headIncrease (Supply.le_nextTy afterArgument 2)))
        appliedSupport

/-- Every fuel-indexed M4 derivation mentions only context variables or
variables freshly allocated during that derivation. -/
theorem ElaboratesFuel.supportProvenance
    {signature : FrozenSignature} (wellFormed : signature.WellFormed)
    {fuel : Nat} {context : Context} {expression : Expr}
    {start finish : Supply} {generated : Generated}
    (derivation : ElaboratesFuel signature fuel context expression start
      generated finish) :
    GeneratedSupportProvenance context start finish generated := by
  induction fuel generalizing context expression start generated finish with
  | zero => simp [ElaboratesFuel] at derivation
  | succ fuel induction =>
      cases expression <;> simp only [ElaboratesFuel] at derivation
      · obtain ⟨scheme, lookup, rfl, rfl⟩ := derivation
        exact (Source.Elaborates.var (signature := signature.base)
          lookup).supportProvenance
      · obtain ⟨rfl, rfl⟩ := derivation
        intro candidate member
        simp [Generated.unificationVars, Ty.unificationVars,
          TypePM.unificationVars, pendingUnificationVars] at member
      · obtain ⟨rfl, rfl⟩ := derivation
        intro candidate member
        have equality : candidate = .ty ⟨start.ty⟩ := by
          simpa [Generated.unificationVars, Ty.unificationVars,
            Cap.unificationVars, TypePM.unificationVars,
            pendingUnificationVars] using member
        subst candidate
        exact Or.inr (by simp [UnificationVar.FreshIn, Supply.nextTy])
      · obtain ⟨generatedBody, bodyDerivation, rfl⟩ := derivation
        exact GeneratedSupportProvenance.fromLam_recursive
          bodyDerivation.supply_le_next (induction bodyDerivation)
      · obtain ⟨generatedFunction, afterFunction, generatedArgument,
          afterArgument, functionDerivation, argumentDerivation, rfl, rfl⟩ :=
          derivation
        exact GeneratedSupportProvenance.fromApp_recursive
          functionDerivation.supply_le_next argumentDerivation.supply_le_next
          (induction functionDerivation) (induction argumentDerivation)
      · obtain ⟨generatedItems, itemsDerivation, rfl⟩ := derivation
        intro candidate member
        exact (itemsDerivation.supportProvenance
          (fun child => child.supply_le_next)
          (fun child => induction child)) candidate (by
            simpa [Generated.unificationVars,
              GeneratedItems.unificationVars, Ty.unificationVars] using member)
      · obtain ⟨generatedValue, afterValue, valueDerivation, closure,
          generatedBody, absorbing, bodyDerivation, rfl⟩ := derivation
        exact GeneratedSupportProvenance.fromLet_recursive
          valueDerivation.supply_le_next closure absorbing
          bodyDerivation.supply_le_next (induction valueDerivation)
          (induction bodyDerivation)
      · obtain ⟨scheme, lookup, arity, closed, callDerivation⟩ := derivation
        exact callDerivation.supportProvenance
          (fun child => child.supply_le_next)
          (fun child => induction child)
          (by simp [Supply.Le, Scheme.instantiate])
          (supportProvenance_closed_instantiate closed)
      · obtain ⟨scheme, lookup, arity, closed, callDerivation⟩ := derivation
        exact callDerivation.supportProvenance
          (fun child => child.supply_le_next)
          (fun child => induction child)
          (by simp [Supply.Le, Scheme.instantiate])
          (supportProvenance_closed_instantiate closed)
      · exact derivation.supportProvenance
          (fun child => child.supply_le_next)
          (fun child => induction child)
          (by simp [Supply.Le, Scheme.instantiate])
          (supportProvenance_closed_instantiate conditionalScheme_closed)
      · exact derivation.supportProvenance
          (fun child => child.supply_le_next)
          (fun child => induction child)
      · exact derivation.supportProvenance wellFormed
          (fun child => child.supply_le_next)
          (fun child => induction child)
          MatcherTyping.PPatElaborates.supply_le_next
          (fun wf targetSupport capabilitySupport outerTo child =>
            child.supportProvenance wf targetSupport capabilitySupport outerTo)
          MatcherTyping.DPatElaborates.supply_le_next
          (fun wf expectedSupport outerTo child =>
            child.supportProvenance wf expectedSupport outerTo)
      · exact derivation.supportProvenance wellFormed
          (fun child => child.supply_le_next)
          (fun child => induction child)
      · exact derivation.supportProvenance wellFormed
          (fun child => child.supply_le_next)
          (fun child => induction child)

/-- Public M4 elaboration inherits support from its hidden fuel witness. -/
theorem Elaborates.supportProvenance
    {signature : FrozenSignature} (wellFormed : signature.WellFormed)
    {context : Context} {expression : Expr} {start finish : Supply}
    {generated : Generated}
    (derivation : Elaborates signature context expression start generated finish) :
    GeneratedSupportProvenance context start finish generated := by
  obtain ⟨fuel, fuelDerivation⟩ := derivation
  exact fuelDerivation.supportProvenance wellFormed

/-- The architecture-level supply-and-support obligation is discharged. -/
theorem supplyAndSupport : M4.CompletenessArchitecture.M4SupplyAndSupport := by
  intro signature fuel context expression start finish generated wellFormed
    derivation
  exact ⟨derivation.supply_le_next,
    derivation.supportProvenance wellFormed⟩

end M4

end TypePM.Source
