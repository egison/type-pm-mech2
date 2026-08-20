import TypePM.Source.M4SupplySupport
import TypePM.Source.LetSupplyStability

/-!
# Fresh-renaming transport for M4 elaboration

This module develops the componentwise renaming facts needed to transport the
fuel-indexed M4 relation.  Unlike callback-only `map` lemmas, these results
rename every type and capability carried by the callback-parametric relations.
-/

namespace TypePM.Source

open ElaborationRenaming

namespace M4FreshRenaming

/-- A context whose variables all come from a well-formed outer context or
from the allocated interval is itself well formed at the interval's end.
This is the context invariant required by recursive callbacks below pattern
bindings and matcher captures. -/
theorem Supply.WellFormedFor.of_contextSupport
    {outerContext childContext : Context} {outerStart finish : Supply}
    (outerWellFormed : outerStart.WellFormedFor outerContext)
    (outerToFinish : outerStart.Le finish)
    (contextSupport : VariablesSupportProvenance outerContext outerStart finish
      childContext.unificationVars) :
    finish.WellFormedFor childContext := by
  simp only [Supply.WellFormedFor, Context.initialSupply, Supply.Le]
  constructor
  · apply TyVar.next_le_of_forall_lt
    intro index member
    have childMember : index ∈ childContext.freeTyVars :=
      mem_dedupFirst.mpr member
    have supported := contextSupport (.ty index) (by
      simp [Context.unificationVars, childMember])
    rcases supported with outer | fresh
    · have outerMember : index ∈ outerContext.freeTyVars := by
        simpa [Context.unificationVars] using outer
      exact Nat.lt_of_lt_of_le
        (Context.freeTy_index_lt_initialSupply outerMember)
        (Nat.le_trans outerWellFormed.1 outerToFinish.1)
    · exact fresh.2
  · apply CapVar.next_le_of_forall_lt
    intro index member
    have childMember : index ∈ childContext.freeCapVars :=
      mem_dedupFirst.mpr member
    have supported := contextSupport (.cap index) (by
      simp [Context.unificationVars, childMember])
    rcases supported with outer | fresh
    · have outerMember : index ∈ outerContext.freeCapVars := by
        simpa [Context.unificationVars] using outer
      exact Nat.lt_of_lt_of_le
        (Context.freeCap_index_lt_initialSupply outerMember)
        (Nat.le_trans outerWellFormed.2 outerToFinish.2)
    · exact fresh.2

def renameDual (rho : VariableRenaming) (dual : Dual) : Dual :=
  ⟨renameCap rho dual.capability, renameTy rho dual.target⟩

def renameGeneratedPattern (rho : VariableRenaming)
    (generated : GeneratedPattern) : GeneratedPattern :=
  ⟨renameDual rho generated.dual, generated.bindings.map (renameTy rho),
    generated.hard.map (renameEquation rho),
    generated.pending.map (renameObligation rho)⟩

def renameGeneratedPatterns (rho : VariableRenaming)
    (generated : GeneratedPatterns) : GeneratedPatterns :=
  ⟨generated.duals.map (renameDual rho),
    generated.bindings.map (renameTy rho),
    generated.hard.map (renameEquation rho),
    generated.pending.map (renameObligation rho)⟩

namespace MatcherTyping

def renameGeneratedChecks (rho : VariableRenaming)
    (generated : TypePM.Source.MatcherTyping.GeneratedChecks) :
    TypePM.Source.MatcherTyping.GeneratedChecks :=
  ⟨generated.hard.map (renameEquation rho),
    generated.pending.map (renameObligation rho)⟩

def renameGeneratedPPat (rho : VariableRenaming)
    (generated : TypePM.Source.MatcherTyping.GeneratedPPat) :
    TypePM.Source.MatcherTyping.GeneratedPPat :=
  ⟨generated.holes.map (renameDual rho),
    generated.captures.map (renameTy rho),
    generated.evidence.map (renameCap rho),
    generated.hard.map (renameEquation rho)⟩

def renameGeneratedPPats (rho : VariableRenaming)
    (generated : TypePM.Source.MatcherTyping.GeneratedPPats) :
    TypePM.Source.MatcherTyping.GeneratedPPats :=
  ⟨generated.holes.map (renameDual rho),
    generated.captures.map (renameTy rho),
    generated.hard.map (renameEquation rho)⟩

def renameGeneratedDPat (rho : VariableRenaming)
    (generated : TypePM.Source.MatcherTyping.GeneratedDPat) :
    TypePM.Source.MatcherTyping.GeneratedDPat :=
  ⟨generated.bindings.map (renameTy rho),
    generated.hard.map (renameEquation rho)⟩

def renameGeneratedDPats (rho : VariableRenaming)
    (generated : TypePM.Source.MatcherTyping.GeneratedDPats) :
    TypePM.Source.MatcherTyping.GeneratedDPats :=
  ⟨generated.bindings.map (renameTy rho),
    generated.hard.map (renameEquation rho)⟩

def renameGeneratedArms (rho : VariableRenaming)
    (generated : TypePM.Source.MatcherTyping.GeneratedArms) :
    TypePM.Source.MatcherTyping.GeneratedArms :=
  ⟨renameGeneratedChecks rho generated.checks⟩

def renameGeneratedMatcherClause (rho : VariableRenaming)
    (generated : TypePM.Source.MatcherTyping.GeneratedMatcherClause) :
    TypePM.Source.MatcherTyping.GeneratedMatcherClause :=
  ⟨generated.holes.map (renameDual rho),
    generated.evidence.map (renameCap rho),
    renameGeneratedChecks rho generated.checks⟩

def renameGeneratedMatcherClauses (rho : VariableRenaming)
    (generated : TypePM.Source.MatcherTyping.GeneratedMatcherClauses) :
    TypePM.Source.MatcherTyping.GeneratedMatcherClauses :=
  ⟨generated.evidences.map (renameCap rho),
    renameGeneratedChecks rho generated.checks⟩

end MatcherTyping

namespace MatchFirstTyping

def renameGeneratedTail (rho : VariableRenaming)
    (generated : TypePM.Source.MatchFirstTyping.GeneratedTail) :
    TypePM.Source.MatchFirstTyping.GeneratedTail :=
  ⟨generated.hard.map (renameEquation rho),
    generated.pending.map (renameObligation rho)⟩

def renameGeneratedArms (rho : VariableRenaming)
    (generated : TypePM.Source.MatchFirstTyping.GeneratedArms) :
    TypePM.Source.MatchFirstTyping.GeneratedArms :=
  ⟨renameTy rho generated.target,
    generated.hard.map (renameEquation rho),
    generated.pending.map (renameObligation rho)⟩

end MatchFirstTyping

@[simp] theorem renameTy_var_of_le
    {rho : VariableRenaming} {boundary : Supply} (fixed : rho.FixesAtOrAbove boundary)
    {index : TyVar} (above : boundary.ty ≤ index.index) :
    renameTy rho (.var index) = .var index := by
  simp [renameTy, VariableRenaming.substitution, Ty.apply, fixed.1 index above]

@[simp] theorem renameCap_var_of_le
    {rho : VariableRenaming} {boundary : Supply} (fixed : rho.FixesAtOrAbove boundary)
    {index : CapVar} (above : boundary.cap ≤ index.index) :
    renameCap rho (.var index) = .var index := by
  simp [renameCap, VariableRenaming.substitution, Cap.apply, fixed.2 index above]

theorem renameTy_eq_self_of_freshSupport
    {rho : VariableRenaming} {start finish : Supply} {target : Ty}
    (fixed : rho.FixesAtOrAbove start)
    (support : VariablesSupportProvenance [] start finish target.unificationVars) :
    renameTy rho target = target := by
  unfold renameTy
  calc
    target.apply rho.substitution = target.apply Subst.id := by
      apply Ty.apply_eq_of_agree target
      · intro index member
        have origin := support (.ty index)
          ((Ty.mem_tyVars_iff_unificationVars index target).mp member)
        rcases origin with impossible | fresh
        · have free : index ∈ Context.freeTyVars [] := by
            simpa [Context.unificationVars] using impossible
          have empty : index ∈ ([] : List TyVar) := by
            simpa [Context.freeTyVars] using mem_dedupFirst.mp free
          simp at empty
        · simp [VariableRenaming.substitution, Subst.id,
            fixed.1 index fresh.1]
      · intro index member
        have origin := support (.cap index)
          ((Ty.mem_capVars_iff_unificationVars index target).mp member)
        rcases origin with impossible | fresh
        · have free : index ∈ Context.freeCapVars [] := by
            simpa [Context.unificationVars] using impossible
          have empty : index ∈ ([] : List CapVar) := by
            simpa [Context.freeCapVars] using mem_dedupFirst.mp free
          simp at empty
        · simp [VariableRenaming.substitution, Subst.id,
            fixed.2 index fresh.1]
    _ = target := Ty.apply_id target

theorem renameCap_eq_self_of_freshSupport
    {rho : VariableRenaming} {start finish : Supply} {capability : Cap}
    (fixed : rho.FixesAtOrAbove start)
    (support : VariablesSupportProvenance [] start finish
      capability.unificationVars) :
    renameCap rho capability = capability := by
  unfold renameCap
  calc
    capability.apply rho.substitution.cap = capability.apply Subst.id.cap := by
      apply Cap.apply_eq_of_agree capability
      intro index member
      have origin := support (.cap index)
        ((Cap.mem_capVars_iff_unificationVars index capability).mp member)
      rcases origin with impossible | fresh
      · have free : index ∈ Context.freeCapVars [] := by
          simpa [Context.unificationVars] using impossible
        have empty : index ∈ ([] : List CapVar) := by
          simpa [Context.freeCapVars] using mem_dedupFirst.mp free
        simp at empty
      · simp [VariableRenaming.substitution, Subst.id,
          fixed.2 index fresh.1]
    _ = capability := Cap.apply_id capability

theorem renameDual_eq_self_of_freshSupport
    {rho : VariableRenaming} {start finish : Supply} {dual : Dual}
    (fixed : rho.FixesAtOrAbove start)
    (support : VariablesSupportProvenance [] start finish (dualVariables dual)) :
    renameDual rho dual = dual := by
  cases dual with
  | mk capability target =>
      have capFixed := renameCap_eq_self_of_freshSupport fixed
        (fun candidate member => support candidate
          (List.mem_append_left _ member))
      have tyFixed := renameTy_eq_self_of_freshSupport fixed
        (fun candidate member => support candidate
          (List.mem_append_right _ member))
      simp [renameDual, capFixed, tyFixed]

/-- Closed dual-scheme instantiation uses only the freshly allocated prefix,
so a renaming fixed from the instantiation supply leaves it literally fixed. -/
theorem DualScheme.instantiate_rename_eq
    {rho : VariableRenaming} {scheme : DualScheme} (closed : scheme.Closed)
    (supply : Supply) (fixed : rho.FixesAtOrAbove supply) :
    (scheme.instantiate supply).1.fields.map (renameDual rho) =
        (scheme.instantiate supply).1.fields ∧
      renameDual rho (scheme.instantiate supply).1.result =
        (scheme.instantiate supply).1.result := by
  have support := DualScheme.instantiate_support closed supply
  constructor
  · have eachFixed : ∀ dual ∈ (scheme.instantiate supply).1.fields,
        renameDual rho dual = dual := by
      intro dual member
      apply renameDual_eq_self_of_freshSupport fixed
      intro candidate candidateMember
      exact support candidate (by
        apply List.mem_append_left
        rw [dualUnificationVars, List.mem_flatMap]
        exact ⟨dual, member, candidateMember⟩)
    have mapFixed : ∀ (fields : List Dual),
        (∀ dual ∈ fields, renameDual rho dual = dual) →
          fields.map (renameDual rho) = fields := by
      intro fields allFixed
      induction fields with
      | nil => rfl
      | cons dual duals induction =>
          simp only [List.map_cons]
          rw [allFixed dual (by simp), induction]
          intro item member
          exact allFixed item (by simp [member])
    exact mapFixed _ eachFixed
  · apply renameDual_eq_self_of_freshSupport fixed
    intro candidate candidateMember
    exact support candidate (List.mem_append_right _ candidateMember)

theorem Scheme.instantiate_rename_eq
    {rho : VariableRenaming} {scheme : Scheme} (closed : scheme.Closed)
    (supply : Supply) (fixed : rho.FixesAtOrAbove supply) :
    renameTy rho (scheme.instantiate supply).1 =
      (scheme.instantiate supply).1 := by
  have instantiated := Scheme.instantiate_variableRenaming_prefix rho scheme
    (fixed.mapsFrom_self.mapsPrefix scheme.tyArity scheme.capArity)
  have closedFixed := Scheme.applyFree_eq_self_of_closed closed rho.substitution
  rw [closedFixed] at instantiated
  exact instantiated.symm

@[simp] theorem MatcherTyping.freshTargets_rename
    {rho : VariableRenaming} {supply : Supply}
    (fixed : rho.FixesAtOrAbove supply) (count : Nat) :
    (TypePM.Source.MatcherTyping.freshTargets supply count).map (renameTy rho) =
      TypePM.Source.MatcherTyping.freshTargets supply count := by
  simp [TypePM.Source.MatcherTyping.freshTargets, List.map_map,
    Function.comp_def, renameTy, VariableRenaming.substitution, Ty.apply,
    fixed.1]

@[simp] theorem Pattern.extendContext_rename
    (rho : VariableRenaming) (bindings : List Ty) (context : Context) :
    renameContext rho (Pattern.extendContext bindings context) =
      Pattern.extendContext (bindings.map (renameTy rho))
        (renameContext rho context) := by
  simp [Pattern.extendContext, renameContext, Context.applyFree,
    Scheme.mono, Scheme.applyFree, renameTy]

theorem Pattern.bindingEquations_rename
    (rho : VariableRenaming) : ∀ {left right checks},
    Pattern.bindingEquations left right = some checks →
      Pattern.bindingEquations (left.map (renameTy rho))
          (right.map (renameTy rho)) =
        some (checks.map (renameEquation rho)) := by
  intro left right checks equality
  induction left generalizing right checks with
  | nil =>
      cases right <;> simp [Pattern.bindingEquations] at equality ⊢
      simpa using equality
  | cons left lefts induction =>
      cases right with
      | nil => simp [Pattern.bindingEquations] at equality
      | cons right rights =>
          simp only [Pattern.bindingEquations] at equality
          cases tailEquality : Pattern.bindingEquations lefts rights with
          | none => simp [tailEquality] at equality
          | some tail =>
              simp [tailEquality] at equality
              subst checks
              simp [Pattern.bindingEquations, induction tailEquality,
                renameEquation, Equation.apply, renameTy]

@[simp] theorem Dual.capabilities_rename
    (rho : VariableRenaming) (duals : List Dual) :
    Dual.capabilities (duals.map (renameDual rho)) =
      (Dual.capabilities duals).map (renameCap rho) := by
  induction duals with
  | nil => rfl
  | cons dual duals induction =>
      simp [Dual.capabilities, renameDual]

@[simp] theorem Ty.applyList_renaming
    (rho : VariableRenaming) (items : List Ty) :
    Ty.applyList rho.substitution items = items.map (renameTy rho) := by
  induction items with
  | nil => rfl
  | cons item items induction =>
      simp [Ty.applyList, renameTy, induction]

@[simp] theorem Cap.applyList_renaming
    (rho : VariableRenaming) (items : List Cap) :
    Cap.applyList rho.substitution.cap items = items.map (renameCap rho) := by
  induction items with
  | nil => rfl
  | cons item items induction =>
      simp [Cap.applyList, renameCap, induction]

@[simp] theorem Dual.targets_rename
    (rho : VariableRenaming) (duals : List Dual) :
    Dual.targets (duals.map (renameDual rho)) =
      (Dual.targets duals).map (renameTy rho) := by
  induction duals with
  | nil => rfl
  | cons dual duals induction =>
      simp [Dual.targets, renameDual]

@[simp] theorem Pattern.dualEquations_rename
    (rho : VariableRenaming) (left right : Dual) :
    (Pattern.dualEquations left right).map (renameEquation rho) =
      Pattern.dualEquations (renameDual rho left) (renameDual rho right) := by
  simp [Pattern.dualEquations, renameDual, renameEquation, Equation.apply,
    renameTy, renameCap]

@[simp] theorem Pattern.fieldEquations_rename
    (rho : VariableRenaming) : ∀ (actual expected : List Dual),
    (Pattern.fieldEquations actual expected).map (renameEquation rho) =
      Pattern.fieldEquations (actual.map (renameDual rho))
        (expected.map (renameDual rho)) := by
  intro actual expected
  induction actual generalizing expected with
  | nil => simp [Pattern.fieldEquations]
  | cons actual actuals induction =>
      cases expected with
      | nil => simp [Pattern.fieldEquations]
      | cons expected expecteds =>
          simp [Pattern.fieldEquations, renameDual, renameEquation,
            Equation.apply, renameTy, renameCap]

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

mutual

/-- User-pattern synthesis commutes with a fresh-local renaming whenever its
embedded-expression callback does. -/
theorem PatternElaboratesUsing.rename
    {rho : VariableRenaming} {boundary : Supply}
    {left right : M4ExpressionElaborationRelation}
    (transport : ∀ {context expression supply generated next},
      boundary.Le supply →
      left context expression supply generated next →
        right (renameContext rho context) expression supply
          (renameGenerated rho generated) next)
    (increases : ∀ {context expression supply generated next},
      left context expression supply generated next → supply.Le next)
    (fixed : rho.FixesAtOrAbove boundary)
    {signature : FrozenSignature} (wellFormed : signature.WellFormed)
    {context arguments pattern bindings supply generated next}
    (boundaryToSupply : boundary.Le supply)
    (derivation : PatternElaboratesUsing left signature context arguments
      pattern bindings supply generated next) :
    PatternElaboratesUsing right signature (renameContext rho context)
      (arguments.map (renameDual rho)) pattern (bindings.map (renameTy rho))
      supply (renameGeneratedPattern rho generated) next := by
  cases derivation with
  | var =>
      have supplyFixed := fixed.mono boundaryToSupply
      simpa [renameGeneratedPattern, renameDual, renameTy, renameCap,
        renameEquation, renameObligation, VariableRenaming.substitution,
        Ty.apply, Cap.apply, supplyFixed.1, supplyFixed.2, List.map_append] using
        (PatternElaboratesUsing.var (ExpressionElaborates := right)
          (signature := signature) (context := renameContext rho context)
          (arguments := arguments.map (renameDual rho))
          (bindings := bindings.map (renameTy rho)) (supply := supply))
  | wild =>
      have supplyFixed := fixed.mono boundaryToSupply
      simpa [renameGeneratedPattern, renameDual, renameTy, renameCap,
        VariableRenaming.substitution, Ty.apply, Cap.apply,
        supplyFixed.1, supplyFixed.2] using
        (PatternElaboratesUsing.wild (ExpressionElaborates := right)
          (signature := signature) (context := renameContext rho context)
          (arguments := arguments.map (renameDual rho))
          (bindings := bindings.map (renameTy rho)) (supply := supply))
  | @value expression bindings supply generated afterExpression
      expressionElaboration =>
      have expressionTransport := transport boundaryToSupply expressionElaboration
      rw [Pattern.extendContext_rename] at expressionTransport
      have afterFixed := fixed.mono
        (Supply.le_trans boundaryToSupply (increases expressionElaboration))
      simpa [renameGeneratedPattern, renameDual, renameGenerated, renameTy,
        renameCap, VariableRenaming.substitution, Cap.apply,
        afterFixed.2] using
        (PatternElaboratesUsing.value expressionTransport)
  | @ctor constructor fields bindings supply scheme generatedFields next lookup
      arity fieldsElaboration =>
      have closed := Signature.WellFormed.patternConstructorClosed_of_lookup
        wellFormed.baseWellFormed lookup
      have supplyFixed := fixed.mono boundaryToSupply
      obtain ⟨fieldsFixed, resultFixed⟩ :=
        DualScheme.instantiate_rename_eq closed supply supplyFixed
      have boundaryToFields : boundary.Le (scheme.instantiate supply).2 := by
        exact Supply.le_trans boundaryToSupply (by
          simp [Supply.Le, DualScheme.instantiate])
      have fieldsTransport := PatternsElaborateUsing.rename transport increases
        fixed wellFormed boundaryToFields fieldsElaboration
      simpa [renameGeneratedPattern, renameGeneratedPatterns, resultFixed,
        fieldsFixed, List.map_append] using
        (PatternElaboratesUsing.ctor lookup arity fieldsTransport)
  | @tuple items bindings supply generatedItems next itemsElaboration =>
      have itemsTransport := PatternsElaborateUsing.rename transport increases
        fixed wellFormed boundaryToSupply itemsElaboration
      simpa [renameGeneratedPattern, renameGeneratedPatterns, renameDual,
        renameTy, renameCap, Ty.apply, Cap.apply, Ty.applyList,
        Cap.applyList] using
        (PatternElaboratesUsing.tuple itemsTransport)
  | @and leftPattern rightPattern bindings supply generatedLeft afterLeft
      generatedRight next leftElaboration rightElaboration =>
      have leftTransport := PatternElaboratesUsing.rename transport increases
        fixed wellFormed boundaryToSupply leftElaboration
      have boundaryToLeft := Supply.le_trans boundaryToSupply
        (PatternElaboratesUsing.supply_le_next increases leftElaboration)
      have rightTransport := PatternElaboratesUsing.rename transport increases
        fixed wellFormed boundaryToLeft rightElaboration
      simpa [renameGeneratedPattern, renameDual, List.map_append] using
        (PatternElaboratesUsing.and leftTransport rightTransport)
  | @or leftPattern rightPattern bindings supply generatedLeft afterLeft
      generatedRight next bindingChecks leftElaboration
      rightElaboration bindingsEqual =>
      have leftTransport := PatternElaboratesUsing.rename transport increases
        fixed wellFormed boundaryToSupply leftElaboration
      have boundaryToLeft := Supply.le_trans boundaryToSupply
        (PatternElaboratesUsing.supply_le_next increases leftElaboration)
      have rightTransport := PatternElaboratesUsing.rename transport increases
        fixed wellFormed boundaryToLeft rightElaboration
      have checksTransport := Pattern.bindingEquations_rename rho bindingsEqual
      simpa [renameGeneratedPattern, renameDual, List.map_append] using
        (PatternElaboratesUsing.or leftTransport rightTransport checksTransport)
  | @embed index bindings supply dual lookup =>
      have renamedLookup : (arguments.map (renameDual rho))[index]? =
          some (renameDual rho dual) := by
        simpa using congrArg (Option.map (renameDual rho)) lookup
      simpa [renameGeneratedPattern] using
        (PatternElaboratesUsing.embed renamedLookup)
  | @app function fields bindings supply scheme generatedFields next lookup arity
      fieldsElaboration =>
      have closed := FrozenSignature.lookupPatternFunction_closed wellFormed lookup
      have supplyFixed := fixed.mono boundaryToSupply
      obtain ⟨fieldsFixed, resultFixed⟩ :=
        DualScheme.instantiate_rename_eq closed supply supplyFixed
      have boundaryToFields : boundary.Le (scheme.instantiate supply).2 := by
        exact Supply.le_trans boundaryToSupply (by
          simp [Supply.Le, DualScheme.instantiate])
      have fieldsTransport := PatternsElaborateUsing.rename transport increases
        fixed wellFormed boundaryToFields fieldsElaboration
      simpa [renameGeneratedPattern, renameGeneratedPatterns, resultFixed,
        fieldsFixed, List.map_append] using
        (PatternElaboratesUsing.app lookup arity fieldsTransport)

/-- List counterpart of `PatternElaboratesUsing.rename`. -/
theorem PatternsElaborateUsing.rename
    {rho : VariableRenaming} {boundary : Supply}
    {left right : M4ExpressionElaborationRelation}
    (transport : ∀ {context expression supply generated next},
      boundary.Le supply →
      left context expression supply generated next →
        right (renameContext rho context) expression supply
          (renameGenerated rho generated) next)
    (increases : ∀ {context expression supply generated next},
      left context expression supply generated next → supply.Le next)
    (fixed : rho.FixesAtOrAbove boundary)
    {signature : FrozenSignature} (wellFormed : signature.WellFormed)
    {context arguments patterns bindings supply generated next}
    (boundaryToSupply : boundary.Le supply)
    (derivation : PatternsElaborateUsing left signature context arguments
      patterns bindings supply generated next) :
    PatternsElaborateUsing right signature (renameContext rho context)
      (arguments.map (renameDual rho)) patterns (bindings.map (renameTy rho))
      supply (renameGeneratedPatterns rho generated) next := by
  cases derivation with
  | nil => exact .nil
  | @cons pattern patterns bindings supply generatedPattern afterPattern
      generatedPatterns next head tail =>
      have headTransport := PatternElaboratesUsing.rename transport increases
        fixed wellFormed boundaryToSupply head
      have boundaryToPattern := Supply.le_trans boundaryToSupply
        (PatternElaboratesUsing.supply_le_next increases head)
      have tailTransport := PatternsElaborateUsing.rename transport increases
        fixed wellFormed boundaryToPattern tail
      simpa [renameGeneratedPatterns, renameGeneratedPattern, List.map_append]
        using (PatternsElaborateUsing.cons headTransport tailTransport)

end

/-- A fuel leaf paired with well-formedness of its callback context. -/
def WellFormedFuelLeaf (signature : FrozenSignature) (fuel : Nat) :
    M4ExpressionElaborationRelation :=
  fun context expression start generated finish =>
    start.WellFormedFor context ∧
      M4.ElaboratesFuel signature fuel context expression start generated finish

mutual

theorem PatternElaboratesUsing.trackContextSupportEarly
    {signature : FrozenSignature} (wellFormed : signature.WellFormed)
    {fuel : Nat} {context : Context} {outerStart start finish : Supply}
    {arguments : PatternContext} {pattern : Pattern} {bindings : List Ty}
    {generated : GeneratedPattern}
    (contextWellFormed : outerStart.WellFormedFor context)
    (argumentsSupport : VariablesSupportProvenance context outerStart start
      (dualUnificationVars arguments))
    (bindingsSupport : VariablesSupportProvenance context outerStart start
      (Ty.unificationVarsList bindings))
    (outerToStart : outerStart.Le start)
    (derivation : PatternElaboratesUsing (M4.ElaboratesFuel signature fuel)
      signature context arguments pattern bindings start generated finish) :
    PatternElaboratesUsing (WellFormedFuelLeaf signature fuel) signature context
      arguments pattern bindings start generated finish := by
  cases derivation with
  | var => exact .var
  | wild => exact .wild
  | @value expression bindings start generated afterExpression expressionElaboration =>
      have extendedSupport := Pattern.extendContext_support bindingsSupport
      exact .value ⟨Supply.WellFormedFor.of_contextSupport contextWellFormed
        outerToStart extendedSupport, expressionElaboration⟩
  | @ctor constructor fields bindings start scheme generatedFields finish lookup
      arity fieldsElaboration =>
      have startToFields : start.Le (scheme.instantiate start).2 := by
        simp [Supply.Le, DualScheme.instantiate]
      exact .ctor lookup arity
        (PatternsElaborateUsing.trackContextSupportEarly wellFormed
          contextWellFormed (argumentsSupport.extend_finish startToFields)
          (bindingsSupport.extend_finish startToFields)
          (Supply.le_trans outerToStart startToFields) fieldsElaboration)
  | @tuple items bindings start generatedItems finish itemsElaboration =>
      exact .tuple (PatternsElaborateUsing.trackContextSupportEarly wellFormed
        contextWellFormed argumentsSupport bindingsSupport outerToStart
        itemsElaboration)
  | @and left right bindings start generatedLeft afterLeft generatedRight finish
      leftElaboration rightElaboration =>
      have startToLeft := PatternElaboratesUsing.supply_le_next
        (fun {context expression start generated finish}
          (child : M4.ElaboratesFuel signature fuel context expression start
            generated finish) => child.supply_le_next) leftElaboration
      have leftSupport := leftElaboration.supportProvenance wellFormed
        (fun {context expression start generated finish}
          (child : M4.ElaboratesFuel signature fuel context expression start
            generated finish) => child.supply_le_next)
        (fun {context expression start generated finish}
          (child : M4.ElaboratesFuel signature fuel context expression start
            generated finish) => child.supportProvenance wellFormed)
        argumentsSupport bindingsSupport outerToStart
      have leftBindings : VariablesSupportProvenance context outerStart
          afterLeft (Ty.unificationVarsList generatedLeft.bindings) := by
        intro candidate member
        exact leftSupport candidate (by
          simp [GeneratedPattern.unificationVars, member])
      exact .and
        (PatternElaboratesUsing.trackContextSupportEarly wellFormed
          contextWellFormed argumentsSupport bindingsSupport outerToStart
          leftElaboration)
        (PatternElaboratesUsing.trackContextSupportEarly wellFormed
          contextWellFormed (argumentsSupport.extend_finish startToLeft)
          leftBindings (Supply.le_trans outerToStart startToLeft)
          rightElaboration)
  | @or left right bindings start generatedLeft afterLeft generatedRight finish
      bindingChecks leftElaboration rightElaboration bindingsEqual =>
      have startToLeft := PatternElaboratesUsing.supply_le_next
        (fun {context expression start generated finish}
          (child : M4.ElaboratesFuel signature fuel context expression start
            generated finish) => child.supply_le_next) leftElaboration
      exact .or
        (PatternElaboratesUsing.trackContextSupportEarly wellFormed
          contextWellFormed argumentsSupport bindingsSupport outerToStart
          leftElaboration)
        (PatternElaboratesUsing.trackContextSupportEarly wellFormed
          contextWellFormed (argumentsSupport.extend_finish startToLeft)
          (bindingsSupport.extend_finish startToLeft)
          (Supply.le_trans outerToStart startToLeft) rightElaboration)
        bindingsEqual
  | embed lookup => exact .embed lookup
  | @app function fields bindings start scheme generatedFields finish lookup
      arity fieldsElaboration =>
      have startToFields : start.Le (scheme.instantiate start).2 := by
        simp [Supply.Le, DualScheme.instantiate]
      exact .app lookup arity
        (PatternsElaborateUsing.trackContextSupportEarly wellFormed
          contextWellFormed (argumentsSupport.extend_finish startToFields)
          (bindingsSupport.extend_finish startToFields)
          (Supply.le_trans outerToStart startToFields) fieldsElaboration)
termination_by pattern.complexity * 2 + 1
decreasing_by
  all_goals simp_wf
  all_goals subst_vars
  all_goals simp
  all_goals omega

theorem PatternsElaborateUsing.trackContextSupportEarly
    {signature : FrozenSignature} (wellFormed : signature.WellFormed)
    {fuel : Nat} {context : Context} {outerStart start finish : Supply}
    {arguments : PatternContext} {patterns : List Pattern} {bindings : List Ty}
    {generated : GeneratedPatterns}
    (contextWellFormed : outerStart.WellFormedFor context)
    (argumentsSupport : VariablesSupportProvenance context outerStart start
      (dualUnificationVars arguments))
    (bindingsSupport : VariablesSupportProvenance context outerStart start
      (Ty.unificationVarsList bindings))
    (outerToStart : outerStart.Le start)
    (derivation : PatternsElaborateUsing (M4.ElaboratesFuel signature fuel)
      signature context arguments patterns bindings start generated finish) :
    PatternsElaborateUsing (WellFormedFuelLeaf signature fuel) signature context
      arguments patterns bindings start generated finish := by
  cases derivation with
  | nil => exact .nil
  | @cons pattern patterns bindings start generatedPattern afterPattern
      generatedPatterns finish head tail =>
      have startToPattern := PatternElaboratesUsing.supply_le_next
        (fun {context expression start generated finish}
          (child : M4.ElaboratesFuel signature fuel context expression start
            generated finish) => child.supply_le_next) head
      have headSupport := head.supportProvenance wellFormed
        (fun {context expression start generated finish}
          (child : M4.ElaboratesFuel signature fuel context expression start
            generated finish) => child.supply_le_next)
        (fun {context expression start generated finish}
          (child : M4.ElaboratesFuel signature fuel context expression start
            generated finish) => child.supportProvenance wellFormed)
        argumentsSupport bindingsSupport outerToStart
      have outputBindings : VariablesSupportProvenance context outerStart
          afterPattern (Ty.unificationVarsList generatedPattern.bindings) := by
        intro candidate member
        exact headSupport candidate (by
          simp [GeneratedPattern.unificationVars, member])
      exact .cons
        (PatternElaboratesUsing.trackContextSupportEarly wellFormed
          contextWellFormed argumentsSupport bindingsSupport outerToStart head)
        (PatternsElaborateUsing.trackContextSupportEarly wellFormed
          contextWellFormed (argumentsSupport.extend_finish startToPattern)
          outputBindings (Supply.le_trans outerToStart startToPattern) tail)
termination_by Pattern.listComplexity patterns * 2
decreasing_by
  all_goals simp_wf
  all_goals subst_vars
  all_goals simp [Pattern.listComplexity]
  all_goals omega

end

/-- Add well-formed-context evidence to every recursive leaf of `matchAll`. -/
theorem MatchAllElaboratesUsing.trackContextSupport
    {signature : FrozenSignature} (wellFormed : signature.WellFormed)
    {fuel : Nat} {context : Context} {target matcher body : Expr}
    {pattern : Pattern} {start finish : Supply} {generated : Generated}
    (contextWellFormed : start.WellFormedFor context)
    (derivation : MatchAllElaboratesUsing (M4.ElaboratesFuel signature fuel)
      signature context target matcher pattern body start generated finish) :
    MatchAllElaboratesUsing (WellFormedFuelLeaf signature fuel) signature context
      target matcher pattern body start generated finish := by
  cases derivation with
  | @mk generatedTarget afterTarget generatedPattern afterPattern
      generatedMatcher afterMatcher generatedBody finish targetElaboration
      patternElaboration matcherElaboration bodyElaboration =>
      have startToTarget := targetElaboration.supply_le_next
      have targetToPattern := patternElaboration.supply_le_next
        (fun {context expression start generated finish}
          (child : M4.ElaboratesFuel signature fuel context expression start
            generated finish) => child.supply_le_next)
      have patternToMatcher := matcherElaboration.supply_le_next
      have emptyArguments : VariablesSupportProvenance context start afterTarget
          (dualUnificationVars []) := by
        intro candidate member
        simp [dualUnificationVars] at member
      have emptyBindings : VariablesSupportProvenance context start afterTarget
          (Ty.unificationVarsList []) := by
        intro candidate member
        simp [Ty.unificationVarsList] at member
      have trackedPattern := PatternElaboratesUsing.trackContextSupportEarly wellFormed
        contextWellFormed emptyArguments emptyBindings startToTarget
        patternElaboration
      have patternSupport := patternElaboration.supportProvenance wellFormed
        (fun {context expression start generated finish}
          (child : M4.ElaboratesFuel signature fuel context expression start
            generated finish) => child.supply_le_next)
        (fun {context expression start generated finish}
          (child : M4.ElaboratesFuel signature fuel context expression start
            generated finish) => child.supportProvenance wellFormed)
        emptyArguments emptyBindings startToTarget
      have bindingsSupport : VariablesSupportProvenance context start afterPattern
          (Ty.unificationVarsList generatedPattern.bindings) := by
        intro candidate member
        exact patternSupport candidate (by
          simp [GeneratedPattern.unificationVars, member])
      have bodyContextSupport :=
        (Pattern.extendContext_support bindingsSupport).extend_finish
          patternToMatcher
      have startToMatcher := Supply.le_trans startToTarget
        (Supply.le_trans targetToPattern patternToMatcher)
      have bodyContextWellFormed := Supply.WellFormedFor.of_contextSupport
        contextWellFormed startToMatcher bodyContextSupport
      exact .mk ⟨contextWellFormed, targetElaboration⟩ trackedPattern
        ⟨contextWellFormed.mono
          (Supply.le_trans startToTarget targetToPattern), matcherElaboration⟩
        ⟨bodyContextWellFormed, bodyElaboration⟩

mutual

/-- Add well-formed-context evidence to every recursive leaf of later
single-result match arms. -/
theorem MatchFirstTyping.TailElaboratesUsing.trackContextSupport
    {signature : FrozenSignature} (wellFormed : signature.WellFormed)
    {fuel : Nat} {context : Context} {targetType matcherType expectedResult : Ty}
    {arms : List MatchFirstArm} {start finish : Supply}
    {generated : TypePM.Source.MatchFirstTyping.GeneratedTail}
    (contextWellFormed : start.WellFormedFor context)
    (derivation : TypePM.Source.MatchFirstTyping.TailElaboratesUsing
      (M4.ElaboratesFuel signature fuel) signature context targetType matcherType
      expectedResult arms start generated finish) :
    TypePM.Source.MatchFirstTyping.TailElaboratesUsing
      (WellFormedFuelLeaf signature fuel) signature context targetType matcherType
      expectedResult arms start generated finish := by
  induction derivation with
  | nil => exact .nil
  | @cons pattern body arms start generatedPattern afterPattern generatedBody
      afterBody generatedTail finish patternElaboration bodyElaboration
      tailElaboration tailInduction =>
      have emptyArguments : VariablesSupportProvenance context start start
          (dualUnificationVars []) := by
        intro candidate member
        simp [dualUnificationVars] at member
      have emptyBindings : VariablesSupportProvenance context start start
          (Ty.unificationVarsList []) := by
        intro candidate member
        simp [Ty.unificationVarsList] at member
      have patternToBody := PatternElaboratesUsing.supply_le_next
        (fun {context expression start generated finish}
          (child : M4.ElaboratesFuel signature fuel context expression start
            generated finish) => child.supply_le_next) patternElaboration
      have patternSupport := patternElaboration.supportProvenance wellFormed
        (fun {context expression start generated finish}
          (child : M4.ElaboratesFuel signature fuel context expression start
            generated finish) => child.supply_le_next)
        (fun {context expression start generated finish}
          (child : M4.ElaboratesFuel signature fuel context expression start
            generated finish) => child.supportProvenance wellFormed)
        emptyArguments emptyBindings (Supply.le_refl start)
      have bindingsSupport : VariablesSupportProvenance context start afterPattern
          (Ty.unificationVarsList generatedPattern.bindings) := by
        intro candidate member
        exact patternSupport candidate (by
          simp [GeneratedPattern.unificationVars, member])
      have bodyContextWellFormed := Supply.WellFormedFor.of_contextSupport
        contextWellFormed patternToBody
        (Pattern.extendContext_support bindingsSupport)
      have bodyToTail := bodyElaboration.supply_le_next
      exact .cons
        (PatternElaboratesUsing.trackContextSupportEarly wellFormed contextWellFormed
          emptyArguments emptyBindings (Supply.le_refl start)
          patternElaboration)
        ⟨bodyContextWellFormed, bodyElaboration⟩
        (tailInduction (contextWellFormed.mono
          (Supply.le_trans patternToBody bodyToTail)))

/-- Add well-formed-context evidence to the fallback and every ordinary arm. -/
theorem MatchFirstTyping.ArmsElaborateUsing.trackContextSupport
    {signature : FrozenSignature} (wellFormed : signature.WellFormed)
    {fuel : Nat} {context : Context} {targetType matcherType : Ty}
    {fallback : Expr} {arms : List MatchFirstArm} {start finish : Supply}
    {generated : TypePM.Source.MatchFirstTyping.GeneratedArms}
    (contextWellFormed : start.WellFormedFor context)
    (derivation : TypePM.Source.MatchFirstTyping.ArmsElaborateUsing
      (M4.ElaboratesFuel signature fuel) signature context targetType matcherType
      fallback arms start generated finish) :
    TypePM.Source.MatchFirstTyping.ArmsElaborateUsing
      (WellFormedFuelLeaf signature fuel) signature context targetType matcherType
      fallback arms start generated finish := by
  cases derivation with
  | fromFallback fallbackElaboration armsElaboration =>
      have startToFallback := fallbackElaboration.supply_le_next
      exact .fromFallback ⟨contextWellFormed, fallbackElaboration⟩
        (MatchFirstTyping.TailElaboratesUsing.trackContextSupport wellFormed
          (contextWellFormed.mono startToFallback) armsElaboration)

end

/-- Add well-formed-context evidence to every recursive leaf of a complete
single-result match. -/
theorem MatchFirstTyping.ElaboratesUsing.trackContextSupport
    {signature : FrozenSignature} (wellFormed : signature.WellFormed)
    {fuel : Nat} {context : Context} {expression : Expr}
    {start finish : Supply} {generated : Generated}
    (contextWellFormed : start.WellFormedFor context)
    (derivation : TypePM.Source.MatchFirstTyping.ElaboratesUsing
      (M4.ElaboratesFuel signature fuel) signature context expression start
      generated finish) :
    TypePM.Source.MatchFirstTyping.ElaboratesUsing
      (WellFormedFuelLeaf signature fuel) signature context expression start
      generated finish := by
  cases derivation with
  | @matchFirst target matcher arms fallback start generatedTarget afterTarget
      generatedMatcher afterMatcher generatedArms finish
      targetElaboration matcherElaboration armsElaboration =>
      have startToTarget := targetElaboration.supply_le_next
      have targetToMatcher := matcherElaboration.supply_le_next
      exact .matchFirst ⟨contextWellFormed, targetElaboration⟩
        ⟨contextWellFormed.mono startToTarget, matcherElaboration⟩
        (MatchFirstTyping.ArmsElaborateUsing.trackContextSupport wellFormed
          (contextWellFormed.mono
            (Supply.le_trans startToTarget targetToMatcher)) armsElaboration)

theorem MatcherTyping.CheckedExpressionElaboratesUsing.trackContextSupport
    {signature : FrozenSignature} {fuel : Nat} {context : Context}
    {expression : Expr} {expected : Ty} {start finish : Supply}
    {generated : TypePM.Source.MatcherTyping.GeneratedChecks}
    (contextWellFormed : start.WellFormedFor context)
    (derivation : TypePM.Source.MatcherTyping.CheckedExpressionElaboratesUsing
      (M4.ElaboratesFuel signature fuel) context expression expected start
      generated finish) :
    TypePM.Source.MatcherTyping.CheckedExpressionElaboratesUsing
      (WellFormedFuelLeaf signature fuel) context expression expected start
      generated finish := by
  cases derivation with
  | mk child => exact .mk ⟨contextWellFormed, child⟩

theorem MatcherTyping.NextMatcherItemsElaborateUsing.trackContextSupport
    {signature : FrozenSignature} {fuel : Nat} {context : Context}
    {items : List Expr} {holes : List Dual} {start finish : Supply}
    {generated : TypePM.Source.MatcherTyping.GeneratedChecks}
    (contextWellFormed : start.WellFormedFor context)
    (derivation : TypePM.Source.MatcherTyping.NextMatcherItemsElaborateUsing
      (M4.ElaboratesFuel signature fuel) context items holes start generated finish) :
    TypePM.Source.MatcherTyping.NextMatcherItemsElaborateUsing
      (WellFormedFuelLeaf signature fuel) context items holes start generated
      finish := by
  induction derivation with
  | nil => exact .nil
  | cons head tail induction =>
      exact .cons
        (MatcherTyping.CheckedExpressionElaboratesUsing.trackContextSupport
          contextWellFormed head)
        (induction (contextWellFormed.mono
          (head.supply_le_next (fun child => child.supply_le_next))))

theorem MatcherTyping.NextMatchersElaborateUsing.trackContextSupport
    {signature : FrozenSignature} {fuel : Nat} {context : Context}
    {expression : Expr} {holes : List Dual} {start finish : Supply}
    {generated : TypePM.Source.MatcherTyping.GeneratedChecks}
    (contextWellFormed : start.WellFormedFor context)
    (derivation : TypePM.Source.MatcherTyping.NextMatchersElaborateUsing
      (M4.ElaboratesFuel signature fuel) context expression holes start generated
      finish) :
    TypePM.Source.MatcherTyping.NextMatchersElaborateUsing
      (WellFormedFuelLeaf signature fuel) context expression holes start generated
      finish := by
  cases derivation with
  | zero checked =>
      exact TypePM.Source.MatcherTyping.NextMatchersElaborateUsing.zero
        (MatcherTyping.CheckedExpressionElaboratesUsing.trackContextSupport
          contextWellFormed checked)
  | one checked =>
      exact TypePM.Source.MatcherTyping.NextMatchersElaborateUsing.one
        (MatcherTyping.CheckedExpressionElaboratesUsing.trackContextSupport
          contextWellFormed checked)
  | many components =>
      exact TypePM.Source.MatcherTyping.NextMatchersElaborateUsing.many
        (MatcherTyping.NextMatcherItemsElaborateUsing.trackContextSupport
          contextWellFormed components)

theorem MatcherTyping.MatcherArmElaboratesUsing.trackContextSupport
    {signature : FrozenSignature} (wellFormed : signature.WellFormed)
    {fuel : Nat} {context : Context} {captures : List Ty}
    {matcherTarget : Ty} {holes : List Dual} {arm : MatcherArm}
    {outerStart start finish : Supply}
    {generated : TypePM.Source.MatcherTyping.GeneratedChecks}
    (contextWellFormed : outerStart.WellFormedFor context)
    (capturesSupport : VariablesSupportProvenance context outerStart start
      (Ty.unificationVarsList captures))
    (targetSupport : VariablesSupportProvenance context outerStart start
      matcherTarget.unificationVars)
    (outerToStart : outerStart.Le start)
    (derivation : TypePM.Source.MatcherTyping.MatcherArmElaboratesUsing
      (M4.ElaboratesFuel signature fuel) MatcherTyping.DPatElaborates signature
      context captures matcherTarget holes arm start generated finish) :
    TypePM.Source.MatcherTyping.MatcherArmElaboratesUsing
      (WellFormedFuelLeaf signature fuel) MatcherTyping.DPatElaborates signature
      context captures matcherTarget holes arm start generated finish := by
  cases derivation with
  | @mk header body start generatedHeader afterHeader generatedBody finish
      headerElaboration bodyElaboration =>
      have startToHeader := headerElaboration.supply_le_next
      have headerSupport := headerElaboration.supportProvenance wellFormed
        targetSupport outerToStart
      have bindingsSupport : VariablesSupportProvenance context outerStart
          afterHeader (Ty.unificationVarsList generatedHeader.bindings) := by
        intro candidate member
        exact headerSupport candidate (by
          simp [MatcherTyping.GeneratedDPat.unificationVars, member])
      have capturesContext := Pattern.extendContext_support capturesSupport
      have bindingsInCaptured :=
        TypePM.Source.MatcherTyping.VariablesSupportProvenance.extend_context captures
          bindingsSupport
      have localBodyContext := Pattern.extendContext_support bindingsInCaptured
      have bodyContextSupport : VariablesSupportProvenance context outerStart
          afterHeader
          (Pattern.extendContext generatedHeader.bindings
            (Pattern.extendContext captures context)).unificationVars := by
        intro candidate member
        rcases localBodyContext candidate member with captured | fresh
        · exact (capturesContext.extend_finish startToHeader) candidate captured
        · exact Or.inr fresh
      have bodyContextWellFormed := Supply.WellFormedFor.of_contextSupport
        contextWellFormed (Supply.le_trans outerToStart startToHeader)
        bodyContextSupport
      exact .mk headerElaboration
        (MatcherTyping.CheckedExpressionElaboratesUsing.trackContextSupport
          bodyContextWellFormed bodyElaboration)

theorem MatcherTyping.MatcherArmsElaborateUsing.trackContextSupport
    {signature : FrozenSignature} (wellFormed : signature.WellFormed)
    {fuel : Nat} {context : Context} {captures : List Ty}
    {matcherTarget : Ty} {holes : List Dual} {arms : List MatcherArm}
    {outerStart start finish : Supply}
    {generated : TypePM.Source.MatcherTyping.GeneratedArms}
    (contextWellFormed : outerStart.WellFormedFor context)
    (capturesSupport : VariablesSupportProvenance context outerStart start
      (Ty.unificationVarsList captures))
    (targetSupport : VariablesSupportProvenance context outerStart start
      matcherTarget.unificationVars)
    (outerToStart : outerStart.Le start)
    (derivation : TypePM.Source.MatcherTyping.MatcherArmsElaborateUsing
      (M4.ElaboratesFuel signature fuel) MatcherTyping.DPatElaborates signature
      context captures matcherTarget holes arms start generated finish) :
    TypePM.Source.MatcherTyping.MatcherArmsElaborateUsing
      (WellFormedFuelLeaf signature fuel) MatcherTyping.DPatElaborates signature
      context captures matcherTarget holes arms start generated finish := by
  induction derivation with
  | nil => exact .nil
  | @cons arm arms start generatedArm afterArm generatedArms finish head tail
      induction =>
      have startToArm := head.supply_le_next
        (fun child => child.supply_le_next)
        MatcherTyping.DPatElaborates.supply_le_next
      exact .cons
        (MatcherTyping.MatcherArmElaboratesUsing.trackContextSupport wellFormed
          contextWellFormed capturesSupport targetSupport outerToStart head)
        (induction (capturesSupport.extend_finish startToArm)
          (targetSupport.extend_finish startToArm)
          (Supply.le_trans outerToStart startToArm))

theorem MatcherTyping.MatcherClauseElaboratesUsing.trackContextSupport
    {signature : FrozenSignature} (wellFormed : signature.WellFormed)
    {fuel : Nat} {context : Context} {matcherTarget : Ty}
    {clause : MatcherClause} {outerStart start finish : Supply}
    {generated : TypePM.Source.MatcherTyping.GeneratedMatcherClause}
    (contextWellFormed : outerStart.WellFormedFor context)
    (targetSupport : VariablesSupportProvenance context outerStart start
      matcherTarget.unificationVars)
    (outerToStart : outerStart.Le start)
    (derivation : TypePM.Source.MatcherTyping.MatcherClauseElaboratesUsing
      (M4.ElaboratesFuel signature fuel) MatcherTyping.PPatElaborates
      MatcherTyping.DPatElaborates signature context matcherTarget clause start
      generated finish) :
    TypePM.Source.MatcherTyping.MatcherClauseElaboratesUsing
      (WellFormedFuelLeaf signature fuel) MatcherTyping.PPatElaborates
      MatcherTyping.DPatElaborates signature context matcherTarget clause start
      generated finish := by
  cases derivation with
  | @mk header nextMatchers arms start generatedHeader afterHeader generatedNext
      afterNext generatedArms finish shape headerElaboration nextElaboration
      armsElaboration =>
      have startToHeader := headerElaboration.supply_le_next
      have headerSupport := headerElaboration.supportProvenance
        (expectedCapability := none) wellFormed
        targetSupport (VariablesSupportProvenance.nil context outerStart start)
        outerToStart
      have holesSupport : VariablesSupportProvenance context outerStart
          afterHeader (dualUnificationVars generatedHeader.holes) := by
        intro candidate member
        exact headerSupport candidate (by
          simp [MatcherTyping.GeneratedPPat.unificationVars, member])
      have capturesSupport : VariablesSupportProvenance context outerStart
          afterHeader (Ty.unificationVarsList generatedHeader.captures) := by
        intro candidate member
        exact headerSupport candidate (by
          simp [MatcherTyping.GeneratedPPat.unificationVars, member])
      have capturedContextSupport := Pattern.extendContext_support capturesSupport
      have capturedContextWellFormed := Supply.WellFormedFor.of_contextSupport
        contextWellFormed (Supply.le_trans outerToStart startToHeader)
        capturedContextSupport
      have trackedNext :=
        MatcherTyping.NextMatchersElaborateUsing.trackContextSupport
          capturedContextWellFormed nextElaboration
      have headerToNext := nextElaboration.supply_le_next
        (fun {context expression start generated finish}
          (child : M4.ElaboratesFuel signature fuel context expression start
            generated finish) => child.supply_le_next)
      exact .mk shape headerElaboration trackedNext
        (MatcherTyping.MatcherArmsElaborateUsing.trackContextSupport wellFormed
          contextWellFormed (capturesSupport.extend_finish headerToNext)
          (targetSupport.extend_finish
            (Supply.le_trans startToHeader headerToNext))
          (Supply.le_trans outerToStart
            (Supply.le_trans startToHeader headerToNext)) armsElaboration)

theorem MatcherTyping.MatcherClausesElaborateUsing.trackContextSupport
    {signature : FrozenSignature} (wellFormed : signature.WellFormed)
    {fuel : Nat} {context : Context} {matcherTarget : Ty}
    {clauses : List MatcherClause} {outerStart start finish : Supply}
    {generated : TypePM.Source.MatcherTyping.GeneratedMatcherClauses}
    (contextWellFormed : outerStart.WellFormedFor context)
    (targetSupport : VariablesSupportProvenance context outerStart start
      matcherTarget.unificationVars)
    (outerToStart : outerStart.Le start)
    (derivation : TypePM.Source.MatcherTyping.MatcherClausesElaborateUsing
      (M4.ElaboratesFuel signature fuel) MatcherTyping.PPatElaborates
      MatcherTyping.DPatElaborates signature context matcherTarget clauses start
      generated finish) :
    TypePM.Source.MatcherTyping.MatcherClausesElaborateUsing
      (WellFormedFuelLeaf signature fuel) MatcherTyping.PPatElaborates
      MatcherTyping.DPatElaborates signature context matcherTarget clauses start
      generated finish := by
  induction derivation with
  | nil => exact .nil
  | @cons clause clauses start generatedClause afterClause generatedClauses finish
      head tail induction =>
      have startToClause := head.supply_le_next
        (fun {context expression start generated finish}
          (child : M4.ElaboratesFuel signature fuel context expression start
            generated finish) => child.supply_le_next)
        MatcherTyping.PPatElaborates.supply_le_next
        MatcherTyping.DPatElaborates.supply_le_next
      exact .cons
        (MatcherTyping.MatcherClauseElaboratesUsing.trackContextSupport
          wellFormed contextWellFormed targetSupport outerToStart head)
        (induction (targetSupport.extend_finish startToClause)
          (Supply.le_trans outerToStart startToClause))

theorem MatcherTyping.MatcherLiteralElaboratesUsing.trackContextSupport
    {signature : FrozenSignature} (wellFormed : signature.WellFormed)
    {fuel : Nat} {context : Context} {clauses : List MatcherClause}
    {start finish : Supply} {generated : Generated}
    (contextWellFormed : start.WellFormedFor context)
    (derivation : TypePM.Source.MatcherTyping.MatcherLiteralElaboratesUsing
      (M4.ElaboratesFuel signature fuel) MatcherTyping.PPatElaborates
      MatcherTyping.DPatElaborates signature context clauses start generated
      finish) :
    TypePM.Source.MatcherTyping.MatcherLiteralElaboratesUsing
      (WellFormedFuelLeaf signature fuel) MatcherTyping.PPatElaborates
      MatcherTyping.DPatElaborates signature context clauses start generated
      finish := by
  cases derivation with
  | @mk generatedClauses finish checked clausesElaboration =>
      let afterRoot : Supply := ⟨start.ty + 1, start.cap + 1⟩
      have startToRoot : start.Le afterRoot := by
        simp [afterRoot, Supply.Le]
      have targetSupport : VariablesSupportProvenance context start afterRoot
          (Ty.unificationVars (.var ⟨start.ty⟩)) := by
        exact (TypePM.Source.freshTy_support context start).extend_finish (by
          simp [afterRoot, Supply.Le, Supply.nextTy])
      exact .mk checked
        (MatcherTyping.MatcherClausesElaborateUsing.trackContextSupport
          wellFormed contextWellFormed targetSupport startToRoot
          clausesElaboration)

/-- Matcher callbacks also remember that their starting supply lies after the
literal's root.  This is the second invariant needed to weaken a fresh-fixing
renaming before applying the fuel induction hypothesis. -/
def ScopedWellFormedFuelLeaf (signature : FrozenSignature) (fuel : Nat)
    (boundary : Supply) : M4ExpressionElaborationRelation :=
  fun context expression start generated finish =>
    boundary.Le start ∧ WellFormedFuelLeaf signature fuel context expression
      start generated finish

def MatcherTyping.ScopedPPatElaborates (rootSignature : FrozenSignature)
    (boundary : Supply) :
    MatcherTyping.PPatElaborationRelation :=
  fun signature pattern expected capability start generated finish =>
    signature = rootSignature ∧ boundary.Le start ∧
      MatcherTyping.PPatElaborates signature pattern expected capability start
        generated finish

def MatcherTyping.ScopedDPatElaborates (rootSignature : FrozenSignature)
    (boundary : Supply) :
    MatcherTyping.DPatElaborationRelation :=
  fun signature pattern expected start generated finish =>
    signature = rootSignature ∧ boundary.Le start ∧
      MatcherTyping.DPatElaborates signature pattern expected start generated finish

theorem MatcherTyping.CheckedExpressionElaboratesUsing.trackBoundary
    {signature : FrozenSignature} {fuel : Nat} {boundary : Supply}
    {context : Context} {expression : Expr} {expected : Ty}
    {start finish : Supply}
    {generated : TypePM.Source.MatcherTyping.GeneratedChecks}
    (boundaryToStart : boundary.Le start)
    (derivation : TypePM.Source.MatcherTyping.CheckedExpressionElaboratesUsing
      (WellFormedFuelLeaf signature fuel) context expression expected start
      generated finish) :
    TypePM.Source.MatcherTyping.CheckedExpressionElaboratesUsing
      (ScopedWellFormedFuelLeaf signature fuel boundary) context expression
      expected start generated finish := by
  cases derivation with
  | mk child => exact .mk ⟨boundaryToStart, child⟩

theorem MatcherTyping.NextMatcherItemsElaborateUsing.trackBoundary
    {signature : FrozenSignature} {fuel : Nat} {boundary : Supply}
    {context : Context} {items : List Expr} {holes : List Dual}
    {start finish : Supply}
    {generated : TypePM.Source.MatcherTyping.GeneratedChecks}
    (boundaryToStart : boundary.Le start)
    (derivation : TypePM.Source.MatcherTyping.NextMatcherItemsElaborateUsing
      (WellFormedFuelLeaf signature fuel) context items holes start generated
      finish) :
    TypePM.Source.MatcherTyping.NextMatcherItemsElaborateUsing
      (ScopedWellFormedFuelLeaf signature fuel boundary) context items holes
      start generated finish := by
  induction derivation with
  | nil => exact .nil
  | cons head tail induction =>
      have startToHead := head.supply_le_next
        (fun child => child.2.supply_le_next)
      exact .cons
        (MatcherTyping.CheckedExpressionElaboratesUsing.trackBoundary
          boundaryToStart head)
        (induction (Supply.le_trans boundaryToStart startToHead))

theorem MatcherTyping.NextMatchersElaborateUsing.trackBoundary
    {signature : FrozenSignature} {fuel : Nat} {boundary : Supply}
    {context : Context} {expression : Expr} {holes : List Dual}
    {start finish : Supply}
    {generated : TypePM.Source.MatcherTyping.GeneratedChecks}
    (boundaryToStart : boundary.Le start)
    (derivation : TypePM.Source.MatcherTyping.NextMatchersElaborateUsing
      (WellFormedFuelLeaf signature fuel) context expression holes start
      generated finish) :
    TypePM.Source.MatcherTyping.NextMatchersElaborateUsing
      (ScopedWellFormedFuelLeaf signature fuel boundary) context expression
      holes start generated finish := by
  cases derivation with
  | zero checked =>
      exact TypePM.Source.MatcherTyping.NextMatchersElaborateUsing.zero
        (MatcherTyping.CheckedExpressionElaboratesUsing.trackBoundary
          boundaryToStart checked)
  | one checked =>
      exact TypePM.Source.MatcherTyping.NextMatchersElaborateUsing.one
        (MatcherTyping.CheckedExpressionElaboratesUsing.trackBoundary
          boundaryToStart checked)
  | many components =>
      exact TypePM.Source.MatcherTyping.NextMatchersElaborateUsing.many
        (MatcherTyping.NextMatcherItemsElaborateUsing.trackBoundary
          boundaryToStart components)

theorem MatcherTyping.MatcherArmElaboratesUsing.trackBoundary
    {signature : FrozenSignature} {fuel : Nat} {boundary : Supply}
    {context : Context} {captures : List Ty} {matcherTarget : Ty}
    {holes : List Dual} {arm : MatcherArm} {start finish : Supply}
    {generated : TypePM.Source.MatcherTyping.GeneratedChecks}
    (boundaryToStart : boundary.Le start)
    (derivation : TypePM.Source.MatcherTyping.MatcherArmElaboratesUsing
      (WellFormedFuelLeaf signature fuel) MatcherTyping.DPatElaborates signature
      context captures matcherTarget holes arm start generated finish) :
    TypePM.Source.MatcherTyping.MatcherArmElaboratesUsing
      (ScopedWellFormedFuelLeaf signature fuel boundary)
      (MatcherTyping.ScopedDPatElaborates signature boundary) signature context captures matcherTarget holes
      arm start generated finish := by
  cases derivation with
  | mk header body =>
      exact .mk ⟨rfl, boundaryToStart, header⟩
        (MatcherTyping.CheckedExpressionElaboratesUsing.trackBoundary
          (Supply.le_trans boundaryToStart header.supply_le_next) body)

theorem MatcherTyping.MatcherArmsElaborateUsing.trackBoundary
    {signature : FrozenSignature} {fuel : Nat} {boundary : Supply}
    {context : Context} {captures : List Ty} {matcherTarget : Ty}
    {holes : List Dual} {arms : List MatcherArm} {start finish : Supply}
    {generated : TypePM.Source.MatcherTyping.GeneratedArms}
    (boundaryToStart : boundary.Le start)
    (derivation : TypePM.Source.MatcherTyping.MatcherArmsElaborateUsing
      (WellFormedFuelLeaf signature fuel) MatcherTyping.DPatElaborates signature
      context captures matcherTarget holes arms start generated finish) :
    TypePM.Source.MatcherTyping.MatcherArmsElaborateUsing
      (ScopedWellFormedFuelLeaf signature fuel boundary)
      (MatcherTyping.ScopedDPatElaborates signature boundary) signature context captures matcherTarget holes
      arms start generated finish := by
  induction derivation with
  | nil => exact .nil
  | cons head tail induction =>
      have startToArm := head.supply_le_next
        (fun child => child.2.supply_le_next)
        MatcherTyping.DPatElaborates.supply_le_next
      exact .cons
        (MatcherTyping.MatcherArmElaboratesUsing.trackBoundary boundaryToStart head)
        (induction (Supply.le_trans boundaryToStart startToArm))

theorem MatcherTyping.MatcherClauseElaboratesUsing.trackBoundary
    {signature : FrozenSignature} {fuel : Nat} {boundary : Supply}
    {context : Context} {matcherTarget : Ty} {clause : MatcherClause}
    {start finish : Supply}
    {generated : TypePM.Source.MatcherTyping.GeneratedMatcherClause}
    (boundaryToStart : boundary.Le start)
    (derivation : TypePM.Source.MatcherTyping.MatcherClauseElaboratesUsing
      (WellFormedFuelLeaf signature fuel) MatcherTyping.PPatElaborates
      MatcherTyping.DPatElaborates signature context matcherTarget clause start
      generated finish) :
    TypePM.Source.MatcherTyping.MatcherClauseElaboratesUsing
      (ScopedWellFormedFuelLeaf signature fuel boundary)
      (MatcherTyping.ScopedPPatElaborates signature boundary)
      (MatcherTyping.ScopedDPatElaborates signature boundary) signature context
      matcherTarget clause start generated finish := by
  cases derivation with
  | mk shape header nextMatchers arms =>
      have startToHeader := header.supply_le_next
      have headerToNext := nextMatchers.supply_le_next
        (fun child => child.2.supply_le_next)
      exact .mk shape ⟨rfl, boundaryToStart, header⟩
        (MatcherTyping.NextMatchersElaborateUsing.trackBoundary
          (Supply.le_trans boundaryToStart startToHeader) nextMatchers)
        (MatcherTyping.MatcherArmsElaborateUsing.trackBoundary
          (Supply.le_trans boundaryToStart
            (Supply.le_trans startToHeader headerToNext)) arms)

theorem MatcherTyping.MatcherClausesElaborateUsing.trackBoundary
    {signature : FrozenSignature} {fuel : Nat} {boundary : Supply}
    {context : Context} {matcherTarget : Ty} {clauses : List MatcherClause}
    {start finish : Supply}
    {generated : TypePM.Source.MatcherTyping.GeneratedMatcherClauses}
    (boundaryToStart : boundary.Le start)
    (derivation : TypePM.Source.MatcherTyping.MatcherClausesElaborateUsing
      (WellFormedFuelLeaf signature fuel) MatcherTyping.PPatElaborates
      MatcherTyping.DPatElaborates signature context matcherTarget clauses start
      generated finish) :
    TypePM.Source.MatcherTyping.MatcherClausesElaborateUsing
      (ScopedWellFormedFuelLeaf signature fuel boundary)
      (MatcherTyping.ScopedPPatElaborates signature boundary)
      (MatcherTyping.ScopedDPatElaborates signature boundary) signature context
      matcherTarget clauses start generated finish := by
  induction derivation with
  | nil => exact .nil
  | cons head tail induction =>
      have startToClause := head.supply_le_next
        (fun child => child.2.supply_le_next)
        MatcherTyping.PPatElaborates.supply_le_next
        MatcherTyping.DPatElaborates.supply_le_next
      exact .cons
        (MatcherTyping.MatcherClauseElaboratesUsing.trackBoundary
          boundaryToStart head)
        (induction (Supply.le_trans boundaryToStart startToClause))

theorem MatcherTyping.MatcherLiteralElaboratesUsing.trackBoundary
    {signature : FrozenSignature} {fuel : Nat} {boundary : Supply}
    {context : Context} {clauses : List MatcherClause} {finish : Supply}
    {generated : Generated}
    (derivation : TypePM.Source.MatcherTyping.MatcherLiteralElaboratesUsing
      (WellFormedFuelLeaf signature fuel) MatcherTyping.PPatElaborates
      MatcherTyping.DPatElaborates signature context clauses boundary generated
      finish) :
    TypePM.Source.MatcherTyping.MatcherLiteralElaboratesUsing
      (ScopedWellFormedFuelLeaf signature fuel boundary)
      (MatcherTyping.ScopedPPatElaborates signature boundary)
      (MatcherTyping.ScopedDPatElaborates signature boundary) signature context
      clauses boundary generated finish := by
  cases derivation with
  | mk checked clausesElaboration =>
      exact .mk checked
        (MatcherTyping.MatcherClausesElaborateUsing.trackBoundary
          (by simp [Supply.Le]) clausesElaboration)

theorem M4.ItemsElaborateUsing.trackScope
    {signature : FrozenSignature} {fuel : Nat} {boundary : Supply}
    {context : Context} {items : List Expr} {start finish : Supply}
    {generated : GeneratedItems}
    (contextWellFormed : start.WellFormedFor context)
    (boundaryToStart : boundary.Le start)
    (derivation : M4.ItemsElaborateUsing (M4.ElaboratesFuel signature fuel)
      context items start generated finish) :
    M4.ItemsElaborateUsing (ScopedWellFormedFuelLeaf signature fuel boundary)
      context items start generated finish := by
  induction derivation with
  | nil => exact .nil
  | cons head tail induction =>
      have startToHead := head.supply_le_next
      exact .cons ⟨boundaryToStart, contextWellFormed, head⟩
        (induction (contextWellFormed.mono startToHead)
          (Supply.le_trans boundaryToStart startToHead))

theorem M4.CallElaboratesUsing.trackScope
    {signature : FrozenSignature} {fuel : Nat} {boundary : Supply}
    {context : Context} {accumulated : Generated} {arguments : List Expr}
    {start finish : Supply} {generated : Generated}
    (contextWellFormed : start.WellFormedFor context)
    (boundaryToStart : boundary.Le start)
    (derivation : M4.CallElaboratesUsing (M4.ElaboratesFuel signature fuel)
      context accumulated arguments start generated finish) :
    M4.CallElaboratesUsing (ScopedWellFormedFuelLeaf signature fuel boundary)
      context accumulated arguments start generated finish := by
  induction derivation with
  | nil => exact .nil
  | cons head tail induction =>
      have startToHead := head.supply_le_next
      have startToTail := Supply.le_trans startToHead
        (Supply.le_nextTy _ 2)
      exact .cons ⟨boundaryToStart, contextWellFormed, head⟩
        (induction (contextWellFormed.mono startToTail)
          (Supply.le_trans boundaryToStart startToTail))

theorem FixElaboratesUsing.trackScope
    {signature : FrozenSignature} {fuel : Nat} {boundary : Supply}
    {context : Context} {expression : Expr} {start finish : Supply}
    {generated : Generated}
    (contextWellFormed : start.WellFormedFor context)
    (boundaryToStart : boundary.Le start)
    (derivation : FixElaboratesUsing (M4.ElaboratesFuel signature fuel) context
      expression start generated finish) :
    FixElaboratesUsing (ScopedWellFormedFuelLeaf signature fuel boundary)
      context expression start generated finish := by
  cases derivation with
  | @fixE body start generatedBody finish direct bodyElaboration =>
      have startToBody : start.Le (Fix.bodySupply body start) := by
        simp only [Fix.bodySupply]
        split <;> simp [Supply.Le, Supply.nextTy]
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
      have bodyWellFormed := Supply.WellFormedFor.of_contextSupport
        contextWellFormed startToBody bodyContextSupport
      exact .fixE direct ⟨Supply.le_trans boundaryToStart startToBody,
        bodyWellFormed, bodyElaboration⟩

@[simp] theorem Generated.fromMatchAll_rename
    (rho : VariableRenaming) (target : Generated)
    (pattern : GeneratedPattern) (matcher body : Generated) :
    renameGenerated rho (Generated.fromMatchAll target pattern matcher body) =
      Generated.fromMatchAll (renameGenerated rho target)
        (renameGeneratedPattern rho pattern) (renameGenerated rho matcher)
        (renameGenerated rho body) := by
  simp [Generated.fromMatchAll, renameGenerated, renameGeneratedPattern,
    renameDual, renameTy, renameCap, renameEquation, renameObligation,
    Equation.apply, CheckObligation.apply, Ty.apply, List.map_append,
    DataTypes.list]

/-- The complete callback-parametric `matchAll` relation transports, including
the or-pattern binding check handled by `PatternElaboratesUsing.rename`. -/
theorem MatchAllElaboratesUsing.rename
    {rho : VariableRenaming} {boundary : Supply}
    {left right : M4ExpressionElaborationRelation}
    (transport : ∀ {context expression supply generated next},
      boundary.Le supply →
      left context expression supply generated next →
        right (renameContext rho context) expression supply
          (renameGenerated rho generated) next)
    (increases : ∀ {context expression supply generated next},
      left context expression supply generated next → supply.Le next)
    (fixed : rho.FixesAtOrAbove boundary)
    {signature : FrozenSignature} (wellFormed : signature.WellFormed)
    {context target matcher pattern body supply generated next}
    (boundaryToSupply : boundary.Le supply)
    (derivation : MatchAllElaboratesUsing left signature context target matcher
      pattern body supply generated next) :
    MatchAllElaboratesUsing right signature (renameContext rho context) target
      matcher pattern body supply (renameGenerated rho generated) next := by
  cases derivation with
  | @mk generatedTarget afterTarget generatedPattern afterPattern
      generatedMatcher afterMatcher generatedBody next targetElaboration
      patternElaboration matcherElaboration bodyElaboration =>
      have targetTransport := transport boundaryToSupply targetElaboration
      have boundaryToTarget := Supply.le_trans boundaryToSupply
        (increases targetElaboration)
      have patternTransport := PatternElaboratesUsing.rename transport increases
        fixed wellFormed boundaryToTarget patternElaboration
      have boundaryToPattern := Supply.le_trans boundaryToTarget
        (PatternElaboratesUsing.supply_le_next increases patternElaboration)
      have matcherTransport := transport boundaryToPattern matcherElaboration
      have boundaryToMatcher := Supply.le_trans boundaryToPattern
        (increases matcherElaboration)
      have bodyTransport := transport boundaryToMatcher bodyElaboration
      rw [Pattern.extendContext_rename] at bodyTransport
      simpa [Generated.fromMatchAll_rename] using
        (MatchAllElaboratesUsing.mk targetTransport patternTransport
          matcherTransport bodyTransport)

mutual

/-- Primitive matcher headers transport together with their expected target
and optional expected capability. -/
theorem PPatElaborates_rename
    {rho : VariableRenaming} {boundary : Supply}
    {signature : FrozenSignature} (wellFormed : signature.WellFormed)
    (fixed : rho.FixesAtOrAbove boundary)
    {pattern expectedTarget expectedCapability supply generated next}
    (boundaryToSupply : boundary.Le supply)
    (derivation : TypePM.Source.MatcherTyping.PPatElaborates signature pattern
      expectedTarget expectedCapability supply generated next) :
    TypePM.Source.MatcherTyping.PPatElaborates signature pattern
      (renameTy rho expectedTarget) (expectedCapability.map (renameCap rho))
      supply (MatcherTyping.renameGeneratedPPat rho generated) next := by
  cases derivation with
  | hole =>
      have supplyFixed := fixed.mono boundaryToSupply
      cases expectedCapability <;>
        simp [MatcherTyping.renameGeneratedPPat, renameDual, renameTy, renameCap,
          renameEquation, Equation.apply, VariableRenaming.substitution,
          Cap.apply, supplyFixed.2] <;>
        exact TypePM.Source.MatcherTyping.PPatElaborates.hole
  | wild =>
      simpa [MatcherTyping.renameGeneratedPPat] using
        (TypePM.Source.MatcherTyping.PPatElaborates.wild
          (signature := signature) (expectedTarget := renameTy rho expectedTarget)
          (expectedCapability := expectedCapability.map (renameCap rho))
          (supply := supply))
  | capture =>
      simpa [MatcherTyping.renameGeneratedPPat] using
        (TypePM.Source.MatcherTyping.PPatElaborates.capture
          (signature := signature) (expectedTarget := renameTy rho expectedTarget)
          (expectedCapability := expectedCapability.map (renameCap rho))
          (supply := supply))
  | @ctor constructor fields expectedTarget expectedCapability supply scheme
      generatedFields next lookup arity fieldsElaboration =>
      have closed := Signature.WellFormed.patternConstructorClosed_of_lookup
        wellFormed.baseWellFormed lookup
      have supplyFixed := fixed.mono boundaryToSupply
      obtain ⟨fieldsFixed, resultFixed⟩ :=
        DualScheme.instantiate_rename_eq closed supply supplyFixed
      have resultTargetFixed :
          renameTy rho (scheme.instantiate supply).1.result.target =
            (scheme.instantiate supply).1.result.target := by
        simpa [renameDual] using congrArg Dual.target resultFixed
      have resultCapabilityFixed :
          renameCap rho (scheme.instantiate supply).1.result.capability =
            (scheme.instantiate supply).1.result.capability := by
        simpa [renameDual] using congrArg Dual.capability resultFixed
      simp only [renameTy] at resultTargetFixed
      simp only [renameCap] at resultCapabilityFixed
      have boundaryToFields : boundary.Le (scheme.instantiate supply).2 :=
        Supply.le_trans boundaryToSupply (by
          simp [Supply.Le, DualScheme.instantiate])
      have fieldsTransport := PPatsElaborate_rename wellFormed fixed
        boundaryToFields fieldsElaboration
      rw [fieldsFixed] at fieldsTransport
      simp only [MatcherTyping.renameGeneratedPPat, Option.map_some, renameCap,
        renameTy, renameEquation, List.map_append, List.map_cons, List.map_nil,
        Equation.apply]
      rw [resultTargetFixed, resultCapabilityFixed]
      cases expectedCapability with
      | none =>
          simpa [MatcherTyping.renameGeneratedPPat,
            MatcherTyping.renameGeneratedPPats, resultFixed, fieldsFixed,
            resultTargetFixed, resultCapabilityFixed,
            renameDual, renameEquation, Equation.apply, renameTy, renameCap,
            List.map_append] using
            (TypePM.Source.MatcherTyping.PPatElaborates.ctor
              (expectedTarget := renameTy rho expectedTarget)
              (expectedCapability := none) lookup arity fieldsTransport)
      | some capability =>
          simpa [MatcherTyping.renameGeneratedPPat,
            MatcherTyping.renameGeneratedPPats, resultFixed, fieldsFixed,
            resultTargetFixed, resultCapabilityFixed,
            renameDual, renameEquation, Equation.apply, renameTy, renameCap,
            List.map_append] using
            (TypePM.Source.MatcherTyping.PPatElaborates.ctor
              (expectedTarget := renameTy rho expectedTarget)
              (expectedCapability := some (renameCap rho capability)) lookup arity
              fieldsTransport)
termination_by TypePM.Source.MatcherTyping.PPat.typingSize pattern * 2 + 1
decreasing_by
  all_goals simp_wf
  all_goals subst_vars
  all_goals simp [TypePM.Source.MatcherTyping.PPat.typingSize]
  all_goals omega

/-- List counterpart of `PPatElaborates_rename`. -/
theorem PPatsElaborate_rename
    {rho : VariableRenaming} {boundary : Supply}
    {signature : FrozenSignature} (wellFormed : signature.WellFormed)
    (fixed : rho.FixesAtOrAbove boundary)
    {patterns expected supply generated next}
    (boundaryToSupply : boundary.Le supply)
    (derivation : TypePM.Source.MatcherTyping.PPatsElaborate signature patterns
      expected supply generated next) :
    TypePM.Source.MatcherTyping.PPatsElaborate signature patterns
      (expected.map (renameDual rho)) supply
      (MatcherTyping.renameGeneratedPPats rho generated) next := by
  cases derivation with
  | nil => exact .nil
  | @cons pattern patterns expected expecteds supply generatedPattern
      afterPattern generatedPatterns next head tail =>
      have headTransport := PPatElaborates_rename wellFormed fixed
        boundaryToSupply head
      have headTransport' : TypePM.Source.MatcherTyping.PPatElaborates signature
          pattern (renameDual rho expected).target
          (some (renameDual rho expected).capability) supply
          (MatcherTyping.renameGeneratedPPat rho generatedPattern)
          afterPattern := by
        simpa [renameDual] using headTransport
      have boundaryToPattern := Supply.le_trans boundaryToSupply head.supply_le_next
      have tailTransport := PPatsElaborate_rename wellFormed fixed
        (next := next) boundaryToPattern tail
      simpa [MatcherTyping.renameGeneratedPPats,
        MatcherTyping.renameGeneratedPPat, renameDual, List.map_append] using
        (TypePM.Source.MatcherTyping.PPatsElaborate.cons headTransport'
          tailTransport)
termination_by TypePM.Source.MatcherTyping.PPat.listTypingSize patterns * 2
decreasing_by
  all_goals simp_wf
  all_goals subst_vars
  all_goals simp [TypePM.Source.MatcherTyping.PPat.listTypingSize]
  all_goals omega

end

theorem MatcherTyping.peelFunctionExact_rename
    (rho : VariableRenaming) : ∀ {count source fields result},
    TypePM.Source.MatcherTyping.peelFunctionExact count source =
        some (fields, result) →
      TypePM.Source.MatcherTyping.peelFunctionExact count (renameTy rho source) =
        some (fields.map (renameTy rho), renameTy rho result) := by
  intro count source fields result equality
  induction count generalizing source fields result with
  | zero =>
      simp [TypePM.Source.MatcherTyping.peelFunctionExact] at equality ⊢
      rcases equality with ⟨rfl, rfl⟩
      exact ⟨rfl, rfl⟩
  | succ count induction =>
      cases source <;>
        simp [TypePM.Source.MatcherTyping.peelFunctionExact] at equality
      case fn domain codomain =>
        cases tailEquality : TypePM.Source.MatcherTyping.peelFunctionExact count
            codomain with
        | none => simp [tailEquality] at equality
        | some output =>
            rcases output with ⟨domains, finalResult⟩
            simp [tailEquality] at equality
            rcases equality with ⟨rfl, rfl⟩
            have renamedTail := induction tailEquality
            unfold renameTy at renamedTail ⊢
            simp only [Ty.apply,
              TypePM.Source.MatcherTyping.peelFunctionExact]
            rw [renamedTail]
            rfl

mutual

/-- Data-pattern headers commute with fresh-local renaming. -/
theorem DPatElaborates_rename
    {rho : VariableRenaming} {boundary : Supply}
    {signature : FrozenSignature} (wellFormed : signature.WellFormed)
    (fixed : rho.FixesAtOrAbove boundary)
    {pattern expected supply generated next}
    (boundaryToSupply : boundary.Le supply)
    (derivation : TypePM.Source.MatcherTyping.DPatElaborates signature pattern
      expected supply generated next) :
    TypePM.Source.MatcherTyping.DPatElaborates signature pattern
      (renameTy rho expected) supply
      (MatcherTyping.renameGeneratedDPat rho generated) next := by
  cases derivation with
  | var =>
      simpa [MatcherTyping.renameGeneratedDPat] using
        (TypePM.Source.MatcherTyping.DPatElaborates.var
          (signature := signature) (expected := renameTy rho expected)
          (supply := supply))
  | wild =>
      simpa [MatcherTyping.renameGeneratedDPat] using
        (TypePM.Source.MatcherTyping.DPatElaborates.wild
          (signature := signature) (expected := renameTy rho expected)
          (supply := supply))
  | @ctor constructor fields expected supply scheme fieldTypes resultType
      generatedFields next lookup arity peel fieldsElaboration =>
      have closed := Signature.WellFormed.dataConstructorClosed_of_lookup
        wellFormed.baseWellFormed lookup
      have supplyFixed := fixed.mono boundaryToSupply
      have instantiatedFixed := Scheme.instantiate_rename_eq closed supply
        supplyFixed
      have renamedPeel := MatcherTyping.peelFunctionExact_rename rho peel
      rw [instantiatedFixed] at renamedPeel
      have boundaryToFields : boundary.Le (scheme.instantiate supply).2 :=
        Supply.le_trans boundaryToSupply (by
          simp [Supply.Le, Scheme.instantiate])
      have fieldsTransport := DPatsElaborate_rename wellFormed fixed
        boundaryToFields fieldsElaboration
      simpa [MatcherTyping.renameGeneratedDPat,
        MatcherTyping.renameGeneratedDPats, renameEquation, Equation.apply,
        renameTy, List.map_append] using
        (TypePM.Source.MatcherTyping.DPatElaborates.ctor lookup arity
          renamedPeel fieldsTransport)
  | @tuple items expected supply fields generatedItems next fieldsEquality
      itemsElaboration =>
      have supplyFixed := fixed.mono boundaryToSupply
      have renamedFields : fields.map (renameTy rho) = fields := by
        rw [fieldsEquality]
        exact MatcherTyping.freshTargets_rename supplyFixed items.length
      have boundaryToItems : boundary.Le (supply.nextTy items.length) :=
        Supply.le_trans boundaryToSupply (Supply.le_nextTy supply items.length)
      have itemsTransport := DPatsElaborate_rename wellFormed fixed
        boundaryToItems itemsElaboration
      rw [renamedFields] at itemsTransport
      simpa [MatcherTyping.renameGeneratedDPat,
        MatcherTyping.renameGeneratedDPats, renameEquation, Equation.apply,
        renameTy, Ty.apply, List.map_append, renamedFields] using
        (TypePM.Source.MatcherTyping.DPatElaborates.tuple
          (expected := renameTy rho expected) fieldsEquality itemsTransport)
termination_by TypePM.Source.MatcherTyping.DPat.typingSize pattern * 2 + 1
decreasing_by
  all_goals simp_wf
  all_goals subst_vars
  all_goals simp [TypePM.Source.MatcherTyping.DPat.typingSize]
  all_goals omega

/-- List counterpart of `DPatElaborates_rename`. -/
theorem DPatsElaborate_rename
    {rho : VariableRenaming} {boundary : Supply}
    {signature : FrozenSignature} (wellFormed : signature.WellFormed)
    (fixed : rho.FixesAtOrAbove boundary)
    {patterns expected supply generated next}
    (boundaryToSupply : boundary.Le supply)
    (derivation : TypePM.Source.MatcherTyping.DPatsElaborate signature patterns
      expected supply generated next) :
    TypePM.Source.MatcherTyping.DPatsElaborate signature patterns
      (expected.map (renameTy rho)) supply
      (MatcherTyping.renameGeneratedDPats rho generated) next := by
  cases derivation with
  | nil => exact .nil
  | @cons pattern patterns expected expecteds supply generatedPattern
      afterPattern generatedPatterns next head tail =>
      have headTransport := DPatElaborates_rename wellFormed fixed
        boundaryToSupply head
      have boundaryToPattern := Supply.le_trans boundaryToSupply
        head.supply_le_next
      have tailTransport := DPatsElaborate_rename wellFormed fixed
        boundaryToPattern tail
      simpa [MatcherTyping.renameGeneratedDPats,
        MatcherTyping.renameGeneratedDPat, List.map_append] using
        (TypePM.Source.MatcherTyping.DPatsElaborate.cons headTransport
          tailTransport)
termination_by TypePM.Source.MatcherTyping.DPat.listTypingSize patterns * 2
decreasing_by
  all_goals simp_wf
  all_goals subst_vars
  all_goals simp [TypePM.Source.MatcherTyping.DPat.listTypingSize]
  all_goals omega

end

@[simp] theorem renameGeneratedChecks_append
    (rho : VariableRenaming) (left right : MatcherTyping.GeneratedChecks) :
    MatcherTyping.renameGeneratedChecks rho (left.append right) =
      (MatcherTyping.renameGeneratedChecks rho left).append
        (MatcherTyping.renameGeneratedChecks rho right) := by
  simp [MatcherTyping.renameGeneratedChecks,
    TypePM.Source.MatcherTyping.GeneratedChecks.append, List.map_append]

@[simp] theorem renameGeneratedChecks_checked
    (rho : VariableRenaming) (generated : Generated) (expected : Ty) :
    MatcherTyping.renameGeneratedChecks rho
        (TypePM.Source.MatcherTyping.GeneratedChecks.checked generated expected) =
      TypePM.Source.MatcherTyping.GeneratedChecks.checked
        (renameGenerated rho generated) (renameTy rho expected) := by
  simp [MatcherTyping.renameGeneratedChecks,
    TypePM.Source.MatcherTyping.GeneratedChecks.checked, renameGenerated,
    renameObligation, CheckObligation.apply, renameTy]

/-- Sibling-list elaboration commutes with any callback transport that also
renames its generated block. -/
theorem M4.ItemsElaborateUsing.rename
    {rho : VariableRenaming}
    {left right : Context → Expr → Supply → Generated → Supply → Prop}
    (transport : ∀ {context expression supply generated next},
      left context expression supply generated next →
        right (renameContext rho context) expression supply
          (renameGenerated rho generated) next)
    {context items supply generated next}
    (derivation : M4.ItemsElaborateUsing left context items supply generated next) :
    M4.ItemsElaborateUsing right (renameContext rho context) items supply
      (renameGeneratedItems rho generated) next := by
  induction derivation with
  | nil => exact .nil
  | @cons item items supply generatedItem afterItem generatedItems next
      head tail induction =>
      simpa [renameGeneratedItems, renameGenerated, renameTy, Ty.applyList,
        List.map_append] using
        (M4.ItemsElaborateUsing.cons (transport head) induction)

/-- A call fold commutes with fresh-local renaming.  The monotonicity premise
is used only to show that the two application-result variables allocated
after each callback are in the fixed future stream. -/
theorem M4.CallElaboratesUsing.rename
    {rho : VariableRenaming} {boundary : Supply}
    {left right : Context → Expr → Supply → Generated → Supply → Prop}
    (transport : ∀ {context expression supply generated next},
      boundary.Le supply →
      left context expression supply generated next →
        right (renameContext rho context) expression supply
          (renameGenerated rho generated) next)
    (increases : ∀ {context expression supply generated next},
      left context expression supply generated next → supply.Le next)
    (fixed : rho.FixesAtOrAbove boundary)
    {context accumulated arguments supply generated next}
    (boundaryToSupply : boundary.Le supply)
    (derivation : M4.CallElaboratesUsing left context accumulated arguments
      supply generated next) :
    M4.CallElaboratesUsing right (renameContext rho context)
      (renameGenerated rho accumulated) arguments supply
      (renameGenerated rho generated) next := by
  induction derivation with
  | nil => exact .nil
  | @cons accumulated argument arguments supply generatedArgument afterArgument
      generated next head tail induction =>
      have supplyToAfter := increases head
      have boundaryToAfter := Supply.le_trans boundaryToSupply supplyToAfter
      have renamedAccumulated :
          renameGenerated rho
              (Generated.fromApp accumulated generatedArgument
                (.var ⟨afterArgument.ty⟩) (.var ⟨afterArgument.ty + 1⟩)) =
            Generated.fromApp (renameGenerated rho accumulated)
              (renameGenerated rho generatedArgument)
              (.var ⟨afterArgument.ty⟩) (.var ⟨afterArgument.ty + 1⟩) := by
        simp [Generated.fromApp, renameGenerated, renameTy, renameEquation,
          renameObligation, Equation.apply, CheckObligation.apply,
          VariableRenaming.substitution, Ty.apply, List.map_append,
          fixed.1 ⟨afterArgument.ty⟩ boundaryToAfter.1,
          fixed.1 ⟨afterArgument.ty + 1⟩
            (Nat.le_trans boundaryToAfter.1 (Nat.le_add_right _ _))]
      rw [renamedAccumulated] at induction
      exact .cons (transport boundaryToSupply head)
        (induction (Supply.le_trans boundaryToAfter
          (Supply.le_nextTy afterArgument 2)))

@[simp] theorem Fix.bodyContext_rename
    (rho : VariableRenaming) (domain codomain : Ty) (context : Context) :
    renameContext rho (Fix.bodyContext domain codomain context) =
      Fix.bodyContext (renameTy rho domain) (renameTy rho codomain)
        (renameContext rho context) := by
  simp [Fix.bodyContext, renameContext, Context.applyFree, Scheme.mono,
    Scheme.applyFree, renameTy, Ty.apply]

@[simp] theorem Generated.fromFix_rename
    (rho : VariableRenaming) (domain codomain : Ty) (body : Generated) :
    renameGenerated rho (Generated.fromFix domain codomain body) =
      Generated.fromFix (renameTy rho domain) (renameTy rho codomain)
        (renameGenerated rho body) := by
  simp [Generated.fromFix, renameGenerated, renameTy, renameEquation,
    Equation.apply, List.map_append, Ty.apply]

/-- The recursive-function component transports once its body callback does.
The syntactic direct-self-reference side condition is unchanged. -/
theorem FixElaboratesUsing.rename
    {rho : VariableRenaming} {boundary : Supply}
    {left right : Context → Expr → Supply → Generated → Supply → Prop}
    (transport : ∀ {context expression supply generated next},
      left context expression supply generated next →
        right (renameContext rho context) expression supply
          (renameGenerated rho generated) next)
    (fixed : rho.FixesAtOrAbove boundary)
    {context expression generated next}
    (derivation : FixElaboratesUsing left context expression boundary generated next) :
    FixElaboratesUsing right (renameContext rho context) expression boundary
      (renameGenerated rho generated) next := by
  cases derivation with
  | @fixE body supply generatedBody next direct bodyElaboration =>
      have bodyTransport := transport bodyElaboration
      have domainFixed : renameTy rho (Fix.domain body boundary) =
          Fix.domain body boundary := by
        cases body <;>
          simp [Fix.domain, renameTy, VariableRenaming.substitution, Ty.apply,
            Cap.apply, fixed.1, fixed.2]
      have codomainFixed : renameTy rho (Fix.codomain body boundary) =
          Fix.codomain body boundary := by
        cases body <;>
          simp [Fix.codomain, renameTy, VariableRenaming.substitution, Ty.apply,
            Cap.apply, fixed.1, fixed.2]
      rw [Fix.bodyContext_rename, domainFixed, codomainFixed] at bodyTransport
      simpa [Generated.fromFix_rename, domainFixed, codomainFixed] using
        (FixElaboratesUsing.fixE direct bodyTransport)

@[simp] theorem MatcherTyping.holeProductTarget_rename
    (rho : VariableRenaming) (holes : List Dual) :
    TypePM.Source.MatcherTyping.holeProductTarget (holes.map (renameDual rho)) =
      renameTy rho (TypePM.Source.MatcherTyping.holeProductTarget holes) := by
  cases holes with
  | nil => simp [TypePM.Source.MatcherTyping.holeProductTarget, renameTy, Ty.apply]
  | cons first rest =>
      cases rest with
      | nil => simp [TypePM.Source.MatcherTyping.holeProductTarget, renameDual]
      | cons second rest =>
          simpa [TypePM.Source.MatcherTyping.holeProductTarget, renameTy,
            Ty.apply] using Dual.targets_rename rho (first :: second :: rest)

@[simp] theorem DataTypes.list_rename
    (rho : VariableRenaming) (target : Ty) :
    DataTypes.list (renameTy rho target) = renameTy rho (DataTypes.list target) := by
  simp [DataTypes.list, renameTy, Ty.apply]

/-- Checking an expression at an expected type commutes with callback
renaming. -/
theorem MatcherTyping.CheckedExpressionElaboratesUsing.rename
    {rho : VariableRenaming}
    {left right : MatcherTyping.ExpressionElaborationRelation}
    (transport : ∀ {context expression supply generated next},
      left context expression supply generated next →
        right (renameContext rho context) expression supply
          (renameGenerated rho generated) next)
    {context expression expected supply generated next}
    (derivation : TypePM.Source.MatcherTyping.CheckedExpressionElaboratesUsing
      left context expression expected supply generated next) :
    TypePM.Source.MatcherTyping.CheckedExpressionElaboratesUsing right
      (renameContext rho context) expression (renameTy rho expected) supply
      (MatcherTyping.renameGeneratedChecks rho generated) next := by
  cases derivation with
  | mk expressionElaboration =>
      simpa [renameGeneratedChecks_checked] using
        (TypePM.Source.MatcherTyping.CheckedExpressionElaboratesUsing.mk
          (transport expressionElaboration))

/-- The zero/one/many next-matcher convention commutes with callback
renaming. -/
theorem MatcherTyping.NextMatcherItemsElaborateUsing.rename
    {rho : VariableRenaming}
    {left right : MatcherTyping.ExpressionElaborationRelation}
    (transport : ∀ {context expression supply generated next},
      left context expression supply generated next →
        right (renameContext rho context) expression supply
          (renameGenerated rho generated) next)
    {context items holes supply generated next}
    (derivation : TypePM.Source.MatcherTyping.NextMatcherItemsElaborateUsing
      left context items holes supply generated next) :
    TypePM.Source.MatcherTyping.NextMatcherItemsElaborateUsing right
      (renameContext rho context) items (holes.map (renameDual rho)) supply
      (MatcherTyping.renameGeneratedChecks rho generated) next := by
  induction derivation with
  | nil => exact .nil
  | cons head tail induction =>
      simpa [renameDual, renameGeneratedChecks_append] using
        (TypePM.Source.MatcherTyping.NextMatcherItemsElaborateUsing.cons
          (MatcherTyping.CheckedExpressionElaboratesUsing.rename transport head)
          induction)

theorem MatcherTyping.NextMatchersElaborateUsing.rename
    {rho : VariableRenaming}
    {left right : MatcherTyping.ExpressionElaborationRelation}
    (transport : ∀ {context expression supply generated next},
      left context expression supply generated next →
        right (renameContext rho context) expression supply
          (renameGenerated rho generated) next)
    {context expression holes supply generated next}
    (derivation : TypePM.Source.MatcherTyping.NextMatchersElaborateUsing
      left context expression holes supply generated next) :
    TypePM.Source.MatcherTyping.NextMatchersElaborateUsing right
      (renameContext rho context) expression (holes.map (renameDual rho)) supply
      (MatcherTyping.renameGeneratedChecks rho generated) next := by
  cases derivation with
  | zero checked =>
      simpa [renameTy, Ty.apply] using
        (TypePM.Source.MatcherTyping.NextMatchersElaborateUsing.zero
          (MatcherTyping.CheckedExpressionElaboratesUsing.rename transport checked))
  | one checked =>
      simpa [renameDual] using
        (TypePM.Source.MatcherTyping.NextMatchersElaborateUsing.one
          (MatcherTyping.CheckedExpressionElaboratesUsing.rename transport checked))
  | many components =>
      simpa using
        (TypePM.Source.MatcherTyping.NextMatchersElaborateUsing.many
          (MatcherTyping.NextMatcherItemsElaborateUsing.rename transport components))

/-- One decomposition arm transports when expression leaves and data-pattern
headers transport. -/
theorem MatcherTyping.MatcherArmElaboratesUsing.rename
    {rho : VariableRenaming}
    {left right : MatcherTyping.ExpressionElaborationRelation}
    {dleft dright : MatcherTyping.DPatElaborationRelation}
    (expressionTransport : ∀ {context expression supply generated next},
      left context expression supply generated next →
        right (renameContext rho context) expression supply
          (renameGenerated rho generated) next)
    (dpatTransport : ∀ {signature pattern expected supply generated next},
      dleft signature pattern expected supply generated next →
        dright signature pattern (renameTy rho expected) supply
          (MatcherTyping.renameGeneratedDPat rho generated) next)
    {signature context captures matcherTarget holes arm supply generated next}
    (derivation : TypePM.Source.MatcherTyping.MatcherArmElaboratesUsing
      left dleft signature context captures matcherTarget holes arm supply
      generated next) :
    TypePM.Source.MatcherTyping.MatcherArmElaboratesUsing right dright signature
      (renameContext rho context) (captures.map (renameTy rho))
      (renameTy rho matcherTarget) (holes.map (renameDual rho)) arm supply
      (MatcherTyping.renameGeneratedChecks rho generated) next := by
  cases derivation with
  | @mk header body supply generatedHeader afterHeader generatedBody next
      headerElaboration bodyElaboration =>
      have bodyTransport :=
        MatcherTyping.CheckedExpressionElaboratesUsing.rename
          expressionTransport bodyElaboration
      rw [Pattern.extendContext_rename, Pattern.extendContext_rename] at bodyTransport
      have bodyTransport' :
          TypePM.Source.MatcherTyping.CheckedExpressionElaboratesUsing right
            (Pattern.extendContext
              (MatcherTyping.renameGeneratedDPat rho generatedHeader).bindings
              (Pattern.extendContext (captures.map (renameTy rho))
                (renameContext rho context))) body
            (DataTypes.list (TypePM.Source.MatcherTyping.holeProductTarget
              (holes.map (renameDual rho)))) afterHeader
            (MatcherTyping.renameGeneratedChecks rho generatedBody) next := by
        simpa [MatcherTyping.renameGeneratedDPat, DataTypes.list_rename,
          MatcherTyping.holeProductTarget_rename] using bodyTransport
      simpa [MatcherTyping.renameGeneratedDPat,
        MatcherTyping.renameGeneratedChecks, List.map_append] using
        (TypePM.Source.MatcherTyping.MatcherArmElaboratesUsing.mk
          (dpatTransport headerElaboration) bodyTransport')

theorem MatcherTyping.MatcherArmsElaborateUsing.rename
    {rho : VariableRenaming}
    {left right : MatcherTyping.ExpressionElaborationRelation}
    {dleft dright : MatcherTyping.DPatElaborationRelation}
    (expressionTransport : ∀ {context expression supply generated next},
      left context expression supply generated next →
        right (renameContext rho context) expression supply
          (renameGenerated rho generated) next)
    (dpatTransport : ∀ {signature pattern expected supply generated next},
      dleft signature pattern expected supply generated next →
        dright signature pattern (renameTy rho expected) supply
          (MatcherTyping.renameGeneratedDPat rho generated) next)
    {signature context captures matcherTarget holes arms supply generated next}
    (derivation : TypePM.Source.MatcherTyping.MatcherArmsElaborateUsing
      left dleft signature context captures matcherTarget holes arms supply
      generated next) :
    TypePM.Source.MatcherTyping.MatcherArmsElaborateUsing right dright signature
      (renameContext rho context) (captures.map (renameTy rho))
      (renameTy rho matcherTarget) (holes.map (renameDual rho)) arms supply
      (MatcherTyping.renameGeneratedArms rho generated) next := by
  induction derivation with
  | nil => exact .nil
  | cons head tail induction =>
      simpa [MatcherTyping.renameGeneratedArms,
        renameGeneratedChecks_append] using
        (TypePM.Source.MatcherTyping.MatcherArmsElaborateUsing.cons
          (MatcherTyping.MatcherArmElaboratesUsing.rename
            (rho := rho) (left := left) (right := right)
            (dleft := dleft) (dright := dright)
            expressionTransport dpatTransport head) induction)

/-- A complete matcher clause transports.  Its shape side condition is purely
syntactic and is therefore preserved verbatim. -/
theorem MatcherTyping.MatcherClauseElaboratesUsing.rename
    {rho : VariableRenaming}
    {left right : MatcherTyping.ExpressionElaborationRelation}
    {pleft pright : MatcherTyping.PPatElaborationRelation}
    {dleft dright : MatcherTyping.DPatElaborationRelation}
    (expressionTransport : ∀ {context expression supply generated next},
      left context expression supply generated next →
        right (renameContext rho context) expression supply
          (renameGenerated rho generated) next)
    (ppatTransport : ∀ {signature pattern expected capability supply generated next},
      pleft signature pattern expected capability supply generated next →
        pright signature pattern (renameTy rho expected)
          (capability.map (renameCap rho)) supply
          (MatcherTyping.renameGeneratedPPat rho generated) next)
    (dpatTransport : ∀ {signature pattern expected supply generated next},
      dleft signature pattern expected supply generated next →
        dright signature pattern (renameTy rho expected) supply
          (MatcherTyping.renameGeneratedDPat rho generated) next)
    {signature context matcherTarget clause supply generated next}
    (derivation : TypePM.Source.MatcherTyping.MatcherClauseElaboratesUsing
      left pleft dleft signature context matcherTarget clause supply generated next) :
    TypePM.Source.MatcherTyping.MatcherClauseElaboratesUsing right pright dright
      signature (renameContext rho context) (renameTy rho matcherTarget) clause
      supply (MatcherTyping.renameGeneratedMatcherClause rho generated) next := by
  cases derivation with
  | mk shape headerElaboration nextElaboration armsElaboration =>
      have nextTransport := MatcherTyping.NextMatchersElaborateUsing.rename
        expressionTransport nextElaboration
      rw [Pattern.extendContext_rename] at nextTransport
      simpa [MatcherTyping.renameGeneratedMatcherClause,
        MatcherTyping.renameGeneratedPPat, MatcherTyping.renameGeneratedArms,
        MatcherTyping.renameGeneratedChecks, List.map_append] using
          (TypePM.Source.MatcherTyping.MatcherClauseElaboratesUsing.mk shape
          (ppatTransport headerElaboration) nextTransport
          (MatcherTyping.MatcherArmsElaborateUsing.rename
            (rho := rho) (left := left) (right := right)
            (dleft := dleft) (dright := dright)
            expressionTransport dpatTransport armsElaboration))

theorem MatcherTyping.MatcherClausesElaborateUsing.rename
    {rho : VariableRenaming}
    {left right : MatcherTyping.ExpressionElaborationRelation}
    {pleft pright : MatcherTyping.PPatElaborationRelation}
    {dleft dright : MatcherTyping.DPatElaborationRelation}
    (expressionTransport : ∀ {context expression supply generated next},
      left context expression supply generated next →
        right (renameContext rho context) expression supply
          (renameGenerated rho generated) next)
    (ppatTransport : ∀ {signature pattern expected capability supply generated next},
      pleft signature pattern expected capability supply generated next →
        pright signature pattern (renameTy rho expected)
          (capability.map (renameCap rho)) supply
          (MatcherTyping.renameGeneratedPPat rho generated) next)
    (dpatTransport : ∀ {signature pattern expected supply generated next},
      dleft signature pattern expected supply generated next →
        dright signature pattern (renameTy rho expected) supply
          (MatcherTyping.renameGeneratedDPat rho generated) next)
    {signature context matcherTarget clauses supply generated next}
    (derivation : TypePM.Source.MatcherTyping.MatcherClausesElaborateUsing
      left pleft dleft signature context matcherTarget clauses supply generated next) :
    TypePM.Source.MatcherTyping.MatcherClausesElaborateUsing right pright dright
      signature (renameContext rho context) (renameTy rho matcherTarget) clauses
      supply (MatcherTyping.renameGeneratedMatcherClauses rho generated) next := by
  induction derivation with
  | nil => exact .nil
  | @cons clause clauses supply generatedClause afterClause generatedClauses
      next head tail induction =>
      cases evidence : generatedClause.evidence <;>
        simpa [MatcherTyping.renameGeneratedMatcherClauses,
          MatcherTyping.renameGeneratedMatcherClause,
          renameGeneratedChecks_append, evidence, List.map_append] using
          (TypePM.Source.MatcherTyping.MatcherClausesElaborateUsing.cons
            (MatcherTyping.MatcherClauseElaboratesUsing.rename
              (rho := rho) (left := left) (right := right)
              (pleft := pleft) (pright := pright)
              (dleft := dleft) (dright := dright)
              expressionTransport ppatTransport dpatTransport head) induction)

@[simp] theorem MatcherTyping.evidenceEquations_rename
    (rho : VariableRenaming) (producer : Cap) (evidences : List Cap) :
    (TypePM.Source.MatcherTyping.evidenceEquations producer evidences).map
        (renameEquation rho) =
      TypePM.Source.MatcherTyping.evidenceEquations (renameCap rho producer)
        (evidences.map (renameCap rho)) := by
  cases evidences <;>
    simp [TypePM.Source.MatcherTyping.evidenceEquations, renameEquation,
      Equation.apply, renameCap, Cap.apply, List.map_map]

/-- The complete matcher-literal relation transports.  All four declarative
static checks remain the same proof object because renaming changes generated
types only, never source clauses or the signature. -/
theorem MatcherTyping.MatcherLiteralElaboratesUsing.rename
    {rho : VariableRenaming} {boundary : Supply}
    {left right : MatcherTyping.ExpressionElaborationRelation}
    {pleft pright : MatcherTyping.PPatElaborationRelation}
    {dleft dright : MatcherTyping.DPatElaborationRelation}
    (expressionTransport : ∀ {context expression supply generated next},
      left context expression supply generated next →
        right (renameContext rho context) expression supply
          (renameGenerated rho generated) next)
    (ppatTransport : ∀ {signature pattern expected capability supply generated next},
      pleft signature pattern expected capability supply generated next →
        pright signature pattern (renameTy rho expected)
          (capability.map (renameCap rho)) supply
          (MatcherTyping.renameGeneratedPPat rho generated) next)
    (dpatTransport : ∀ {signature pattern expected supply generated next},
      dleft signature pattern expected supply generated next →
        dright signature pattern (renameTy rho expected) supply
          (MatcherTyping.renameGeneratedDPat rho generated) next)
    (fixed : rho.FixesAtOrAbove boundary)
    {signature context clauses generated next}
    (derivation : TypePM.Source.MatcherTyping.MatcherLiteralElaboratesUsing
      left pleft dleft signature context clauses boundary generated next) :
    TypePM.Source.MatcherTyping.MatcherLiteralElaboratesUsing right pright dright
      signature (renameContext rho context) clauses boundary
      (renameGenerated rho generated) next := by
  cases derivation with
  | mk checked clausesElaboration =>
      have clausesTransport :=
        MatcherTyping.MatcherClausesElaborateUsing.rename
          (rho := rho) (left := left) (right := right)
          (pleft := pleft) (pright := pright)
          (dleft := dleft) (dright := dright)
          expressionTransport ppatTransport dpatTransport clausesElaboration
      have targetFixed : renameTy rho (.var ⟨boundary.ty⟩) = .var ⟨boundary.ty⟩ :=
        renameTy_var_of_le fixed (Nat.le_refl _)
      rw [targetFixed] at clausesTransport
      simpa [renameGenerated, MatcherTyping.renameGeneratedMatcherClauses,
        MatcherTyping.renameGeneratedChecks,
        renameTy, renameCap, VariableRenaming.substitution, Ty.apply, Cap.apply,
        List.map_append,
        MatcherTyping.evidenceEquations_rename, fixed.1, fixed.2] using
        (TypePM.Source.MatcherTyping.MatcherLiteralElaboratesUsing.mk checked
          clausesTransport)

@[simp] theorem MatchFirstTyping.GeneratedTail.fromArm_rename
    (rho : VariableRenaming) (targetType matcherType expectedResult : Ty)
    (pattern : GeneratedPattern) (body : Generated) :
    MatchFirstTyping.renameGeneratedTail rho
        (TypePM.Source.MatchFirstTyping.GeneratedTail.fromArm
          targetType matcherType expectedResult pattern body) =
      TypePM.Source.MatchFirstTyping.GeneratedTail.fromArm
        (renameTy rho targetType) (renameTy rho matcherType)
        (renameTy rho expectedResult) (renameGeneratedPattern rho pattern)
        (renameGenerated rho body) := by
  simp [MatchFirstTyping.renameGeneratedTail,
    TypePM.Source.MatchFirstTyping.GeneratedTail.fromArm,
    renameGeneratedPattern, renameGenerated, renameDual, renameEquation,
    renameObligation, Equation.apply, CheckObligation.apply, renameTy, renameCap,
    Ty.apply, List.map_append]

@[simp] theorem MatchFirstTyping.GeneratedArms.fromFallback_rename
    (rho : VariableRenaming) (fallback : Generated)
    (arms : TypePM.Source.MatchFirstTyping.GeneratedTail) :
    MatchFirstTyping.renameGeneratedArms rho
        (TypePM.Source.MatchFirstTyping.GeneratedArms.fromFallback fallback arms) =
      TypePM.Source.MatchFirstTyping.GeneratedArms.fromFallback
        (renameGenerated rho fallback)
        (MatchFirstTyping.renameGeneratedTail rho arms) := by
  simp [MatchFirstTyping.renameGeneratedArms,
    MatchFirstTyping.renameGeneratedTail,
    TypePM.Source.MatchFirstTyping.GeneratedArms.fromFallback,
    renameGenerated, List.map_append]

@[simp] theorem Generated.fromMatchFirst_rename
    (rho : VariableRenaming) (target matcher : Generated)
    (arms : TypePM.Source.MatchFirstTyping.GeneratedArms) :
    renameGenerated rho
        (TypePM.Source.MatchFirstTyping.Generated.fromMatchFirst target matcher arms) =
      TypePM.Source.MatchFirstTyping.Generated.fromMatchFirst
        (renameGenerated rho target)
        (renameGenerated rho matcher)
        (MatchFirstTyping.renameGeneratedArms rho arms) := by
  simp [TypePM.Source.MatchFirstTyping.Generated.fromMatchFirst,
    MatchFirstTyping.renameGeneratedArms, renameGenerated, List.map_append]

/-- Later single-result match arms commute with fresh-local renaming. -/
theorem MatchFirstTyping.TailElaboratesUsing.rename
    {rho : VariableRenaming} {boundary : Supply}
    {left right : M4ExpressionElaborationRelation}
    (transport : ∀ {context expression supply generated next},
      boundary.Le supply →
      left context expression supply generated next →
        right (renameContext rho context) expression supply
          (renameGenerated rho generated) next)
    (increases : ∀ {context expression supply generated next},
      left context expression supply generated next → supply.Le next)
    (fixed : rho.FixesAtOrAbove boundary)
    {signature : FrozenSignature} (wellFormed : signature.WellFormed)
    {context targetType matcherType expectedResult arms supply generated next}
    (boundaryToSupply : boundary.Le supply)
    (derivation : TypePM.Source.MatchFirstTyping.TailElaboratesUsing left
      signature context targetType matcherType expectedResult arms supply
      generated next) :
    TypePM.Source.MatchFirstTyping.TailElaboratesUsing right signature
      (renameContext rho context) (renameTy rho targetType)
      (renameTy rho matcherType) (renameTy rho expectedResult) arms supply
      (MatchFirstTyping.renameGeneratedTail rho generated) next := by
  induction derivation with
  | nil => exact .nil
  | @cons pattern body arms supply generatedPattern afterPattern generatedBody
      afterBody generatedTail next patternElaboration bodyElaboration
      tailElaboration induction =>
      have patternTransport := PatternElaboratesUsing.rename transport increases
        fixed wellFormed boundaryToSupply patternElaboration
      have boundaryToPattern := Supply.le_trans boundaryToSupply
        (PatternElaboratesUsing.supply_le_next increases patternElaboration)
      have bodyTransport := transport boundaryToPattern bodyElaboration
      rw [Pattern.extendContext_rename] at bodyTransport
      have boundaryToBody := Supply.le_trans boundaryToPattern
        (increases bodyElaboration)
      have tailTransport := induction boundaryToBody
      have armRename := MatchFirstTyping.GeneratedTail.fromArm_rename rho
        targetType matcherType expectedResult generatedPattern generatedBody
      have hardRename :
          (TypePM.Source.MatchFirstTyping.GeneratedTail.fromArm targetType
            matcherType expectedResult generatedPattern generatedBody).hard.map
              (renameEquation rho) =
            (TypePM.Source.MatchFirstTyping.GeneratedTail.fromArm
              (renameTy rho targetType) (renameTy rho matcherType)
              (renameTy rho expectedResult)
              (renameGeneratedPattern rho generatedPattern)
              (renameGenerated rho generatedBody)).hard := by
        simpa [MatchFirstTyping.renameGeneratedTail] using
          congrArg TypePM.Source.MatchFirstTyping.GeneratedTail.hard armRename
      have pendingRename :
          (TypePM.Source.MatchFirstTyping.GeneratedTail.fromArm targetType
            matcherType expectedResult generatedPattern generatedBody).pending.map
              (renameObligation rho) =
            (TypePM.Source.MatchFirstTyping.GeneratedTail.fromArm
              (renameTy rho targetType) (renameTy rho matcherType)
              (renameTy rho expectedResult)
              (renameGeneratedPattern rho generatedPattern)
              (renameGenerated rho generatedBody)).pending := by
        simpa [MatchFirstTyping.renameGeneratedTail] using
          congrArg TypePM.Source.MatchFirstTyping.GeneratedTail.pending armRename
      simpa [MatchFirstTyping.renameGeneratedTail,
        hardRename, pendingRename, List.map_append] using
        (TypePM.Source.MatchFirstTyping.TailElaboratesUsing.cons
          patternTransport bodyTransport tailTransport)

/-- The fallback and ordinary arms commute with fresh-local renaming. -/
theorem MatchFirstTyping.ArmsElaborateUsing.rename
    {rho : VariableRenaming} {boundary : Supply}
    {left right : M4ExpressionElaborationRelation}
    (transport : ∀ {context expression supply generated next},
      boundary.Le supply →
      left context expression supply generated next →
        right (renameContext rho context) expression supply
          (renameGenerated rho generated) next)
    (increases : ∀ {context expression supply generated next},
      left context expression supply generated next → supply.Le next)
    (fixed : rho.FixesAtOrAbove boundary)
    {signature : FrozenSignature} (wellFormed : signature.WellFormed)
    {context targetType matcherType fallback arms supply generated next}
    (boundaryToSupply : boundary.Le supply)
    (derivation : TypePM.Source.MatchFirstTyping.ArmsElaborateUsing left
      signature context targetType matcherType fallback arms supply generated next) :
    TypePM.Source.MatchFirstTyping.ArmsElaborateUsing right signature
      (renameContext rho context) (renameTy rho targetType)
      (renameTy rho matcherType) fallback arms supply
      (MatchFirstTyping.renameGeneratedArms rho generated) next := by
  cases derivation with
  | fromFallback fallbackElaboration armsElaboration =>
      have fallbackTransport := transport boundaryToSupply fallbackElaboration
      have boundaryToFallback := Supply.le_trans boundaryToSupply
        (increases fallbackElaboration)
      have armsTransport := MatchFirstTyping.TailElaboratesUsing.rename
        transport increases fixed wellFormed boundaryToFallback armsElaboration
      simpa [MatchFirstTyping.GeneratedArms.fromFallback_rename] using
        (TypePM.Source.MatchFirstTyping.ArmsElaborateUsing.fromFallback
          fallbackTransport armsTransport)

/-- The complete single-result match relation transports. -/
theorem MatchFirstTyping.ElaboratesUsing.rename
    {rho : VariableRenaming} {boundary : Supply}
    {left right : M4ExpressionElaborationRelation}
    (transport : ∀ {context expression supply generated next},
      boundary.Le supply →
      left context expression supply generated next →
        right (renameContext rho context) expression supply
          (renameGenerated rho generated) next)
    (increases : ∀ {context expression supply generated next},
      left context expression supply generated next → supply.Le next)
    (fixed : rho.FixesAtOrAbove boundary)
    {signature : FrozenSignature} (wellFormed : signature.WellFormed)
    {context expression generated next}
    (derivation : TypePM.Source.MatchFirstTyping.ElaboratesUsing left signature
      context expression boundary generated next) :
    TypePM.Source.MatchFirstTyping.ElaboratesUsing right signature
      (renameContext rho context) expression boundary
      (renameGenerated rho generated) next := by
  cases derivation with
  | @matchFirst target matcher arms fallback supply generatedTarget afterTarget
      generatedMatcher afterMatcher generatedArms next
      targetElaboration matcherElaboration armsElaboration =>
      have targetTransport := transport (Supply.le_refl boundary)
        targetElaboration
      have boundaryToTarget := increases targetElaboration
      have matcherTransport := transport boundaryToTarget matcherElaboration
      have boundaryToMatcher := Supply.le_trans boundaryToTarget
        (increases matcherElaboration)
      have armsTransport := MatchFirstTyping.ArmsElaborateUsing.rename
        transport increases fixed wellFormed boundaryToMatcher armsElaboration
      simpa [Generated.fromMatchFirst_rename] using
        (TypePM.Source.MatchFirstTyping.ElaboratesUsing.matchFirst
          targetTransport matcherTransport armsTransport)

/-! ## Exact remaining recursive boundary

The component theorems above expose the one invariant that a fuel induction
must thread through expression callbacks.  Pattern bindings and matcher
captures change the callback context, so a bare induction hypothesis requiring
only `childStart.WellFormedFor childContext` cannot be supplied by the generic
callback interface.  The strengthened property below records precisely that
the child context is supported by the original context and the already
allocated interval.  `Supply.WellFormedFor.of_contextSupport` then recovers the
ordinary child-context well-formedness premise.
-/

mutual

/-- Enrich every embedded-expression callback in a user-pattern derivation
with the support of the context at that callback. -/
theorem PatternElaboratesUsing.trackContextSupport
    {signature : FrozenSignature} (wellFormed : signature.WellFormed)
    {fuel : Nat} {context : Context} {outerStart start finish : Supply}
    {arguments : PatternContext} {pattern : Pattern} {bindings : List Ty}
    {generated : GeneratedPattern}
    (contextWellFormed : outerStart.WellFormedFor context)
    (argumentsSupport : VariablesSupportProvenance context outerStart start
      (dualUnificationVars arguments))
    (bindingsSupport : VariablesSupportProvenance context outerStart start
      (Ty.unificationVarsList bindings))
    (outerToStart : outerStart.Le start)
    (derivation : PatternElaboratesUsing (M4.ElaboratesFuel signature fuel)
      signature context arguments pattern bindings start generated finish) :
    PatternElaboratesUsing
      (WellFormedFuelLeaf signature fuel)
      signature context arguments pattern bindings start generated finish := by
  cases derivation with
  | var => exact .var
  | wild => exact .wild
  | @value expression bindings start generated afterExpression expressionElaboration =>
      have bindingsAtStart := bindingsSupport.extend_finish (Supply.le_refl start)
      have extendedSupport := Pattern.extendContext_support bindingsAtStart
      have childWellFormed := Supply.WellFormedFor.of_contextSupport
        contextWellFormed outerToStart extendedSupport
      exact .value ⟨childWellFormed, expressionElaboration⟩
  | @ctor constructor fields bindings start scheme generatedFields finish lookup
      arity fieldsElaboration =>
      have startToFields : start.Le (scheme.instantiate start).2 := by
        simp [Supply.Le, DualScheme.instantiate]
      exact .ctor lookup arity
        (PatternsElaborateUsing.trackContextSupport wellFormed
          contextWellFormed (argumentsSupport.extend_finish startToFields)
          (bindingsSupport.extend_finish startToFields)
          (Supply.le_trans outerToStart startToFields) fieldsElaboration)
  | @tuple items bindings start generatedItems finish itemsElaboration =>
      exact .tuple (PatternsElaborateUsing.trackContextSupport wellFormed
        contextWellFormed argumentsSupport bindingsSupport outerToStart
        itemsElaboration)
  | @and left right bindings start generatedLeft afterLeft generatedRight finish
      leftElaboration rightElaboration =>
      have startToLeft := PatternElaboratesUsing.supply_le_next
        (fun {context expression start generated finish}
          (child : M4.ElaboratesFuel signature fuel context expression start
            generated finish) => child.supply_le_next) leftElaboration
      have leftSupport := leftElaboration.supportProvenance wellFormed
        (fun {context expression start generated finish}
          (child : M4.ElaboratesFuel signature fuel context expression start
            generated finish) => child.supply_le_next)
        (fun {context expression start generated finish}
          (child : M4.ElaboratesFuel signature fuel context expression start
            generated finish) => child.supportProvenance wellFormed)
        argumentsSupport bindingsSupport outerToStart
      have leftBindings : VariablesSupportProvenance context outerStart
          afterLeft (Ty.unificationVarsList generatedLeft.bindings) := by
        intro candidate member
        exact leftSupport candidate (by
          simp [GeneratedPattern.unificationVars, member])
      exact .and
        (PatternElaboratesUsing.trackContextSupport wellFormed contextWellFormed
          argumentsSupport bindingsSupport outerToStart leftElaboration)
        (PatternElaboratesUsing.trackContextSupport wellFormed
          contextWellFormed (argumentsSupport.extend_finish startToLeft) leftBindings
          (Supply.le_trans outerToStart startToLeft) rightElaboration)
  | @or left right bindings start generatedLeft afterLeft generatedRight finish
      bindingChecks leftElaboration rightElaboration bindingsEqual =>
      have startToLeft := PatternElaboratesUsing.supply_le_next
        (fun {context expression start generated finish}
          (child : M4.ElaboratesFuel signature fuel context expression start
            generated finish) => child.supply_le_next) leftElaboration
      exact .or
        (PatternElaboratesUsing.trackContextSupport wellFormed contextWellFormed
          argumentsSupport bindingsSupport outerToStart leftElaboration)
        (PatternElaboratesUsing.trackContextSupport wellFormed
          contextWellFormed (argumentsSupport.extend_finish startToLeft)
          (bindingsSupport.extend_finish startToLeft)
          (Supply.le_trans outerToStart startToLeft) rightElaboration)
        bindingsEqual
  | embed lookup => exact .embed lookup
  | @app function fields bindings start scheme generatedFields finish lookup
      arity fieldsElaboration =>
      have startToFields : start.Le (scheme.instantiate start).2 := by
        simp [Supply.Le, DualScheme.instantiate]
      exact .app lookup arity
        (PatternsElaborateUsing.trackContextSupport wellFormed
          contextWellFormed (argumentsSupport.extend_finish startToFields)
          (bindingsSupport.extend_finish startToFields)
          (Supply.le_trans outerToStart startToFields) fieldsElaboration)
termination_by pattern.complexity * 2 + 1
decreasing_by
  all_goals simp_wf
  all_goals subst_vars
  all_goals simp
  all_goals omega

/-- List counterpart of `PatternElaboratesUsing.trackContextSupport`. -/
theorem PatternsElaborateUsing.trackContextSupport
    {signature : FrozenSignature} (wellFormed : signature.WellFormed)
    {fuel : Nat} {context : Context} {outerStart start finish : Supply}
    {arguments : PatternContext} {patterns : List Pattern} {bindings : List Ty}
    {generated : GeneratedPatterns}
    (contextWellFormed : outerStart.WellFormedFor context)
    (argumentsSupport : VariablesSupportProvenance context outerStart start
      (dualUnificationVars arguments))
    (bindingsSupport : VariablesSupportProvenance context outerStart start
      (Ty.unificationVarsList bindings))
    (outerToStart : outerStart.Le start)
    (derivation : PatternsElaborateUsing (M4.ElaboratesFuel signature fuel)
      signature context arguments patterns bindings start generated finish) :
    PatternsElaborateUsing
      (WellFormedFuelLeaf signature fuel)
      signature context arguments patterns bindings start generated finish := by
  cases derivation with
  | nil => exact .nil
  | @cons pattern patterns bindings start generatedPattern afterPattern
      generatedPatterns finish head tail =>
      have startToPattern := PatternElaboratesUsing.supply_le_next
        (fun {context expression start generated finish}
          (child : M4.ElaboratesFuel signature fuel context expression start
            generated finish) => child.supply_le_next) head
      have headSupport := head.supportProvenance wellFormed
        (fun {context expression start generated finish}
          (child : M4.ElaboratesFuel signature fuel context expression start
            generated finish) => child.supply_le_next)
        (fun {context expression start generated finish}
          (child : M4.ElaboratesFuel signature fuel context expression start
            generated finish) => child.supportProvenance wellFormed)
        argumentsSupport bindingsSupport outerToStart
      have outputBindings : VariablesSupportProvenance context outerStart
          afterPattern (Ty.unificationVarsList generatedPattern.bindings) := by
        intro candidate member
        exact headSupport candidate (by
          simp [GeneratedPattern.unificationVars, member])
      exact .cons
        (PatternElaboratesUsing.trackContextSupport wellFormed contextWellFormed
          argumentsSupport bindingsSupport outerToStart head)
        (PatternsElaborateUsing.trackContextSupport wellFormed
          contextWellFormed (argumentsSupport.extend_finish startToPattern) outputBindings
          (Supply.le_trans outerToStart startToPattern) tail)
termination_by Pattern.listComplexity patterns * 2
decreasing_by
  all_goals simp_wf
  all_goals subst_vars
  all_goals simp [Pattern.listComplexity]
  all_goals omega

end

/-- Full fuel-indexed fresh-renaming transport.  The proof simultaneously
tracks well-formed child contexts and the monotone supply boundary through
every callback-parametric M4 component. -/
theorem M4.ElaboratesFuel.rename
    {rho : VariableRenaming} {signature : FrozenSignature} {fuel : Nat}
    {context : Context} {expression : Expr} {start finish : Supply}
    {generated : Generated}
    (signatureWellFormed : signature.WellFormed)
    (derivation : M4.ElaboratesFuel signature fuel context expression start
      generated finish)
    (wellFormed : start.WellFormedFor context)
    (fixed : rho.FixesAtOrAbove start) :
    M4.ElaboratesFuel signature fuel (renameContext rho context) expression
      start (renameGenerated rho generated) finish := by
  induction fuel generalizing context expression start generated finish with
  | zero => simp [M4.ElaboratesFuel] at derivation
  | succ fuel induction =>
      cases expression with
      | var index =>
          simp only [M4.ElaboratesFuel] at derivation ⊢
          obtain ⟨scheme, lookup, rfl, rfl⟩ := derivation
          have renamedLookup :
              (renameContext rho context)[index]? =
                some (scheme.applyFree rho.substitution) := by
            simpa [renameContext, Context.applyFree] using
              congrArg (Option.map (Scheme.applyFree rho.substitution)) lookup
          have instantiated := Scheme.instantiate_variableRenaming_prefix rho
            scheme (fixed.mapsFrom_self.mapsPrefix scheme.tyArity scheme.capArity)
          refine ⟨scheme.applyFree rho.substitution, renamedLookup, ?_, ?_⟩
          · simp [renameGenerated, renameTy, instantiated]
          · rfl
      | lit literal =>
          simp only [M4.ElaboratesFuel] at derivation ⊢
          rcases derivation with ⟨rfl, rfl⟩
          simp [renameGenerated, renameTy, Ty.apply]
      | something =>
          simp only [M4.ElaboratesFuel] at derivation ⊢
          rcases derivation with ⟨rfl, rfl⟩
          simp [renameGenerated, renameTy, VariableRenaming.substitution,
            Ty.apply, Cap.apply, fixed.1]
      | lam body =>
          simp only [M4.ElaboratesFuel] at derivation ⊢
          obtain ⟨generatedBody, bodyElaboration, rfl⟩ := derivation
          have bodyTransport := induction bodyElaboration
            wellFormed.monomorphic_cons_nextTy
            (fixed.mono (Supply.le_nextTy start 1))
          have contextEquality :
              renameContext rho (.mono (.var ⟨start.ty⟩) :: context) =
                .mono (.var ⟨start.ty⟩) :: renameContext rho context := by
            simp [renameContext, Context.applyFree, Scheme.mono,
              Scheme.applyFree, VariableRenaming.substitution,
              Ty.apply, fixed.1]
          rw [contextEquality] at bodyTransport
          exact ⟨renameGenerated rho generatedBody, bodyTransport, by
            simp [Generated.fromLam, renameGenerated, renameTy,
              VariableRenaming.substitution, Ty.apply, fixed.1]⟩
      | app function argument =>
          simp only [M4.ElaboratesFuel] at derivation ⊢
          obtain ⟨generatedFunction, afterFunction, generatedArgument,
            afterArgument, functionElaboration, argumentElaboration, rfl, rfl⟩ :=
            derivation
          have functionTransport := induction
            functionElaboration wellFormed fixed
          have startToFunction := functionElaboration.supply_le_next
          have argumentTransport := induction
            argumentElaboration (wellFormed.mono startToFunction)
            (fixed.mono startToFunction)
          have startToArgument := Supply.le_trans startToFunction
            argumentElaboration.supply_le_next
          have domainFixed := fixed.1 ⟨afterArgument.ty⟩ startToArgument.1
          have resultFixed := fixed.1 ⟨afterArgument.ty + 1⟩
            (Nat.le_trans startToArgument.1 (Nat.le_add_right _ _))
          refine ⟨renameGenerated rho generatedFunction, afterFunction,
            renameGenerated rho generatedArgument, afterArgument,
            functionTransport, argumentTransport, ?_, rfl⟩
          simp [Generated.fromApp, renameGenerated, renameTy, renameEquation,
            renameObligation, Equation.apply, CheckObligation.apply,
            VariableRenaming.substitution, Ty.apply, List.map_append,
            domainFixed, resultFixed]
      | tuple items =>
          simp only [M4.ElaboratesFuel] at derivation ⊢
          obtain ⟨generatedItems, itemsElaboration, rfl⟩ := derivation
          have tracked := M4.ItemsElaborateUsing.trackScope wellFormed
            (Supply.le_refl start) itemsElaboration
          have transported := M4.ItemsElaborateUsing.rename
            (rho := rho)
            (fun {context expression supply generated next}
              (child : ScopedWellFormedFuelLeaf signature fuel start context
                expression supply generated next) =>
              induction child.2.2 child.2.1
                (fixed.mono child.1)) tracked
          exact ⟨renameGeneratedItems rho generatedItems, transported, by
            simp [renameGenerated, renameGeneratedItems, renameTy, Ty.apply]⟩
      | letE value body =>
          simp only [M4.ElaboratesFuel] at derivation ⊢
          obtain ⟨generatedValue, afterValue, valueElaboration, closure,
            generatedBody, absorbing, bodyElaboration, rfl⟩ := derivation
          have valueTransport := induction valueElaboration
            wellFormed fixed
          let renamedClosure := renameClosure rho closure
          have renamedAbsorbing : renamedClosure.Absorbing :=
            renameClosure_absorbing rho closure absorbing
          have valueIncrease := valueElaboration.supply_le_next
          have valueSupport := valueElaboration.supportProvenance
            signatureWellFormed
          have sourceBodySupply :=
            TypePM.Source.PrincipalBlockClosure.letBodySupply_eq closure
              absorbing valueSupport wellFormed valueIncrease
          have renamedWellFormed := fixed.wellFormedFor_renameContext wellFormed
          have renamedValueSupport := valueTransport.supportProvenance
            signatureWellFormed
          have targetBodySupply :=
            TypePM.Source.PrincipalBlockClosure.letBodySupply_eq renamedClosure
              renamedAbsorbing renamedValueSupport renamedWellFormed valueIncrease
          have bodyWellFormedAtValue :=
            TypePM.Source.PrincipalBlockClosure.closedContext_initialSupply_le
              closure absorbing valueSupport wellFormed valueIncrease
          have closedWellFormed : Supply.WellFormedFor
              (context.applyFree closure.substitution) afterValue :=
            bodyWellFormedAtValue
          have bodyWellFormed : Supply.WellFormedFor
              ((context.applyFree closure.substitution).generalize closure.target ::
                context.applyFree closure.substitution)
              (afterValue.join
                (context.applyFree closure.substitution).initialSupply) := by
            rw [sourceBodySupply]
            exact closedWellFormed.generalized_cons closure.target
          have startToBody : start.Le
              (afterValue.join
                (context.applyFree closure.substitution).initialSupply) :=
            Supply.le_trans valueElaboration.supply_le_next
              (Supply.le_join_left _ _)
          have bodyTransport := induction bodyElaboration
            bodyWellFormed (fixed.mono startToBody)
          have closedContextEquality := renameContext_applyClosure rho context closure
          have generalizedEquality :
              ((context.applyFree closure.substitution).generalize
                closure.target).applyFree rho.substitution =
              ((renameContext rho context).applyFree
                renamedClosure.substitution).generalize renamedClosure.target := by
            calc
              _ = (renameContext rho
                    (context.applyFree closure.substitution)).generalize
                    (renameTy rho closure.target) :=
                Context.generalize_variableRenaming_exact rho _ _
              _ = _ := by rw [closedContextEquality, renameClosure_target]
          have bodyContextEquality :
              renameContext rho
                ((context.applyFree closure.substitution).generalize
                    closure.target :: context.applyFree closure.substitution) =
              ((renameContext rho context).applyFree
                    renamedClosure.substitution).generalize renamedClosure.target ::
                (renameContext rho context).applyFree
                  renamedClosure.substitution := by
            change ((context.applyFree closure.substitution).generalize
              closure.target).applyFree rho.substitution ::
              renameContext rho (context.applyFree closure.substitution) = _
            rw [generalizedEquality, closedContextEquality]
          rw [bodyContextEquality] at bodyTransport
          have startsEqual :
              afterValue.join
                ((renameContext rho context).applyFree
                  renamedClosure.substitution).initialSupply =
              afterValue.join
                (context.applyFree closure.substitution).initialSupply := by
            rw [targetBodySupply, sourceBodySupply]
          have targetBodyTransport : M4.ElaboratesFuel signature fuel
              (((renameContext rho context).applyFree
                    renamedClosure.substitution).generalize renamedClosure.target ::
                (renameContext rho context).applyFree
                  renamedClosure.substitution)
              body
              (afterValue.join
                ((renameContext rho context).applyFree
                  renamedClosure.substitution).initialSupply)
              (renameGenerated rho generatedBody) finish := by
            rw [startsEqual]
            exact bodyTransport
          refine ⟨renameGenerated rho generatedValue, afterValue, valueTransport,
            renamedClosure, renameGenerated rho generatedBody, renamedAbsorbing,
            targetBodyTransport, ?_⟩
          rw [renameGenerated_fromLet,
            Context.interfaceEquations_renameVariables]
          congr 2
          exact (renameClosure_substitution rho closure).symm
      | ctor constructor arguments =>
          simp only [M4.ElaboratesFuel] at derivation ⊢
          obtain ⟨scheme, lookup, arity, closed, call⟩ := derivation
          have instantiatedFixed := Scheme.instantiate_rename_eq closed start fixed
          have startToCall : start.Le (scheme.instantiate start).2 := by
            simp [Supply.Le, Scheme.instantiate]
          have tracked := M4.CallElaboratesUsing.trackScope
            (wellFormed.mono startToCall) startToCall call
          have callTransport := M4.CallElaboratesUsing.rename
            (rho := rho) (boundary := start)
            (fun _ child => induction child.2.2 child.2.1
              (fixed.mono child.1))
            (fun child => child.2.2.supply_le_next) fixed startToCall tracked
          refine ⟨scheme, lookup, arity, closed, ?_⟩
          simpa [renameGenerated, instantiatedFixed] using callTransport
      | prim operation arguments =>
          simp only [M4.ElaboratesFuel] at derivation ⊢
          obtain ⟨scheme, lookup, arity, closed, call⟩ := derivation
          have instantiatedFixed := Scheme.instantiate_rename_eq closed start fixed
          have startToCall : start.Le (scheme.instantiate start).2 := by
            simp [Supply.Le, Scheme.instantiate]
          have tracked := M4.CallElaboratesUsing.trackScope
            (wellFormed.mono startToCall) startToCall call
          have callTransport := M4.CallElaboratesUsing.rename
            (rho := rho) (boundary := start)
            (fun _ child => induction child.2.2 child.2.1
              (fixed.mono child.1))
            (fun child => child.2.2.supply_le_next) fixed startToCall tracked
          refine ⟨scheme, lookup, arity, closed, ?_⟩
          simpa [renameGenerated, instantiatedFixed] using callTransport
      | ifE condition thenBranch elseBranch =>
          simp only [M4.ElaboratesFuel] at derivation ⊢
          have closed := conditionalScheme_closed
          have instantiatedFixed := Scheme.instantiate_rename_eq closed start fixed
          have startToCall : start.Le (conditionalScheme.instantiate start).2 := by
            simp [Supply.Le, Scheme.instantiate]
          have tracked := M4.CallElaboratesUsing.trackScope
            (wellFormed.mono startToCall) startToCall derivation
          have callTransport := M4.CallElaboratesUsing.rename
            (rho := rho) (boundary := start)
            (fun _ child => induction child.2.2 child.2.1
              (fixed.mono child.1))
            (fun child => child.2.2.supply_le_next) fixed startToCall tracked
          simpa [renameGenerated, instantiatedFixed] using callTransport
      | fixE body =>
          simp only [M4.ElaboratesFuel] at derivation ⊢
          have tracked := FixElaboratesUsing.trackScope wellFormed
            (Supply.le_refl start) derivation
          exact FixElaboratesUsing.rename
            (fun child => induction child.2.2 child.2.1
              (fixed.mono child.1)) fixed tracked
      | matcher clauses =>
          simp only [M4.ElaboratesFuel] at derivation ⊢
          have wellFormedTracked :=
            MatcherTyping.MatcherLiteralElaboratesUsing.trackContextSupport
              signatureWellFormed wellFormed derivation
          have tracked :=
            MatcherTyping.MatcherLiteralElaboratesUsing.trackBoundary
              wellFormedTracked
          exact MatcherTyping.MatcherLiteralElaboratesUsing.rename
            (fun child => induction child.2.2 child.2.1
              (fixed.mono child.1))
            (fun child => by
              rcases child with ⟨rfl, boundaryToSupply, child⟩
              exact PPatElaborates_rename signatureWellFormed fixed
                boundaryToSupply child)
            (fun child => by
              rcases child with ⟨rfl, boundaryToSupply, child⟩
              exact DPatElaborates_rename signatureWellFormed fixed
                boundaryToSupply child) fixed tracked
      | matchAll target matcher pattern body =>
          simp only [M4.ElaboratesFuel] at derivation ⊢
          have tracked := MatchAllElaboratesUsing.trackContextSupport
            signatureWellFormed wellFormed derivation
          exact MatchAllElaboratesUsing.rename
            (fun boundaryToSupply child =>
              induction child.2 child.1
                (fixed.mono boundaryToSupply))
            (fun child => child.2.supply_le_next) fixed signatureWellFormed
            (Supply.le_refl start) tracked
      | matchFirst target matcher arms =>
          simp only [M4.ElaboratesFuel] at derivation ⊢
          have tracked := MatchFirstTyping.ElaboratesUsing.trackContextSupport
            signatureWellFormed wellFormed derivation
          exact MatchFirstTyping.ElaboratesUsing.rename
            (fun boundaryToSupply child =>
              induction child.2 child.1
                (fixed.mono boundaryToSupply))
            (fun child => child.2.supply_le_next) fixed signatureWellFormed
            tracked

/-- Concrete witness for the architecture boundary. -/
theorem m4FreshRenamingTransport :
    TypePM.Source.M4.CompletenessArchitecture.M4FreshRenamingTransport := by
  exact fun signatureWellFormed derivation wellFormed fixed =>
    M4.ElaboratesFuel.rename signatureWellFormed derivation wellFormed fixed

end M4FreshRenaming

end TypePM.Source
