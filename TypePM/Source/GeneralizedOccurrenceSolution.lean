import TypePM.AbsorbingBlockClosure
import TypePM.RuntimeTyping
import TypePM.SchemeTransport
import TypePM.Source.ElaborationTransport
import TypePM.Source.M4LetRuntimeWorldStep

/-!
# Semantic solutions for generalized `let` occurrences

Closing a `let` right-hand side chooses one exact principal substitution, but
each use of the generalized binding may choose a different fresh
instantiation.  This module constructs the corresponding child semantic
solution directly from the principal closure, the finite outer-context
interface, and the occurrence supply.  It is independent of any evaluator,
search strategy, or source/runtime typing relation.

The context agreement below is deliberately scheme-level:
`context.applyFree child = context.applyFree outer`.  An unconditional claim
about every already-instantiated scheme occurrence would be false because an
arbitrary instantiation supply may reuse a name changed by the right-hand-side
closure.  Such a pointwise occurrence claim additionally needs freshness or a
prefix-agreement premise.  Consequently this construction does not by itself
transport `SchemeFuelValueSafe` or `SchemeDemandEnvironmentSafe` from an outer
solution to an open polymorphic child world.
-/

namespace TypePM.Source

/-- Replace the variables generalized from `target` by the fresh names chosen
at one occurrence, and apply `outer` everywhere else. -/
def Context.generalizedOccurrencePostSubstitution
    (context : Context) (target : Ty) (supply : Supply)
    (outer : Subst) : Subst :=
  { ty := fun index =>
      if context.generalizedTyVars target |>.contains index then
        outer.ty
          (Scheme.boundTyInstance supply
            ((context.generalizedTyVars target).idxOf index))
      else
        outer.ty index
    cap := fun index =>
      if context.generalizedCapVars target |>.contains index then
        outer.cap
          (Scheme.boundCapInstance supply
            ((context.generalizedCapVars target).idxOf index))
      else
        outer.cap index }

namespace Context

theorem generalizedOccurrencePostSubstitution_ty_of_not_generalized
    {context : Context} {target : Ty} {supply : Supply} {outer : Subst}
    {index : TyVar}
    (notGeneralized : index ∉ context.generalizedTyVars target) :
    (context.generalizedOccurrencePostSubstitution target supply outer).ty
        index = outer.ty index := by
  simp only [generalizedOccurrencePostSubstitution]
  have absent : (context.generalizedTyVars target).contains index = false := by
    apply Bool.eq_false_iff.mpr
    intro present
    exact notGeneralized (List.contains_iff_mem.mp present)
  rw [absent]
  simp

theorem generalizedOccurrencePostSubstitution_cap_of_not_generalized
    {context : Context} {target : Ty} {supply : Supply} {outer : Subst}
    {index : CapVar}
    (notGeneralized : index ∉ context.generalizedCapVars target) :
    (context.generalizedOccurrencePostSubstitution target supply outer).cap
        index = outer.cap index := by
  simp only [generalizedOccurrencePostSubstitution]
  have absent : (context.generalizedCapVars target).contains index = false := by
    apply Bool.eq_false_iff.mpr
    intro present
    exact notGeneralized (List.contains_iff_mem.mp present)
  rw [absent]
  simp

private theorem generalizedOccurrencePostSubstitution_ty_hit
    {context : Context} {target : Ty} {supply : Supply} {outer : Subst}
    {index : TyVar}
    (membership : index ∈ context.generalizedTyVars target) :
    (context.generalizedOccurrencePostSubstitution target supply outer).ty
        index =
      outer.ty
        (Scheme.boundTyInstance supply
          ((context.generalizedTyVars target).idxOf index)) := by
  simp only [generalizedOccurrencePostSubstitution]
  have present : (context.generalizedTyVars target).contains index = true :=
    List.contains_iff_mem.mpr membership
  rw [present]
  simp

private theorem generalizedOccurrencePostSubstitution_cap_hit
    {context : Context} {target : Ty} {supply : Supply} {outer : Subst}
    {index : CapVar}
    (membership : index ∈ context.generalizedCapVars target) :
    (context.generalizedOccurrencePostSubstitution target supply outer).cap
        index =
      outer.cap
        (Scheme.boundCapInstance supply
          ((context.generalizedCapVars target).idxOf index)) := by
  simp only [generalizedOccurrencePostSubstitution]
  have present : (context.generalizedCapVars target).contains index = true :=
    List.contains_iff_mem.mpr membership
  rw [present]
  simp

theorem generalizedOccurrencePostSubstitution_agrees
    (context : Context) (target : Ty) (supply : Supply) (outer : Subst) :
    context.SubstitutionsAgree
      (context.generalizedOccurrencePostSubstitution target supply outer)
      outer := by
  constructor
  · intro index contextMember
    apply generalizedOccurrencePostSubstitution_ty_of_not_generalized
    intro generalized
    exact (Context.mem_generalizedTyVars.mp generalized).2 contextMember
  · intro index contextMember
    apply generalizedOccurrencePostSubstitution_cap_of_not_generalized
    intro generalized
    exact (Context.mem_generalizedCapVars.mp generalized).2 contextMember

theorem applyFree_generalizedOccurrencePostSubstitution
    (context : Context) (target : Ty) (supply : Supply) (outer : Subst) :
    context.applyFree
        (context.generalizedOccurrencePostSubstitution target supply outer) =
      context.applyFree outer :=
  Context.applyFree_eq_of_substitutionsAgree
    (context.generalizedOccurrencePostSubstitution_agrees target supply outer)

end Context

private theorem idxOf_getElem_of_nodup
    {α : Type} [BEq α] [LawfulBEq α]
    (items : List α) (nodup : items.Nodup) (position : Nat)
    (within : position < items.length) :
    items.idxOf items[position] = position := by
  induction items generalizing position with
  | nil => simp at within
  | cons head tail induction =>
      cases position with
      | zero => simp
      | succ position =>
          have tailWithin : position < tail.length := by simpa using within
          have headNotMem : head ∉ tail := (List.nodup_cons.mp nodup).1
          have notHead : head ≠ tail[position] := by
            intro equality
            apply headNotMem
            rw [equality]
            exact List.getElem_mem tailWithin
          have beqFalse : (head == tail[position]) = false := by
            simp [notHead]
          simp [List.idxOf_cons, beqFalse,
            induction (List.nodup_cons.mp nodup).2 position tailWithin]

private theorem generalizedOccurrence_target
    (context : Context) (target : Ty) (supply : Supply) (outer : Subst) :
    target.apply
        (context.generalizedOccurrencePostSubstitution target supply outer) =
      ((context.generalize target).instantiate supply).1.apply outer := by
  let scheme := context.generalize target
  let post := context.generalizedOccurrencePostSubstitution target supply outer
  let boundTy := context.generalizedTyVars target
  let boundCap := context.generalizedCapVars target
  have postAgrees :=
    context.generalizedOccurrencePostSubstitution_agrees target supply outer
  have schemeFreeEq : scheme.applyFree post = scheme.applyFree outer := by
    apply Scheme.applyFree_eq_of_agree
    · intro index membership
      apply postAgrees.1 index
      exact (Context.mem_generalize_freeTyVars.mp (by
        simpa [scheme] using membership)).2
    · intro index membership
      apply postAgrees.2 index
      exact (Context.mem_generalize_freeCapVars.mp (by
        simpa [scheme] using membership)).2
  have bodyFreeEq :
      scheme.body.applyFree post = scheme.body.applyFree outer := by
    exact congrArg Scheme.body schemeFreeEq
  have boundTyNodup : boundTy.Nodup := by
    dsimp only [boundTy, Context.generalizedTyVars]
    exact dedupFirst_nodup _
  have boundCapNodup : boundCap.Nodup := by
    dsimp only [boundCap, Context.generalizedCapVars]
    exact dedupFirst_nodup _
  calc
    target.apply post =
        (scheme.body.openBound (tyNameAt boundTy) (capNameAt boundCap)).apply
          post := by
      exact congrArg (fun current : Ty => current.apply post) (by
        simpa [scheme, boundTy, boundCap] using
          (context.generalize_open target).symm)
    _ = (scheme.body.applyFree post).openBound
          (fun position => (tyNameAt boundTy position).apply post)
          (fun position => (capNameAt boundCap position).apply post.cap) := by
      exact (PolyTy.openBound_applyFree post (tyNameAt boundTy)
        (capNameAt boundCap) scheme.body).symm
    _ = (scheme.body.applyFree outer).openBound
          (fun position =>
            (Ty.var (Scheme.boundTyInstance supply position)).apply outer)
          (fun position =>
            (Cap.var (Scheme.boundCapInstance supply position)).apply
              outer.cap) := by
      rw [bodyFreeEq]
      apply Scheme.PolyTy.openBound_eq_of_wellScoped
        (PolyTy.applyFree_wellScoped outer scheme.tyArity scheme.capArity
          scheme.wellScoped)
      · intro position within
        have boundWithin : position < boundTy.length := by
          simpa [scheme, boundTy] using within
        let index := boundTy[position]
        have membership : index ∈ boundTy := List.getElem_mem boundWithin
        have nameEq : tyNameAt boundTy position = .var index := by
          simp [tyNameAt, index, List.getElem?_eq_getElem boundWithin]
        have hit := Context.generalizedOccurrencePostSubstitution_ty_hit
          (context := context) (target := target) (supply := supply)
          (outer := outer) (index := index) (by
            simpa [boundTy] using membership)
        have indexEq : boundTy.idxOf index = position := by
          exact idxOf_getElem_of_nodup boundTy boundTyNodup position boundWithin
        calc
          (tyNameAt boundTy position).apply post = post.ty index := by
            rw [nameEq]
            rfl
          _ = outer.ty (Scheme.boundTyInstance supply (boundTy.idxOf index)) := by
            simpa [post, boundTy] using hit
          _ = outer.ty (Scheme.boundTyInstance supply position) := by
            rw [indexEq]
          _ =
              (Ty.var (Scheme.boundTyInstance supply position)).apply outer :=
            rfl
      · intro position within
        have boundWithin : position < boundCap.length := by
          simpa [scheme, boundCap] using within
        let index := boundCap[position]
        have membership : index ∈ boundCap := List.getElem_mem boundWithin
        have nameEq : capNameAt boundCap position = .var index := by
          simp [capNameAt, index, List.getElem?_eq_getElem boundWithin]
        have hit := Context.generalizedOccurrencePostSubstitution_cap_hit
          (context := context) (target := target) (supply := supply)
          (outer := outer) (index := index) (by
            simpa [boundCap] using membership)
        have indexEq : boundCap.idxOf index = position := by
          exact idxOf_getElem_of_nodup boundCap boundCapNodup position boundWithin
        calc
          (capNameAt boundCap position).apply post.cap = post.cap index := by
            rw [nameEq]
            rfl
          _ = outer.cap
              (Scheme.boundCapInstance supply (boundCap.idxOf index)) := by
            simpa [post, boundCap] using hit
          _ = outer.cap (Scheme.boundCapInstance supply position) := by
            rw [indexEq]
          _ =
              (Cap.var (Scheme.boundCapInstance supply position)).apply
                outer.cap := rfl
    _ = (scheme.body.openBound
          (fun position => .var (Scheme.boundTyInstance supply position))
          (fun position => .var (Scheme.boundCapInstance supply position))).apply
            outer := by
      exact PolyTy.openBound_applyFree outer
        (fun position => .var (Scheme.boundTyInstance supply position))
        (fun position => .var (Scheme.boundCapInstance supply position))
        scheme.body
    _ = ((context.generalize target).instantiate supply).1.apply outer := by
      rfl

/-- One occurrence-specific semantic solution for an exact generalized
right-hand-side closure.  `postSubstitution` records how the occurrence is
chosen; `solution_eq` makes explicit that the child solution is a
postcomposition of the exact principal closure. -/
structure GeneralizedOccurrenceSolution
    {generated : Generated} (context : Context)
    (closure : PrincipalBlockClosure generated) (outer : Subst)
    (supply : Supply) : Type where
  postSubstitution : Subst
  solution : Subst
  solution_eq :
    solution = Subst.compose postSubstitution closure.substitution
  semantic : generated.SemanticSolution solution
  target_eq :
    generated.target.apply solution =
      (Scheme.instantiate
        ((context.applyFree closure.substitution).generalize closure.target)
        supply).1.apply outer
  context_eq : context.applyFree solution = context.applyFree outer
  closure_absorbed :
    Subst.compose solution closure.substitution = solution

namespace GeneralizedOccurrenceSolution

/-- Pointwise form of `context_eq` for one exact source-context lookup. -/
theorem scheme_applyFree_eq
    {position : Nat} {scheme : Scheme}
    (occurrence : GeneralizedOccurrenceSolution context closure outer supply)
    (sourceLookup : context[position]? = some scheme) :
    scheme.applyFree occurrence.solution = scheme.applyFree outer := by
  have contexts := congrArg (fun current : Context => current[position]?)
    occurrence.context_eq
  simpa [Context.applyFree, sourceLookup] using contexts

/-- A finite strengthening from scheme-level agreement to one instantiated
source occurrence.  The additional premises require `child` and `outer` to
agree on every position in the fresh prefixes opened by this scheme. -/
theorem schemeOccurrence_eq_of_prefix_agreement
    {position : Nat} {scheme : Scheme}
    (occurrence : GeneralizedOccurrenceSolution context closure outer supply)
    (sourceLookup : context[position]? = some scheme)
    (occurrenceSupply : Supply)
    (tyPrefix : ∀ offset, offset < scheme.tyArity →
      occurrence.solution.ty (Scheme.boundTyInstance occurrenceSupply offset) =
        outer.ty (Scheme.boundTyInstance occurrenceSupply offset))
    (capPrefix : ∀ offset, offset < scheme.capArity →
      occurrence.solution.cap
          (Scheme.boundCapInstance occurrenceSupply offset) =
        outer.cap (Scheme.boundCapInstance occurrenceSupply offset)) :
    (scheme.instantiate occurrenceSupply).1.apply occurrence.solution =
      (scheme.instantiate occurrenceSupply).1.apply outer := by
  have schemeEq := occurrence.scheme_applyFree_eq sourceLookup
  have bodyEq : scheme.body.applyFree occurrence.solution =
      scheme.body.applyFree outer :=
    congrArg Scheme.body schemeEq
  change
    Ty.apply occurrence.solution (scheme.body.openBound
        (fun offset => .var (Scheme.boundTyInstance occurrenceSupply offset))
        (fun offset => .var (Scheme.boundCapInstance occurrenceSupply offset))) =
      Ty.apply outer (scheme.body.openBound
        (fun offset => .var (Scheme.boundTyInstance occurrenceSupply offset))
        (fun offset => .var (Scheme.boundCapInstance occurrenceSupply offset)))
  rw [← PolyTy.openBound_applyFree, ← PolyTy.openBound_applyFree, bodyEq]
  apply Scheme.PolyTy.openBound_eq_of_wellScoped
    (PolyTy.applyFree_wellScoped outer scheme.tyArity scheme.capArity
      scheme.wellScoped)
  · intro offset within
    exact tyPrefix offset within
  · intro offset within
    exact capPrefix offset within

/-- Strong fixed-stream corollary of
`schemeOccurrence_eq_of_prefix_agreement`.  It is convenient but generally
stronger than the finite condition needed by an actual occurrence. -/
theorem schemeOccurrence_eq_of_fixed
    {position : Nat} {scheme : Scheme}
    (occurrence : GeneralizedOccurrenceSolution context closure outer supply)
    (sourceLookup : context[position]? = some scheme)
    (occurrenceSupply : Supply)
    (childFixed : occurrenceSupply.FixedBy occurrence.solution)
    (outerFixed : occurrenceSupply.FixedBy outer) :
    (scheme.instantiate occurrenceSupply).1.apply occurrence.solution =
      (scheme.instantiate occurrenceSupply).1.apply outer := by
  apply occurrence.schemeOccurrence_eq_of_prefix_agreement sourceLookup
    occurrenceSupply
  · intro offset _within
    simpa [Scheme.boundTyInstance] using
      (childFixed.1 offset).trans (outerFixed.1 offset).symm
  · intro offset _within
    simpa [Scheme.boundCapInstance] using
      (childFixed.2 offset).trans (outerFixed.2 offset).symm

end GeneralizedOccurrenceSolution

private theorem semanticSolution_postcompose
    {generated : Generated} {earlier : Subst}
    (semantic : generated.SemanticSolution earlier) (later : Subst) :
    generated.SemanticSolution (Subst.compose later earlier) := by
  constructor
  · exact solves_postcompose semantic.1 later
  · intro obligation membership
    obtain ⟨conversionClass, conversion⟩ := semantic.2 obligation membership
    exact ⟨conversionClass, by
      simpa only [Ty.apply_compose] using
        TypePM.Runtime.CheckConversion.apply conversion later⟩

/-- Construct the occurrence solution from the exact principal closure.  The
absorbing closure law is used to record that applying the right-hand-side
principal substitution again has no effect on the child solution. -/
def PrincipalBlockClosure.generalizedOccurrenceSolution
    {generated : Generated} (closure : PrincipalBlockClosure generated)
    (absorbing : closure.Absorbing) (context : Context) (outer : Subst)
    (interfaceSolved :
      Solves outer (context.interfaceEquations closure.substitution))
    (supply : Supply) :
    GeneralizedOccurrenceSolution context closure outer supply := by
  let closedContext := context.applyFree closure.substitution
  let post := closedContext.generalizedOccurrencePostSubstitution
    closure.target supply outer
  let child := Subst.compose post closure.substitution
  refine
    { postSubstitution := post
      solution := child
      solution_eq := rfl
      semantic := semanticSolution_postcompose
        (TypePM.Source.Typing.PrincipalBlockClosure.semanticSolution closure)
        post
      target_eq := ?_
      context_eq := ?_
      closure_absorbed := ?_ }
  · change generated.target.apply child = _
    calc
      generated.target.apply child = closure.target.apply post := by
        simp [child, PrincipalBlockClosure.target, Ty.apply_compose]
      _ =
          ((closedContext.generalize closure.target).instantiate supply).1.apply
            outer := generalizedOccurrence_target closedContext closure.target
              supply outer
      _ = _ := rfl
  · change context.applyFree child = context.applyFree outer
    calc
      context.applyFree child = closedContext.applyFree post := by
        simp [child, closedContext, Context.applyFree_compose]
      _ = closedContext.applyFree outer := by
        exact Context.applyFree_generalizedOccurrencePostSubstitution
          closedContext closure.target supply outer
      _ = context.applyFree outer := by
        exact (context.applyFree_interface_transport closure.substitution outer
          interfaceSolved).symm
  · change Subst.compose child closure.substitution = child
    calc
      Subst.compose child closure.substitution =
          Subst.compose post
            (Subst.compose closure.substitution closure.substitution) := by
        exact (Subst.compose_assoc post closure.substitution
          closure.substitution).symm
      _ = Subst.compose post closure.substitution := by
        rw [closure.substitution_idempotent absorbing]
      _ = child := rfl

namespace M4.LetRuntimeWorld

/-- Exact M4 `letE` wrapper.  It consumes precisely the right-hand-side
principal closure, absorbing proof, and outer interface solution stored in
the body world; no evaluation or search result is assumed. -/
def generalizedOccurrenceSolution
    {signature : FrozenSignature} {context : Context}
    {value body : Expr} {supply : Supply} {generated : Generated}
    {next : Supply} {fuel : Nat} {outer : Subst}
    {runtimeContext : List Ty} {provenance : List Bool}
    (world : LetRuntimeWorld (signature := signature) (context := context)
      (value := value) (body := body) (supply := supply)
      (generated := generated) (next := next) fuel outer runtimeContext
      provenance)
    (occurrenceSupply : Supply) :
    TypePM.Source.GeneralizedOccurrenceSolution
      (generated := world.valueGenerated) context world.valueClosure outer
        occurrenceSupply :=
  TypePM.Source.PrincipalBlockClosure.generalizedOccurrenceSolution
    world.valueClosure world.valueAbsorbing context outer world.interfaceSolved
      occurrenceSupply

end M4.LetRuntimeWorld

end TypePM.Source
