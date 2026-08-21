import TypePM.Source.FullM2Completion

/-!
# Ordinary Damas--Milner typing for the pattern-free source fragment

The types, type schemes, context, expressions, and typing judgment in this
module are independent of Type-PM.  The explicit embedding is capability-free:
it cannot construct matcher, slot, data, product, or capability-variable types.
-/

namespace TypePM.Source.DamasMilner

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

local macro "compute_unification" : tactic =>
  `(tactic|
    repeat
      rw [unifyLoop.eq_def]
      simp [reduce, tyEquations, capEquations, eliminatedVariable?,
        unificationVars, Equation.unificationVars, TypePM.Ty.unificationVars,
        TypePM.Ty.unificationVarsList, Cap.unificationVars,
        Cap.unificationVarsList, rawNodeCount, solvedNodeCount,
        Equation.solvedNodeCount, TypePM.Ty.nodeCount,
        TypePM.Ty.nodeCountList, Cap.nodeCount, Cap.nodeCountList,
        TypePM.Ty.occursTy, TypePM.Ty.occursTyList, Cap.occurs,
        Cap.occursList, Equation.apply, TypePM.Ty.apply,
        TypePM.Ty.applyList, Cap.apply, Cap.applyList, Subst.singleTy,
        Subst.singleCap, Subst.compose, Subst.id])

/-! ## Independent ordinary types and schemes -/

inductive Ty where
  | var (index : Nat)
  | int
  | fn (domain codomain : Ty)
deriving Repr, DecidableEq

def Ty.embed : Ty → TypePM.Ty
  | .var index => .var ⟨index⟩
  | .int => .int
  | .fn domain codomain => .fn domain.embed codomain.embed

def Ty.restrict? : TypePM.Ty → Option Ty
  | .var index => some (.var index.index)
  | .int => some .int
  | .fn domain codomain => return .fn (← restrict? domain) (← restrict? codomain)
  | _ => none

@[simp] theorem Ty.restrict_embed (target : Ty) :
    Ty.restrict? target.embed = some target := by
  induction target <;> simp_all [Ty.embed, Ty.restrict?]

def Ty.freeVars : Ty → List Nat
  | .var index => [index]
  | .int => []
  | .fn domain codomain => domain.freeVars ++ codomain.freeVars

inductive PolyTy where
  | free (index : Nat)
  | bound (index : Nat)
  | int
  | fn (domain codomain : PolyTy)
deriving Repr, DecidableEq

def PolyTy.WellScoped (arity : Nat) : PolyTy → Prop
  | .free _ | .int => True
  | .bound index => index < arity
  | .fn domain codomain => domain.WellScoped arity ∧ codomain.WellScoped arity

def PolyTy.openBound (bound : Nat → Ty) : PolyTy → Ty
  | .free index => .var index
  | .bound index => bound index
  | .int => .int
  | .fn domain codomain => .fn (domain.openBound bound) (codomain.openBound bound)

def PolyTy.close (bound : List Nat) : Ty → PolyTy
  | .var index =>
      if bound.contains index then .bound (bound.idxOf index) else .free index
  | .int => .int
  | .fn domain codomain => .fn (close bound domain) (close bound codomain)

def PolyTy.freeVars : PolyTy → List Nat
  | .free index => [index]
  | .bound _ | .int => []
  | .fn domain codomain => domain.freeVars ++ codomain.freeVars

theorem PolyTy.close_wellScoped (bound : List Nat) (target : Ty) :
    (PolyTy.close bound target).WellScoped bound.length := by
  induction target with
  | var index =>
      simp only [PolyTy.close]
      split <;> rename_i member
      · exact List.idxOf_lt_length_iff.mpr (List.contains_iff_mem.mp member)
      · trivial
  | int => trivial
  | fn domain codomain domainIH codomainIH => exact ⟨domainIH, codomainIH⟩

def PolyTy.embed : PolyTy → Source.PolyTy
  | .free index => .free ⟨index⟩
  | .bound index => .bound index
  | .int => .int
  | .fn domain codomain => .fn domain.embed codomain.embed

theorem PolyTy.embed_wellScoped {body : PolyTy} {arity : Nat}
    (scopeProof : body.WellScoped arity) :
    body.embed.WellScoped arity 0 := by
  induction body <;> simp_all [PolyTy.WellScoped, PolyTy.embed,
    Source.PolyTy.WellScoped]

@[simp] theorem PolyTy.embed_openBound (body : PolyTy)
    (bound : Nat → Ty) :
    (body.openBound bound).embed =
      body.embed.openBound (fun index => (bound index).embed) (fun _ => .any) := by
  induction body <;> simp_all [PolyTy.openBound, PolyTy.embed, Ty.embed,
    Source.PolyTy.openBound]

theorem idxOf_map_tyVar (names : List Nat) (index : Nat) :
    (names.map fun name => TypePM.TyVar.mk name).idxOf ⟨index⟩ =
      names.idxOf index := by
  induction names with
  | nil => rfl
  | cons head tail induction =>
      by_cases equality : head = index
      · subst head
        simp
      · have natBeq : (head == index) = false := by simp [equality]
        have tyBeq : (TypePM.TyVar.mk head == TypePM.TyVar.mk index) = false := by
          simp [equality]
        simp [List.idxOf_cons, natBeq, tyBeq, induction]

theorem PolyTy.embed_close (names : List Nat) (target : Ty) :
    (PolyTy.close names target).embed =
      Source.PolyTy.close (names.map fun index => TypePM.TyVar.mk index) []
        target.embed := by
  induction target with
  | var index =>
      by_cases member : index ∈ names
      · simp [PolyTy.close, PolyTy.embed, Ty.embed, Source.PolyTy.close,
          List.contains_iff_mem, member, idxOf_map_tyVar]
      · simp [PolyTy.close, PolyTy.embed, Ty.embed, Source.PolyTy.close,
          List.contains_iff_mem, member]
  | int => rfl
  | fn domain codomain domainIH codomainIH =>
      simp [PolyTy.close, PolyTy.embed, Source.PolyTy.close, Ty.embed,
        domainIH, codomainIH]

structure Scheme where
  arity : Nat
  body : PolyTy
  wellScoped : body.WellScoped arity
deriving Repr

def Scheme.mono (target : Ty) : Scheme :=
  ⟨0, PolyTy.close [] target, PolyTy.close_wellScoped [] target⟩

def Scheme.Instantiates (scheme : Scheme) (target : Ty) : Prop :=
  ∃ bound : Nat → Ty, target = scheme.body.openBound bound

def Scheme.freeVars (scheme : Scheme) : List Nat := scheme.body.freeVars

def Scheme.embed (scheme : Scheme) : Source.Scheme :=
  ⟨scheme.arity, 0, scheme.body.embed,
    PolyTy.embed_wellScoped scheme.wellScoped⟩

theorem PolyTy.open_close_nil (target : Ty) (bound : Nat → Ty) :
    (PolyTy.close [] target).openBound bound = target := by
  induction target <;> simp_all [PolyTy.close, PolyTy.openBound]

@[simp] theorem Scheme.embed_mono (target : Ty) :
    (Scheme.mono target).embed = Source.Scheme.mono target.embed := by
  apply Source.Scheme.eq_of_body_eq
  induction target <;> simp_all [Scheme.mono, Scheme.embed, PolyTy.close,
    PolyTy.embed, Source.Scheme.mono, Source.PolyTy.ofTy, Ty.embed]

theorem Scheme.instantiates_embed {scheme : Scheme} {target : Ty}
    (instanceOf : scheme.Instantiates target) :
    scheme.embed.Instantiates target.embed := by
  rcases instanceOf with ⟨bound, rfl⟩
  exact ⟨fun index => (bound index).embed, fun _ => .any,
    PolyTy.embed_openBound _ _⟩

abbrev Context := List Scheme

def Context.embed (context : Context) : Source.Context :=
  context.map Scheme.embed

def Context.freeVars (context : Context) : List Nat :=
  dedupFirst (context.flatMap Scheme.freeVars)

@[simp] theorem Context.embed_lookup {context : Context} {index : Nat}
    {scheme : Scheme} (lookup : context[index]? = some scheme) :
    context.embed[index]? = some scheme.embed := by
  simpa [Context.embed] using congrArg (Option.map Scheme.embed) lookup

/-! ## Independent pattern-free expressions -/

inductive Expr where
  | var (index : Nat)
  | lit (value : Int)
  | lam (body : Expr)
  | app (function argument : Expr)
  | letE (value body : Expr)
  | fixE (body : Expr)
deriving Repr, DecidableEq

def Expr.embed : Expr → Source.Expr
  | .var index => .var index
  | .lit value => .lit value
  | .lam body => .lam body.embed
  | .app function argument => .app function.embed argument.embed
  | .letE value body => .letE value.embed body.embed
  | .fixE body => .fixE body.embed

def Expr.restrict? : Source.Expr → Option Expr
  | .var index => some (.var index)
  | .lit value => some (.lit value)
  | .lam body => return .lam (← restrict? body)
  | .app function argument =>
      return .app (← restrict? function) (← restrict? argument)
  | .letE value body => return .letE (← restrict? value) (← restrict? body)
  | .fixE body => return .fixE (← restrict? body)
  | _ => none

@[simp] theorem Expr.restrict_embed (expression : Expr) :
    Expr.restrict? expression.embed = some expression := by
  induction expression <;> simp_all [Expr.embed, Expr.restrict?]

mutual

/-- Independent direct-self check for the small expression syntax.  The
tracked recursive variable may occur only in an application head. -/
def directSafe (tracked : Nat) : Expr → Bool
  | .var index => index != tracked
  | .lit _ => true
  | .lam body => directSafe (tracked + 1) body
  | .app function argument =>
      directHeadSafe tracked function && directSafe tracked argument
  | .letE value body =>
      directSafe tracked value && directSafe (tracked + 1) body
  | .fixE _ => false

/-- Application-head counterpart of `directSafe`; a variable at the head is
allowed, including the tracked recursive variable. -/
def directHeadSafe (tracked : Nat) : Expr → Bool
  | .var _ => true
  | .lit _ => true
  | .lam body => directSafe (tracked + 1) body
  | .app function argument =>
      directHeadSafe tracked function && directSafe tracked argument
  | .letE value body =>
      directSafe tracked value && directSafe (tracked + 1) body
  | .fixE _ => false

end

/-- Independent direct-self condition for the separate unary-fix extension. -/
def DirectSelf (body : Expr) : Prop := directSafe 1 body = true

instance (body : Expr) : Decidable (DirectSelf body) :=
  inferInstanceAs (Decidable (directSafe 1 body = true))

/-! ## Independent ordinary typing -/

/-- A declarative generalization certificate.  `names` are exactly the
variables abstracted from the value type; the ordinary typing rules never
refer to Type-PM schemes or capabilities. -/
inductive Generalizes (context : Context) (target : Ty) : Scheme → Prop where
  | intro (names : List Nat) (nodup : names.Nodup)
      (exactNames : ∀ name,
        name ∈ names ↔ name ∈ target.freeVars ∧ name ∉ context.freeVars) :
      Generalizes context target
        ⟨names.length, PolyTy.close names target,
          PolyTy.close_wellScoped names target⟩

inductive Typing : Context → Expr → Ty → Prop where
  | var {context index scheme target}
      (lookup : context[index]? = some scheme)
      (instanceOf : scheme.Instantiates target) :
      Typing context (.var index) target
  | lit {context value} : Typing context (.lit value) .int
  | lam {context body domain codomain}
      (bodyTyping : Typing (Scheme.mono domain :: context) body codomain) :
      Typing context (.lam body) (.fn domain codomain)
  | app {context function argument domain codomain}
      (functionTyping : Typing context function (.fn domain codomain))
      (argumentTyping : Typing context argument domain) :
      Typing context (.app function argument) codomain
  | letE {context value body valueType bodyType scheme}
      (valueTyping : Typing context value valueType)
      (generalizes : Generalizes context valueType scheme)
      (bodyTyping : Typing (scheme :: context) body bodyType) :
      Typing context (.letE value body) bodyType

/-- The direct unary fix rule is kept separate from ordinary M2
Damas--Milner typing.  Its body is an M2 expression under monomorphic
argument and self binders. -/
inductive FixTyping : Context → Expr → Ty → Ty → Prop where
  | fixE {context body domain codomain}
      (direct : DirectSelf body)
      (bodyTyping : Typing
        (Scheme.mono domain :: Scheme.mono (.fn domain codomain) :: context)
        body codomain) :
      FixTyping context body domain codomain

namespace Typing

theorem monoVar {context : Context} {index : Nat} {target : Ty}
    (lookup : context[index]? = some (Scheme.mono target)) :
    Typing context (.var index) target := by
  apply var lookup
  exact ⟨fun _ => .int, (PolyTy.open_close_nil target _).symm⟩

end Typing

/-! ## General representation theorem -/

/-- Ordinary capability-free typing over the public representations.  This
relation is syntax-directed and does not mention inference or constraints.
It is a representation bridge, not Type-PM's constraint-based `Source.Typing`.
-/
inductive EmbeddedTyping : Source.Context → Source.Expr → TypePM.Ty → Prop where
  | var {context index scheme target}
      (lookup : context[index]? = some scheme)
      (instanceOf : scheme.Instantiates target) :
      EmbeddedTyping context (.var index) target
  | lit {context value} : EmbeddedTyping context (.lit value) .int
  | lam {context body domain codomain}
      (bodyTyping : EmbeddedTyping (.mono domain :: context) body codomain) :
      EmbeddedTyping context (.lam body) (.fn domain codomain)
  | app {context function argument domain codomain}
      (functionTyping : EmbeddedTyping context function (.fn domain codomain))
      (argumentTyping : EmbeddedTyping context argument domain) :
      EmbeddedTyping context (.app function argument) codomain
  | letE {context value body valueType bodyType scheme}
      (valueTyping : EmbeddedTyping context value valueType)
      (generalizes : ∃ names : List Nat,
        scheme.tyArity = names.length ∧ scheme.capArity = 0 ∧
          scheme.body = Source.PolyTy.close
            (names.map fun index => TypePM.TyVar.mk index) [] valueType)
      (bodyTyping : EmbeddedTyping (scheme :: context) body bodyType) :
      EmbeddedTyping context (.letE value body) bodyType

inductive EmbeddedFixTyping : Source.Context → Source.Expr →
    TypePM.Ty → TypePM.Ty → Prop where
  | fixE {context body domain codomain}
      (direct : ∃ original : Expr,
        original.embed = body ∧ DirectSelf original)
      (bodyTyping : EmbeddedTyping
        (.mono domain :: .mono (.fn domain codomain) :: context) body codomain) :
      EmbeddedFixTyping context body domain codomain

theorem Typing.embed {context : Context} {expression : Expr} {target : Ty}
    (typing : Typing context expression target) :
    EmbeddedTyping context.embed expression.embed target.embed := by
  induction typing with
  | var lookup instanceOf =>
      exact .var (Context.embed_lookup lookup)
        (Scheme.instantiates_embed instanceOf)
  | lit => exact .lit
  | lam bodyTyping induction =>
      rw [Context.embed] at induction
      simp only [List.map_cons, Scheme.embed_mono] at induction
      exact EmbeddedTyping.lam induction
  | app _ _ functionIH argumentIH => exact .app functionIH argumentIH
  | letE _ generalizes _ valueIH bodyIH =>
      cases generalizes with
      | intro names nodup exactNames =>
          exact .letE valueIH
            ⟨names, rfl, rfl, by simp [Scheme.embed, PolyTy.embed_close]⟩ bodyIH

theorem FixTyping.embed {context : Context} {body : Expr} {domain codomain : Ty}
    (typing : FixTyping context body domain codomain) :
    EmbeddedFixTyping context.embed body.embed domain.embed codomain.embed := by
  cases typing with
  | fixE direct bodyTyping =>
      have bodyIH := Typing.embed bodyTyping
      rw [Context.embed] at bodyIH
      simp only [List.map_cons, Scheme.embed_mono, Ty.embed] at bodyIH
      exact .fixE ⟨_, rfl, direct⟩ bodyIH

/-! ## Regressions -/

def identityScheme : Scheme :=
  ⟨1, .fn (.bound 0) (.bound 0), by simp [PolyTy.WellScoped]⟩

def polymorphicIdentityAt (value : Int) : Expr :=
  .letE (.lam (.var 0)) (.app (.var 0) (.lit value))

theorem polymorphicIdentityAt_typing (value : Int) :
    Typing [] (polymorphicIdentityAt value) .int := by
  apply Typing.letE (valueType := .fn (.var 0) (.var 0))
      (scheme := identityScheme)
  · exact .lam (Typing.monoVar (by simp))
  · exact .intro [0] (by simp) (by
      intro name
      simp [Ty.freeVars, Context.freeVars, dedupFirst, dedup])
  · apply Typing.app (domain := .int)
    · apply Typing.var (scheme := identityScheme) (by simp)
      exact ⟨fun _ => .int, rfl⟩
    · exact .lit

def polymorphicIdentity : Expr := polymorphicIdentityAt 1

theorem polymorphicIdentity_typing :
    Typing [] polymorphicIdentity .int := by
  simpa [polymorphicIdentity] using polymorphicIdentityAt_typing 1

private def identityValueGenerated : Generated :=
  { target := .fn (.var ⟨0⟩) (.var ⟨0⟩)
    hard := []
    pending := [] }

private theorem emptyGenerated_close (target : TypePM.Ty) :
    inferGeneratedUsing unify { target := target, hard := [], pending := [] } =
      some {
        substitution := Subst.id
        target := target } := by
  unfold inferGeneratedUsing saturateUsing saturateLoop unify
  simp
  compute_unification
  simp [promoteUnder, residualEquations, Subst.compose,
    TypePM.Ty.apply, Cap.apply]
  compute_unification
  change target.apply Subst.id = target
  exact TypePM.Ty.apply_id target

private theorem identityValueGenerated_close :
    inferGeneratedUsing unify identityValueGenerated =
      some {
        substitution := Subst.id
        target := .fn (.var ⟨0⟩) (.var ⟨0⟩) } := by
  simpa [identityValueGenerated] using
    emptyGenerated_close (.fn (.var ⟨0⟩) (.var ⟨0⟩))

/-- Literals are a general closed DM fragment whose embedding is accepted by
public M2 inference in every source context. -/
theorem literal_infer_exact (signature : Signature) (context : Context)
    (value : Int) :
    Source.infer signature context.embed (.lit value) = some .int := by
  unfold Source.infer Source.elaborateRoot
  simp [Source.elaborate, emptyGenerated_close]

/-- Public constraint-based typing of every embedded DM literal. -/
theorem literal_sourceTyping {signature : Signature}
    (wellFormed : signature.WellFormed) (context : Context) (value : Int) :
    Source.Typing signature context.embed (.lit value) .int :=
  Source.Inference.infer_success_typing wellFormed
    (literal_infer_exact signature context value)

/-- Every DM derivation in the literal fragment embeds directly into the
public constraint-based typing relation, including its derived target. -/
theorem Typing.embed_literal {signature : Signature}
    (wellFormed : signature.WellFormed) {context : Context} {value : Int}
    {target : Ty} (typing : Typing context (.lit value) target) :
    Source.Typing signature context.embed (.lit value) target.embed := by
  cases typing
  simpa [Ty.embed] using literal_sourceTyping wellFormed context value

/-- Every DM variable derivation is accepted by public inference.  The
public result is its own fresh representative of the embedded scheme
instance, so this theorem states acceptance rather than literal type
equality. -/
theorem Typing.variable_infer_isSome {signature : Signature}
    {context : Context} {index : Nat} {target : Ty}
    (typing : Typing context (.var index) target) :
    Source.infer signature context.embed (.var index) ≠ none := by
  cases typing with
  | var lookup _ =>
      have embeddedLookup := Context.embed_lookup lookup
      unfold Source.infer Source.elaborateRoot
      simp [Source.elaborate, embeddedLookup, emptyGenerated_close]

private def polymorphicIdentityGenerated : Generated :=
  { target := .var ⟨3⟩
    hard := [.ty (.fn (.var ⟨1⟩) (.var ⟨1⟩))
      (.fn (.var ⟨2⟩) (.var ⟨3⟩))]
    pending := [⟨.int, .var ⟨2⟩⟩] }

private theorem polymorphicIdentityAt_elaborate (signature : Signature)
    (value : Int) :
    Source.elaborate signature []
      (polymorphicIdentityAt value).embed ⟨0, 0⟩ =
        some (polymorphicIdentityGenerated, ⟨4, 0⟩) := by
  have closeLiteral : inferGeneratedUsing unify
      { target := .fn (.var ⟨0⟩) (.var ⟨0⟩),
        hard := [], pending := [] } =
      some ({
        substitution := Subst.id
        target := (.fn (.var ⟨0⟩) (.var ⟨0⟩) : TypePM.Ty) } :
          InferenceResult) := by
    simpa [identityValueGenerated] using identityValueGenerated_close
  simp [polymorphicIdentityAt, Expr.embed, Source.elaborate,
    Source.Scheme.instantiate, Source.Scheme.mono,
    Source.Context.initialSupply, Supply.nextTy, TyVar.next, CapVar.next]
  rw [closeLiteral]
  simp [polymorphicIdentityGenerated, Source.Context.applyFree,
    Source.Context.generalize, Source.Context.generalizedTyVars,
    Source.Context.generalizedCapVars, Source.Context.freeTyVars,
    Source.Context.freeCapVars, Source.Context.interfaceEquations,
    Source.Generated.fromLet, Supply.join, Source.Scheme.boundTyInstance,
    Source.Scheme.boundCapInstance, Source.PolyTy.close,
    Source.PolyTy.openBound, TypePM.Ty.tyVars, TypePM.Ty.capVars,
    dedupFirst, dedup, TyVar.next, CapVar.next]

private theorem polymorphicIdentityGenerated_close :
    (inferGeneratedUsing unify polymorphicIdentityGenerated).bind
      (fun result => some result.target) = some .int := by
  unfold inferGeneratedUsing saturateUsing saturateLoop unify
  simp only [polymorphicIdentityGenerated]
  compute_unification
  simp [promoteUnder, TypePM.Ty.couldSpecial,
    TypePM.Ty.mayBecomeMatcher, TypePM.Ty.mayBecomeMatcherItems,
    TypePM.Ty.mayBecomeMatcherProduct,
    TypePM.Ty.mayBecomeExpectedSlot, TypePM.Ty.apply,
    TypePM.Ty.applyList, Cap.apply, Cap.applyList, Subst.compose,
    Subst.id, Subst.singleTy, Subst.singleCap]
  rw [saturateLoop.eq_def]
  simp [promoteUnder, TypePM.Ty.apply, TypePM.Ty.applyList, Cap.apply,
    Cap.applyList, Subst.compose, Subst.id, Subst.singleTy,
    Subst.singleCap]
  compute_unification
  simp [residualEquations, TypePM.Ty.apply, TypePM.Ty.applyList,
    Cap.apply, Cap.applyList, Subst.compose, Subst.id, Subst.singleTy,
    Subst.singleCap]
  compute_unification

/-- Public M2 inference accepts the entire integer-indexed family of
polymorphic identity lets represented by `polymorphicIdentityAt`. -/
theorem polymorphicIdentityAt_infer_exact (value : Int) :
    Source.infer Paper1Signature.signature []
      (polymorphicIdentityAt value).embed = some .int := by
  unfold Source.infer Source.elaborateRoot
  rw [show Source.Context.initialSupply [] = ⟨0, 0⟩ by rfl,
    polymorphicIdentityAt_elaborate Paper1Signature.signature]
  exact polymorphicIdentityGenerated_close

/-- The same executable bridge is independent of the source signature,
because the embedded family uses only variables, literals, lambdas,
applications, and `let`. -/
theorem polymorphicIdentityAt_infer_exact_for
    (signature : Signature) (value : Int) :
    Source.infer signature [] (polymorphicIdentityAt value).embed =
      some .int := by
  unfold Source.infer Source.elaborateRoot
  rw [show Source.Context.initialSupply [] = ⟨0, 0⟩ by rfl,
    polymorphicIdentityAt_elaborate signature]
  exact polymorphicIdentityGenerated_close

/-- The independent DM derivation has a genuine proof in the public
constraint-based `Source.Typing` relation, obtained through public inference
soundness rather than through `EmbeddedTyping`. -/
theorem polymorphicIdentityAt_sourceTyping (value : Int) :
    Source.Typing Paper1Signature.signature []
      (polymorphicIdentityAt value).embed .int :=
  Source.Inference.infer_success_typing Paper1Signature.wellFormed
    (polymorphicIdentityAt_infer_exact value)

theorem polymorphicIdentityAt_sourceTyping_for
    {signature : Signature} (wellFormed : signature.WellFormed)
    (value : Int) :
    Source.Typing signature [] (polymorphicIdentityAt value).embed .int :=
  Source.Inference.infer_success_typing wellFormed
    (polymorphicIdentityAt_infer_exact_for signature value)

theorem polymorphicIdentity_dm_and_source (value : Int) :
    Typing [] (polymorphicIdentityAt value) .int ∧
      Source.Typing Paper1Signature.signature []
        (polymorphicIdentityAt value).embed .int :=
  ⟨polymorphicIdentityAt_typing value,
    polymorphicIdentityAt_sourceTyping value⟩

/-!
## Boundary of the general bridge

The remaining general direction is the conventional Hindley--Milner
completeness statement

`Typing [] expression target →
  Source.Typing signature [] expression.embed target.embed`.

Unlike `polymorphicIdentityAt_sourceTyping_for`, proving it requires a
derivation-parametric alignment between ordinary DM generalization and the
principal closure chosen at every public `letE` boundary.  In particular,
the public generalized context is built from the principal closure target,
whereas a DM derivation may choose any instance of that principal type.  The
statement is recorded here as the exact next theorem, rather than hidden
behind an unproved proposition alias.
-/

def directFix : Expr := .fixE (.app (.var 1) (.var 0))

theorem directFix_typing (domain codomain : Ty) :
    FixTyping [] (.app (.var 1) (.var 0)) domain codomain := by
  apply FixTyping.fixE
  · rfl
  · apply Typing.app (domain := domain)
    · exact Typing.monoVar (by simp)
    · exact Typing.monoVar (by simp)

end TypePM.Source.DamasMilner
