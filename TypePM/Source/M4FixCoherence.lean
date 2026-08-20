import TypePM.Source.M4FreshRenamingTransport
import TypePM.Source.M4OrdinaryCoherence

/-!
# Coherence for M4 recursive-function roots

The `fixE` rule reserves its domain and codomain before elaborating the body.
Both derivations therefore use the same body context and body supply.  Body
coherence can be lifted through the common recursive-function result shape and
the common final equation, then upgraded by the general M4 supported-to-full
closure theorem.
-/

namespace TypePM.Source.M4.CompletenessArchitecture

open TypePM.Source
open InterfaceAliasDecomposition.AliasFreshness

private theorem fixBodyStart_le (body : Expr) (start : Supply) :
    start.Le (Fix.bodySupply body start) := by
  simp only [Fix.bodySupply]
  split <;> simp [Supply.Le, Supply.nextTy]

private theorem fixBodyWellFormed
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

private theorem fixDomainAvoids
    {body : Expr} {start finish : Supply} {hidden : List UnificationVar}
    (fresh : VariablesFreshIn (Fix.bodySupply body start) finish hidden) :
    TypeAvoids hidden (Fix.domain body start) := by
  intro candidate member hiddenMember
  have range := fresh candidate hiddenMember
  have earlier : candidate.FreshIn start (Fix.bodySupply body start) := by
    cases candidate <;> simp only [Fix.domain] at member <;>
      split at member <;>
      simp_all [Fix.bodySupply, Ty.unificationVars, Cap.unificationVars,
        UnificationVar.FreshIn, Supply.nextTy] <;> omega
  cases candidate <;>
    simp only [UnificationVar.FreshIn] at earlier range <;> omega

private theorem fixCodomainAvoids
    {body : Expr} {start finish : Supply} {hidden : List UnificationVar}
    (fresh : VariablesFreshIn (Fix.bodySupply body start) finish hidden) :
    TypeAvoids hidden (Fix.codomain body start) := by
  intro candidate member hiddenMember
  have range := fresh candidate hiddenMember
  have earlier : candidate.FreshIn start (Fix.bodySupply body start) := by
    cases candidate <;> simp only [Fix.codomain] at member <;>
      split at member <;>
      simp_all [Fix.bodySupply, Ty.unificationVars, Cap.unificationVars,
        UnificationVar.FreshIn, Supply.nextTy] <;> omega
  cases candidate <;>
    simp only [UnificationVar.FreshIn] at earlier range <;> omega

private theorem entailedPendingEq_weakenAppendEquation
    {reference : List Equation} {left right : List CheckObligation}
    (aligned : EntailedPendingEq reference left right) (equation : Equation) :
    EntailedPendingEq (reference ++ [equation]) left right := by
  induction aligned with
  | nil => exact .nil
  | cons head tail induction =>
      exact .cons
        (head.weaken (fun substitution solved =>
          (solves_append substitution reference [equation]).mp solved |>.1))
        induction

/-- Semantic alignment survives the fixed recursive-function wrapper. -/
private theorem entailedGeneratedAlignment_fromFix
    {left right : Generated} (domain codomain : Ty)
    (aligned : EntailedGeneratedAlignment left right) :
    EntailedGeneratedAlignment
      (Generated.fromFix domain codomain left)
      (Generated.fromFix domain codomain right) := by
  have hard : HardEquivalent
      (left.hard ++ [.ty left.target codomain])
      (right.hard ++ [.ty right.target codomain]) := by
    intro substitution
    simp only [solves_append, solves_cons, solves_nil, and_true]
    constructor
    · rintro ⟨leftSolved, equationSolved⟩
      have targetEquality := aligned.targetEntailed substitution leftSolved
      exact ⟨(aligned.hardEquivalent substitution).mp leftSolved, by
        simpa [Equation.Holds] using targetEquality.symm ▸ equationSolved⟩
    · rintro ⟨rightSolved, equationSolved⟩
      have leftSolved :=
        (aligned.hardEquivalent substitution).mpr rightSolved
      have targetEquality := aligned.targetEntailed substitution leftSolved
      exact ⟨leftSolved, by
        simpa [Equation.Holds] using targetEquality ▸ equationSolved⟩
  refine ⟨?_, EntailedTypeEq.refl _ (.fn domain codomain), ?_⟩
  · simpa [Generated.fromFix] using hard
  · simpa [Generated.fromFix] using
      entailedPendingEq_weakenAppendEquation aligned.pendingAligned
        (.ty left.target codomain)

private theorem addAll_fromFix
    (aliases : List FreshAliasSequence.Alias) (domain codomain : Ty)
    (body : Generated) :
    FreshAliasSequence.addAll aliases
        (Generated.fromFix domain codomain body) =
      Generated.fromFix domain codomain
        (FreshAliasSequence.addAll aliases body) := by
  induction aliases generalizing body with
  | nil => rfl
  | cons alias aliases induction =>
      rw [FreshAliasSequence.addAll, FreshAliasSequence.addAll]
      have one : alias.add (Generated.fromFix domain codomain body) =
          Generated.fromFix domain codomain (alias.add body) := by
        cases alias <;> cases body <;>
          simp [FreshAliasSequence.Alias.add,
            FreshAliasElimination.addTyAlias,
            FreshAliasElimination.addCapAlias, Generated.fromFix]
      rw [one]
      exact induction (alias.add body)

private theorem scopedBy_fromFix
    {body : Generated} {aliases : List FreshAliasSequence.Alias}
    {hidden : List UnificationVar} {domain codomain : Ty}
    (scopeProof : ScopedBy body.unificationVars aliases)
    (freshInHidden : ∀ alias, alias ∈ aliases →
      freshVariable alias ∈ hidden)
    (domainAvoids : TypeAvoids hidden domain)
    (codomainAvoids : TypeAvoids hidden codomain) :
    ScopedBy (Generated.fromFix domain codomain body).unificationVars
      aliases := by
  refine ⟨scopeProof.1, ?_⟩
  intro alias aliasMember
  have endpoints := scopeProof.2 alias aliasMember
  have hiddenMember := freshInHidden alias aliasMember
  constructor
  · intro member
    by_cases bodyMember : freshVariable alias ∈ body.unificationVars
    · exact endpoints.1 bodyMember
    · have outside :
          freshVariable alias ∈ domain.unificationVars ∨
            freshVariable alias ∈ codomain.unificationVars := by
        simp [Generated.fromFix, Generated.unificationVars,
          TypePM.unificationVars, Equation.unificationVars]
          at member bodyMember ⊢
        simp_all [Ty.unificationVars]
      rcases outside with domainMember | codomainMember
      · exact domainAvoids _ domainMember hiddenMember
      · exact codomainAvoids _ codomainMember hiddenMember
  · have existing := endpoints.2
    simp only [Generated.unificationVars, List.mem_append] at existing
    simp only [Generated.fromFix, Generated.unificationVars,
      Ty.unificationVars, Equation.unificationVars,
      TypePM.unificationVars, unificationVars_append,
      List.mem_append]
    rcases existing with (targetMember | hardMember) | pendingMember
    · exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inl targetMember))))
    · exact Or.inl (Or.inr (Or.inl hardMember))
    · exact Or.inr pendingMember

/-- Lift a supported body certificate through the deterministic `fixE`
generated-block wrapper. -/
private def supportedCertificate_fromFix
    {start next : Supply} {left right : Generated}
    (certificate : SupportedEntailedAlignmentCertificate start next left right)
    (domain codomain : Ty)
    (domainAvoids : TypeAvoids certificate.hidden domain)
    (codomainAvoids : TypeAvoids certificate.hidden codomain) :
    SupportedEntailedAlignmentCertificate start next
      (Generated.fromFix domain codomain left)
      (Generated.fromFix domain codomain right) :=
  { hidden := certificate.hidden
    hiddenFresh := certificate.hiddenFresh
    leftAliases := certificate.leftAliases
    rightAliases := certificate.rightAliases
    leftAliasFresh := certificate.leftAliasFresh
    rightAliasFresh := certificate.rightAliasFresh
    leftScoped := scopedBy_fromFix certificate.leftScoped
      certificate.leftAliasFresh domainAvoids codomainAvoids
    rightScoped := scopedBy_fromFix certificate.rightScoped
      certificate.rightAliasFresh domainAvoids codomainAvoids
    aligned := by
      rw [addAll_fromFix, addAll_fromFix]
      exact entailedGeneratedAlignment_fromFix domain codomain
        certificate.aligned }

private theorem supportedFix {body : Expr}
    (bodyProperty : SupportedM4FuelPairProperty body) :
    SupportedM4FuelPairProperty (.fixE body) := by
  intro signature context start leftGenerated rightGenerated leftNext rightNext
    leftFuel rightFuel signatureWellFormed wellFormed leftElaboration
    rightElaboration
  cases leftFuel with
  | zero => simp [ElaboratesFuel] at leftElaboration
  | succ leftFuel =>
      cases rightFuel with
      | zero => simp [ElaboratesFuel] at rightElaboration
      | succ rightFuel =>
          simp only [ElaboratesFuel] at leftElaboration rightElaboration
          cases leftElaboration with
          | @fixE _ _ leftBody _ leftDirect leftBodyElaboration =>
              cases rightElaboration with
              | @fixE _ _ rightBody _ rightDirect rightBodyElaboration =>
                  have bodyWellFormed := fixBodyWellFormed wellFormed
                    (FixElaboratesUsing.fixE leftDirect leftBodyElaboration)
                  obtain ⟨bodyResult⟩ := bodyProperty signatureWellFormed
                    bodyWellFormed leftBodyElaboration rightBodyElaboration
                  cases bodyResult.next_eq
                  let bodyAtOuter := bodyResult.certificate.rebase
                    (bodyResult.certificate.hiddenFresh.widen
                      (fixBodyStart_le body start) (Supply.le_refl leftNext))
                  exact ⟨
                    { next_eq := rfl
                      certificate := supportedCertificate_fromFix bodyAtOuter
                        (Fix.domain body start) (Fix.codomain body start)
                        (by
                          simpa [bodyAtOuter,
                            SupportedEntailedAlignmentCertificate.rebase] using
                            fixDomainAvoids
                              bodyResult.certificate.hiddenFresh)
                        (by
                          simpa [bodyAtOuter,
                            SupportedEntailedAlignmentCertificate.rebase] using
                            fixCodomainAvoids
                              bodyResult.certificate.hiddenFresh) }⟩

/-- The recursive-function constructor-local coherence obligation. -/
theorem fixCoherenceStep : FixCoherenceStep := by
  intro body induction
  apply SupportedM4FuelPairProperty.toFull
  apply supportedFix
  apply FullM4FuelPairProperty.toSupported
  exact induction body (by simp [Expr.complexity])

end TypePM.Source.M4.CompletenessArchitecture
