import TypePM.Source.RecursiveLetSupportSafety
import TypePM.Source.FreshIntervalRenaming

/-!
# Direct comparison of complete `let` blocks

The failed source-safe alignment route first renamed an isolated child and
then attempted to insert it into every enclosing frame.  A direct comparison
does not need that intermediate claim.  This module packages the exact
constructive invariant: after each admissible frame is applied, the two
complete blocks reduce to a common block by finite fresh-alias sequences.
-/

namespace TypePM.Source

namespace GeneratedEquationCommonCore

noncomputable def coreBlock
    {left right : Generated}
    (decomposition : GeneratedEquationCommonCore left right) : Generated :=
  { target := left.target
    hard := decomposition.equations.core
    pending := left.pending }

theorem framedCore_eq_plug_coreBlock
    {left right : Generated}
    (decomposition : GeneratedEquationCommonCore left right)
    (generatedFrame : GeneratedFrame) :
    decomposition.framedCore generatedFrame =
      generatedFrame.plug decomposition.coreBlock := by
  rcases left with ⟨leftTarget, leftHard, leftPending⟩
  rcases right with ⟨rightTarget, rightHard, rightPending⟩
  have targetEquality := decomposition.target_eq
  have pendingEquality := decomposition.pending_eq
  simp only at targetEquality pendingEquality
  subst rightTarget
  subst rightPending
  induction generatedFrame generalizing leftTarget leftPending
      leftHard rightHard with
  | hole => rfl
  | lam domain outer induction =>
      change (decomposition.frame (.lam domain .hole)).framedCore outer = _
      calc
        _ = outer.plug
            (decomposition.frame (.lam domain .hole)).coreBlock :=
          induction _ _ _ _ (decomposition.frame (.lam domain .hole))
        _ = _ := by rfl
  | appFunction argument domain target outer induction =>
      change (decomposition.frame
        (.appFunction argument domain target .hole)).framedCore outer = _
      calc
        _ = outer.plug (decomposition.frame
            (.appFunction argument domain target .hole)).coreBlock :=
          induction _ _ _ _ (decomposition.frame
            (.appFunction argument domain target .hole))
        _ = _ := by
          simp [coreBlock, GeneratedEquationCommonCore.frame,
            GeneratedFrame.plug, Generated.fromApp,
            InterfaceAliasDecomposition.EquationLists.EquationCommonCore.appendSame,
            List.append_assoc]
  | appArgument function domain target outer induction =>
      change (decomposition.frame
        (.appArgument function domain target .hole)).framedCore outer = _
      calc
        _ = outer.plug (decomposition.frame
            (.appArgument function domain target .hole)).coreBlock :=
          induction _ _ _ _ (decomposition.frame
            (.appArgument function domain target .hole))
        _ = _ := by
          simp [coreBlock, GeneratedEquationCommonCore.frame,
            GeneratedFrame.plug, Generated.fromApp,
            InterfaceAliasDecomposition.EquationLists.EquationCommonCore.appendSame,
            List.append_assoc]
  | tupleItem before after outer induction =>
      change (decomposition.frame
        (.tupleItem before after .hole)).framedCore outer = _
      calc
        _ = outer.plug (decomposition.frame
            (.tupleItem before after .hole)).coreBlock :=
          induction _ _ _ _ (decomposition.frame
            (.tupleItem before after .hole))
        _ = _ := by
          simp [coreBlock, GeneratedEquationCommonCore.frame,
            GeneratedFrame.plug, GeneratedItems.asTuple,
            GeneratedItems.append, GeneratedItems.singleton,
            GeneratedItems.cons, GeneratedItems.nil,
            InterfaceAliasDecomposition.EquationLists.EquationCommonCore.appendSame]
  | letBody effects outer induction =>
      change (decomposition.frame
        (.letBody effects .hole)).framedCore outer = _
      calc
        _ = outer.plug (decomposition.frame
            (.letBody effects .hole)).coreBlock :=
          induction _ _ _ _ (decomposition.frame
            (.letBody effects .hole))
        _ = _ := by
          simp [coreBlock, GeneratedEquationCommonCore.frame,
            GeneratedFrame.plug, Generated.fromLet]

end GeneratedEquationCommonCore

/-- A constructive certificate for a scoped comparison of two complete
generated blocks.  In the intended use, `left` and `right` are the two
`Generated.fromLet` blocks returned by distinct elaborations of one source
`letE`.

The certificate mentions neither a renaming of an isolated body nor
`SourceSafeWholeLetAlignment`.  Normalization is requested after applying
the frame, so it also permits the two unframed targets to differ when their
interface equations reconcile them once a constructor observes the target. -/
structure DirectGeneratedComparisonCertificate
    (start next : Supply) (left right : Generated) where
  hidden : List UnificationVar
  hiddenFresh : VariablesFreshIn start next hidden
  normalize : ∀ (frame : GeneratedFrame), frame.Avoids hidden →
    FreshAliasSequence.CommonCoreEquivalent
      (frame.plug left) (frame.plug right)

/-- A sufficient general-`let` premise stated only at the corrected
complete-block boundary.  Besides the independently necessary supply
agreement, it asks for direct finite-alias normalization of the blocks
actually returned by the two source derivations.

This proposition is intentionally kept as a useful sufficient interface.
It is not valid for every derivation of the current source judgment: hard
aliases cannot rename a representative occurring in a delayed checking
obligation.  `SourceSafeAlignmentCounterexample.not_directLetNormalizationHandler`
kernel-checks that boundary. -/
def DirectLetNormalizationHandler : Prop :=
  ∀ {signature : Signature} {context : Context} {value body : Expr} {start : Supply}
      {leftGenerated rightGenerated : Generated}
      {leftNext rightNext : Supply},
    start.WellFormedFor context →
      Elaborates signature context (.letE value body) start leftGenerated leftNext →
        Elaborates signature context (.letE value body) start rightGenerated rightNext →
          leftNext = rightNext ∧
            Nonempty (DirectGeneratedComparisonCertificate start leftNext
              leftGenerated rightGenerated)

namespace DirectGeneratedComparisonCertificate

/-- Hard-only fresh-alias normalization cannot alter the delayed checking
obligations.  This elementary consequence is the exact boundary exposed by
the general source counterexample. -/
theorem commonCore_pending_eq
    {left right : Generated}
    (equivalent : FreshAliasSequence.CommonCoreEquivalent left right) :
    left.pending = right.pending := by
  rcases equivalent with
    ⟨core, leftAliases, rightAliases, _leftAdmissible,
      _rightAdmissible, _leftHard, _rightHard, leftPending, rightPending⟩
  calc
    left.pending = (FreshAliasSequence.addAll leftAliases core).pending :=
      leftPending.symm
    _ = core.pending := FreshAliasSequence.addAll_pending _ _
    _ = (FreshAliasSequence.addAll rightAliases core).pending :=
      (FreshAliasSequence.addAll_pending _ _).symm
    _ = right.pending := rightPending

/-- Every direct certificate therefore requires literal equality of the two
unframed delayed-obligation lists. -/
theorem pending_eq
    {start next : Supply} {left right : Generated}
    (certificate :
      DirectGeneratedComparisonCertificate start next left right) :
    left.pending = right.pending :=
  commonCore_pending_eq (certificate.normalize .hole (by trivial))

/-! ## A common core that renames hard and delayed constraints together -/

/-- A finite-name-aware common core.  Each side first applies one finite
bijective change of variable names to the entire core, including delayed
checking obligations, and may then add a finite admissible hard-alias
sequence.  Thus one name correspondence acts on hard and delayed constraints
together, while the hard aliases still account for representative-sensitive
interface equations.

Unlike `FreshAliasSequence.CommonCoreEquivalent`, this relation does not
force the two concrete delayed-obligation lists to be literally equal. -/
structure RenamingAwareCommonCoreEquivalent (left right : Generated) where
  core : Generated
  leftRenaming : VariableRenaming
  rightRenaming : VariableRenaming
  leftFinite : leftRenaming.FiniteSupport
  rightFinite : rightRenaming.FiniteSupport
  leftAliases : List FreshAliasSequence.Alias
  rightAliases : List FreshAliasSequence.Alias
  leftAdmissible : FreshAliasSequence.Admissible leftAliases
    (ElaborationRenaming.renameGenerated leftRenaming core)
  rightAdmissible : FreshAliasSequence.Admissible rightAliases
    (ElaborationRenaming.renameGenerated rightRenaming core)
  leftHard : HardEquivalent
    (FreshAliasSequence.addAll leftAliases
      (ElaborationRenaming.renameGenerated leftRenaming core)).hard
    left.hard
  rightHard : HardEquivalent
    (FreshAliasSequence.addAll rightAliases
      (ElaborationRenaming.renameGenerated rightRenaming core)).hard
    right.hard
  leftPending :
    (ElaborationRenaming.renameGenerated leftRenaming core).pending =
      left.pending
  rightPending :
    (ElaborationRenaming.renameGenerated rightRenaming core).pending =
      right.pending

namespace RenamingAwareCommonCoreEquivalent

/-- A finite renaming followed by admissible hard aliases preserves and
reflects block acceptance.  This is the soundness theorem needed before the
new relation can replace the refuted hard-only direct certificate. -/
theorem blockAccepts_iff
    {left right : Generated}
    (equivalent : RenamingAwareCommonCoreEquivalent left right) :
    BlockAccepts left ↔ BlockAccepts right := by
  let leftCore := ElaborationRenaming.renameGenerated
    equivalent.leftRenaming equivalent.core
  let rightCore := ElaborationRenaming.renameGenerated
    equivalent.rightRenaming equivalent.core
  have leftPresentation : BlockAccepts leftCore ↔ BlockAccepts left :=
    FreshAliasSequence.blockAccepts_iff_of_addAll_hardEquivalent
      equivalent.leftAliases leftCore left equivalent.leftAdmissible
      equivalent.leftHard (by
        simpa [leftCore] using equivalent.leftPending)
  have rightPresentation : BlockAccepts rightCore ↔ BlockAccepts right :=
    FreshAliasSequence.blockAccepts_iff_of_addAll_hardEquivalent
      equivalent.rightAliases rightCore right equivalent.rightAdmissible
      equivalent.rightHard (by
        simpa [rightCore] using equivalent.rightPending)
  exact leftPresentation.symm |>.trans
    ((ElaborationRenaming.blockAccepts_renameVariables_iff
      equivalent.leftRenaming equivalent.core).symm.trans
      (ElaborationRenaming.blockAccepts_renameVariables_iff
        equivalent.rightRenaming equivalent.core)) |>.trans
    rightPresentation

end RenamingAwareCommonCoreEquivalent

/-- Frame-wise form of `RenamingAwareCommonCoreEquivalent`.  This is the
replacement target for the refuted hard-only certificate: every admissible
frame may choose its own finite common-core presentation, but each
presentation renames hard and delayed constraints together. -/
structure RenamingAwareDirectGeneratedComparisonCertificate
    (start next : Supply) (left right : Generated) where
  hidden : List UnificationVar
  hiddenFresh : VariablesFreshIn start next hidden
  normalize : ∀ (frame : GeneratedFrame), frame.Avoids hidden →
    Nonempty (RenamingAwareCommonCoreEquivalent
      (frame.plug left) (frame.plug right))

namespace RenamingAwareDirectGeneratedComparisonCertificate

/-- The new frame-wise certificate is sound for the existing scoped source
comparison consumed by constructor composition. -/
theorem scopedGeneratedComparison
    {start next : Supply} {left right : Generated}
    (certificate :
      RenamingAwareDirectGeneratedComparisonCertificate
        start next left right) :
    ScopedGeneratedComparison start next next left right := by
  refine ⟨rfl, certificate.hidden, certificate.hiddenFresh, ?_⟩
  intro frame frameAvoids
  obtain ⟨equivalent⟩ := certificate.normalize frame frameAvoids
  exact equivalent.blockAccepts_iff

end RenamingAwareDirectGeneratedComparisonCertificate

/-- A second candidate general-`let` invariant.  It repairs the empty-frame
delayed-checking gap in `DirectLetNormalizationHandler`, but remains too
strong under frames: a fixed sibling can observe whether two occurrences use
the same inherited name.  The source-derived refutation is
`SourceSafeAlignmentCounterexample.not_renamingAwareDirectLetNormalizationHandler`.
-/
def RenamingAwareDirectLetNormalizationHandler : Prop :=
  ∀ {signature : Signature} {context : Context} {value body : Expr}
      {start : Supply} {leftGenerated rightGenerated : Generated}
      {leftNext rightNext : Supply},
    start.WellFormedFor context →
      Elaborates signature context (.letE value body) start
          leftGenerated leftNext →
        Elaborates signature context (.letE value body) start
            rightGenerated rightNext →
          leftNext = rightNext ∧
            Nonempty (RenamingAwareDirectGeneratedComparisonCertificate
              start leftNext leftGenerated rightGenerated)

/-- The corrected normalization handler closes ordinary source composition
without assuming literal equality of delayed-obligation lists. -/
theorem RenamingAwareDirectGeneratedComparisonCertificate.letComparisonHandler
    (normalize : RenamingAwareDirectLetNormalizationHandler) :
    LetComparisonHandler := by
  intro signature context value body start leftGenerated rightGenerated
    leftNext rightNext wellFormed leftElaboration rightElaboration
  obtain ⟨nextEquality, ⟨certificate⟩⟩ :=
    normalize wellFormed leftElaboration rightElaboration
  subst rightNext
  exact certificate.scopedGeneratedComparison

/-! ## The minimal sound complete-block endpoint -/

/-- The minimal direct certificate records exactly the contextual acceptance
equivalence consumed by source-constructor composition.  It deliberately does
not require the two sides to arise from one syntactic common core: the
source-derived counterexample shows that both the hard-only and bijective-
renaming common-core presentations are too restrictive. -/
structure DirectContextualGeneratedComparisonCertificate
    (start next : Supply) (left right : Generated) where
  hidden : List UnificationVar
  hiddenFresh : VariablesFreshIn start next hidden
  normalize : ∀ (frame : GeneratedFrame), frame.Avoids hidden →
    (BlockAccepts (frame.plug left) ↔ BlockAccepts (frame.plug right))

namespace DirectContextualGeneratedComparisonCertificate

theorem scopedGeneratedComparison
    {start next : Supply} {left right : Generated}
    (certificate :
      DirectContextualGeneratedComparisonCertificate start next left right) :
    ScopedGeneratedComparison start next next left right := by
  refine ⟨rfl, certificate.hidden, certificate.hiddenFresh, ?_⟩
  intro frame frameAvoids
  exact certificate.normalize frame frameAvoids

end DirectContextualGeneratedComparisonCertificate

/-- General `letE` coherence stated using only the minimal direct contextual
certificate and explicit supply agreement. -/
def DirectContextualLetComparisonHandler : Prop :=
  ∀ {signature : Signature} {context : Context} {value body : Expr}
      {start : Supply} {leftGenerated rightGenerated : Generated}
      {leftNext rightNext : Supply},
    start.WellFormedFor context →
      Elaborates signature context (.letE value body) start
          leftGenerated leftNext →
        Elaborates signature context (.letE value body) start
            rightGenerated rightNext →
          leftNext = rightNext ∧
            Nonempty (DirectContextualGeneratedComparisonCertificate
              start leftNext leftGenerated rightGenerated)

/-- The minimal direct formulation is neither stronger nor weaker than the
existing `LetComparisonHandler`; it merely exposes its supply and frame-wise
components.  The completed M2 proof constructs the equivalent handler through
the supported semantic certificates in `FullM2Completion`. -/
theorem directContextualLetComparisonHandler_iff :
    DirectContextualLetComparisonHandler ↔ LetComparisonHandler := by
  constructor
  · intro direct signature context value body start leftGenerated
      rightGenerated leftNext rightNext wellFormed leftElaboration
      rightElaboration
    obtain ⟨nextEquality, ⟨certificate⟩⟩ :=
      direct wellFormed leftElaboration rightElaboration
    subst rightNext
    exact certificate.scopedGeneratedComparison
  · intro handler signature context value body start leftGenerated
      rightGenerated leftNext rightNext wellFormed leftElaboration
      rightElaboration
    obtain ⟨nextEquality, hidden, hiddenFresh, related⟩ :=
      handler wellFormed leftElaboration rightElaboration
    exact ⟨nextEquality,
      ⟨{ hidden := hidden
         hiddenFresh := hiddenFresh
         normalize := by
           intro frame frameAvoids
           exact related frame frameAvoids }⟩⟩

/-- A frame-stable generated equation decomposition is a convenient
sufficient presentation of the direct normalization invariant. -/
noncomputable def ofEquationCommonCore
    {start next : Supply} {left right : Generated}
    (hidden : List UnificationVar)
    (hiddenFresh : VariablesFreshIn start next hidden)
    (decomposition : GeneratedEquationCommonCore left right)
    (frameAdmissible : decomposition.FrameAdmissible hidden) :
    DirectGeneratedComparisonCertificate start next left right :=
  { hidden := hidden
    hiddenFresh := hiddenFresh
    normalize := by
      intro frame frameAvoids
      let framed := decomposition.frame frame
      let core := decomposition.framedCore frame
      obtain ⟨leftAdmissible, rightAdmissible⟩ :=
        frameAdmissible frame frameAvoids
      exact ⟨core, framed.equations.leftAliases,
        framed.equations.rightAliases, leftAdmissible, rightAdmissible,
        by
          rw [InterfaceAliasDecomposition.EquationLists.addAll_hard]
          exact framed.equations.leftEquivalent,
        by
          rw [InterfaceAliasDecomposition.EquationLists.addAll_hard]
          exact framed.equations.rightEquivalent,
        by simp [core, framed, GeneratedEquationCommonCore.framedCore],
        by simp [core, framed, GeneratedEquationCommonCore.framedCore,
          framed.pending_eq]⟩ }

/-- A direct complete-block certificate is exactly strong enough to produce
the endpoint consumed by source-composition. -/
theorem scopedGeneratedComparison
    {start next : Supply} {left right : Generated}
    (certificate :
      DirectGeneratedComparisonCertificate start next left right) :
    ScopedGeneratedComparison start next next left right := by
  exact ⟨rfl, certificate.hidden, certificate.hiddenFresh,
    fun frame frameAvoids =>
      (certificate.normalize frame frameAvoids).blockAccepts_iff⟩

/-- Direct complete-block normalization closes the existing source
composition handler without any isolated-child renaming premise. -/
theorem letComparisonHandler
    (normalize : DirectLetNormalizationHandler) : LetComparisonHandler := by
  intro signature context value body start leftGenerated rightGenerated leftNext
    rightNext wellFormed leftElaboration rightElaboration
  obtain ⟨nextEquality, ⟨certificate⟩⟩ :=
    normalize wellFormed leftElaboration rightElaboration
  subst rightNext
  exact certificate.scopedGeneratedComparison

end DirectGeneratedComparisonCertificate

end TypePM.Source
