import TypePM.Source.RecursiveLetSupportSafety

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

/-- The remaining general-`let` premise stated only at the corrected
complete-block boundary.  Besides the independently necessary supply
agreement, it asks for direct finite-alias normalization of the blocks
actually returned by the two source derivations. -/
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
