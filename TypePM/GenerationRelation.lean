import TypePM.Generation

/-!
# Relational specification of M1 constraint generation

`Generates` and `GeneratesItems` describe the pure generator without calling
the executable functions in their constructors.  In particular, the supply
threading and the order in which sibling constraints are appended are part of
the relation rather than hidden in an implementation state.

The equivalence theorems at the end show that the executable generator is an
exact decision procedure for this relation.
-/

namespace TypePM

mutual

/-- Relational specification of generation for one expression. -/
inductive Generates : Context → Expr → Nat → Generated → Nat → Prop where
  | var {context index supply target} :
      context[index]? = some target →
      Generates context (.var index) supply
        ⟨target, [], []⟩ supply
  | lit {context value supply} :
      Generates context (.lit value) supply
        ⟨.int, [], []⟩ supply
  | something {context supply} :
      Generates context .something supply
        ⟨.matcher .any (.var ⟨supply⟩), [], []⟩ (supply + 1)
  | lam {context body supply generatedBody next} :
      Generates (.var ⟨supply⟩ :: context) body (supply + 1)
        generatedBody next →
      Generates context (.lam body) supply
        ⟨.fn (.var ⟨supply⟩) generatedBody.target,
          generatedBody.hard, generatedBody.pending⟩ next
  | app {context function argument supply generatedFunction afterFunction
      generatedArgument afterArgument} :
      Generates context function supply generatedFunction afterFunction →
      Generates context argument afterFunction generatedArgument afterArgument →
      Generates context (.app function argument) supply
        ⟨.var ⟨afterArgument + 1⟩,
          generatedFunction.hard ++ generatedArgument.hard ++
            [.ty generatedFunction.target
              (.fn (.var ⟨afterArgument⟩) (.var ⟨afterArgument + 1⟩))],
          generatedFunction.pending ++ generatedArgument.pending ++
            [⟨generatedArgument.target, .var ⟨afterArgument⟩⟩]⟩
        (afterArgument + 2)
  | tuple {context items supply generatedItems next} :
      GeneratesItems context items supply generatedItems next →
      Generates context (.tuple items) supply
        ⟨.prod generatedItems.targets,
          generatedItems.hard, generatedItems.pending⟩ next

/-- Relational specification of left-to-right generation for expression
lists. -/
inductive GeneratesItems :
    Context → List Expr → Nat → GeneratedItems → Nat → Prop where
  | nil {context supply} :
      GeneratesItems context [] supply ⟨[], [], []⟩ supply
  | cons {context item items supply generatedItem afterItem generatedItems next} :
      Generates context item supply generatedItem afterItem →
      GeneratesItems context items afterItem generatedItems next →
      GeneratesItems context (item :: items) supply
        ⟨generatedItem.target :: generatedItems.targets,
          generatedItem.hard ++ generatedItems.hard,
          generatedItem.pending ++ generatedItems.pending⟩ next

end

mutual

/-- Every successful executable generation has a relational derivation. -/
theorem generate_to_generates
    {context : Context} {expression : Expr} {supply next : Nat}
    {generated : Generated}
    (success : generate context expression supply = some (generated, next)) :
    Generates context expression supply generated next := by
  cases expression with
  | var index =>
      cases lookup : context[index]? with
      | none => simp [generate, lookup] at success
      | some target =>
          have resultEquality :
              (Generated.mk target [] [], supply) = (generated, next) :=
            Option.some.inj (by simpa [generate, lookup] using success)
          injection resultEquality with generatedEquality nextEquality
          subst generated
          subst next
          exact .var lookup
  | lit value =>
      have resultEquality :
          (Generated.mk .int [] [], supply) = (generated, next) :=
        Option.some.inj (by simpa [generate] using success)
      injection resultEquality with generatedEquality nextEquality
      subst generated
      subst next
      exact .lit
  | something =>
      have resultEquality :
          (Generated.mk (.matcher .any (.var ⟨supply⟩)) [] [], supply + 1) =
            (generated, next) :=
        Option.some.inj (by simpa [generate] using success)
      injection resultEquality with generatedEquality nextEquality
      subst generated
      subst next
      exact .something
  | lam body =>
      cases bodyResult : generate (.var ⟨supply⟩ :: context) body (supply + 1) with
      | none => simp [generate, bodyResult] at success
      | some result =>
          cases result with
          | mk generatedBody afterBody =>
              have resultEquality :
                  (Generated.mk (.fn (.var ⟨supply⟩) generatedBody.target)
                      generatedBody.hard generatedBody.pending,
                    afterBody) = (generated, next) :=
                Option.some.inj
                  (by simpa [generate, bodyResult] using success)
              injection resultEquality with generatedEquality nextEquality
              subst generated
              subst next
              exact .lam (generate_to_generates bodyResult)
  | app function argument =>
      cases functionResult : generate context function supply with
      | none => simp [generate, functionResult] at success
      | some result =>
          cases result with
          | mk generatedFunction afterFunction =>
              cases argumentResult : generate context argument afterFunction with
              | none =>
                  simp [generate, functionResult, argumentResult] at success
              | some result =>
                  cases result with
                  | mk generatedArgument afterArgument =>
                      have resultEquality :
                          (Generated.mk (.var ⟨afterArgument + 1⟩)
                              (generatedFunction.hard ++ generatedArgument.hard ++
                                [.ty generatedFunction.target
                                  (.fn (.var ⟨afterArgument⟩)
                                    (.var ⟨afterArgument + 1⟩))])
                              (generatedFunction.pending ++
                                generatedArgument.pending ++
                                [⟨generatedArgument.target,
                                  .var ⟨afterArgument⟩⟩]),
                            afterArgument + 2) = (generated, next) :=
                        Option.some.inj
                          (by
                            simpa [generate, functionResult, argumentResult]
                              using success)
                      injection resultEquality with generatedEquality nextEquality
                      subst generated
                      subst next
                      exact .app
                        (generate_to_generates functionResult)
                        (generate_to_generates argumentResult)
  | tuple items =>
      cases itemsResult : generateItems context items supply with
      | none => simp [generate, itemsResult] at success
      | some result =>
          cases result with
          | mk generatedItems afterItems =>
              have resultEquality :
                  (Generated.mk (.prod generatedItems.targets)
                      generatedItems.hard generatedItems.pending,
                    afterItems) = (generated, next) :=
                Option.some.inj
                  (by simpa [generate, itemsResult] using success)
              injection resultEquality with generatedEquality nextEquality
              subst generated
              subst next
              exact .tuple (generateItems_to_generatesItems itemsResult)

/-- Every successful executable list generation has a relational
derivation. -/
theorem generateItems_to_generatesItems
    {context : Context} {expressions : List Expr} {supply next : Nat}
    {generated : GeneratedItems}
    (success : generateItems context expressions supply = some (generated, next)) :
    GeneratesItems context expressions supply generated next := by
  cases expressions with
  | nil =>
      have resultEquality :
          (GeneratedItems.mk [] [] [], supply) = (generated, next) :=
        Option.some.inj (by simpa [generateItems] using success)
      injection resultEquality with generatedEquality nextEquality
      subst generated
      subst next
      exact .nil
  | cons expression expressions =>
      cases itemResult : generate context expression supply with
      | none => simp [generateItems, itemResult] at success
      | some result =>
          cases result with
          | mk generatedItem afterItem =>
              cases itemsResult : generateItems context expressions afterItem with
              | none =>
                  simp [generateItems, itemResult, itemsResult] at success
              | some result =>
                  cases result with
                  | mk generatedItems afterItems =>
                      have resultEquality :
                          (GeneratedItems.mk
                              (generatedItem.target :: generatedItems.targets)
                              (generatedItem.hard ++ generatedItems.hard)
                              (generatedItem.pending ++ generatedItems.pending),
                            afterItems) = (generated, next) :=
                        Option.some.inj
                          (by
                            simpa [generateItems, itemResult, itemsResult]
                              using success)
                      injection resultEquality with generatedEquality nextEquality
                      subst generated
                      subst next
                      exact .cons
                        (generate_to_generates itemResult)
                        (generateItems_to_generatesItems itemsResult)

end

mutual

/-- A relational derivation is executed by `generate` without loss. -/
theorem generates_to_generate
    {context : Context} {expression : Expr} {supply next : Nat}
    {generated : Generated}
    (derivation : Generates context expression supply generated next) :
    generate context expression supply = some (generated, next) := by
  cases derivation with
  | var lookup => simp [generate, lookup]
  | lit => rfl
  | something => rfl
  | lam bodyDerivation =>
      simp [generate, generates_to_generate bodyDerivation]
  | app functionDerivation argumentDerivation =>
      simp [generate, generates_to_generate functionDerivation,
        generates_to_generate argumentDerivation]
  | tuple itemsDerivation =>
      simp [generate, generatesItems_to_generateItems itemsDerivation]

/-- A relational list derivation is executed by `generateItems` without
loss. -/
theorem generatesItems_to_generateItems
    {context : Context} {expressions : List Expr} {supply next : Nat}
    {generated : GeneratedItems}
    (derivation : GeneratesItems context expressions supply generated next) :
    generateItems context expressions supply = some (generated, next) := by
  cases derivation with
  | nil => rfl
  | cons itemDerivation itemsDerivation =>
      simp [generateItems, generates_to_generate itemDerivation,
        generatesItems_to_generateItems itemsDerivation]

end

theorem generate_eq_some_iff_generates
    {context : Context} {expression : Expr} {supply next : Nat}
    {generated : Generated} :
    generate context expression supply = some (generated, next) ↔
      Generates context expression supply generated next :=
  ⟨generate_to_generates, generates_to_generate⟩

theorem generateItems_eq_some_iff_generatesItems
    {context : Context} {expressions : List Expr} {supply next : Nat}
    {generated : GeneratedItems} :
    generateItems context expressions supply = some (generated, next) ↔
      GeneratesItems context expressions supply generated next :=
  ⟨generateItems_to_generatesItems, generatesItems_to_generateItems⟩

end TypePM
