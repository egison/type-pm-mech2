import TypePM.Source.M4Elaboration

/-!
# M4 matcher-literal checkpoint

This module types the final `MatcherClause` syntax without extending or
weakening the M3 expression elaborator.  Pattern-pattern headers synthesize
ordered hole duals and capture types.  Data patterns synthesize ordered arm
bindings.  The stored next-matcher expression is interpreted by the paper's
zero/one/many convention, and every resulting expression is checked in the
consumer direction against its hole's matcher slot.

Expressions embedded in next-matcher positions and arm bodies are deliberately
limited to the already verified M3 elaborator.  In particular, this checkpoint
does not silently accept recursive `fixE`, nested matcher literals, or nested
`matchAll` expressions.  The interfaces below are arranged so that a later
recursive M4 expression elaborator can replace that boundary without changing
the clause rules.
-/

namespace TypePM.Source

namespace MatcherTyping

set_option linter.unusedSimpArgs false

/-- Constraints contributed by a component whose own result type is consumed
by the surrounding matcher rule. -/
structure GeneratedChecks where
  hard : List Equation
  pending : List CheckObligation
deriving Repr

namespace GeneratedChecks

def empty : GeneratedChecks := ⟨[], []⟩

def append (left right : GeneratedChecks) : GeneratedChecks :=
  ⟨left.hard ++ right.hard, left.pending ++ right.pending⟩

def checked (generated : Generated) (expected : Ty) : GeneratedChecks :=
  ⟨generated.hard, generated.pending ++ [⟨generated.target, expected⟩]⟩

end GeneratedChecks

/-- Header synthesis result.  `evidence` is absent for root hole, wildcard,
and capture headers; only a root pattern constructor creates structural
producer evidence. -/
structure GeneratedPPat where
  holes : List Dual
  captures : List Ty
  evidence : Option Cap
  hard : List Equation
deriving Repr

structure GeneratedPPats where
  holes : List Dual
  captures : List Ty
  hard : List Equation
deriving Repr

structure GeneratedDPat where
  bindings : List Ty
  hard : List Equation
deriving Repr

structure GeneratedDPats where
  bindings : List Ty
  hard : List Equation
deriving Repr

namespace PPat

mutual

def typingSize : PPat → Nat
  | .hole | .wild | .capture => 1
  | .ctor _ fields => listTypingSize fields + 1

def listTypingSize : List PPat → Nat
  | [] => 0
  | pattern :: patterns => typingSize pattern + listTypingSize patterns + 1

end

end PPat

namespace DPat

mutual

def typingSize : DPat → Nat
  | .var | .wild => 1
  | .ctor _ fields | .tuple fields => listTypingSize fields + 1

def listTypingSize : List DPat → Nat
  | [] => 0
  | pattern :: patterns => typingSize pattern + listTypingSize patterns + 1

end


/-- A variable or wildcard is the fail-closed final arm accepted by this
checkpoint's exhaustive arm check. -/
def isIrrefutable : DPat → Bool
  | .var | .wild => true
  | _ => false

end DPat

/-- Peel exactly `count` curried domains, leaving the data result. -/
def peelFunctionExact : Nat → Ty → Option (List Ty × Ty)
  | 0, result => some ([], result)
  | count + 1, .fn domain result => do
      let (domains, finalResult) ← peelFunctionExact count result
      pure (domain :: domains, finalResult)
  | _ + 1, _ => none

def freshTargets (supply : Supply) (count : Nat) : List Ty :=
  (List.range count).map (fun offset => .var ⟨supply.ty + offset⟩)

mutual

/-- Type a primitive pattern against one target.  `expectedCapability` is
present only below a pattern constructor; a root hole is intentionally not
equated with the enclosing matcher's producer capability. -/
def elaboratePPat
    (signature : FrozenSignature) :
    PPat → Ty → Option Cap → Supply → Option (GeneratedPPat × Supply)
  | .hole, expectedTarget, expectedCapability, supply =>
      let capability : Cap := .var ⟨supply.cap⟩
      let hard := match expectedCapability with
        | some expected => [.cap capability expected]
        | none => []
      some
        (⟨[⟨capability, expectedTarget⟩], [], none, hard⟩,
          ⟨supply.ty, supply.cap + 1⟩)
  | .wild, _, _, supply => some (⟨[], [], none, []⟩, supply)
  | .capture, expectedTarget, _, supply =>
      some (⟨[], [expectedTarget], none, []⟩, supply)
  | .ctor constructor fields, expectedTarget, expectedCapability, supply => do
      let scheme ← signature.lookupPatternConstructor constructor
      if fields.length = scheme.fields.length then
        let instantiated := scheme.instantiate supply
        let (generatedFields, next) ←
          elaboratePPatFields signature fields instantiated.1.fields
            instantiated.2
        let outerCapability := match expectedCapability with
          | some expected => [.cap instantiated.1.result.capability expected]
          | none => []
        pure
          (⟨generatedFields.holes, generatedFields.captures,
            some instantiated.1.result.capability,
            [.ty instantiated.1.result.target expectedTarget] ++
              outerCapability ++ generatedFields.hard⟩,
            next)
      else
        none
termination_by pattern => MatcherTyping.PPat.typingSize pattern * 2 + 1
decreasing_by
  all_goals simp_wf
  all_goals simp_all [MatcherTyping.PPat.typingSize,
    MatcherTyping.PPat.listTypingSize]
  all_goals omega

/-- Left-to-right typing of constructor fields against their frozen duals. -/
def elaboratePPatFields
    (signature : FrozenSignature) :
    List PPat → List Dual → Supply → Option (GeneratedPPats × Supply)
  | [], [], supply => some (⟨[], [], []⟩, supply)
  | pattern :: patterns, expected :: expecteds, supply => do
      let (generatedPattern, afterPattern) ←
        elaboratePPat signature pattern expected.target
          (some expected.capability) supply
      let (generatedPatterns, next) ←
        elaboratePPatFields signature patterns expecteds afterPattern
      pure
        (⟨generatedPattern.holes ++ generatedPatterns.holes,
          generatedPattern.captures ++ generatedPatterns.captures,
          generatedPattern.hard ++ generatedPatterns.hard⟩,
          next)
  | _, _, _ => none
termination_by patterns => MatcherTyping.PPat.listTypingSize patterns * 2
decreasing_by
  all_goals simp_wf
  all_goals simp_all [MatcherTyping.PPat.typingSize,
    MatcherTyping.PPat.listTypingSize]
  all_goals omega

end

mutual

/-- Type one data pattern against the matcher target and return its arm
bindings in left-to-right source order. -/
def elaborateDPat
    (signature : FrozenSignature) :
    DPat → Ty → Supply → Option (GeneratedDPat × Supply)
  | .var, expected, supply => some (⟨[expected], []⟩, supply)
  | .wild, _, supply => some (⟨[], []⟩, supply)
  | .ctor constructor fields, expected, supply => do
      let scheme ← signature.lookupDataConstructor constructor
      if fields.length = scheme.callArity then
        let instantiated := scheme.instantiate supply
        let (fieldTypes, resultType) ←
          peelFunctionExact fields.length instantiated.1
        let (generatedFields, next) ←
          elaborateDPatFields signature fields fieldTypes instantiated.2
        pure
          (⟨generatedFields.bindings,
            [.ty resultType expected] ++ generatedFields.hard⟩,
            next)
      else
        none
  | .tuple items, expected, supply => do
      let fields := freshTargets supply items.length
      let afterFields := supply.nextTy items.length
      let (generatedItems, next) ←
        elaborateDPatFields signature items fields afterFields
      pure
        (⟨generatedItems.bindings,
          [.ty expected (.prod fields)] ++ generatedItems.hard⟩,
          next)
termination_by pattern => MatcherTyping.DPat.typingSize pattern * 2 + 1
decreasing_by
  all_goals simp_wf
  all_goals simp_all [MatcherTyping.DPat.typingSize,
    MatcherTyping.DPat.listTypingSize]
  all_goals omega

/-- Left-to-right typing of data-pattern children. -/
def elaborateDPatFields
    (signature : FrozenSignature) :
    List DPat → List Ty → Supply → Option (GeneratedDPats × Supply)
  | [], [], supply => some (⟨[], []⟩, supply)
  | pattern :: patterns, expected :: expecteds, supply => do
      let (generatedPattern, afterPattern) ←
        elaborateDPat signature pattern expected supply
      let (generatedPatterns, next) ←
        elaborateDPatFields signature patterns expecteds afterPattern
      pure
        (⟨generatedPattern.bindings ++ generatedPatterns.bindings,
          generatedPattern.hard ++ generatedPatterns.hard⟩,
          next)
  | _, _, _ => none
termination_by patterns => MatcherTyping.DPat.listTypingSize patterns * 2
decreasing_by
  all_goals simp_wf
  all_goals simp_all [MatcherTyping.DPat.typingSize,
    MatcherTyping.DPat.listTypingSize]
  all_goals omega

end

/-- Runtime and static decomposition products share this convention: no
holes use the empty tuple, one hole is scalar, and two or more holes use an
exact product. -/
def holeProductTarget : List Dual → Ty
  | [] => .prod []
  | [hole] => hole.target
  | holes => .prod (Dual.targets holes)

/-- Each arm must end in a variable or wildcard catch-all. -/
def armsCatchAllLast : List MatcherArm → Bool
  | [] => false
  | [arm] => MatcherTyping.DPat.isIrrefutable arm.header
  | _ :: rest => armsCatchAllLast rest

def DPat.rootDataFormer?
    (signature : FrozenSignature) : DPat → Option DataFormer
  | .ctor constructor _ => do
      let scheme ← signature.lookupDataConstructor constructor
      (Signature.constructorResult? scheme.body).map Prod.fst
  | _ => none

def DPat.isGeneralConstructor
    (constructor : DataCtor) (arity : Nat) : DPat → Bool
  | .ctor actual fields =>
      actual == constructor && fields.length == arity &&
        fields.all MatcherTyping.DPat.isIrrefutable
  | _ => false

/-- An arm list is exhaustive either by a final irrefutable arm or by
covering every frozen data constructor of every root data former it mentions.
This accepts the Paper-1 join arms `[nil, cons]` without inventing a wildcard
arm that is absent from the source. -/
def armCoverageOK
    (signature : FrozenSignature) (arms : List MatcherArm) : Bool :=
  armsCatchAllLast arms ||
    (arms.isEmpty == false &&
      signature.base.dataConstructors.all (fun declaration =>
        match Signature.constructorResult? declaration.scheme.body with
        | some (former, _) =>
            let mentioned := arms.any (fun arm =>
              MatcherTyping.DPat.rootDataFormer? signature arm.header == some former)
            !mentioned || arms.any (fun arm =>
              MatcherTyping.DPat.isGeneralConstructor declaration.constructor
                declaration.scheme.callArity arm.header)
        | none => false))

/-- The literal catch-all is uniquely last (checked by `checkShapes`) and has
the exact single variable arm required by the paper. -/
def finalCatchAllVariableArm : List MatcherClause → Bool
  | [] => false
  | [clause] =>
      match clause.header, clause.arms with
      | .hole, [.mk .var _] => true
      | _, _ => false
  | _ :: rest => finalCatchAllVariableArm rest

def PPat.rootFormer?
    (signature : FrozenSignature) : PPat → Option PatternFormer
  | .ctor constructor _ => do
      let scheme ← signature.lookupPatternConstructor constructor
      match scheme.result.capability with
      | .con former _ => some former
      | _ => none
  | _ => none

def PPat.isGeneralConstructor
    (constructor : PatternCtor) (arity : Nat) : PPat → Bool
  | .ctor actual fields =>
      actual == constructor && fields.length == arity &&
        fields.all (fun field => match field with | .hole => true | _ => false)
  | _ => false

/-- Shallow frozen-signature coverage.  For every capability former mentioned
by a root constructor, every frozen constructor of that former must have its
all-hole general clause.  Specialized clauses do not count. -/
def rootCoverageOK
    (signature : FrozenSignature) (clauses : List MatcherClause) : Bool :=
  signature.base.patternConstructors.all (fun declaration =>
    match declaration.scheme.result.capability with
    | .con former _ =>
        let mentioned := clauses.any (fun clause =>
          MatcherTyping.PPat.rootFormer? signature clause.header == some former)
        !mentioned || clauses.any (fun clause =>
          MatcherTyping.PPat.isGeneralConstructor declaration.constructor
            declaration.scheme.fields.length clause.header)
    | _ => false)

/-- A structural pattern-pattern constructor can refine the data constructor
seen by its clause.  The source-defined `list` matcher therefore needs only a
`cons` data arm in its `cons` clause (and only `nil` in its `nil` clause).
`join` does not refine to one constructor and still uses ordinary coverage. -/
def structurallyRefinedArmCoverage (clause : MatcherClause) : Bool :=
  let hasConstructor (wanted : DataCtor) := clause.arms.any (fun arm =>
    match arm.header with
    | .ctor actual _ => actual == wanted
    | _ => false)
  match clause.header with
  | .ctor .nil _ => hasConstructor .nil
  | .ctor .cons _ => hasConstructor .cons
  | _ => false

def staticChecks
    (signature : FrozenSignature) (clauses : List MatcherClause) : Bool :=
  MatcherClause.checkShapes signature clauses &&
    clauses.all (fun clause => armCoverageOK signature clause.arms ||
      structurallyRefinedArmCoverage clause) &&
    finalCatchAllVariableArm clauses &&
    rootCoverageOK signature clauses

/-- Type an expression at one expected type using an explicit checking
obligation. -/
def elaborateCheckedExpression
    (signature : FrozenSignature) (context : Context)
    (expression : Expr) (expected : Ty) (supply : Supply) :
    Option (GeneratedChecks × Supply) := do
  let (generated, next) ← elaborate signature.base context expression supply
  pure (GeneratedChecks.checked generated expected, next)

/-- Check a k-product's components separately and directionally. -/
def elaborateNextMatcherItems
    (signature : FrozenSignature) (context : Context) :
    List Expr → List Dual → Supply → Option (GeneratedChecks × Supply)
  | [], [], supply => some (GeneratedChecks.empty, supply)
  | item :: items, hole :: holes, supply => do
      let (generatedItem, afterItem) ←
        elaborateCheckedExpression signature context item
          (.slot hole.capability hole.target) supply
      let (generatedItems, next) ←
        elaborateNextMatcherItems signature context items holes afterItem
      pure (generatedItem.append generatedItems, next)
  | _, _, _ => none

/-- Enforce and type the next-matcher 0/1/k convention. -/
def elaborateNextMatchers
    (signature : FrozenSignature) (context : Context)
    (expression : Expr) (holes : List Dual) (supply : Supply) :
    Option (GeneratedChecks × Supply) :=
  match holes with
  | [] =>
      match expression with
      | .tuple [] =>
          elaborateCheckedExpression signature context expression (.prod []) supply
      | _ => none
  | [hole] =>
      elaborateCheckedExpression signature context expression
        (.slot hole.capability hole.target) supply
  | _ :: _ :: _ =>
      match expression with
      | .tuple items =>
          elaborateNextMatcherItems signature context items holes supply
      | _ => none

structure GeneratedArms where
  checks : GeneratedChecks
deriving Repr

/-- Type one decomposition arm.  Data-pattern bindings precede header
captures, and the body must produce a list of canonical decomposition
products. -/
def elaborateMatcherArm
    (signature : FrozenSignature) (context : Context)
    (captures : List Ty) (matcherTarget : Ty) (holes : List Dual) :
    MatcherArm → Supply → Option (GeneratedChecks × Supply)
  | .mk header body, supply => do
      let (generatedHeader, afterHeader) ←
        elaborateDPat signature header matcherTarget supply
      let armContext := Pattern.extendContext generatedHeader.bindings
        (Pattern.extendContext captures context)
      let (generatedBody, next) ←
        elaborateCheckedExpression signature armContext body
          (DataTypes.list (holeProductTarget holes)) afterHeader
      pure
        (⟨generatedHeader.hard ++ generatedBody.hard,
          generatedBody.pending⟩,
          next)

/-- Type arms in source order. -/
def elaborateMatcherArms
    (signature : FrozenSignature) (context : Context)
    (captures : List Ty) (matcherTarget : Ty) (holes : List Dual) :
    List MatcherArm → Supply → Option (GeneratedArms × Supply)
  | [], supply => some (⟨GeneratedChecks.empty⟩, supply)
  | arm :: arms, supply => do
      let (generatedArm, afterArm) ←
        elaborateMatcherArm signature context captures matcherTarget holes arm supply
      let (generatedArms, next) ←
        elaborateMatcherArms signature context captures matcherTarget holes arms
          afterArm
      pure (⟨generatedArm.append generatedArms.checks⟩, next)

structure GeneratedMatcherClause where
  holes : List Dual
  evidence : Option Cap
  checks : GeneratedChecks
deriving Repr

/-- Type one final source matcher clause. -/
def elaborateMatcherClause
    (signature : FrozenSignature) (context : Context)
    (matcherTarget : Ty) (clause : MatcherClause) (supply : Supply) :
    Option (GeneratedMatcherClause × Supply) := do
  if clause.toShape.check signature then
    let (generatedHeader, afterHeader) ←
      elaboratePPat signature clause.header matcherTarget none supply
    let capturedContext := Pattern.extendContext generatedHeader.captures context
    let (generatedNext, afterNext) ←
      elaborateNextMatchers signature capturedContext clause.nextMatchers
        generatedHeader.holes afterHeader
    let (generatedArms, next) ←
      elaborateMatcherArms signature context generatedHeader.captures matcherTarget
        generatedHeader.holes clause.arms afterNext
    pure
      (⟨generatedHeader.holes, generatedHeader.evidence,
        ⟨generatedHeader.hard ++ generatedNext.hard ++
            generatedArms.checks.hard,
          generatedNext.pending ++ generatedArms.checks.pending⟩⟩,
        next)
  else
    none

structure GeneratedMatcherClauses where
  evidences : List Cap
  checks : GeneratedChecks
deriving Repr

/-- Type clauses in source order at one shared target. -/
def elaborateMatcherClauses
    (signature : FrozenSignature) (context : Context) (matcherTarget : Ty) :
    List MatcherClause → Supply → Option (GeneratedMatcherClauses × Supply)
  | [], supply => some (⟨[], GeneratedChecks.empty⟩, supply)
  | clause :: clauses, supply => do
      let (generatedClause, afterClause) ←
        elaborateMatcherClause signature context matcherTarget clause supply
      let (generatedClauses, next) ←
        elaborateMatcherClauses signature context matcherTarget clauses afterClause
      let evidences := match generatedClause.evidence with
        | some evidence => evidence :: generatedClauses.evidences
        | none => generatedClauses.evidences
      pure
        (⟨evidences, generatedClause.checks.append generatedClauses.checks⟩,
          next)

def evidenceEquations (producer : Cap) : List Cap → List Equation
  | [] => [.cap producer .any]
  | evidences => evidences.map (fun evidence => .cap producer evidence)

/-- Executable matcher-literal constraint generation over final source
clauses. -/
def elaborateMatcherLiteral
    (signature : FrozenSignature) (context : Context)
    (clauses : List MatcherClause) (supply : Supply) :
    Option (Generated × Supply) := do
  if staticChecks signature clauses then
    let matcherTarget : Ty := .var ⟨supply.ty⟩
    let producer : Cap := .var ⟨supply.cap⟩
    let afterRoot : Supply := ⟨supply.ty + 1, supply.cap + 1⟩
    let (generatedClauses, next) ←
      elaborateMatcherClauses signature context matcherTarget clauses afterRoot
    pure
      (⟨.matcher producer matcherTarget,
        evidenceEquations producer generatedClauses.evidences ++
          generatedClauses.checks.hard,
        generatedClauses.checks.pending⟩,
        next)
  else
    none

/-- Close a matcher literal with the existing M1/M2 saturation and certified
unifier machinery. -/
def inferMatcherLiteral
    (signature : FrozenSignature) (context : Context)
    (clauses : List MatcherClause) : Option Ty := do
  let (generated, _) ←
    elaborateMatcherLiteral signature context clauses context.initialSupply
  let closed ← inferGeneratedUsing unify generated
  pure closed.target

/-- Callback shape used to compose matcher-clause typing with a larger M4
expression elaborator (for example, the fix-aware dispatcher). -/
abbrev ExpressionElaborator :=
  Context → Expr → Supply → Option (Generated × Supply)

/-- Abstract expression judgment used by the composable matcher rules.  A
recursive M4 dispatcher can instantiate this with its own independent
relation, including fix and single-result matching cases. -/
abbrev ExpressionElaborationRelation :=
  Context → Expr → Supply → Generated → Supply → Prop

def elaborateCheckedExpressionUsing
    (expressionElaborator : ExpressionElaborator)
    (context : Context) (expression : Expr) (expected : Ty) (supply : Supply) :
    Option (GeneratedChecks × Supply) := do
  let (generated, next) ← expressionElaborator context expression supply
  pure (GeneratedChecks.checked generated expected, next)

def elaborateNextMatcherItemsUsing
    (expressionElaborator : ExpressionElaborator) (context : Context) :
    List Expr → List Dual → Supply → Option (GeneratedChecks × Supply)
  | [], [], supply => some (GeneratedChecks.empty, supply)
  | item :: items, hole :: holes, supply => do
      let (generatedItem, afterItem) ←
        elaborateCheckedExpressionUsing expressionElaborator context item
          (.slot hole.capability hole.target) supply
      let (generatedItems, next) ←
        elaborateNextMatcherItemsUsing expressionElaborator context items holes
          afterItem
      pure (generatedItem.append generatedItems, next)
  | _, _, _ => none

def elaborateNextMatchersUsing
    (expressionElaborator : ExpressionElaborator) (context : Context)
    (expression : Expr) (holes : List Dual) (supply : Supply) :
    Option (GeneratedChecks × Supply) :=
  match holes with
  | [] =>
      match expression with
      | .tuple [] =>
          elaborateCheckedExpressionUsing expressionElaborator context expression
            (.prod []) supply
      | _ => none
  | [hole] =>
      elaborateCheckedExpressionUsing expressionElaborator context expression
        (.slot hole.capability hole.target) supply
  | _ :: _ :: _ =>
      match expression with
      | .tuple items =>
          elaborateNextMatcherItemsUsing expressionElaborator context items holes
            supply
      | _ => none

def elaborateMatcherArmUsing
    (expressionElaborator : ExpressionElaborator)
    (signature : FrozenSignature) (context : Context)
    (captures : List Ty) (matcherTarget : Ty) (holes : List Dual) :
    MatcherArm → Supply → Option (GeneratedChecks × Supply)
  | .mk header body, supply => do
      let (generatedHeader, afterHeader) ←
        elaborateDPat signature header matcherTarget supply
      let armContext := Pattern.extendContext generatedHeader.bindings
        (Pattern.extendContext captures context)
      let (generatedBody, next) ←
        elaborateCheckedExpressionUsing expressionElaborator armContext body
          (DataTypes.list (holeProductTarget holes)) afterHeader
      pure
        (⟨generatedHeader.hard ++ generatedBody.hard, generatedBody.pending⟩,
          next)

def elaborateMatcherArmsUsing
    (expressionElaborator : ExpressionElaborator)
    (signature : FrozenSignature) (context : Context)
    (captures : List Ty) (matcherTarget : Ty) (holes : List Dual) :
    List MatcherArm → Supply → Option (GeneratedArms × Supply)
  | [], supply => some (⟨GeneratedChecks.empty⟩, supply)
  | arm :: arms, supply => do
      let (generatedArm, afterArm) ← elaborateMatcherArmUsing expressionElaborator
        signature context captures matcherTarget holes arm supply
      let (generatedArms, next) ← elaborateMatcherArmsUsing expressionElaborator
        signature context captures matcherTarget holes arms afterArm
      pure (⟨generatedArm.append generatedArms.checks⟩, next)

def elaborateMatcherClauseUsing
    (expressionElaborator : ExpressionElaborator)
    (signature : FrozenSignature) (context : Context)
    (matcherTarget : Ty) (clause : MatcherClause) (supply : Supply) :
    Option (GeneratedMatcherClause × Supply) := do
  if clause.toShape.check signature then
    let (generatedHeader, afterHeader) ←
      elaboratePPat signature clause.header matcherTarget none supply
    let capturedContext := Pattern.extendContext generatedHeader.captures context
    let (generatedNext, afterNext) ← elaborateNextMatchersUsing
      expressionElaborator capturedContext clause.nextMatchers generatedHeader.holes
      afterHeader
    let (generatedArms, next) ← elaborateMatcherArmsUsing expressionElaborator
      signature context generatedHeader.captures matcherTarget generatedHeader.holes
      clause.arms afterNext
    pure
      (⟨generatedHeader.holes, generatedHeader.evidence,
        ⟨generatedHeader.hard ++ generatedNext.hard ++
            generatedArms.checks.hard,
          generatedNext.pending ++ generatedArms.checks.pending⟩⟩,
        next)
  else
    none

def elaborateMatcherClausesUsing
    (expressionElaborator : ExpressionElaborator)
    (signature : FrozenSignature) (context : Context) (matcherTarget : Ty) :
    List MatcherClause → Supply → Option (GeneratedMatcherClauses × Supply)
  | [], supply => some (⟨[], GeneratedChecks.empty⟩, supply)
  | clause :: clauses, supply => do
      let (generatedClause, afterClause) ← elaborateMatcherClauseUsing
        expressionElaborator signature context matcherTarget clause supply
      let (generatedClauses, next) ← elaborateMatcherClausesUsing
        expressionElaborator signature context matcherTarget clauses afterClause
      let evidences := match generatedClause.evidence with
        | some evidence => evidence :: generatedClauses.evidences
        | none => generatedClauses.evidences
      pure
        (⟨evidences, generatedClause.checks.append generatedClauses.checks⟩,
          next)

/-- Composable matcher-literal entrypoint.  The callback is used for every
next-matcher and arm-body expression, while header, scope, product convention,
coverage, and result assembly remain fixed here. -/
def elaborateMatcherLiteralUsing
    (expressionElaborator : ExpressionElaborator)
    (signature : FrozenSignature) (context : Context)
    (clauses : List MatcherClause) (supply : Supply) :
    Option (Generated × Supply) := do
  if staticChecks signature clauses then
    let matcherTarget : Ty := .var ⟨supply.ty⟩
    let producer : Cap := .var ⟨supply.cap⟩
    let afterRoot : Supply := ⟨supply.ty + 1, supply.cap + 1⟩
    let (generatedClauses, next) ← elaborateMatcherClausesUsing
      expressionElaborator signature context matcherTarget clauses afterRoot
    pure
      (⟨.matcher producer matcherTarget,
        evidenceEquations producer generatedClauses.evidences ++
          generatedClauses.checks.hard,
        generatedClauses.checks.pending⟩,
        next)
  else
    none

/-! ## Callback-parametric relational judgment -/

abbrev PPatElaborationRelation :=
  FrozenSignature → PPat → Ty → Option Cap → Supply → GeneratedPPat → Supply →
    Prop

abbrev DPatElaborationRelation :=
  FrozenSignature → DPat → Ty → Supply → GeneratedDPat → Supply → Prop

/-- One callback-elaborated expression checked at an expected type. -/
inductive CheckedExpressionElaboratesUsing
    (expressionRelation : ExpressionElaborationRelation)
    (context : Context) :
    Expr → Ty → Supply → GeneratedChecks → Supply → Prop where
  | mk {expression expected supply generated next}
      (expressionElaboration :
        expressionRelation context expression supply generated next) :
      CheckedExpressionElaboratesUsing expressionRelation context expression
        expected supply (GeneratedChecks.checked generated expected) next

inductive NextMatcherItemsElaborateUsing
    (expressionRelation : ExpressionElaborationRelation)
    (context : Context) :
    List Expr → List Dual → Supply → GeneratedChecks → Supply → Prop where
  | nil {supply} :
      NextMatcherItemsElaborateUsing expressionRelation context [] [] supply
        GeneratedChecks.empty supply
  | cons {item items hole holes supply generatedItem afterItem generatedItems next}
      (head : CheckedExpressionElaboratesUsing expressionRelation context item
        (.slot hole.capability hole.target) supply generatedItem afterItem)
      (tail : NextMatcherItemsElaborateUsing expressionRelation context items holes
        afterItem generatedItems next) :
      NextMatcherItemsElaborateUsing expressionRelation context (item :: items)
        (hole :: holes) supply (generatedItem.append generatedItems) next

inductive NextMatchersElaborateUsing
    (expressionRelation : ExpressionElaborationRelation)
    (context : Context) :
    Expr → List Dual → Supply → GeneratedChecks → Supply → Prop where
  | zero {supply generated next}
      (checked : CheckedExpressionElaboratesUsing expressionRelation context
        (.tuple []) (.prod []) supply generated next) :
      NextMatchersElaborateUsing expressionRelation context (.tuple []) [] supply
        generated next
  | one {expression hole supply generated next}
      (checked : CheckedExpressionElaboratesUsing expressionRelation context
        expression (.slot hole.capability hole.target) supply generated next) :
      NextMatchersElaborateUsing expressionRelation context expression [hole]
        supply generated next
  | many {items first second rest supply generated next}
      (components : NextMatcherItemsElaborateUsing expressionRelation context items
        (first :: second :: rest) supply generated next) :
      NextMatchersElaborateUsing expressionRelation context (.tuple items)
        (first :: second :: rest) supply generated next

inductive MatcherArmElaboratesUsing
    (expressionRelation : ExpressionElaborationRelation)
    (dpatRelation : DPatElaborationRelation)
    (signature : FrozenSignature) (context : Context)
    (captures : List Ty) (matcherTarget : Ty) (holes : List Dual) :
    MatcherArm → Supply → GeneratedChecks → Supply → Prop where
  | mk {header body supply generatedHeader afterHeader generatedBody next}
      (headerElaboration : dpatRelation signature header matcherTarget supply
        generatedHeader afterHeader)
      (bodyElaboration : CheckedExpressionElaboratesUsing expressionRelation
        (Pattern.extendContext generatedHeader.bindings
          (Pattern.extendContext captures context))
        body (DataTypes.list (holeProductTarget holes)) afterHeader
        generatedBody next) :
      MatcherArmElaboratesUsing expressionRelation dpatRelation signature context captures
        matcherTarget holes (.mk header body) supply
        ⟨generatedHeader.hard ++ generatedBody.hard, generatedBody.pending⟩ next

inductive MatcherArmsElaborateUsing
    (expressionRelation : ExpressionElaborationRelation)
    (dpatRelation : DPatElaborationRelation)
    (signature : FrozenSignature) (context : Context)
    (captures : List Ty) (matcherTarget : Ty) (holes : List Dual) :
    List MatcherArm → Supply → GeneratedArms → Supply → Prop where
  | nil {supply} :
      MatcherArmsElaborateUsing expressionRelation dpatRelation signature context captures
        matcherTarget holes [] supply ⟨GeneratedChecks.empty⟩ supply
  | cons {arm arms supply generatedArm afterArm generatedArms next}
      (head : MatcherArmElaboratesUsing expressionRelation dpatRelation signature context
        captures matcherTarget holes arm supply generatedArm afterArm)
      (tail : MatcherArmsElaborateUsing expressionRelation dpatRelation signature context
        captures matcherTarget holes arms afterArm generatedArms next) :
      MatcherArmsElaborateUsing expressionRelation dpatRelation signature context captures
        matcherTarget holes (arm :: arms) supply
        ⟨generatedArm.append generatedArms.checks⟩ next

inductive MatcherClauseElaboratesUsing
    (expressionRelation : ExpressionElaborationRelation)
    (ppatRelation : PPatElaborationRelation)
    (dpatRelation : DPatElaborationRelation)
    (signature : FrozenSignature) (context : Context) (matcherTarget : Ty) :
    MatcherClause → Supply → GeneratedMatcherClause → Supply → Prop where
  | mk {header nextMatchers arms supply generatedHeader afterHeader generatedNext
      afterNext generatedArms next}
      (shape : (MatcherClause.mk header nextMatchers arms).toShape.check signature =
        true)
      (headerElaboration : ppatRelation signature header matcherTarget none
        supply generatedHeader afterHeader)
      (nextElaboration : NextMatchersElaborateUsing expressionRelation
        (Pattern.extendContext generatedHeader.captures context)
        nextMatchers generatedHeader.holes afterHeader generatedNext afterNext)
      (armsElaboration : MatcherArmsElaborateUsing expressionRelation dpatRelation signature
        context generatedHeader.captures matcherTarget generatedHeader.holes arms
        afterNext generatedArms next) :
      MatcherClauseElaboratesUsing expressionRelation ppatRelation dpatRelation signature context matcherTarget
        (.mk header nextMatchers arms) supply
        ⟨generatedHeader.holes, generatedHeader.evidence,
          ⟨generatedHeader.hard ++ generatedNext.hard ++ generatedArms.checks.hard,
            generatedNext.pending ++ generatedArms.checks.pending⟩⟩ next

inductive MatcherClausesElaborateUsing
    (expressionRelation : ExpressionElaborationRelation)
    (ppatRelation : PPatElaborationRelation)
    (dpatRelation : DPatElaborationRelation)
    (signature : FrozenSignature) (context : Context) (matcherTarget : Ty) :
    List MatcherClause → Supply → GeneratedMatcherClauses → Supply → Prop where
  | nil {supply} :
      MatcherClausesElaborateUsing expressionRelation ppatRelation dpatRelation signature context
        matcherTarget [] supply ⟨[], GeneratedChecks.empty⟩ supply
  | cons {clause clauses supply generatedClause afterClause generatedClauses next}
      (head : MatcherClauseElaboratesUsing expressionRelation ppatRelation dpatRelation signature context
        matcherTarget clause supply generatedClause afterClause)
      (tail : MatcherClausesElaborateUsing expressionRelation ppatRelation dpatRelation signature context
        matcherTarget clauses afterClause generatedClauses next) :
      MatcherClausesElaborateUsing expressionRelation ppatRelation dpatRelation signature context matcherTarget
        (clause :: clauses) supply
        ⟨match generatedClause.evidence with
          | some evidence => evidence :: generatedClauses.evidences
          | none => generatedClauses.evidences,
          generatedClause.checks.append generatedClauses.checks⟩ next

/-- Independent matcher-literal relation parameterized only at expression
leaves.  This is the proof-level composition point for a recursive M4
dispatcher. -/
inductive MatcherLiteralElaboratesUsing
    (expressionRelation : ExpressionElaborationRelation)
    (ppatRelation : PPatElaborationRelation)
    (dpatRelation : DPatElaborationRelation)
    (signature : FrozenSignature) (context : Context) :
    List MatcherClause → Supply → Generated → Supply → Prop where
  | mk {clauses supply generatedClauses next}
      (checked : staticChecks signature clauses = true)
      (clausesElaboration : MatcherClausesElaborateUsing expressionRelation
        ppatRelation dpatRelation signature context (.var ⟨supply.ty⟩) clauses
        ⟨supply.ty + 1, supply.cap + 1⟩ generatedClauses next) :
      MatcherLiteralElaboratesUsing expressionRelation ppatRelation dpatRelation
        signature context clauses
        supply
        ⟨.matcher (.var ⟨supply.cap⟩) (.var ⟨supply.ty⟩),
          evidenceEquations (.var ⟨supply.cap⟩) generatedClauses.evidences ++
            generatedClauses.checks.hard,
          generatedClauses.checks.pending⟩ next

mutual

/-- Independent relational header typing. -/
inductive PPatElaborates (signature : FrozenSignature) :
    PPat → Ty → Option Cap → Supply → GeneratedPPat → Supply → Prop where
  | hole {expectedTarget expectedCapability supply} :
      PPatElaborates signature .hole expectedTarget expectedCapability supply
        ⟨[⟨.var ⟨supply.cap⟩, expectedTarget⟩], [], none,
          match expectedCapability with
          | some expected => [.cap (.var ⟨supply.cap⟩) expected]
          | none => []⟩
        ⟨supply.ty, supply.cap + 1⟩
  | wild {expectedTarget expectedCapability supply} :
      PPatElaborates signature .wild expectedTarget expectedCapability supply
        ⟨[], [], none, []⟩ supply
  | capture {expectedTarget expectedCapability supply} :
      PPatElaborates signature .capture expectedTarget expectedCapability supply
        ⟨[], [expectedTarget], none, []⟩ supply
  | ctor {constructor fields expectedTarget expectedCapability supply scheme
      generatedFields next}
      (lookup : signature.lookupPatternConstructor constructor = some scheme)
      (arity : fields.length = scheme.fields.length)
      (fieldsElaboration : PPatsElaborate signature fields
        (scheme.instantiate supply).1.fields (scheme.instantiate supply).2
        generatedFields next) :
      PPatElaborates signature (.ctor constructor fields) expectedTarget
        expectedCapability supply
        ⟨generatedFields.holes, generatedFields.captures,
          some (scheme.instantiate supply).1.result.capability,
          [.ty (scheme.instantiate supply).1.result.target expectedTarget] ++
            (match expectedCapability with
             | some expected =>
                 [.cap (scheme.instantiate supply).1.result.capability expected]
             | none => []) ++ generatedFields.hard⟩ next

/-- Independent relational left-to-right field typing. -/
inductive PPatsElaborate (signature : FrozenSignature) :
    List PPat → List Dual → Supply → GeneratedPPats → Supply → Prop where
  | nil {supply} :
      PPatsElaborate signature [] [] supply ⟨[], [], []⟩ supply
  | cons {pattern patterns expected expecteds supply generatedPattern
      afterPattern generatedPatterns next}
      (head : PPatElaborates signature pattern expected.target
        (some expected.capability) supply generatedPattern afterPattern)
      (tail : PPatsElaborate signature patterns expecteds afterPattern
        generatedPatterns next) :
      PPatsElaborate signature (pattern :: patterns) (expected :: expecteds)
        supply
        ⟨generatedPattern.holes ++ generatedPatterns.holes,
          generatedPattern.captures ++ generatedPatterns.captures,
          generatedPattern.hard ++ generatedPatterns.hard⟩ next

end


mutual

/-- Independent relational data-pattern typing. -/
inductive DPatElaborates (signature : FrozenSignature) :
    DPat → Ty → Supply → GeneratedDPat → Supply → Prop where
  | var {expected supply} :
      DPatElaborates signature .var expected supply ⟨[expected], []⟩ supply
  | wild {expected supply} :
      DPatElaborates signature .wild expected supply ⟨[], []⟩ supply
  | ctor {constructor fields expected supply scheme fieldTypes resultType
      generatedFields next}
      (lookup : signature.lookupDataConstructor constructor = some scheme)
      (arity : fields.length = scheme.callArity)
      (peel : peelFunctionExact fields.length (scheme.instantiate supply).1 =
        some (fieldTypes, resultType))
      (fieldsElaboration : DPatsElaborate signature fields fieldTypes
        (scheme.instantiate supply).2 generatedFields next) :
      DPatElaborates signature (.ctor constructor fields) expected supply
        ⟨generatedFields.bindings,
          [.ty resultType expected] ++ generatedFields.hard⟩ next
  | tuple {items expected supply fields generatedItems next}
      (fieldsEquality : fields = freshTargets supply items.length)
      (itemsElaboration : DPatsElaborate signature items fields
        (supply.nextTy items.length) generatedItems next) :
      DPatElaborates signature (.tuple items) expected supply
        ⟨generatedItems.bindings,
          [.ty expected (.prod fields)] ++ generatedItems.hard⟩ next

/-- Independent relational data-pattern-list typing. -/
inductive DPatsElaborate (signature : FrozenSignature) :
    List DPat → List Ty → Supply → GeneratedDPats → Supply → Prop where
  | nil {supply} :
      DPatsElaborate signature [] [] supply ⟨[], []⟩ supply
  | cons {pattern patterns expected expecteds supply generatedPattern
      afterPattern generatedPatterns next}
      (head : DPatElaborates signature pattern expected supply generatedPattern
        afterPattern)
      (tail : DPatsElaborate signature patterns expecteds afterPattern
        generatedPatterns next) :
      DPatsElaborate signature (pattern :: patterns) (expected :: expecteds)
        supply
        ⟨generatedPattern.bindings ++ generatedPatterns.bindings,
          generatedPattern.hard ++ generatedPatterns.hard⟩ next

end


/-- Independent relation for one M3 expression checked at an explicit type. -/
inductive CheckedExpressionElaborates
    (signature : FrozenSignature) (context : Context) :
    Expr → Ty → Supply → GeneratedChecks → Supply → Prop where
  | mk {expression expected supply generated next}
      (expressionElaboration : Elaborates signature.base context expression
        supply generated next) :
      CheckedExpressionElaborates signature context expression expected supply
        (GeneratedChecks.checked generated expected) next

/-- Independent relation for separately checked product components. -/
inductive NextMatcherItemsElaborate
    (signature : FrozenSignature) (context : Context) :
    List Expr → List Dual → Supply → GeneratedChecks → Supply → Prop where
  | nil {supply} :
      NextMatcherItemsElaborate signature context [] [] supply
        GeneratedChecks.empty supply
  | cons {item items hole holes supply generatedItem afterItem generatedItems next}
      (head : CheckedExpressionElaborates signature context item
        (.slot hole.capability hole.target) supply generatedItem afterItem)
      (tail : NextMatcherItemsElaborate signature context items holes afterItem
        generatedItems next) :
      NextMatcherItemsElaborate signature context (item :: items) (hole :: holes)
        supply (generatedItem.append generatedItems) next

/-- Independent relation for the zero/one/k next-matcher convention. -/
inductive NextMatchersElaborate
    (signature : FrozenSignature) (context : Context) :
    Expr → List Dual → Supply → GeneratedChecks → Supply → Prop where
  | zero {supply generated next}
      (checked : CheckedExpressionElaborates signature context (.tuple [])
        (.prod []) supply generated next) :
      NextMatchersElaborate signature context (.tuple []) [] supply generated next
  | one {expression hole supply generated next}
      (checked : CheckedExpressionElaborates signature context expression
        (.slot hole.capability hole.target) supply generated next) :
      NextMatchersElaborate signature context expression [hole] supply generated next
  | many {items first second rest supply generated next}
      (components : NextMatcherItemsElaborate signature context items
        (first :: second :: rest) supply generated next) :
      NextMatchersElaborate signature context (.tuple items)
        (first :: second :: rest) supply generated next

/-- Independent relation for one decomposition arm. -/
inductive MatcherArmElaborates
    (signature : FrozenSignature) (context : Context)
    (captures : List Ty) (matcherTarget : Ty) (holes : List Dual) :
    MatcherArm → Supply → GeneratedChecks → Supply → Prop where
  | mk {header body supply generatedHeader afterHeader generatedBody next}
      (headerElaboration : DPatElaborates signature header matcherTarget supply
        generatedHeader afterHeader)
      (bodyElaboration : CheckedExpressionElaborates signature
        (Pattern.extendContext generatedHeader.bindings
          (Pattern.extendContext captures context))
        body (DataTypes.list (holeProductTarget holes)) afterHeader
        generatedBody next) :
      MatcherArmElaborates signature context captures matcherTarget holes
        (.mk header body) supply
        ⟨generatedHeader.hard ++ generatedBody.hard, generatedBody.pending⟩ next

/-- Independent source-order arm relation. -/
inductive MatcherArmsElaborate
    (signature : FrozenSignature) (context : Context)
    (captures : List Ty) (matcherTarget : Ty) (holes : List Dual) :
    List MatcherArm → Supply → GeneratedArms → Supply → Prop where
  | nil {supply} : MatcherArmsElaborate signature context captures matcherTarget
      holes [] supply ⟨GeneratedChecks.empty⟩ supply
  | cons {arm arms supply generatedArm afterArm generatedArms next}
      (head : MatcherArmElaborates signature context captures matcherTarget holes
        arm supply generatedArm afterArm)
      (tail : MatcherArmsElaborate signature context captures matcherTarget holes
        arms afterArm generatedArms next) :
      MatcherArmsElaborate signature context captures matcherTarget holes
        (arm :: arms) supply ⟨generatedArm.append generatedArms.checks⟩ next

/-- Independent relation for one final source clause. -/
inductive MatcherClauseElaborates
    (signature : FrozenSignature) (context : Context) (matcherTarget : Ty) :
    MatcherClause → Supply → GeneratedMatcherClause → Supply → Prop where
  | mk {header nextMatchers arms supply generatedHeader afterHeader generatedNext
      afterNext generatedArms next}
      (shape : (MatcherClause.mk header nextMatchers arms).toShape.check signature =
        true)
      (headerElaboration : PPatElaborates signature header matcherTarget none
        supply generatedHeader afterHeader)
      (nextElaboration : NextMatchersElaborate signature
        (Pattern.extendContext generatedHeader.captures context)
        nextMatchers generatedHeader.holes afterHeader generatedNext afterNext)
      (armsElaboration : MatcherArmsElaborate signature context
        generatedHeader.captures matcherTarget generatedHeader.holes arms afterNext
        generatedArms next) :
      MatcherClauseElaborates signature context matcherTarget
        (.mk header nextMatchers arms) supply
        ⟨generatedHeader.holes, generatedHeader.evidence,
          ⟨generatedHeader.hard ++ generatedNext.hard ++ generatedArms.checks.hard,
            generatedNext.pending ++ generatedArms.checks.pending⟩⟩ next

/-- Independent source-order clause relation. -/
inductive MatcherClausesElaborate
    (signature : FrozenSignature) (context : Context) (matcherTarget : Ty) :
    List MatcherClause → Supply → GeneratedMatcherClauses → Supply → Prop where
  | nil {supply} : MatcherClausesElaborate signature context matcherTarget [] supply
      ⟨[], GeneratedChecks.empty⟩ supply
  | cons {clause clauses supply generatedClause afterClause generatedClauses next}
      (head : MatcherClauseElaborates signature context matcherTarget clause supply
        generatedClause afterClause)
      (tail : MatcherClausesElaborate signature context matcherTarget clauses
        afterClause generatedClauses next) :
      MatcherClausesElaborate signature context matcherTarget (clause :: clauses)
        supply
        ⟨match generatedClause.evidence with
          | some evidence => evidence :: generatedClauses.evidences
          | none => generatedClauses.evidences,
          generatedClause.checks.append generatedClauses.checks⟩ next

/-- Independent relational matcher-literal judgment. -/
inductive MatcherLiteralElaborates
    (signature : FrozenSignature) (context : Context) :
    List MatcherClause → Supply → Generated → Supply → Prop where
  | mk {clauses supply generatedClauses next}
      (checked : staticChecks signature clauses = true)
      (clausesElaboration : MatcherClausesElaborate signature context
        (.var ⟨supply.ty⟩) clauses ⟨supply.ty + 1, supply.cap + 1⟩
        generatedClauses next) :
      MatcherLiteralElaborates signature context clauses supply
        ⟨.matcher (.var ⟨supply.cap⟩) (.var ⟨supply.ty⟩),
          evidenceEquations (.var ⟨supply.cap⟩) generatedClauses.evidences ++
            generatedClauses.checks.hard,
          generatedClauses.checks.pending⟩ next

mutual

/-- Executable primitive-pattern typing is sound for its independent
relation. -/
theorem elaboratePPat_sound
    {signature : FrozenSignature} {pattern : PPat} {expectedTarget : Ty}
    {expectedCapability : Option Cap} {supply next : Supply}
    {generated : GeneratedPPat}
    (success : elaboratePPat signature pattern expectedTarget expectedCapability supply =
      some (generated, next)) :
    PPatElaborates signature pattern expectedTarget expectedCapability supply
      generated next := by
  cases pattern with
  | hole =>
      cases expectedCapability <;>
        simp [elaboratePPat] at success <;>
        rcases success with ⟨rfl, rfl⟩ <;> exact .hole
  | wild =>
      simp [elaboratePPat] at success
      rcases success with ⟨rfl, rfl⟩
      exact .wild
  | capture =>
      simp [elaboratePPat] at success
      rcases success with ⟨rfl, rfl⟩
      exact .capture
  | ctor constructor fields =>
      cases lookup : signature.lookupPatternConstructor constructor with
      | none => simp [elaboratePPat, lookup] at success
      | some scheme =>
          by_cases arity : fields.length = scheme.fields.length
          · cases fieldsResult : elaboratePPatFields signature fields
                (scheme.instantiate supply).1.fields
                (scheme.instantiate supply).2 with
            | none => simp [elaboratePPat, lookup, arity, fieldsResult] at success
            | some output =>
                rcases output with ⟨generatedFields, afterFields⟩
                simp [elaboratePPat, lookup, arity, fieldsResult] at success
                rcases success with ⟨rfl, rfl⟩
                exact .ctor lookup arity
                  (elaboratePPatFields_sound fieldsResult)
          · simp [elaboratePPat, lookup, arity] at success
termination_by MatcherTyping.PPat.typingSize pattern * 2 + 1
decreasing_by
  all_goals simp_wf
  all_goals simp_all [MatcherTyping.PPat.typingSize,
    MatcherTyping.PPat.listTypingSize]
  all_goals omega

/-- Executable primitive-pattern field typing is sound. -/
theorem elaboratePPatFields_sound
    {signature : FrozenSignature} {patterns : List PPat} {expected : List Dual}
    {supply next : Supply} {generated : GeneratedPPats}
    (success : elaboratePPatFields signature patterns expected supply =
      some (generated, next)) :
    PPatsElaborate signature patterns expected supply generated next := by
  cases patterns with
  | nil =>
      cases expected with
      | nil =>
          simp [elaboratePPatFields] at success
          rcases success with ⟨rfl, rfl⟩
          exact .nil
      | cons expected expecteds =>
          simp [elaboratePPatFields] at success
  | cons pattern patterns =>
      cases expected with
      | nil => simp [elaboratePPatFields] at success
      | cons expected expecteds =>
          cases patternResult : elaboratePPat signature pattern expected.target
              (some expected.capability) supply with
          | none => simp [elaboratePPatFields, patternResult] at success
          | some output =>
              rcases output with ⟨generatedPattern, afterPattern⟩
              cases patternsResult : elaboratePPatFields signature patterns expecteds
                  afterPattern with
              | none =>
                  simp [elaboratePPatFields, patternResult, patternsResult] at success
              | some rest =>
                  rcases rest with ⟨generatedPatterns, afterPatterns⟩
                  simp [elaboratePPatFields, patternResult, patternsResult] at success
                  rcases success with ⟨rfl, rfl⟩
                  exact .cons (elaboratePPat_sound patternResult)
                    (elaboratePPatFields_sound patternsResult)
termination_by MatcherTyping.PPat.listTypingSize patterns * 2
decreasing_by
  all_goals simp_wf
  all_goals simp_all [MatcherTyping.PPat.typingSize,
    MatcherTyping.PPat.listTypingSize]
  all_goals omega

end


mutual

/-- Executable data-pattern typing is sound. -/
theorem elaborateDPat_sound
    {signature : FrozenSignature} {pattern : DPat} {expected : Ty}
    {supply next : Supply} {generated : GeneratedDPat}
    (success : elaborateDPat signature pattern expected supply =
      some (generated, next)) :
    DPatElaborates signature pattern expected supply generated next := by
  cases pattern with
  | var =>
      simp [elaborateDPat] at success
      rcases success with ⟨rfl, rfl⟩
      exact .var
  | wild =>
      simp [elaborateDPat] at success
      rcases success with ⟨rfl, rfl⟩
      exact .wild
  | ctor constructor fields =>
      cases lookup : signature.lookupDataConstructor constructor with
      | none => simp [elaborateDPat, lookup] at success
      | some scheme =>
          by_cases arity : fields.length = scheme.callArity
          · cases peelResult : peelFunctionExact scheme.callArity
                (scheme.instantiate supply).1 with
            | none => simp [elaborateDPat, lookup, arity, peelResult] at success
            | some peeled =>
                rcases peeled with ⟨fieldTypes, resultType⟩
                have peel : peelFunctionExact fields.length
                    (scheme.instantiate supply).1 =
                    some (fieldTypes, resultType) := by
                  rw [arity]
                  exact peelResult
                cases fieldsResult : elaborateDPatFields signature fields fieldTypes
                    (scheme.instantiate supply).2 with
                | none =>
                    simp [elaborateDPat, lookup, arity, peelResult,
                      fieldsResult] at success
                | some output =>
                    rcases output with ⟨generatedFields, afterFields⟩
                    simp [elaborateDPat, lookup, arity, peelResult,
                      fieldsResult] at success
                    rcases success with ⟨rfl, rfl⟩
                    exact .ctor lookup arity peel
                      (elaborateDPatFields_sound fieldsResult)
          · simp [elaborateDPat, lookup, arity] at success
  | tuple items =>
      cases itemsResult : elaborateDPatFields signature items
          (freshTargets supply items.length) (supply.nextTy items.length) with
      | none => simp [elaborateDPat, itemsResult] at success
      | some output =>
          rcases output with ⟨generatedItems, afterItems⟩
          simp [elaborateDPat, itemsResult] at success
          rcases success with ⟨rfl, rfl⟩
          exact .tuple rfl (elaborateDPatFields_sound itemsResult)
termination_by MatcherTyping.DPat.typingSize pattern * 2 + 1
decreasing_by
  all_goals simp_wf
  all_goals simp_all [MatcherTyping.DPat.typingSize,
    MatcherTyping.DPat.listTypingSize]
  all_goals omega

/-- Executable data-pattern field typing is sound. -/
theorem elaborateDPatFields_sound
    {signature : FrozenSignature} {patterns : List DPat} {expected : List Ty}
    {supply next : Supply} {generated : GeneratedDPats}
    (success : elaborateDPatFields signature patterns expected supply =
      some (generated, next)) :
    DPatsElaborate signature patterns expected supply generated next := by
  cases patterns with
  | nil =>
      cases expected with
      | nil =>
          simp [elaborateDPatFields] at success
          rcases success with ⟨rfl, rfl⟩
          exact .nil
      | cons expected expecteds => simp [elaborateDPatFields] at success
  | cons pattern patterns =>
      cases expected with
      | nil => simp [elaborateDPatFields] at success
      | cons expected expecteds =>
          cases patternResult : elaborateDPat signature pattern expected supply with
          | none => simp [elaborateDPatFields, patternResult] at success
          | some output =>
              rcases output with ⟨generatedPattern, afterPattern⟩
              cases patternsResult : elaborateDPatFields signature patterns expecteds
                  afterPattern with
              | none =>
                  simp [elaborateDPatFields, patternResult, patternsResult] at success
              | some rest =>
                  rcases rest with ⟨generatedPatterns, afterPatterns⟩
                  simp [elaborateDPatFields, patternResult, patternsResult] at success
                  rcases success with ⟨rfl, rfl⟩
                  exact .cons (elaborateDPat_sound patternResult)
                    (elaborateDPatFields_sound patternsResult)
termination_by MatcherTyping.DPat.listTypingSize patterns * 2
decreasing_by
  all_goals simp_wf
  all_goals simp_all [MatcherTyping.DPat.typingSize,
    MatcherTyping.DPat.listTypingSize]
  all_goals omega

end

/-- Executable M3-boundary checking is sound. -/
theorem elaborateCheckedExpression_sound
    {signature : FrozenSignature} (wellFormed : signature.WellFormed)
    {context : Context} {expression : Expr} {expected : Ty}
    {supply next : Supply} {generated : GeneratedChecks}
    (success : elaborateCheckedExpression signature context expression expected supply =
      some (generated, next)) :
    CheckedExpressionElaborates signature context expression expected supply
      generated next := by
  cases expressionResult : elaborate signature.base context expression supply with
  | none => simp [elaborateCheckedExpression, expressionResult] at success
  | some output =>
      rcases output with ⟨generatedExpression, afterExpression⟩
      simp [elaborateCheckedExpression, expressionResult] at success
      rcases success with ⟨rfl, rfl⟩
      exact .mk (elaborate_sound wellFormed.baseWellFormed expressionResult)

theorem elaborateNextMatcherItems_sound
    {signature : FrozenSignature} (wellFormed : signature.WellFormed)
    {context : Context} {items : List Expr} {holes : List Dual}
    {supply next : Supply} {generated : GeneratedChecks}
    (success : elaborateNextMatcherItems signature context items holes supply =
      some (generated, next)) :
    NextMatcherItemsElaborate signature context items holes supply generated next := by
  induction items generalizing holes supply generated next with
  | nil =>
      cases holes with
      | nil =>
          simp [elaborateNextMatcherItems] at success
          rcases success with ⟨rfl, rfl⟩
          exact .nil
      | cons hole holes => simp [elaborateNextMatcherItems] at success
  | cons item items induction =>
      cases holes with
      | nil => simp [elaborateNextMatcherItems] at success
      | cons hole holes =>
          cases itemResult : elaborateCheckedExpression signature context item
              (.slot hole.capability hole.target) supply with
          | none => simp [elaborateNextMatcherItems, itemResult] at success
          | some output =>
              rcases output with ⟨generatedItem, afterItem⟩
              cases itemsResult : elaborateNextMatcherItems signature context items
                  holes afterItem with
              | none =>
                  simp [elaborateNextMatcherItems, itemResult, itemsResult] at success
              | some rest =>
                  rcases rest with ⟨generatedItems, afterItems⟩
                  simp [elaborateNextMatcherItems, itemResult, itemsResult] at success
                  rcases success with ⟨rfl, rfl⟩
                  exact .cons
                    (elaborateCheckedExpression_sound wellFormed itemResult)
                    (induction itemsResult)

theorem elaborateNextMatchers_sound
    {signature : FrozenSignature} (wellFormed : signature.WellFormed)
    {context : Context} {expression : Expr} {holes : List Dual}
    {supply next : Supply} {generated : GeneratedChecks}
    (success : elaborateNextMatchers signature context expression holes supply =
      some (generated, next)) :
    NextMatchersElaborate signature context expression holes supply generated next := by
  cases holes with
  | nil =>
      cases expression with
      | tuple items =>
          cases items with
          | nil =>
              exact .zero (elaborateCheckedExpression_sound wellFormed (by
                simpa [elaborateNextMatchers] using success))
          | cons item items => simp [elaborateNextMatchers] at success
      | var | lit | something | lam | app | letE | ctor | prim | ifE | fixE |
          matcher | matchAll | matchFirst => simp [elaborateNextMatchers] at success
  | cons first rest =>
      cases rest with
      | nil =>
          exact .one (elaborateCheckedExpression_sound wellFormed (by
            simpa [elaborateNextMatchers] using success))
      | cons second rest =>
          cases expression with
          | tuple items =>
              exact .many (elaborateNextMatcherItems_sound wellFormed (by
                simpa [elaborateNextMatchers] using success))
          | var | lit | something | lam | app | letE | ctor | prim | ifE | fixE |
              matcher | matchAll | matchFirst =>
                simp [elaborateNextMatchers] at success

theorem elaborateMatcherArm_sound
    {signature : FrozenSignature} (wellFormed : signature.WellFormed)
    {context : Context} {captures : List Ty} {matcherTarget : Ty}
    {holes : List Dual} {arm : MatcherArm} {supply next : Supply}
    {generated : GeneratedChecks}
    (success : elaborateMatcherArm signature context captures matcherTarget holes arm
      supply = some (generated, next)) :
    MatcherArmElaborates signature context captures matcherTarget holes arm supply
      generated next := by
  cases arm with
  | mk header body =>
      cases headerResult : elaborateDPat signature header matcherTarget supply with
      | none => simp [elaborateMatcherArm, headerResult] at success
      | some output =>
          rcases output with ⟨generatedHeader, afterHeader⟩
          cases bodyResult : elaborateCheckedExpression signature
              (Pattern.extendContext generatedHeader.bindings
                (Pattern.extendContext captures context))
              body (DataTypes.list (holeProductTarget holes)) afterHeader with
          | none => simp [elaborateMatcherArm, headerResult, bodyResult] at success
          | some bodyOutput =>
              rcases bodyOutput with ⟨generatedBody, afterBody⟩
              simp [elaborateMatcherArm, headerResult, bodyResult] at success
              rcases success with ⟨rfl, rfl⟩
              exact .mk (elaborateDPat_sound headerResult)
                (elaborateCheckedExpression_sound wellFormed bodyResult)

theorem elaborateMatcherArms_sound
    {signature : FrozenSignature} (wellFormed : signature.WellFormed)
    {context : Context} {captures : List Ty} {matcherTarget : Ty}
    {holes : List Dual} {arms : List MatcherArm} {supply next : Supply}
    {generated : GeneratedArms}
    (success : elaborateMatcherArms signature context captures matcherTarget holes arms
      supply = some (generated, next)) :
    MatcherArmsElaborate signature context captures matcherTarget holes arms supply
      generated next := by
  induction arms generalizing supply generated next with
  | nil =>
      simp [elaborateMatcherArms] at success
      rcases success with ⟨rfl, rfl⟩
      exact .nil
  | cons arm arms induction =>
      cases armResult : elaborateMatcherArm signature context captures matcherTarget
          holes arm supply with
      | none => simp [elaborateMatcherArms, armResult] at success
      | some output =>
          rcases output with ⟨generatedArm, afterArm⟩
          cases armsResult : elaborateMatcherArms signature context captures
              matcherTarget holes arms afterArm with
          | none => simp [elaborateMatcherArms, armResult, armsResult] at success
          | some rest =>
              rcases rest with ⟨generatedArms, afterArms⟩
              simp [elaborateMatcherArms, armResult, armsResult] at success
              rcases success with ⟨rfl, rfl⟩
              exact .cons (elaborateMatcherArm_sound wellFormed armResult)
                (induction armsResult)

theorem elaborateMatcherClause_sound
    {signature : FrozenSignature} (wellFormed : signature.WellFormed)
    {context : Context} {matcherTarget : Ty} {clause : MatcherClause}
    {supply next : Supply} {generated : GeneratedMatcherClause}
    (success : elaborateMatcherClause signature context matcherTarget clause supply =
      some (generated, next)) :
    MatcherClauseElaborates signature context matcherTarget clause supply generated next := by
  cases clause with
  | mk header nextMatchers arms =>
      cases shapeValue :
          (MatcherClause.mk header nextMatchers arms).toShape.check signature with
      | false =>
          simp [elaborateMatcherClause, shapeValue] at success
      | true =>
        cases headerResult : elaboratePPat signature header matcherTarget none supply with
        | none =>
            simp [elaborateMatcherClause, MatcherClause.header,
              MatcherClause.nextMatchers, MatcherClause.arms, shapeValue,
              headerResult] at success
        | some output =>
            rcases output with ⟨generatedHeader, afterHeader⟩
            cases nextResult : elaborateNextMatchers signature
                (Pattern.extendContext generatedHeader.captures context)
                nextMatchers generatedHeader.holes afterHeader with
            | none =>
                simp [elaborateMatcherClause, MatcherClause.header,
                  MatcherClause.nextMatchers, MatcherClause.arms, shapeValue,
                  headerResult, nextResult] at success
            | some nextOutput =>
                rcases nextOutput with ⟨generatedNext, afterNext⟩
                cases armsResult : elaborateMatcherArms signature context
                    generatedHeader.captures matcherTarget generatedHeader.holes arms
                    afterNext with
                | none =>
                    simp [elaborateMatcherClause, MatcherClause.header,
                      MatcherClause.nextMatchers, MatcherClause.arms, shapeValue,
                      headerResult, nextResult, armsResult] at success
                | some armsOutput =>
                    rcases armsOutput with ⟨generatedArms, afterArms⟩
                    simp [elaborateMatcherClause, MatcherClause.header,
                      MatcherClause.nextMatchers, MatcherClause.arms, shapeValue,
                      headerResult, nextResult, armsResult] at success
                    rcases success with ⟨rfl, rfl⟩
                    simpa [List.append_assoc] using
                      (MatcherClauseElaborates.mk shapeValue
                        (elaboratePPat_sound headerResult)
                        (elaborateNextMatchers_sound wellFormed nextResult)
                        (elaborateMatcherArms_sound wellFormed armsResult))

theorem elaborateMatcherClauses_sound
    {signature : FrozenSignature} (wellFormed : signature.WellFormed)
    {context : Context} {matcherTarget : Ty} {clauses : List MatcherClause}
    {supply next : Supply} {generated : GeneratedMatcherClauses}
    (success : elaborateMatcherClauses signature context matcherTarget clauses supply =
      some (generated, next)) :
    MatcherClausesElaborate signature context matcherTarget clauses supply generated next := by
  induction clauses generalizing supply generated next with
  | nil =>
      simp [elaborateMatcherClauses] at success
      rcases success with ⟨rfl, rfl⟩
      exact .nil
  | cons clause clauses induction =>
      cases clauseResult : elaborateMatcherClause signature context matcherTarget clause
          supply with
      | none => simp [elaborateMatcherClauses, clauseResult] at success
      | some output =>
          rcases output with ⟨generatedClause, afterClause⟩
          cases clausesResult : elaborateMatcherClauses signature context matcherTarget
              clauses afterClause with
          | none =>
              simp [elaborateMatcherClauses, clauseResult, clausesResult] at success
          | some rest =>
              rcases rest with ⟨generatedClauses, afterClauses⟩
              simp [elaborateMatcherClauses, clauseResult, clausesResult] at success
              rcases success with ⟨rfl, rfl⟩
              exact .cons (elaborateMatcherClause_sound wellFormed clauseResult)
                (induction clausesResult)

/-- Main acceptance soundness theorem for executable matcher-literal
elaboration. -/
theorem elaborateMatcherLiteral_sound
    {signature : FrozenSignature} (wellFormed : signature.WellFormed)
    {context : Context} {clauses : List MatcherClause} {supply next : Supply}
    {generated : Generated}
    (success : elaborateMatcherLiteral signature context clauses supply =
      some (generated, next)) :
    MatcherLiteralElaborates signature context clauses supply generated next := by
  cases checkedValue : staticChecks signature clauses with
  | false => simp [elaborateMatcherLiteral, checkedValue] at success
  | true =>
    cases clausesResult : elaborateMatcherClauses signature context
        (.var ⟨supply.ty⟩) clauses ⟨supply.ty + 1, supply.cap + 1⟩ with
    | none => simp [elaborateMatcherLiteral, checkedValue, clausesResult] at success
    | some output =>
        rcases output with ⟨generatedClauses, afterClauses⟩
        simp [elaborateMatcherLiteral, checkedValue, clausesResult] at success
        rcases success with ⟨rfl, rfl⟩
        exact .mk checkedValue
          (elaborateMatcherClauses_sound wellFormed clausesResult)

/-! ## Soundness of callback-parametric matcher elaboration -/

theorem elaborateCheckedExpressionUsing_sound
    {expressionElaborator : ExpressionElaborator}
    {expressionRelation : ExpressionElaborationRelation}
    (expressionSound : ∀ {context expression supply generated next},
      expressionElaborator context expression supply = some (generated, next) →
        expressionRelation context expression supply generated next)
    {context : Context} {expression : Expr} {expected : Ty}
    {supply next : Supply} {generated : GeneratedChecks}
    (success : elaborateCheckedExpressionUsing expressionElaborator context
      expression expected supply = some (generated, next)) :
    CheckedExpressionElaboratesUsing expressionRelation context expression
      expected supply generated next := by
  cases result : expressionElaborator context expression supply with
  | none => simp [elaborateCheckedExpressionUsing, result] at success
  | some output =>
      rcases output with ⟨generatedExpression, afterExpression⟩
      simp [elaborateCheckedExpressionUsing, result] at success
      rcases success with ⟨rfl, rfl⟩
      exact .mk (expressionSound result)

theorem elaborateNextMatcherItemsUsing_sound
    {expressionElaborator : ExpressionElaborator}
    {expressionRelation : ExpressionElaborationRelation}
    (expressionSound : ∀ {context expression supply generated next},
      expressionElaborator context expression supply = some (generated, next) →
        expressionRelation context expression supply generated next)
    {context : Context} {items : List Expr} {holes : List Dual}
    {supply next : Supply} {generated : GeneratedChecks}
    (success : elaborateNextMatcherItemsUsing expressionElaborator context items
      holes supply = some (generated, next)) :
    NextMatcherItemsElaborateUsing expressionRelation context items holes supply
      generated next := by
  induction items generalizing holes supply generated next with
  | nil =>
      cases holes with
      | nil =>
          simp [elaborateNextMatcherItemsUsing] at success
          rcases success with ⟨rfl, rfl⟩
          exact .nil
      | cons hole holes => simp [elaborateNextMatcherItemsUsing] at success
  | cons item items induction =>
      cases holes with
      | nil => simp [elaborateNextMatcherItemsUsing] at success
      | cons hole holes =>
          cases itemResult : elaborateCheckedExpressionUsing expressionElaborator
              context item (.slot hole.capability hole.target) supply with
          | none =>
              simp [elaborateNextMatcherItemsUsing, itemResult] at success
          | some output =>
              rcases output with ⟨generatedItem, afterItem⟩
              cases itemsResult : elaborateNextMatcherItemsUsing expressionElaborator
                  context items holes afterItem with
              | none =>
                  simp [elaborateNextMatcherItemsUsing, itemResult, itemsResult]
                    at success
              | some rest =>
                  rcases rest with ⟨generatedItems, afterItems⟩
                  simp [elaborateNextMatcherItemsUsing, itemResult, itemsResult]
                    at success
                  rcases success with ⟨rfl, rfl⟩
                  exact .cons
                    (elaborateCheckedExpressionUsing_sound expressionSound itemResult)
                    (induction itemsResult)

theorem elaborateNextMatchersUsing_sound
    {expressionElaborator : ExpressionElaborator}
    {expressionRelation : ExpressionElaborationRelation}
    (expressionSound : ∀ {context expression supply generated next},
      expressionElaborator context expression supply = some (generated, next) →
        expressionRelation context expression supply generated next)
    {context : Context} {expression : Expr} {holes : List Dual}
    {supply next : Supply} {generated : GeneratedChecks}
    (success : elaborateNextMatchersUsing expressionElaborator context expression
      holes supply = some (generated, next)) :
    NextMatchersElaborateUsing expressionRelation context expression holes supply
      generated next := by
  cases holes with
  | nil =>
      cases expression with
      | tuple items =>
          cases items with
          | nil =>
              exact .zero (elaborateCheckedExpressionUsing_sound expressionSound (by
                simpa [elaborateNextMatchersUsing] using success))
          | cons item items => simp [elaborateNextMatchersUsing] at success
      | var | lit | something | lam | app | letE | ctor | prim | ifE | fixE |
          matcher | matchAll | matchFirst =>
            simp [elaborateNextMatchersUsing] at success
  | cons first rest =>
      cases rest with
      | nil =>
          exact .one (elaborateCheckedExpressionUsing_sound expressionSound (by
            simpa [elaborateNextMatchersUsing] using success))
      | cons second rest =>
          cases expression with
          | tuple items =>
              exact .many (elaborateNextMatcherItemsUsing_sound expressionSound (by
                simpa [elaborateNextMatchersUsing] using success))
          | var | lit | something | lam | app | letE | ctor | prim | ifE | fixE |
              matcher | matchAll | matchFirst =>
                simp [elaborateNextMatchersUsing] at success

theorem elaborateMatcherArmUsing_sound
    {expressionElaborator : ExpressionElaborator}
    {expressionRelation : ExpressionElaborationRelation}
    (expressionSound : ∀ {context expression supply generated next},
      expressionElaborator context expression supply = some (generated, next) →
        expressionRelation context expression supply generated next)
    {signature : FrozenSignature} {context : Context} {captures : List Ty}
    {matcherTarget : Ty} {holes : List Dual} {arm : MatcherArm}
    {supply next : Supply} {generated : GeneratedChecks}
    (success : elaborateMatcherArmUsing expressionElaborator signature context
      captures matcherTarget holes arm supply = some (generated, next)) :
    MatcherArmElaboratesUsing expressionRelation DPatElaborates signature context
      captures matcherTarget holes arm supply generated next := by
  cases arm with
  | mk header body =>
      cases headerResult : elaborateDPat signature header matcherTarget supply with
      | none => simp [elaborateMatcherArmUsing, headerResult] at success
      | some output =>
          rcases output with ⟨generatedHeader, afterHeader⟩
          cases bodyResult : elaborateCheckedExpressionUsing expressionElaborator
              (Pattern.extendContext generatedHeader.bindings
                (Pattern.extendContext captures context))
              body (DataTypes.list (holeProductTarget holes)) afterHeader with
          | none =>
              simp [elaborateMatcherArmUsing, headerResult, bodyResult] at success
          | some bodyOutput =>
              rcases bodyOutput with ⟨generatedBody, afterBody⟩
              simp [elaborateMatcherArmUsing, headerResult, bodyResult] at success
              rcases success with ⟨rfl, rfl⟩
              exact .mk (elaborateDPat_sound headerResult)
                (elaborateCheckedExpressionUsing_sound expressionSound bodyResult)

theorem elaborateMatcherArmsUsing_sound
    {expressionElaborator : ExpressionElaborator}
    {expressionRelation : ExpressionElaborationRelation}
    (expressionSound : ∀ {context expression supply generated next},
      expressionElaborator context expression supply = some (generated, next) →
        expressionRelation context expression supply generated next)
    {signature : FrozenSignature} {context : Context} {captures : List Ty}
    {matcherTarget : Ty} {holes : List Dual} {arms : List MatcherArm}
    {supply next : Supply} {generated : GeneratedArms}
    (success : elaborateMatcherArmsUsing expressionElaborator signature context
      captures matcherTarget holes arms supply = some (generated, next)) :
    MatcherArmsElaborateUsing expressionRelation DPatElaborates signature context
      captures matcherTarget holes arms supply generated next := by
  induction arms generalizing supply generated next with
  | nil =>
      simp [elaborateMatcherArmsUsing] at success
      rcases success with ⟨rfl, rfl⟩
      exact .nil
  | cons arm arms induction =>
      cases armResult : elaborateMatcherArmUsing expressionElaborator signature
          context captures matcherTarget holes arm supply with
      | none => simp [elaborateMatcherArmsUsing, armResult] at success
      | some output =>
          rcases output with ⟨generatedArm, afterArm⟩
          cases armsResult : elaborateMatcherArmsUsing expressionElaborator signature
              context captures matcherTarget holes arms afterArm with
          | none =>
              simp [elaborateMatcherArmsUsing, armResult, armsResult] at success
          | some rest =>
              rcases rest with ⟨generatedArms, afterArms⟩
              simp [elaborateMatcherArmsUsing, armResult, armsResult] at success
              rcases success with ⟨rfl, rfl⟩
              exact .cons
                (elaborateMatcherArmUsing_sound expressionSound armResult)
                (induction armsResult)

theorem elaborateMatcherClauseUsing_sound
    {expressionElaborator : ExpressionElaborator}
    {expressionRelation : ExpressionElaborationRelation}
    (expressionSound : ∀ {context expression supply generated next},
      expressionElaborator context expression supply = some (generated, next) →
        expressionRelation context expression supply generated next)
    {signature : FrozenSignature} {context : Context} {matcherTarget : Ty}
    {clause : MatcherClause} {supply next : Supply}
    {generated : GeneratedMatcherClause}
    (success : elaborateMatcherClauseUsing expressionElaborator signature context
      matcherTarget clause supply = some (generated, next)) :
    MatcherClauseElaboratesUsing expressionRelation PPatElaborates DPatElaborates
      signature context matcherTarget clause supply generated next := by
  cases clause with
  | mk header nextMatchers arms =>
      cases shapeValue :
          (MatcherClause.mk header nextMatchers arms).toShape.check signature with
      | false => simp [elaborateMatcherClauseUsing, shapeValue] at success
      | true =>
        cases headerResult : elaboratePPat signature header matcherTarget none supply with
        | none =>
            simp [elaborateMatcherClauseUsing, MatcherClause.header,
              MatcherClause.nextMatchers, MatcherClause.arms, shapeValue,
              headerResult] at success
        | some output =>
            rcases output with ⟨generatedHeader, afterHeader⟩
            cases nextResult : elaborateNextMatchersUsing expressionElaborator
                (Pattern.extendContext generatedHeader.captures context)
                nextMatchers generatedHeader.holes afterHeader with
            | none =>
                simp [elaborateMatcherClauseUsing, MatcherClause.header,
                  MatcherClause.nextMatchers, MatcherClause.arms, shapeValue,
                  headerResult, nextResult] at success
            | some nextOutput =>
                rcases nextOutput with ⟨generatedNext, afterNext⟩
                cases armsResult : elaborateMatcherArmsUsing expressionElaborator
                    signature context generatedHeader.captures matcherTarget
                    generatedHeader.holes arms afterNext with
                | none =>
                    simp [elaborateMatcherClauseUsing, MatcherClause.header,
                      MatcherClause.nextMatchers, MatcherClause.arms, shapeValue,
                      headerResult, nextResult, armsResult] at success
                | some armsOutput =>
                    rcases armsOutput with ⟨generatedArms, afterArms⟩
                    simp [elaborateMatcherClauseUsing, MatcherClause.header,
                      MatcherClause.nextMatchers, MatcherClause.arms, shapeValue,
                      headerResult, nextResult, armsResult] at success
                    rcases success with ⟨rfl, rfl⟩
                    simpa [List.append_assoc] using
                      (MatcherClauseElaboratesUsing.mk shapeValue
                        (elaboratePPat_sound headerResult)
                        (elaborateNextMatchersUsing_sound expressionSound nextResult)
                        (elaborateMatcherArmsUsing_sound expressionSound armsResult))

theorem elaborateMatcherClausesUsing_sound
    {expressionElaborator : ExpressionElaborator}
    {expressionRelation : ExpressionElaborationRelation}
    (expressionSound : ∀ {context expression supply generated next},
      expressionElaborator context expression supply = some (generated, next) →
        expressionRelation context expression supply generated next)
    {signature : FrozenSignature} {context : Context} {matcherTarget : Ty}
    {clauses : List MatcherClause} {supply next : Supply}
    {generated : GeneratedMatcherClauses}
    (success : elaborateMatcherClausesUsing expressionElaborator signature context
      matcherTarget clauses supply = some (generated, next)) :
    MatcherClausesElaborateUsing expressionRelation PPatElaborates DPatElaborates
      signature context matcherTarget clauses supply generated next := by
  induction clauses generalizing supply generated next with
  | nil =>
      simp [elaborateMatcherClausesUsing] at success
      rcases success with ⟨rfl, rfl⟩
      exact .nil
  | cons clause clauses induction =>
      cases clauseResult : elaborateMatcherClauseUsing expressionElaborator signature
          context matcherTarget clause supply with
      | none => simp [elaborateMatcherClausesUsing, clauseResult] at success
      | some output =>
          rcases output with ⟨generatedClause, afterClause⟩
          cases clausesResult : elaborateMatcherClausesUsing expressionElaborator
              signature context matcherTarget clauses afterClause with
          | none =>
              simp [elaborateMatcherClausesUsing, clauseResult, clausesResult]
                at success
          | some rest =>
              rcases rest with ⟨generatedClauses, afterClauses⟩
              simp [elaborateMatcherClausesUsing, clauseResult, clausesResult]
                at success
              rcases success with ⟨rfl, rfl⟩
              exact .cons
                (elaborateMatcherClauseUsing_sound expressionSound clauseResult)
                (induction clausesResult)

/-- The composable executable entrypoint is sound whenever its expression
callback is sound.  Header relations remain the independently defined
`PPatElaborates` and `DPatElaborates` judgments. -/
theorem elaborateMatcherLiteralUsing_sound
    {expressionElaborator : ExpressionElaborator}
    {expressionRelation : ExpressionElaborationRelation}
    (expressionSound : ∀ {context expression supply generated next},
      expressionElaborator context expression supply = some (generated, next) →
        expressionRelation context expression supply generated next)
    {signature : FrozenSignature} {context : Context}
    {clauses : List MatcherClause} {supply next : Supply}
    {generated : Generated}
    (success : elaborateMatcherLiteralUsing expressionElaborator signature context
      clauses supply = some (generated, next)) :
    MatcherLiteralElaboratesUsing expressionRelation PPatElaborates DPatElaborates
      signature context clauses supply generated next := by
  cases checkedValue : staticChecks signature clauses with
  | false =>
      simp [elaborateMatcherLiteralUsing, checkedValue] at success
  | true =>
    cases clausesResult : elaborateMatcherClausesUsing expressionElaborator signature
        context (.var ⟨supply.ty⟩) clauses
        ⟨supply.ty + 1, supply.cap + 1⟩ with
    | none =>
        simp [elaborateMatcherLiteralUsing, checkedValue, clausesResult] at success
    | some output =>
        rcases output with ⟨generatedClauses, afterClauses⟩
        simp [elaborateMatcherLiteralUsing, checkedValue, clausesResult] at success
        rcases success with ⟨rfl, rfl⟩
        exact .mk checkedValue
          (elaborateMatcherClausesUsing_sound expressionSound clausesResult)

end MatcherTyping

end TypePM.Source
