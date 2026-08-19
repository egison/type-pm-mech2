# 独立したType-PM型付けの設計

## 目標

型付け可能性を，実行可能な制約解決手続き（solver）の状態，source順の履歴，推論終了後の再検査
（terminal audit）に依存しない帰納的な判断`Typing`で定義する．その後で，独立判断に対する
推論器の健全性，完全性，主要性と，動的意味論に対する型安全性を証明する．

双方向型付けとは，式自身から周囲の要求を適用する前の型を求めるsynthesisと，既知の要求型
として式を使えるかを調べるcheckingを分ける方法である．暗黙のmatcher変換はcheckingにだけ
置き，synthesisの型を複数の異なる最外型構成子へ分岐させない．

旧実装は外部の比較対象であり，新体系の定義，証明，buildへ依存させない．旧`SourceTyping`，
trace，validator，terminal audit，旧推論器，互換層を再実装しない．後方互換性は要件ではなく，
各段階で新仕様に合わせて構文とAPIを直接更新する．

## 設計上の不変条件

1. `Typing`は関係的制約生成，宣言的飽和，制約を満たす代入だけから定義する．実行可能な
   `generate`，`unify`，`infer`を定義に含めない．
2. matcher producerをslot要求へ合わせる変換は，外側の構文，context，signatureから得た要求に
   基づいてのみ選ぶ．型を付けるためだけにslot構造を推測しない．
3. 同じblockのchecking要求は，同じhard制約の解で一括して分類する．特殊変換または最後まで
   保留される制約を解いた結果は，siblingの分類へ戻さない．特殊変換になり得ないと確定した
   通常の型等式だけは一斉にhard制約へ移し，次のhard制約解決の回で全要求へ反映してよい．
4. source構文から生成したすべてのchecking要求について，最終代入の下で変換が存在するか，
   通常の型等式としてhard制約へ移されたことを証明する．この全件追跡をcoverageと呼ぶ．
5. 新しく割り当てる通常の型変数とcapability変数は，それぞれ開始時のsupply以上，終了時の
   supply未満に置き，context由来の変数と区別する．
6. 同じsourceから生成した制約blockについて，fresh変数名の有限な付け替えと
   hard／pending worklistの置換は受理を変えない．source AST自体の並べ替えは，
   位置の意味が変わるため一般定理にしない．

hard制約とは，暗黙変換の選択に依存せず必ず満たす型等式である．飽和とは，後続のどの代入でも
特殊なmatcher変換になり得ないchecking要求を通常の型等式へ一斉に移し，再びhard制約を解く操作を，
それ以上移せなくなるまで繰り返すことである．この昇格で得た通常の型等式は次の回の分類に
影響してよいが，特殊変換や最後まで保留された制約を解いた結果は分類へ戻さない．

adequacyは，実行可能な評価器の成功結果を関係的評価でも導出できる性質である．progressは，
型が付いた未完了状態が一歩進むか正常な不一致になる性質である．no-stuckは，規則の適用不能を
表す`stuck`へ到達しない性質である．

## 段階と完了条件

| 段階 | 状態 | 完了条件の要約 |
|---|---|---|
| M0 | done | 最小構文のraw synthesis，局所checking，tuple of matchersの主要性 |
| M1 | done | lambda/applicationを含む独立`Typing`と公開`infer`の健全性・完全性・主要性，制約処理順序不変性，順序境界回帰 |
| M2 | partial | bound-index scheme，`letE`，value block一般化，M2全構文に対する公開推論の健全性，吸収的closureの有限support内への局所性，source生成変数の由来と割当区間，`let`境界のsupply安定性は実装済み．`letE`を含まない断片では完全性・受理同値・決定可能性・主要性・有限な変数名変更による一意性も証明済み．一般の`letE`に対する完全性と主要性は未証明 |
| M3 | partial | 4種類の宣言名，5 primitive，`Ty.data`／`Cap.con`，Bool/List constructor scheme，primitive scheme，List pattern scheme，有限signatureと整合性検査は実装済み．source接続は未実装 |
| M4 | not-started | pattern，`matchAll`，matcher literal，`fix`，pattern functionの静的メタ理論 |
| M5 | not-started | 評価，matching，adequacy，型保存，progress，no-stuck |

### M0：独立した基礎

M0は，型，二種類の変数への同時代入，`var`，整数，`something`，tupleのraw synthesis，
明示された要求型へのcheckingを定義する．`(something, something)`はrawにはproduct of
matchersだけをsynthesizeし，外からmatcherまたはslotの要求型が与えられた場合だけ変換する．

`RootChecks`は要求型の由来を証明しない局所関係であり，source acceptanceではない．M0の完了は
`Regression.pair_principal`などで検証済みである．

### M1：順序に依存しない制約block

M1はlambdaとapplicationを追加し，一つのblockからhard制約，保留中のchecking要求，raw結果型を
純粋に生成する．現時点で次を実装済みである．

- `GenerationRelation`による実行可能生成器と関係的生成の同値
- `GenerationFreshness`によるsupply単調性と生成変数の範囲
- 二種類の変数を扱い，入力だけから必ず停止する`unify`の健全性，完全性，最も一般的な解
- `Saturation`による宣言的な一括昇格と，`SaturationProcedure`のsoundness
- 抽象solverの完全性を仮定した`SaturationProcedureCompleteness`
- 最も一般的な解の選び方に依存しない昇格結果と飽和終点の一意性
- `Permutation`による制約順序の基本不変性と，`SaturationRenaming`によるhard／pendingの
  両worklistを含む飽和の不変性
- `SourcePermutation`によるfresh型変数の有限な付け替え，生成済みのsibling blockの並べ替え，
  制約と解の輸送
- terminal auditや実行器を含まない`Typing`
- 生成されたすべてのchecking要求に対する`DeclarativeCoverage`
- 抽象solverに対する`inferUsing_sound`と`inferUsing_complete`
- `unify`を使う公開`infer`と，M1断片に対する健全性`Inference.infer_success_typing`
- M1断片に対する完全性`Typing.infer_isSome`，受理同値`Inference.typable_iff_infer_isSome`，
  受理可能性を計算で判定する`Inference.typableDecidable`
- 公開`infer`結果の主要性`Inference.infer_principal`と，成功結果を主要な型付けとしてまとめる
  `Inference.infer_success_principalTyping`
- 二つの主要な代表型が互いに代入から得られることを示す`PrincipalTyping.mutualInstances`
- 二つの主要な代表型が，通常の型変数とcapability変数の有限な出現集合上で双方向に
  逆となる変数名の付け替えだけ異なることを示す`PrincipalTyping.finiteRenaming_unique`
- 通常等式へ昇格したchecking要求が，どの後続代入の下でも特殊なmatcher変換には
  ならないことを示す`promoteUnder_equation_no_special_after`
- 特殊変換が選ばれるとき，要求型の最外にmatcherまたはslotが既に明示されていることを示す
  `Resolution.special_expected_head`
- fresh変数名のhard／pending worklistの管理的な違いがblock受理を変えないことを示す
  `Generated.AlphaEq.blockAccepts_iff`

M1の一般的な順序非依存性は，source ASTを任意に並べ替える性質ではない．同じsourceから生成した
制約blockについて，fresh変数名の有限な付け替えとhard／pending worklistの置換が受理を変えない
ことを意味する．tuple位置を変えた境界programは，公開`infer`の正確な結果と，独立した
`Typing`またはその不存在まで個別に検証済みである．

| program | M1で固定する結果 | 現状 |
|---|---|---|
| `M1Examples.useFirst` | `acceptedType`で受理する | `infer_useFirst_exact`と`useFirst_typing`で検証済み |
| `M1Examples.applicationFirst` | sibling順序を変えても同じ`acceptedType`で受理する | `infer_applicationFirst_exact`，`applicationFirst_typing`，`accepted_orders_same_target`で検証済み |
| `M1Examples.singletonFirst` | 共有lambda domainへmatcherとproduct matcherの非互換な要求が生じ，拒否する | `infer_singletonFirst_none`と`singletonFirst_not_typable`で検証済み |
| `M1Examples.pairFirst` | 上記の順序を変えても拒否する | `infer_pairFirst_none`と`pairFirst_not_typable`で検証済み |
| `Regression.pair` | raw product型が主要である | `infer_pair_exact_raw_product`と`pair_raw_product_typing`，公開`infer`の一般主要性で検証済み |

実装済みの主要moduleは`Unification.lean`，`UnificationCorrectness.lean`，
`UnificationTermination.lean`，`Inference.lean`，`InferenceCompleteness.lean`，
`InferenceExactness.lean`，`Principality.lean`，`GenerationRenaming.lean`，
`SaturationRenaming.lean`，`BlockOrderInvariance.lean`，`M1BoundaryRegression.lean`である．

### M2：schemeと一般化

M2では量化変数を持たない型（monotype）だけのM1 `Context`とは別に，schemeを要素とする
`Source.Context`を定義し，M2のsource構文へ`letE`を追加した．schemeの量化変数は自然数位置で表し，
well-scopednessを構造体に保持する．これにより，束縛変数名を変更するalpha同値をschemeの公開等式へ
持ち込まず，自由変数への恒等代入と代入の合成を通常の等式として扱える．この表現は束縛変数名に
関してcanonicalであるが，未使用binderを許すため，scheme全体の一意な標準形ではない．
`Source.Context`内の自由変数は固定された仮定ではなく，推論中の未知変数として最終代入で
具体化され得る．scheme内部で位置により束縛される量化変数とは区別する．

`letE`は右辺value blockを完全に閉じてから一般化するfull-cut方式を採用する．右辺のhard制約と
保留checking要求を主要かつ吸収的な代入で解き，その代入を周囲のcontextへ適用してから右辺型を
一般化する．吸収的とは，任意の後続解の前にその主要代入をもう一度適用しても後続解が変わらない
性質である．右辺の未解決要求はbodyへ渡さない．周囲の自由変数に対する右辺代入の効果だけを
`Context.interfaceEquations`という有限な型等式列として親blockへ戻す．この閉じた境界は仕様上の
選択であり，bodyから右辺へ要求を逆流させて受理範囲を広げる方式は現段階では採らない．

現時点で次を実装し，kernelで検査している．

- `Scheme`のbound-index表現，well-scopedness，自由変数への代入，instantiate，generalize，freshness
- executableなsource elaborationと独立した`Elaborates`関係，および実行結果から関係的導出を得るsoundness
- `PrincipalBlockClosure.Absorbing`と，公開`Source.infer`の成功から`Source.PrincipalTyping`および
  `Source.Typing`を得るsoundness
- closureの局所性，すなわち生成blockの有限support外を変更せず，support内の変数の代入像にも
  support外の変数を導入しない性質が吸収性から従うこと
- source elaborationが生成する各変数は入力context由来か，開始supply以上かつ終了supply未満の
  半開区間で割り当てられた変数であること
- 局所性と生成変数の由来から，`let`で閉じたcontextの初期supplyはvalueの終了supply以下となり，
  body開始時のjoinがvalueの終了supplyへ簡約できること
- contextの有限な境界を特徴付ける`solves_interfaceEquations_iff`と，そのcontext代入輸送
- 二種類の変数の全単射な名前変更と一般化対象リストの対応を仮定すると，一般化が代入と可換になる輸送補題
- 異なる主要block closureの代入が相互にfactorすること，結果型とcontextの双方向輸送，
  scheme具体化が一方向の代入に沿って保存されること
- 実際に割り当てた有限なfresh区間を別のsupplyへ合わせる変数名変更と，source elaboration，生成済みblock，
  block受理を二種類の変数名変更に沿って運ぶ補題
- closureの自由変数上の有限な対応を大域的な変数名変更へ拡張し，閉じたcontext，結果型，一般化schemeを
  文字どおり一致させる補題
- hard制約列が同じ解集合を持つときの飽和とblock受理の輸送，および型変数・capability変数の
  どちらについても，保留checking要求を含む一般のblockにfreshな別名等式（新しい補助変数を
  既存変数と等しいとする制約）を追加・除去しても受理が変わらないこと
- 左右のblockがそれぞれ有限な別名等式列と，hard制約の順序・向き・自明式だけの違いを経て
  共通のblockへ戻る場合の受理同値
- `letE`を含まない断片について，公開`Source.infer`の完全性，受理同値，受理可能性の決定可能性，
  返却型の主要性，二つの主要型の有限な変数名変更による一意性
- 一般の`letE`に対する完全性を，公開推論と同じfreshness条件の下で関係的elaborationの
  受理可能な代表を実行可能elaborationの受理可能な代表へ運ぶ条件
  `WellFormedElaborationAcceptanceComplete`へ還元した条件付き定理
- 多相identityと論文P1-L09の明示的`let`について，公開推論の正確な結果と`Source.Typing`
- full-cut境界でbody要求を右辺へ戻さない例について，公開推論が`none`を返すこと

最後の負例は実行可能推論の境界を固定するが，`Source.Typing`の不存在はまだ証明していない．
また，一般の`letE`を含むsource elaboration全体の完全性はまだ与えていない．別名等式を含む
一般の保留checkingと飽和の輸送，closureの局所性，生成変数の由来，`let`境界のsupply安定性は
証明済みである．同じ生成blockを閉じる任意の二つの吸収的closureからは，閉じたcontext，結果型，
一般化schemeの正確な対応と，interface差の有限な別名等式分解，その別名端点のsupport上の新鮮さまで
自動構成できる．well-formed supplyより後を固定する名前変更によるnested body輸送も証明済みである．
異なるvalue生成blockを比較する場合も，名前変更後の`let`全体についてtarget，hard制約，保留checkingを
同時に対応させ，rootの受理同値とtargetの相互代入関係まで証明済みである．残る核心は，周囲の制約blockが
移動対象の変数と別名等式の新しい端点を使わないことを，source生成のfresh区間から入れ子ごとに導くことである．
一般の主要性にはさらに，入れ子`letE`で異なる主要closureを選んでも
最終結果型が互いに代入で得られるという整合性が必要である．この整合性から一般の主要型の有限な
変数名変更による一意性が従う条件付き定理は用意済みである．正確には，この残件を
公開推論が使うfreshness条件を明示した
`WellFormedElaborationPrincipalityComplete`として切り出し，そこから受理完全性，受理同値，
決定可能性，公開推論の主要性，主要型の有限な変数名変更による一意性まで証明しているが，
条件そのものは未証明である．任意の開始supplyではcontextの自由変数とfresh変数が衝突し得る．
等式の向きを反転する手続きも正当な吸収的solverであること，候補となる二つの局所結果が相互instanceで
ないこと，開始supplyがwell-formedでないことを独立に検証しているため，公開目標はwell-formed supplyに
限定する．これらを一つの完全なelaboration導出へ接続していないので，この障害module単独では
任意supply版の完全性条件の否定までは主張しない．
また，異なるlet closureから得る生成済みblock全体が一つの
大域的な変数名変更だけで一致するという主張も，自明式と別名等式の差を持つclosed反例により偽である．
残る証明は，scope外から観測できない局所変数と有限な別名等式による比較として定式化する．

schemeからmonotypeを作る操作をinstantiate（具体化），自由な変数をschemeの量化変数にする操作を
generalize（一般化）と呼ぶ．実装moduleは`UnificationSupport.lean`，
`AbsorbingSupportRange.lean`，`GeneratedSupport.lean`，`ResolutionSupport.lean`，
`BlockClosureSupport.lean`，`Scheme.lean`，`SchemeTransport.lean`，
`GeneralizationTransport.lean`，`ContextInterface.lean`，`ContextInterfaceRegression.lean`，
`BlockClosure.lean`，`AbsorbingUnification.lean`，
`AbsorbingBlockClosure.lean`，`BlockClosureTransport.lean`，`Source/Syntax.lean`，
`HardWorklistEquivalence.lean`，`FreshAliasElimination.lean`，`FreshAliasSaturation.lean`，
`FreshAliasSequence.lean`，`Source/Elaboration.lean`，
`Source/ElaborationTransport.lean`，`Source/ElaborationRenaming.lean`，
`Source/InterfaceClosureTransport.lean`，`Source/FreshIntervalRenaming.lean`，
`Source/FinitePartialRenaming.lean`，`Source/AlignmentComposition.lean`，
`Source/GeneratedAcceptanceTransport.lean`，`Source/ClosureSupportRenaming.lean`，
`Source/LocalizedClosure.lean`，`Source/SupplyWellFormed.lean`，
`Source/SchemeSupportBounds.lean`，`Source/GeneratedSupportBounds.lean`，
`Source/ContextInterfaceSupport.lean`，`Source/LetSupplyStability.lean`，
`Source/InterfaceAliasCounterexample.lean`，`Source/GlobalRenamingCounterexample.lean`，
`Source/UnwellFormedSupplyPrincipalityCounterexample.lean`，
`Source/InterfaceAliasDecomposition.lean`，`Source/InterfaceAliasFreshness.lean`，
`Source/ScopedGeneratedEquivalence.lean`，`Source/ScopedElaborationComposition.lean`，
`Source/RecursiveLetInvariant.lean`，`Source/CrossGeneratedLetNormalization.lean`，
`Source/ElaborationCompleteness.lean`，
`Source/Principality.lean`，`Source/ConditionalPrincipality.lean`，`Source/M2Regression.lean`である．
論文listing P1-L09の`let`例は，
静的な公開推論結果と`Source.Typing`まで検証済みである．このlistingは評価結果を示す例ではないため，
M5の実行回帰の対象外である．

### M3：data，primitive，signature

M3ではdata constructorとpattern constructorを別のsignature項目として定義する．signatureは
source構文の外から与えられる型要求の表である．List，Boolなどのdata型，constructor，および
論文例に必要な整数演算，list append，`member`，`deleteFirst`，`map`を追加する．primitiveは
言語処理系が直接実装する基本操作である．名前だけで信頼せず，型とM5の実行意味を同じ一覧で
追跡できる形にする．

最初の基盤として，`Names.lean`で`DataFormer`，`DataCtor`，`PatternFormer`，`PatternCtor`を
別々の名前型にし，同じ綴りを安全に別namespaceで使えることを固定した．`Primitive.lean`では論文で
必要な`add`，`append`，`member`，`deleteFirst`，`map`だけを有限に列挙した．型には引数付きdata適用
`Ty.data`と，引数付きpattern capability適用`Cap.con`を追加し，代入，scheme，単一化とその健全性・完全性・
停止性，有限support，変数名変更まで同じ構造を扱うようにした．同名・同引数数なら引数を分解して単一化し，
名前または引数数が違えば拒否する．Bool/List constructorと5 primitiveには閉じたschemeを与えた．Listの
`nil`，`cons`，`join` pattern schemeは一つのelement capabilityを共有し，result targetとresult capabilityの
former・引数数を有限signatureの宣言と照合する．primitiveの表は名前ごとのcanonical schemeとの一致も検査する．
source構文とelaboration，実行意味はまだM3/M5の完了条件に数えない．

実装moduleは`DataTypes.lean`，`Signature.lean`，`Constructors.lean`，`Primitives.lean`，
`PatternDeclarations.lean`，`M3DeclarationsRegression.lean`である．論文listing P1-L03のpattern declarationと，
multiset matcherのclause headerに必要なsignatureは検証済みである．次にconstructor／primitive／ifを
source elaborationへ接続する．

### M4：patternとmatcher

M4ではpattern，`matchAll`，matcher literal，直接自己再帰の`fix`，pattern functionを追加する．
patternの左から右の変数束縛，value pattern内の式の型付け，pattern constructorが要求する
capabilityとtarget，matcher producerからslotへの一方向のcheckingを独立規則として定義する．
matcher literalのclauseはmatcherを構成する分岐であり，holeは次のmatcherへ処理を委譲する
pattern位置である．

DESIGNの旧版ではpattern functionをM4の一覧に明記していなかったが，論文のP1/P2回帰をM0--M5に
収めるため，M4の正式な対象とする．pattern functionの引数付きprogramについて，旧実装の拒否を
仕様として継承しない．新`Typing`で受理または拒否を判定し，拒否の場合は宣言的な非導出を示す．

予定moduleは`PatternSyntax.lean`，`PatternTyping.lean`，`MatcherTyping.lean`，
`MatchAllTyping.lean`，`PatternFunctions.lean`，`M4EgisonRegression.lean`である．M4完了時には
論文listingの全静的正例について公開`infer`と`Typing`を，静的負例について`Typing`の不存在を
検証する．

### M5：動的意味論と型安全性

M5ではvalue，環境，pattern binding，matching atomとmatching state，関係的評価`Eval`，fuel付き
評価器`evalFuel`を定義する．fuelは再帰の深さを制限する自然数であり，fuel切れと，適用できる
規則がない`stuck`を区別する．
matching atomは，一つのpatternを一つのmatcherで一つの値へ照合する途中課題であり，matching
stateは複数の途中課題と既に得た束縛をまとめた実行状態である．

実行可能評価の成功から関係的評価を得るadequacy，関係的評価から十分大きいfuelでの成功を得る
完全性，型保存，局所progress，matching結果の型整合性，任意fuelでのno-stuckを証明する．
一般の停止性や，幅優先探索の完全性はM5の型安全性の完了条件に含めない．

予定moduleは`Values.lean`，`Evaluation.lean`，`Matching.lean`，`EvalFuel.lean`，
`EvaluationAdequacy.lean`，`RuntimeTyping.lean`，`CoreSafety.lean`，`NoStuck.lean`である．

## 論文の番号付き結果を証明する順序

論文の番号付き結果5.1--5.8は，旧定理をそのまま移植せず，次の新しい依存順で証明する．

| 順序 | 目標 | 必要な基盤 | 予定module／theorem |
|---|---|---|---|
| 1 | M1断片の受理健全性5.1 | 関係的生成，単一化，飽和，coverage | `Inference.lean`／`Inference.infer_success_typing` |
| 2 | M1断片の受理完全性5.2 | 実行可能生成の完全性，solver完全性，飽和手続きの完全性 | `InferenceCompleteness.lean`／`Typing.infer_isSome` |
| 3 | 受理同値5.3 | 1と2 | `InferenceExactness.lean`／`Inference.typable_iff_infer_isSome` |
| 4 | 主要な代表型の一意性5.4と主要性5.5 | 最も一般的な解，飽和一意性，変数名の付け替え | `RenamingUniqueness.lean`／`PrincipalTyping.finiteRenaming_unique`，`Principality.lean`／`Inference.infer_principal` |
| 5 | M2--M4への静的定理の拡張 | 各構文の関係的生成と実行可能生成の同値 | 各段階のgeneration／typing module |
| 6 | 静的型付けから実行時型付けへの橋5.6 | M5のruntime typing | `RuntimeTyping.lean`／`Typing.toRuntimeTyping` |
| 7 | 条件付きcore safety 5.7 | 評価とmatchingの型保存，局所progress | `CoreSafety.lean`／`Typing.coreSafety` |
| 8 | no-stuck 5.8 | adequacy，fuel帰納法，5.6 | `NoStuck.lean`／`Typing.neverStuck`，`Inference.infer_neverStuck` |

5.1--5.5の対応結果はM1断片について証明済みである．5.4は，二つの主要な代表型が
通常の型変数とcapability変数の有限な出現集合上で双方向に逆となる変数名の付け替えだけ異なることとして
定式化している．これらをM2--M4で増えた構文へ拡張し，論文が扱う全構文に対する
定理が揃った時点だけ最終的な`done`を付ける．5.6は新体系に推論状態がないため，
状態消去ではなく静的型付けから実行時型付けへの構造的な変換となる．
一般の`Typing`結果には主要型の具体例も含まれるため，5.4相当はすべての`Typing`結果を互いに
renamingとする主張ではなく，主要性を満たす代表型どうしの一意性として定式化する．

## Egison回帰の配置

READMEの一貫確認ロードマップを，静的段階と動的段階に分けて実装する．動的回帰は対応する
静的program定義をimportし，同じfixtureを再利用する．fixtureとは，回帰で共有するprogram，
signature，期待型，期待値の組である．

| 機能 | 静的回帰 | 動的回帰 |
|---|---|---|
| 非線形pattern | `M4NonLinearPatternRegression.lean` | `M5NonLinearPatternExecution.lean` |
| 基本multiset | `M4MultisetRegression.lean` | `M5MultisetExecution.lean` |
| 一般再帰multiset | `M4GeneralMultisetRegression.lean` | `M5GeneralMultisetExecution.lean` |
| pattern function | `M4PatternFunctionRegression.lean` | `M5PatternFunctionExecution.lean` |
| 三機能の合成 | `M4CompositionRegression.lean` | `M5CompositionExecution.lean` |

正例ごとに`*_infer_success`，`*_typing`，`*_eval_exact`，`*_eval_relational`，
`*_never_stuck`を揃える．静的負例は`*_not_typable`を先に証明し，5.1の健全性を使って
`*_infer_rejected`を導く．正常な不一致は`*_typing`と`*_eval_exact`の両方を持ち，期待値を
空の結果列とする．

## Multiset matcherの実装境界

READMEに列挙した7 clauseを，一つの巨大な実行primitiveとして先に追加しない．

1. M3でList data，pattern declaration，各clauseが使うprimitiveの型を定義する．
2. M4で7 clauseをsource matcher literalとして型付けし，clause順序とholeの要求型を検証する．
3. M5で同じ定義を評価し，nil，head-only，value-cons，general cons，join，whole-value，catch-allの
   具体例を個別に固定する．
4. 性能のために専用primitiveへ置き換える場合は，source定義と同じ結果列を返す対応定理を先に
   証明する．

分岐は値ではなく入力中の出現位置で区別する．`join`は末尾の分割を再帰的に列挙し，各段階で
現在の要素を右側へ置く全結果を，左側へ置く全結果より先に返す．この順序を実装都合で変更する
場合は，READMEの期待結果，論文，回帰を同じ変更で更新する．

## 論文code listingの追跡

READMEの`P1-L01`--`P1-L15`を，論文1の全code listingを漏れなく追跡する一覧（inventory）とする．論文sourceの
`lstlisting`出現順をIDへ対応させる．旧リポジトリのprogramをimportせず，各例を新構文で
`Paper1Programs.lean`へ記述する．機能別回帰で証明した結果を`Paper1Inventory.lean`から
まとめて参照できるようにする．

追跡は次の五段階で行う．

1. source構文で表現できる．
2. 静的正例は`Typing`と公開`infer`成功，静的負例は`Typing`不存在を持つ．
3. 実行例は正確な`evalFuel`等式を持つ．
4. adequacyにより関係的`Eval`へ接続する．
5. 型付きclosed programは任意fuelでno-stuckを持つ．

各listingの性質に不要な段階は「対象外」と明記する．例えばpattern declarationだけのP1-L03は
動的評価を要求しない．一方，正常なmatch failureのP1-L14は全五段階を要求する．論文listingの
追加，削除，期待結果の変更は，README inventoryと`Paper1Inventory.lean`の同時更新を必須とする．

P1-L08は特に注意が必要である．旧論文はsource順により片方を拒否するが，新M1の目標は
`M1Examples.useFirst`と`applicationFirst`の両方を受理することである．この結果は
`M1BoundaryRegression`で証明済みであり，READMEで`done`とする．旧論文のlistingと説明は，
論文を新仕様に合わせる段階で両順序受理へ更新する．

## terminal auditを除いたと主張する条件

M1断片で`Typing`を定義しただけでは，論文全体からterminal auditを除けたとは主張しない．
次のすべてを追加公理なしで証明した後に限り，公開仕様から除けたと記載する．

- M0--M4の全source構文に対する独立した`Typing`
- 公開`infer`の健全性，完全性，受理同値，主要性
- M5の静的型付けから実行時型付けへの橋，型保存，progress，no-stuck
- READMEの論文定理対応表とcode listing inventoryの完了

旧実装のaudit済み結果や実行回帰は比較資料であり，この条件を満たす証明の代用にはならない．
