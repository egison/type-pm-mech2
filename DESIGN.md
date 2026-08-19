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
| M3 | partial | 宣言名，`Ty.data`／`Cap.con`，Bool/Listとprimitiveのscheme，List pattern scheme，有限signatureの整合性検査，constructor／primitive／`ifE`のsource構文とsignature付きelaborationは実装済み．論文listing全体の静的回帰はM4型付け待ち |
| M4 | partial | pattern function名とfrozen signature，matcher headerの静的検査，直接の相互再帰構文，shapeへのcanonicalな消去，user patternと単一`matchAll`節，Paper 1の派生surface `match`，matcher literal/clauseのcallback-parametricな実行可能・関係的型付け，単項・単相の直接自己再帰`fixE` checkpointは実装済み．matcher-root再帰を含む統合M4推論，pattern function本体とfreeze checkerの静的メタ理論は未実装 |
| M5 | partial | multisetの順序付き分解，具体的matcher clause dispatch，matching state/search，`matchAll`と派生surface `matchFirst`を含む全core式の関係的・実行可能評価，5 primitiveの一般value実行，成功時健全性，有限完全性，fuel単調性は実装済み．`matchFirst`はarmをsource順に試し，最初の非空な`matchAll`探索結果の先頭だけを使う．順序と重複branch，`timeout`／`stuck`を保存する．pattern function atom，実行時型付け，型保存，progress，型付けからのno-stuckは未実装 |

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
名前変更が有限な`hidden`集合の外を固定するとき，子blockの名前変更を`hidden`を使わない親blockへ安全に
差し込めること，および後続bodyのcontextに由来する変数が先行valueの開始supplyより前なら，source生成の
由来からbodyがvalue区間の`hidden`名を避けることは証明済みである．ただし，未来のfresh名を固定するだけでは
過去の名前交換を排除できず，共通hard制約だけの証拠からは保留checking内の別名端点を復元できない．この二つの
不足は反例で固定している．さらに，well-formedな開始supplyから得た実際のsource `let`導出と二つの
吸収的closureについても，closure結果を合わせる名前変更が継承context変数を動かすため，`hidden`の外を
固定する十分条件を満たさない例を証明した．従ってこの十分条件を一般のsource帰納法で構成する方針は採用しない．
完全性に残るsource側の仕事は，interfaceの別名等式除去とbody比較を一体化し，子blockだけの名前変更を
中間目標にせず，完全な`Generated.fromLet` blockどうしの`ScopedGeneratedComparison`を直接構成することである．
この修正後の目標は，保留checkingを持たない先のsource由来反例自身について成立することを検証した．しかし，
左右の完全なblockを各許容frame内で有限なfresh別名等式列から同じblockへ正規化する
`DirectLetNormalizationHandler`は，bodyの保留checkingにclosure代表名が現れるsource導出により偽である．
さらに，共通block全体を左右で別々の有限な全単射によって名前変更してからhard別名等式を加える
`RenamingAwareDirectLetNormalizationHandler`も偽である．固定frameが継承変数を観測すると，一方の保留checkingでは
二つの位置が同じ名前になり，もう一方では異なる名前になるため，全単射な名前変更では共通化できない．
この二段階の反例をkernel proofとして固定した．

正しい最小境界は，構文上の共通blockを要求せず，終了supplyの一致と各許容frameでの受理同値だけを持つ
`DirectContextualLetComparisonHandler`である．これは既存の`LetComparisonHandler`と同値であることを証明済みである．
一般のsource帰納法では，interface等式の解がbodyの保留checkingに現れる代表名の差を吸収することを直接使って，
この受理同値を構成する必要がある．この構成は未証明である．
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
`Source/RecursiveLetSupportSafety.lean`，`Source/DirectLetComparison.lean`，
`Source/SourceSafeAlignmentCounterexample.lean`，
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
`Source.Expr`にdata constructor呼出し，primitive呼出し，`ifE`を追加し，有限signatureを実行可能な
elaboration，関係的elaboration，公開`infer`，`Typing`へ明示的に渡す．constructorとprimitiveの
引数処理は，通常のapplicationと同じ`Generated.fromApp`を左から畳み込む`elaborateCall`と
`ElaboratesCall`を共用する．signatureの整合性からlookupしたschemeがclosedであることを得て，
実行成功を独立した関係へ写す．support，freshness，変数名変更，`let`比較の諸定理もこの
第三のcall帰納に拡張した．実行意味はM5で追加する．

実装moduleは`DataTypes.lean`，`Signature.lean`，`Constructors.lean`，`Primitives.lean`，
`PatternDeclarations.lean`，`M3DeclarationsRegression.lean`，`Source/Elaboration.lean`，`Source/M3Regression.lean`である．
論文listing P1-L03のpattern declarationと，multiset matcherのclause headerに必要なsignatureは検証済みである．

### M4：patternとmatcher

M4ではpattern，`matchAll`，matcher literal，直接自己再帰の`fix`，pattern functionを追加する．
最初の基盤として，pattern function名をほかの宣言名と混同できない別の型にし，M3のsignatureへ
pattern function名と`DualScheme`のinterfaceを加える`FrozenSignature`を定義した．その整合性条件は，
基礎signatureの整合性，pattern function名の重複がないこと，各schemeに自由な型変数とcapability変数が
ないこと，bound indexが量化範囲内にあることからなる．pattern function本体を宣言として保持する層と，
本体からinterfaceを作るfreeze checkerはまだ定義しない．

matcher clause本体より先に，headerの静的な形だけを`PPat`と`DPat`として定義する．`PPat`はhole，wildcard，
capture，pattern constructorからなり，`DPat`は変数，wildcard，data constructor，tupleからなる．binder名は
構文に保持せず，左から右の出現位置を連続する自然数で要約する．holeとcaptureの位置は別の種類にし，それぞれの
番号に重複がなく，互いに混同できないことを証明する．captureが最初のholeより後に現れないことを実行可能な
検査で確認し，pattern／data constructorの引数数をfrozen signatureのschemeと照合する．この検査層は
式を参照せず，後から定義する直接のsource構文と分離する．

次のcheckpointでは，このheaderを順序付きdata-pattern arm headerと組み合わせる`MatcherClauseShape`を
定義する．これは実行式を含まない．metadata（構文に付随する検査用情報）として，headerが委譲するholeを
0個，1個，固定された`k`個（2個以上）に分類し，実際のhole数との一致を検査する．各armのbinding slotは
`DPat`から得る左から右の順序と一致しなければならず，重複を許さない．data-variable slotとheaderのcapture slotは
異なる種類として保持するため衝突しない．clause列ではbare holeのcatch-all headerを最後に一つだけ置く．
この検査はclause本体の型付けや実行を仮定せず，それらの健全性を主張しない．

その上に，source ASTとして`Expr`，`Pattern`，`MatcherClause`，`MatcherArm`，`MatchFirstArm`を直接の
相互帰納型で定義した．matcher literalはclause列を，clauseは次のmatcherを作る式とbody式を，value patternは
式を直接保持する．opaqueな拡張nodeは置かない．実際のclauseから式を消した`MatcherClauseShape`への変換は，
hole数規約とarmのbinding順をheaderから導く．構文全体には`Repr`と構造的な複雑度を与えた．
`Expr.matchFirst`はPaper 1 Appendix Aの単一結果`match`を保持する派生surface nodeであり，formal coreの
新しいprimitiveではない．

この構文checkpointはM4型付けの完成を意味しない．既存の実行可能elaborationは`fixE`，matcher literal，
`matchAll`と`matchFirst`に`none`を返し，関係的`Elaborates`にも対応するconstructorを置かない．従って未実装規則が既存の
M0--M3定理を経由して受理されたように見えることはない．`PatternTyping`と`MatcherTyping`の導入時に，この
明示的な未受理を実際の生成規則へ置き換える．

patternの左から右の変数束縛，value pattern内の式の型付け，pattern constructorが要求する
capabilityとtarget，matcher producerからslotへの一方向のcheckingを独立規則として定義する．
matcher literalのclauseはmatcherを構成する分岐であり，holeは次のmatcherへ処理を委譲する
pattern位置である．

`fixE`は単項・単相の直接自己再帰だけを受理する．本体contextは引数，自己，外側contextの順であり，
de Bruijn indexでは引数が0，自己が1である．自己の使用はapplicationの直接のcalleeに限り，bareな値，
argument位置，`letE`による別名，内側の`fixE`が外側の自己を取り込むmutual-styleの形を拒否する．
この構文検査は最終的な`Expr`／`Pattern`／`MatcherClause`／`MatcherArm`全体を相互に走査する．lambdaと
`letE`のbodyでは1，value patternでは左側で生成済みのbinder数，`matchAll` bodyではpattern全体の
binder数，matcher arm bodyではdata binder数とcapture数だけ追跡indexをずらす．next-matcher式は
matcher定義環境で評価するのでclause binderによるずれを入れない．

型生成ではfreshなdomainとcodomainを一つずつ割り当て，自己へ`domain → codomain`を単相schemeとして
置き，本体結果とcodomainをhard等式で接続する．`elaborateFixUsing`／`FixElaboratesUsing`は本体規則を
引数に取る合成点であり，M3規則に特殊化した`elaborateFix`／`FixElaborates`の実行健全性と，solver成功から
独立した`FixTyping`を得る健全性を証明した．ただし現時点の特殊化はmatcher literal本体を拒否する．
matcher literal側の合成点と再帰的dispatcherを結び，対応する関係的soundnessを証明するまで，
matcher-root再帰および一般multiset matcherの静的型付けは未実装である．

派生`match`の型付けは`M4MatchFirstTyping`に分離する．targetとmatcherを一度ずつ合成した後，各arm patternを
空binding列からsource順に合成し，pattern targetと共通targetをhard等式で結ぶ．matcherは各armの
`MatcherSlot`へ一方向にcheckingし，bodyはpattern bindingを前置したcontextで合成する．最初のbody型を
直接の結果型とし，後続body型をすべて等置する．空arm列と，最後に構造的に必ず一致するpatternを持たない
arm列は拒否する．ここで必ず一致するpatternは変数，wildcard，およびそれらだけからなるtupleである．
実行可能・関係的規則はいずれも式elaboratorをcallbackとして受け取り，実行可能規則の関係的健全性を証明した．
`Expr.tuplePatternLambda`はPaper 1のtuple-pattern lambdaをlambdaとこの派生nodeへ展開する．

matcher literalの型付けは`M4MatcherTyping`に分離する．headerのhole/captureとarmのdata bindingを
source順に合成し，0個を空tuple，1個をscalar，2個以上を同じ要素数の積とする規約を次matcher式と
分解結果の両方に使う．各次matcherはholeの`MatcherSlot`へ一方向にcheckingし，arm bodyは分解積の
List型へcheckingする．最後のcatch-all，pattern constructorの浅い網羅性，data armの網羅性を先に検査する．
`MatcherLiteralElaboratesUsing`は式の関係を引数に取る独立判断であり，
`elaborateMatcherLiteralUsing_sound`はcallbackの健全性からmatcher literal全体の関係的導出を構成する．
したがって再帰的dispatcherは`fixE`，`matchAll`，`matchFirst`の規則をこの一つの式関係へ接続できる．
現checkpointの直接入口はM3式だけを使う．Paper 1の7 clauseは正確な外側header/arm，全body構文，静的網羅性を
検証するが，再帰的bodyを含む全体の推論は統合dispatcherまで未完了として残す．

DESIGNの旧版ではpattern functionをM4の一覧に明記していなかったが，論文のP1/P2回帰をM0--M5に
収めるため，M4の正式な対象とする．pattern functionの引数付きprogramについて，旧実装の拒否を
仕様として継承しない．新`Typing`で受理または拒否を判定し，拒否の場合は宣言的な非導出を示す．

実装moduleには`Source/M4Elaboration.lean`，`Source/M4MatcherTyping.lean`，`Source/M4FixTyping.lean`と各回帰を含む．残る予定moduleは
`PatternFunctionDefinition.lean`では，独立したpattern本体の型付け，frozen interfaceとの引数数・結果dualの一致，
runtime本体表との双方向対応を定義した．また，private binderを持たず埋込み引数を宣言順に一度ずつ使う
inline実行可能断片を切り出した．`unit`と`pass`の正例，private binder，value式，重複・逆順引数の負例を
検証済みである．一般のprivate bindingを隔離するruntime nodeは残る．残る予定moduleは
`MatchAllTyping.lean`，一般pattern function実行，`M4EgisonRegression.lean`である．M4完了時には
論文listingの全静的正例について公開`infer`と`Typing`を，静的負例について`Typing`の不存在を
検証する．

### M5：動的意味論と型安全性

M5ではvalue，環境，pattern binding，matching atomとmatching state，関係的評価`Eval`，fuel付き
評価器`evalFuel`を定義する．fuelは再帰の深さを制限する自然数であり，fuel切れと，適用できる
規則がない`stuck`を区別する．
matching atomは，一つのpatternを一つのmatcherで一つの値へ照合する途中課題であり，matching
stateは複数の途中課題と既に得た束縛をまとめた実行状態である．

`Runtime/FuelResult.lean`は，成功`ok`，fuel切れ`timeout`，規則不足`stuck`を互いに異なる
constructorとして定義する．左から右へlistを処理する`traverse`について，成功結果と独立した
点ごとの関係`Traverses`の同値，および各要素がstuckしなければ全体もstuckしないことを証明済みである．
これは後続の式評価とclause body評価で共用する結果型であり，評価規則自体はまだ含まない．

`Runtime/Environment.lean`は，de Bruijn index 0を最新の値とする実行環境をlistとして定義する．
実行可能な`getElem?`と関係的lookup `Lookup`の同値，lookup結果の一意性，先頭への値追加による
indexのずれ，既存環境の末尾への追加に対するlookup保存を証明済みである．

`Runtime/DepthFirstSearch.lean`は，一つの答えを返す状態と，順序付き後続状態へ展開する状態を
区別し，後続状態を残りのworklistの前に置く深さ優先探索を定義する．実行可能な
`depthFirstFuel`の成功から関係的`DepthFirst`を得る健全性，有限な関係導出が十分なfuelで成功する
完全性，fuelを増やしても成功結果が変わらないこと，各状態の一歩が`stuck`しなければ
探索全体も`stuck`しないことを証明する．このmoduleは後続のmatching stateの具体定義に依存しない．

`Runtime/GroundValue.lean`は，整数，data constructor適用，tupleからなる再帰的な閉じた値だけを
扱う．Bool/Listのcanonical constructorとlist view/buildを持つが，closure，matcher，matching stateは
後続の一般runtime valueへ残す．`Runtime/GroundPrimitive.lean`は，`add`，`append`，`member`，
`deleteFirst`，callbackを受け取る`map`をこのground fragment上で実行する．不正引数は`stuck`となり，
`map` callbackの`timeout`と`stuck`は左から右へ伝播する．各操作には実行関数を参照しない関係仕様を
別に定義し，成功についてadequacyとcompletenessを個別および`PrimOp` dispatch全体で証明済みである．
`deleteFirst`の最初の出現だけを除く関係は`Runtime.OrderedChoice`の`DeletesFirst`を再利用する．
これらはprimitive単体のdelta規則であり，完全な`Expr` evaluatorやmatcher evaluatorの主張ではない．

`Runtime/DataPattern.lean`はmatcher clauseのdata-pattern armだけを先に実行可能にする．
`DPat`のvariable，wildcard，data constructor，tupleをground dataへ構造的に照合し，constructor名と
要素数を正確に検査する．binding列は左から右のsource順を保つ．実行関数と独立した関係仕様の
双方向対応，および実行時binding数と静的`DPat.bindingCount`の一致を証明する．これはclause bodyの
評価結果をarmへdispatchする一部分であり，clause bodyやmatcher全体の実行をまだ主張しない．

`Runtime/PatternPattern.lean`はmatcher clause headerの`PPat`と利用者のsource `Pattern`の
構造照合を実装する．holeは入力patternを，captureはvalue pattern内の式を左から右へ抽出し，
constructor mismatchとfield数不一致を明示的な失敗にする．captureされた式はmatcherの保存環境で
後から評価するため，この段階では式を値へ変換しない．独立した関係仕様との双方向対応と静的な
hole／capture数との一致を証明し，multiset matcherの7 headerを個別に実行した．完全なclause
dispatchにはcapture式評価，data arm選択，body評価，decompositionの生成がさらに必要である．

`M4MatcherClauseShapeRegression.lean`と`Runtime/ClauseDispatchRegression.lean`の7節fixtureは，
入れ子の`match`のpatternを外側のmatcher armと混同せず，論文の外側data patternをそのまま保持する．
specialized cons三節のarmはすべて`$tgt`一つ，join節はnil／consの二つであり，captureはpattern-pattern
header側だけに置く．

`Runtime/OrderedDispatch.lean`は，clauseとdata armをsource順に試す共通のfirst-success制御を
定義する．通常の不一致`miss`だけが後続候補へ進み，`hit`は直ちに選択される．fuel切れ`timeout`と
規則不足`stuck`は後続候補で隠さず伝播する．実行関数と独立した順序付き関係の双方向対応，および
候補ごとの一歩がstuckしない場合のdispatch全体のno-stuckを証明する．

`Runtime/Values.lean`は，M4で確定した`Source.Expr`と`Source.MatcherClause`に対する完全なruntime
valueを定義する．data constructorの子，tuple要素，closure環境は通常の`List`でsource順を保ち，
探索分岐の重複除去には利用しない．function closureは通常／再帰のtag，定義時環境，bodyを保持する．
matcher closureは論文どおり定義時環境，元のclause列，未試行suffixを保持する．初期化と一clause進める
操作についてsuffix不変条件を証明した．構造的比較はfirst-order value，すなわち整数・data
constructor・tupleだけで定義し，closure，matcher，`something`では常に失敗する．先行する
`GroundValue`からの順序を保つ埋込み，groundへの部分射影，往復，埋込みの単射も検証済みである．
`Runtime/ValueDataPattern.lean`はdata-pattern arm照合をこの一般valueへ持ち上げる．variableと
wildcardはclosure，matcher value，`something`も受け取る一方，data constructorとtupleだけを
constructor名・要素数が一致するとき構造分解する．実行関数と独立した関係仕様の双方向対応と，
返すbinding数が静的`DPat.bindingCount`に一致することを証明する．
`Runtime/ValueShape.lean`はclauseのhole数に応じたruntime積の規約を定義する．0個は空tuple，
1個はscalar，2個以上は正確な要素数のtupleであり，decomposition全体はcanonicalなList valueで
表す．全入力を`Option`で検査し，候補順を保持した復号と不正形の拒否を回帰で固定する．
`Runtime/MatchingState.lean`は，pattern，matcher value，target valueからなるmatching atomと，
順序付きの後続atom分岐を定義する．`something`のvariable／wildcard／value規則，
tupleの正確な要素数での子atom生成，product matcherから`something`への一回委譲を実行する．
構造的な独立関係との双方向対応と，埋め込み式評価のno-stuckを仮定した局所no-stuckを証明する．
不一致は通常の空分岐または後続dispatchとして扱い，この局所層で`stuck`にしない．
`Runtime/MatchingSearch.lean`はatomのordered branchを具体的なmatching state列へ変換し，
各branchのworkを元の残りworkより先に処理する．pattern bindingは静的`Pattern.extendContext`と同じsource順で末尾へ追加し，
後続branch 0個を正常な不一致とする．`DepthFirstSearch`との接続後もsource順と重複branchを保存する．
独立関係との対応と，全atomを扱う局所reducerのno-stuckから任意fuelの探索no-stuckを得る定理を持つ．
atom reductionに渡す評価環境は`bindings ++ environment`であり，左側のbinderを読む
後続value patternの実行順序を`Pattern.extendContext`と一致させる．
`Runtime/CombinedAtomReducer.lean`は複数のatom規則族の優先順位を固定する．先行側の
`miss`だけがfallbackを許し，hit，timeout，stuckは保存する．fallbackが全atomを扱い，
両方がstuckしなければ，合成reducerとそれを使う全bounded searchがstuckしない．
`Runtime/Evaluation.lean`，`Runtime/EvalFuel.lean`，`Runtime/EvaluationAdequacy.lean`，
`Runtime/EvaluationCompleteness.lean`は，`matchAll`と派生surface `matchFirst`を含む全core式のcall-by-value評価を定義する．
通常closureでは引数をindex 0に置き，再帰closureでは引数をindex 0，自己をindex 1に置く．
一般value上の5 primitive，実行成功のadequacy，有限な関係導出の完全性，成功値のfuel単調性を
検証する．`matchAll`はclause式評価を含むatom還元と深さ優先探索を接続し，
関係`Eval`でもarm，clause，atom，探索の帰納的関係を直接記録する．`matchFirst`はtargetとmatcherを
一度ずつ評価し，各armで同じ順序付き`matchAll`探索を実行する．空結果だけが次armへ進み，最初の
非空結果の先頭binding groupでbodyを評価する．このAppendix Aの展開との対応は実行器の等式と独立な
`EvalMatchFirstArms`関係で固定し，成功時健全性，有限完全性，fuel単調性まで接続した．空arm列は
動的には`stuck`だが，静的な網羅性検査が受理済みprogramでは除外する．pattern function atomは次の依存項目である．

先行する`Runtime/OrderedChoice.lean`は，matchingの選択肢を通常の`List`で保持し，入力位置の
順序と重複を保存する．general-consの一要素選択とjoinの左右分割について，三要素での正確な
順序，重複する値を持つ別位置の分岐数，`2^n`個のjoin分割を証明済みである．これは探索器の
基礎であり，clause dispatchや式評価の実装済みを意味しない．実行可能な二つの列挙について，
位置を一つ除く関係`RemovesOne`，および各位置を左右へ割り当てる関係`Splits`とのmembership同値を
証明済みである．値が現れる最初の位置だけを除く`DeletesFirst`も，実行可能な成功・不在判定と
同値であり，後続matching関係のadequacyに再利用する．

実行可能評価の成功から関係的評価を得るadequacy，関係的評価から十分大きいfuelでの成功を得る
完全性，型保存，局所progress，matching結果の型整合性，任意fuelでのno-stuckを証明する．
一般の停止性や，幅優先探索の完全性はM5の型安全性の完了条件に含めない．

実装済みの一般value／matching基盤moduleは`Values.lean`，`MatchingState.lean`，`MatchingSearch.lean`，`CombinedAtomReducer.lean`である．後続予定moduleは`Evaluation.lean`，`Matching.lean`，`EvalFuel.lean`，
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

P1-L04の7-clause `multiset`は，`member`／`deleteFirst`，nested `matchAll`，source順を保つ2本の
`map`，tuple-pattern lambda，whole-valueの派生`match`を含めて`Source/Paper1Programs.lean`へ
記述する．このASTを静的型付けと動的評価の両方からimportし，短縮したcallback fixtureを定義本体の
代用にしない．

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
