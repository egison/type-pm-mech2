# type-pm-mech2

`type-pm-mech2`は，Type-PMのsource programに直接型を与える判断を，推論終了後の
再検査（terminal audit）や推論履歴に依存しない形で定義し直すLean 4プロジェクトである．
capabilityは，matcherが入力値のどの形を観察するかを表す型情報である．
matcher producerは実際のmatcher値の型であり，matcher slotは使用箇所がmatcherへ課す要求型で
ある．

旧実装は別リポジトリ[`type-pm-mech`](../type-pm-mech/)に保存する．比較が必要な場合は
両リポジトリを別々に参照，実行する．旧推論器，旧`SourceTyping`，互換層，旧仕様専用の
回帰をこのリポジトリへコピーせず，新体系の依存関係にも含めない．旧実装で証明済みで
あることは，新体系の項目を`done`にする根拠にはしない．

## 開発段階の状態

状態は次の三つで記録する．`done`はその段階の完了条件をすべてLeanで検証済み，
`partial`は必要な定義または補題の一部だけを検証済み，`not-started`は段階固有の実装を
まだ開始していないことを表す．

solverは制約を満たす代入を計算する手続きである．freshnessは，新しく割り当てた型変数が
既存の変数と重ならない性質である．
raw synthesisとは，周囲の要求型や暗黙変換を適用する前に，式自身から型を求める判断である．
主要性とは，その型から代入によって他のすべての型付け結果を得られる性質である．制約blockとは，
同じ変数の有効範囲で生じる制約をまとめて生成し，一括して解く単位である．hard制約は，
暗黙変換の選択に依存せず満たす必要がある型等式である．

| 段階 | 内容 | 状態 | 現在の根拠と不足 |
|---|---|---|---|
| M0 | 型，二種類の変数への代入，raw synthesis，局所checking | done | tuple of matchersのraw主要性と明示された要求型への変換まで検証済みである |
| M1 | lambda，application，順序に依存しない制約block，宣言的受理，推論 | done | 独立した`Typing`，必ず停止する`unify`，公開`infer`の健全性・完全性・受理同値・主要性，主要型の有限な変数名の付け替え，slot構造を推測しない局所不変条件，fresh変数名とhard／pending worklistの管理的な順序変更に対するblock受理不変性，4つの境界回帰を検証済みである |
| M2 | 多相型を表すscheme，`let`，value blockの一般化 | partial | bound-index scheme（量化変数を名前でなく位置で表すscheme），`letE`，閉じたvalue blockの一般化，M2全構文に対する公開`Source.infer`の健全性，正例2件とfull-cut境界の実行可能な拒否を検証済みである．さらに，吸収的なclosureの有限support内への局所性，source生成変数の由来と割当区間，`let`で閉じたcontextのsupplyとbody開始joinの安定性を証明済みである．`letE`を含まない断片では完全性・受理同値・決定可能性・主要性・主要型の有限な変数名変更による一意性も検証済みである．一般の`letE`に対する完全性と主要性は未証明である |
| M3 | data constructor，pattern constructor，primitive，signature | partial | 宣言名，`Ty.data`／`Cap.con`，Bool/Listとprimitiveのscheme，Listのpattern scheme，有限signatureの整合性検査に加え，sourceのconstructor／primitive／`ifE`，signature付きelaborationとその関係的健全性を実装済みである．論文listing全体の静的回帰はM4型付け完成後に残る |
| M4 | pattern，`matchAll`，matcher literal，`fix`，pattern function | partial | pattern function名とfrozen signature，検査済みのsource本体をfrozen interfaceとruntime表へ対応させる境界，private binderを持たないinline断片の全source構文上の展開，matcher clause headerのpattern pattern／data pattern，clause構造と直接の相互再帰構文，user patternと単一`matchAll`節，Paper 1の派生surface構文`match`（単一結果を返すsource順の複数arm），単項・単相の直接自己再帰`fixE` checkpointを実装済みである．派生`match`は最後のarmが構造的に必ず一致することを検査する．論文の7-clause `multiset`本体も省略なしのsource ASTとして固定した．matcher-root再帰を含む統合M4 elaborationと，一般のprivate bindingを持つpattern function実行は未定義である |
| M5 | 動的意味論，実行可能評価器，型安全性 | partial | multiset分解，具体的matcher clause dispatch，順序付き深さ優先探索，一般のruntime value，`Expr.matchAll`と派生surface `Expr.matchFirst`を含むcall-by-value関係`Eval`とfuel付き`evalFuel`を実装済みである．`matchFirst`はtargetとmatcherを一度ずつ評価し，各armで`matchAll`と同じ探索を行い，最初に結果を持つarmの先頭binding groupだけでbodyを評価する．source順，重複branch，`timeout`／`stuck`を保存し，実行成功の関係的健全性，有限導出の完全性，fuel単調性も両形式について検証済みである．検査済みinline pattern functionはsource展開後に同じ評価器で実行する．閉じた整数と再帰的tupleについては，実行時型付け，型保存，任意fuelでのno-stuckまで証明済みである．closure，primitive，matcherと探索状態，一般pattern functionへの型安全性拡張は未完了である |

M1の`Typing`は，実行可能な生成器，単一化手続き，`infer`，terminal auditを定義に含まない．
実行側では，必ず停止する`unify`について健全性，完全性，最も一般的な解を返す性質を証明し，
これを使う公開`infer`を定義した．M1断片については，公開`infer`の健全性，完全性，受理同値，
受理可能性の決定可能性，返却型の主要性を証明済みである．特殊変換が選ばれるときは，要求型の
最外にmatcherまたはslotが既に現れていることを`Resolution.special_expected_head`で証明している．
`Generated.AlphaEq.blockAccepts_iff`は，fresh変数名，hard制約列，保留checking列が管理的に異なる
alpha同値な生成済み制約blockの受理可能性が同値であることを証明する．同じsourceの第二の生成導出へは
`TypingDerivation.transportAlphaEq`で型付け証拠も輸送できる．これはsource ASTの任意の
並べ替えではない．tuple成分の並べ替えは値とproduct型の位置も変えるため，特定の境界programは
`M1BoundaryRegression`で個別に結果を固定する．

M2では，量化された通常の型変数とcapability変数を自然数位置で表すbound-index schemeを追加した．
これは束縛変数名に関してcanonical（名前の選び方に依存しない）だが，未使用binderを許すため，
scheme全体の一意な標準形ではない．well-scopedness（束縛位置が量化範囲内にある性質）は
`Scheme`の構成要件であり，自由変数への恒等代入は文字どおり同じschemeを返す．`letE`は右辺の
制約blockを完全に閉じてから一般化するfull-cut方式である．この境界では右辺の未解決要求をbodyへ
流さず，周囲のcontextへの影響だけを有限な型等式として親blockへ返す．公開`Source.infer`の成功から，
実行手続きと独立した`Source.Typing`を得る健全性を証明済みである．多相identity，論文P1-L09の
明示的`let`は`infer`の正確な結果と`Typing`を検証済みであり，bodyから右辺へ要求を逆流させる例は
full-cut境界で`infer = none`となることを検証済みである．この負例について`Typing`の不存在までは，
受理完全性が未証明であるため現時点では主張しない．

`Source.Context`内の自由変数は固定された仮定ではなく，推論中の未知変数であり，最終代入で
具体化され得る．これはscheme内部で位置により束縛される量化変数とは別である．

closureの局所性とは，生成blockに現れない変数を代入が変更せず，生成blockに現れる変数の
代入像にもその有限support外の変数が現れない性質である．吸収性からこの局所性が従い，公開手続きが
返すclosureにも成立することを証明した．またsource elaborationが生成する各変数は，入力context由来か，
開始supply以上かつ終了supply未満の半開区間で新しく割り当てられた変数である．この由来と局所性により，
`let`のvalueを閉じた後のcontextの初期supplyはvalueの終了supply以下であり，body開始時の防御的な
joinはvalueの終了supplyそのものに簡約できる．

同じvalue生成blockを閉じる二つの吸収的closureについては，閉じたcontext，value結果型，一般化schemeを
一つの有限な変数名変更で対応させ，interface制約の差を左右それぞれの有限な別名等式列と共通制約へ
自動分解するところまで証明済みである．各別名の新しい端点が観測可能な有限supportの外にあり，既存端点が
support内にあることも自動導出する．共通interface制約とbodyを合わせたblock全体がその新しい端点を使わないなら，
保留checkingを含むblockの受理同値を得られる．また，well-formed supplyより後の名前を固定する変数名変更なら，nested `letE`を含むbody elaboration
全体を同じ開始・終了supplyのまま輸送できる．異なるvalue生成blockを比較する場合も，名前変更後の左右について
interfaceとbodyを合わせた`let`全体の結果型，hard制約，保留checkingを同時に対応させ，rootでの受理同値と
結果型の相互代入関係まで証明済みである．残る条件は，周囲の制約blockが移動対象の変数を共有しないことと，
有限な別名等式の新しい端点を周囲のblockが使わないことを，source生成変数の由来から各入れ子位置で導くことである．
子blockだけを名前変更すると，周囲が移動対象を共有する場合には受理が変わり得ることも反例で固定した．
変数名変更が有限な`hidden`集合の外を固定するなら，名前変更と任意の`hidden`を使わない親blockへの差し込みが
可換であり，子blockの受理を親の文脈でも保てることを証明した．また，後続bodyのcontextに由来する変数が
先行valueの開始supplyより前にあるなら，source生成変数の由来からそのbodyがvalue区間の`hidden`名を使わない
ことも導出できる．一方，未来のfresh名だけを固定する条件は過去の名前交換を禁止せず，共通hard制約だけの
証拠は保留checkingに現れる別名端点を記録しないため，この二つの弱い条件だけでは親blockへ持ち上げられない．
これら二つの不足はそれぞれkernel proofによる反例で固定した．さらに，well-formedな開始supplyを持つ
実際のsource `let`導出と二つの吸収的closureを構成し，closure結果を合わせる名前変更が継承された
context変数を動かすため，`hidden`の外を固定する上記の十分条件を満たせないことも証明した．従って
一般の`let`証明では，子blockの名前変更を単独で親へ持ち上げてはならない．interfaceの別名等式除去と
body比較を先に組み合わせ，完全な`Generated.fromLet` blockどうしの`ScopedGeneratedComparison`を
直接構成する必要がある．この反例の二つの完全な`Generated.fromLet` blockについては，継承変数を
動かす名前変更を使わず，freshな別名端点を各許容frame内で除去する直接比較を証明した．一般の場合に
十分な前提として，二つの終了supplyの一致と，各許容frameを適用した後の完全なblockどうしを有限なfresh別名
等式列で共通blockへ正規化できることを`DirectLetNormalizationHandler`として切り出した．ただし，この前提は
現在の関係的elaborationの任意の二導出については偽である．同じwell-formedなsource `let`の二導出で，closureの
代表名がbodyの保留checkingに現れる例を構成した．fresh別名列はhard制約だけを変更し，保留checkingを文字通り
同じに保つため，この二つの完全blockは空frameですでに共通blockへ正規化できない．この否定も
`not_directLetNormalizationHandler`としてkernel proofで固定した．従って一般のM2完全性には，保留checkingを
名前変更に沿って比較できる，より一般的な直接比較関係が必要である．その最小の置換候補として，有限な
変数名変更を共通blockのhard制約と保留checkingの両方へ同時に適用し，その後にhard制約だけへ許容可能な
別名等式列を加える`RenamingAwareCommonCoreEquivalent`を定義した．この関係がblock受理同値を導くことと，
上記の否定例の二blockが実際にこの関係を持つことを証明済みである．各許容frameでこの関係を構成する
`RenamingAwareDirectGeneratedComparisonCertificate`から既存の`ScopedGeneratedComparison`が従うことも
証明した．しかし，この二つ目の候補も一般のframeでは強すぎる．固定された外側の保留checkingが継承変数を
一度使い，body側が一方では同じ継承変数，もう一方では異なる代表変数を使うframeを構成した．一つの共通blockを
左右の全単射な変数名変更へ写すとき，全単射はこの「同じ名前／異なる名前」という関係を変えられない．frameが
`hidden`を避けることと，このframeで`RenamingAwareCommonCoreEquivalent`が存在しないこと，従って
`RenamingAwareDirectLetNormalizationHandler`が偽であることをkernel proofで固定した．

これら二つの反例を踏まえた最小の正しい境界として，許容frameごとの受理同値を直接持つ
`DirectContextualGeneratedComparisonCertificate`と`DirectContextualLetComparisonHandler`を定義した．
後者が既存の`LetComparisonHandler`と同値であることも証明した．これは構文上の共通blockを不必要に要求しないが，
一般のwell-formedな`let`二導出についての構成そのものは未証明である．従ってM2の次の目標は，interfaceの
別名等式がbodyの保留checkingに現れる代表名の差を意味的に吸収する補題を作り，この最小境界をsource導出の
構造に沿って直接証明することである．

生成済みblockの受理については，元のhard制約を解き，各保留checkingが最終代入後に何らかの変換を持つという
単純な意味だけでは不十分である．productの要素が後の代入でmatcherになる一つの保留checkingを構成し，変換自体は
存在するが，変換の種類を代入前に選ぶ残余等式は解けず，blockが拒否されることをkernel proofで固定した．
そこで，hard制約による変換種類の選択，それ以上の通常等式への移動がないこと，選ばれた各変換の残余等式を
一つの代入が同時に解くことを記録する`StableSemanticSolution`を定義した．これは実行可能な推論手続きを含まない
宣言的な条件であり，`blockAccepts_iff_exists_stableSemanticSolution`で`BlockAccepts`と同値であることを証明した．
hard制約が同じ解集合を持ち，保留checkingが同じなら，この証拠を直接輸送できる．二つのclosure代表が作る
interface制約は，bodyが空でも同じ解集合を持たない場合があるため，この直接輸送だけでは一般の`let`比較にならない．
有限な変数名変更をhard制約と保留checkingへ同時に適用し，freshな別名等式による共通の精密化を持つことが
追加条件である．この条件の下で，異なるclosure代表が作る`Generated.fromLet`間の
`StableSemanticSolution`の存在同値を証明した．一般の許容frameについてこの追加条件自体が強すぎるという
既存の反例は残るため，最終的な不足は引き続きframeごとの意味的な受理同値をsource導出から直接作ることである．

`SchemeTransport`，`GeneralizationTransport`，`ContextInterface`，`BlockClosureTransport`に加えて，
`Source/ElaborationTransport`以下では，実際に割り当てた有限なfresh区間の名前合わせ，source elaborationと
生成済みblockの二種類の変数名変更，異なる主要block closureが作るcontext境界等式を解く性質，closureの有限な
自由変数対応から大域的な変数名変更を作る補題を用意した．hard制約列については，並びや等式の向きではなく
同じ解集合を持つことによる輸送も検証した．別名等式とは，新しい補助変数を既存変数と等しいとする制約である．
型変数とcapability変数のどちらについても，保留checking要求を含む一般のblockへ，そのblockに現れない
補助変数の別名等式を追加または除去しても受理が変わらないことを検証済みである．さらに，左右が
それぞれ有限個の別名等式と，hard制約の順序・向き・自明式だけの違いを経て同じ制約blockへ戻る場合の
受理同値も証明済みである．

これらを用いて，`letE`を含まないsource式について，宣言的`Typing`があれば公開`Source.infer`が成功する
完全性，受理同値，受理可能性の決定可能性，公開推論結果の主要性，二つの主要型が有限な変数名変更だけ異なる
ことを証明済みである．一般の`letE`については，公開推論と同じfreshness条件の下で，関係的elaborationの
受理可能な代表を実行可能elaborationの受理可能な代表へ運ぶ条件
`WellFormedElaborationAcceptanceComplete`まで還元している．closureの局所性，生成変数の
由来，`let`境界のsupply安定性は証明済みだが，これらを任意の二つの右辺closureの有限な別名分解と
共通blockの構成へ接続する完全性証明はまだ完了していない．hard制約だけを変更する共通blockでも，
hard制約と保留checkingを一つの全単射な名前対応で同時に変える共通blockでも，一般のframeは扱えないことが
反例で確定した．次の証明では構文上の共通blockを要求せず，interface等式の解がbodyの保留checkingを
意味的に同一視することを使って，frameごとの受理同値を直接示す必要がある．一般の
主要性にはさらに，入れ子`letE`で異なる主要closureを選んでも結果型が互いに代入で得られるという
最終的な整合性が必要である．この不足は，開始supplyがcontext内の全自由変数より新しいことを
要求する`WellFormedElaborationPrincipalityComplete`という一つの条件へ切り出している．公開推論は
常に`context.initialSupply`から始まるためこの前提を満たす．この条件から受理完全性，受理同値，
決定可能性，公開推論の主要性，主要型の有限な変数名変更による
一意性がすべて従うことは証明済みである．したがってM2全体は引き続き`partial`である．

このfreshness前提を外すと，contextの自由変数と後から割り当てる変数が衝突し得る．その障害を示すため，
等式の向きを反転する手続きも正当な吸収的solverであること，候補となる二つの局所結果が互いに代入で
得られないこと，使用した開始supplyがwell-formedでないことをそれぞれkernel proofとして保存する．
これらを一つの完全なelaboration導出へ接続していないため，このmodule単独では任意supply版の
完全性条件そのものの否定までは主張しない．また，同じclosed programの異なる正しいlet closureから得る生成済み
blockが，全体を一度だけ変数名変更した形で一致するというさらに強い主張も偽である．一方が
非自明な別名等式を持ち，他方が自明式を持つ反例を保存している．したがって一般証明は，大域的な
名前変更ではなく，有限な別名等式とscope外から観測できない局所変数を使う比較として進める．

この基盤を実装するmoduleは`UnificationSupport.lean`，`AbsorbingSupportRange.lean`，
`GeneratedSupport.lean`，`ResolutionSupport.lean`，`BlockClosureSupport.lean`，
`GeneratedSemanticAcceptance.lean`，`GeneratedStableSemanticAcceptance.lean`，
`HardWorklistEquivalence.lean`，`FreshAliasElimination.lean`，
`FreshAliasSaturation.lean`，`FreshAliasSequence.lean`，
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
`Source/GeneratedStableSemanticAcceptance.lean`，
`Source/SourceSafeAlignmentCounterexample.lean`，
`Source/ElaborationCompleteness.lean`，
`Source/Principality.lean`，`Source/ConditionalPrincipality.lean`である．

## M3の宣言基盤

M3の宣言を実装する前段として，data型を作る名前，data値を作るconstructor名，patternの能力を表す
名前，pattern constructor名をLean上でも別々の型にした．たとえばdataの`nil`とpatternの`nil`は
同じ綴りを持てるが，誤って互いのlookupに渡せない．また，論文のmultiset matcherが使う
`add`，`append`，`member`，`deleteFirst`，`map`を有限な`PrimOp`として列挙した．さらに，data型の
引数付き適用`Ty.data`と，patternが提供する能力の引数付き適用`Cap.con`を
追加した．この二つの構造は，二種類の変数への代入，多相scheme，単一化，有限support，変数名変更の
全経路で扱われる．同じ名前で引数数も同じなら各引数を単一化し，名前または引数数が違えば拒否することを
正負6件の回帰で確認した．

BoolとListのdata constructor，`add`，`append`，`member`，`deleteFirst`，`map`，Listのpattern constructor
`nil`，`cons`，`join`には，量化変数を含む正確なschemeを定義した．有限signatureの整合性検査は，名前の
重複がないこと，schemeが閉じていること，data resultとpattern resultの名前・引数数がformer宣言と一致すること，
primitive名とcanonical schemeが一致することを確認する．古い誤ったList capabilityの引数数を持つsignatureを
拒否する負例もkernel proofで固定した．

`Source.Expr`にdata constructor呼出し，primitive呼出し，`ifE`を追加し，公開`Source.infer`と
独立した`Source.Typing`の両方がsignatureを明示的に受け取るようにした．constructorとprimitiveの
引数は通常のapplicationと同じ`Generated.fromApp`制約を左から順に積み重ねる．宣言にない
名，引数数の不一致，引数型の不一致を拒否し，Boolの二つのconstructorとListの`nil`の
正確な公開推論結果，List `cons`，`add`，`ifE`の生成成功，推論成功からの関係的
`Typing`を`Source/M3Regression.lean`で固定した．M5のground-data primitive規則も追加済みだが，
source式の評価規則にはまだ接続していない．

## M4のfrozen signature基盤

pattern function名をほかの宣言名とは別の型にし，M3のsignatureとpattern function interfaceの有限な
リストをまとめる`FrozenSignature`を追加した．pattern function interfaceは名前と`DualScheme`だけを保持し，
整合性条件は名前の重複がないこと，各schemeがclosedであること，bound indexが量化範囲内にあることを要求する．
lookupで得たschemeがこれらの条件を満たすことと，Paper 1のpattern functionを含まないfrozen signatureの
正確なlookupをkernel proofで確認した．この基盤にはpattern function本体を置かず，本体からinterfaceを作る
境界は別の`PatternFunctionDefinition`に置く．そこでは本体の独立した`PatternElaborates`導出，保存schemeとの
引数数・結果dualの一致，runtime表とsource interfaceの双方向対応を要求する．さらに，private binderを持たず，
埋込み引数を宣言順に一度ずつ使うinline実行可能断片を定義した．引数なしの`unit`と，引数をそのまま渡す
`pass`について正確な検査証拠と展開結果をkernel proofで固定し，private binder，value式，重複・逆順の
埋込み引数をこの断片では拒否する．一般のprivate bindingを隔離するruntime matching nodeと，その本体を
検査してfrozen signatureを構成する公開手続きはまだ未実装である．

`PatternFunctionExpansion`は最終的な相互再帰source構文をすべて走査し，このinline断片の
`Pattern.app`を検査済み本体へ置き換える．value pattern，matcher clauseの式，`matchAll`，派生
`matchFirst`の内側も再帰的に展開する．未定義名，引数数の不一致，裸の引数参照，private binderや
重複引数を持つ本体は明示的に失敗する．`Runtime.evalPatternFunctionsFuel`は展開後の式だけを既存の
`evalFuel`へ渡し，成功時健全性，有限な関係的導出からの完全性，fuel単調性を証明する．引数なしの
`unit`と引数をそのまま渡す`pass`を実際の`matchAll`で終端まで評価し，正確な結果をkernel proofで固定した．

matcher clause headerの静的な形だけを表す`PPat`と`DPat`も追加した．pattern patternである`PPat`は，
matcher clauseがpatternのどの部分を次へ委譲し，どの部分を値として取り出すかを表す．data patternである
`DPat`は，matcher実装がdata constructorやtupleを分解するときの形を表す．binderは利用者が指定する名前を
持たず，左から右の位置で番号を割り当てる．この番号が重複しないこと，holeとcaptureの番号を別の種類として
区別できること，captureが最初のholeより前にあること，constructorの引数数がfrozen signatureと一致することを
検査する．multiset matcherの7個のclause headerについて，hole順序と0／1／2個の個数，capture数，shape検査を
kernel proofで固定した．`#$value :: $`は受理し，順序を逆にした`$ :: #$value`は拒否する．このmoduleは
式を含まないheader検査を，sourceのmatcher clause本体とは分離して定義する．

次の構造層として`MatcherClauseShape`を追加した．これは一つの`PPat` header，順序付き`DPat` arm header，
metadata（構文に付随する検査用情報）としてのhole数規約だけを持つ．hole数規約は0個，1個，固定された
`k`個（2個以上）を区別し，実際のheaderのhole数と一致するか検査する．各armのdata binding slotは
`DPat`の左から右の順序と正確に一致し，重複せず，headerのcapture slotとは種類が異なることを証明した．
clause列ではbare holeだけからなるcatch-all headerをちょうど最後に要求する．multiset matcherの7 clauseに
arm headerを付けた構造がこの検査を通ることと，catch-allが途中にある場合，constructor引数数が違う場合，
binding slotが重複する場合，hole数規約が違う場合を拒否することをkernel proofで固定した．

source構文は`Expr`，`Pattern`，`MatcherClause`，`MatcherArm`を一つの相互帰納型として定義した．
`Expr`は既存のM0--M3構文に`fixE`，matcher literal，`matchAll`と派生surface node `matchFirst`を加え，`Pattern`は変数，wildcard，
式を持つvalue pattern，pattern constructor，tuple，namelessなpattern引数参照，pattern function適用を
持つ．matcher clauseは`PPat` header，次のmatcherを計算する式，順序付きarmからなり，各armは`DPat`
headerとbody式を持つ．opaqueな拡張nodeは使わない．実際のclauseから`MatcherClauseShape`への消去では，
hole数規約とdata-variableの順序を構文からcanonicalに導くため，利用者が矛盾するmetadataを与えられない．
全構文に`Repr`と構造的な複雑度を定義し，既存のM0--M3 elaboration・support・freshness・名前変更・`let`
比較の証明が同じ構文上でcompileすることを確認した．`matchFirst`はPaper 1 Appendix Aの`match`を
表す入力側の派生構文であり，formal coreへ新しいprimitiveを追加するものではない．M3までの既存`elaborate`は引き続き`fixE`，
matcher literal，`matchAll`，`matchFirst`を明示的に拒否し，M2--M3の証明境界を変更しない．その上に
`M4Elaboration`を追加し，user patternの実行可能な`elaboratePattern`と独立した関係
`PatternElaborates`，および単一match siteの`elaborateMatchAll`と`MatchAllElaborates`を定義した．
patternはcapabilityとtarget型の組を合成し，binder型をsource順にcontextへ追加する．value patternは
左にあるbinderだけを参照できる．pattern constructorと名前付きpattern functionはfrozen
`DualScheme`をinstantiateし，子patternのtarget型とcapabilityを宣言fieldへ等式制約として接続する．
pattern function適用時に本体を再検査せず，保存済みinterfaceだけを使う．`matchAll`はtarget型と
pattern targetをhard等式で結び，matcher式を`MatcherSlot`へ向けた一方向の保留checkingとして記録し，
pattern binderを前置したcontextでbodyを型付けして，body型のListを返す．実行可能生成から関係的判断への
健全性もkernel proofで確認した．

`M4MatchFirstTyping`はtargetとmatcherを一度ずつ型付けし，各armをsource順に検査する．arm patternは
空のbinding列から始め，pattern targetを共通targetへhard等式で結び，matcherを各patternの
`MatcherSlot`へ一方向にcheckingする．bodyはpattern bindingを前置したcontextで型付けし，最初のbody型を
直接の結果型として，後続body型をすべてそれへ等置するためList層を加えない．空arm列と，最後のpatternが
変数・wildcard・それらだけからなるtupleでないarm列は拒否する．`Expr.tuplePatternLambda`により
`\(hs,ts) -> body`をlambdaと`matchFirst`へ正確に展開できる．実行可能規則はcallbackを受け取る形で，
関係的規則との健全性も証明済みである．

`M4PatternTypingRegression`では，binder後のvalue patternが成功し，binder前の参照が失敗すること，
list tailの`#x`がoccurs checkで拒否されること，value expressionのList／Integer不一致，`something`の
`Any` capabilityがcons patternのList capability要求を満たせないことを分離した回帰で固定した．また，
variable patternを使う`matchAll`の正確な推論結果，matcher-to-slot保留制約，pattern引数参照，frozen
pattern-function interfaceだけを使う適用を確認した．matcher literalと`fixE`を再帰的に型付けし，
同じ公開`infer`へ統合する作業は残る．

`M4MatcherTyping`は，最終的なsourceのmatcher literalとclause本体に対する制約生成を追加する．
pattern-pattern headerからholeとcaptureを左から右に合成し，captureを次matcher式より先にscopeへ入れる．
次matcherはholeが0個なら空tuple，1個ならscalar，2個以上なら同じ要素数のtupleとし，各要素を
対応する`MatcherSlot`へ一方向にcheckingする．data-pattern armのbindingはbody contextの先頭に置き，
bodyにはholeの0／1／複数規約による分解積のList型を要求する．clause順，最後のcatch-all，pattern
constructorの浅い網羅性，data armの網羅性も実行前に検査する．実行可能規則とは別に帰納的な関係を定義し，
実行結果から関係的導出を得る健全性を証明した．

式を再帰的に型付けする合成点は`elaborateMatcherLiteralUsing`であり，式の独立関係を引数に取る
`MatcherLiteralElaboratesUsing`と，callbackの健全性だけを仮定する
`elaborateMatcherLiteralUsing_sound`を公開する．これにより`fixE`，`matchAll`，`matchFirst`を扱う
最終dispatcherを後から結べるが，このcheckpoint自身は埋め込み式にM3 elaboratorを使う．回帰はPaper 1の
7 clauseについて修正済みの外側arm（nilはnil／wild，head・value・generalはvariable，joinはnil／cons，
whole・catchはvariable）と7個すべてのbody構文，静的網羅性を固定する．general-cons，join，whole-valueのbodyは
入れ子の`matchAll`，再帰matcher，tuple-pattern lambda，単一結果matchを含むため，統合dispatcherでの
全7 clause推論は未完了である．

`M4FixTyping`は，単項・単相の`fixE`だけを独立した型付けcheckpointとして追加する．本体contextは
引数，自己，外側contextの順であり，de Bruijn index（最も内側を0とする変数番号）では引数が0，
自己が1である．自己はapplicationの直接のcalleeとしてだけ使え，値として返す，argumentとして渡す，
`letE`で別名にする，内側の`fixE`から外側の自己を参照する形は拒否する．検査は最終的な相互`Source`
構文全体を走査し，lambdaと`letE`のbody，左から右のpattern binder，matcher armのdata binderとcaptureに
応じて自己のindexをずらす．next-matcher式はmatcher定義環境で評価されるため，clause binderによるindexの
ずれはない．正例は実行可能elaboration，関係的`FixElaborates`，solverを通した正確な推論結果，独立した
`FixTyping`へ接続し，bare／alias／higher-order／mutual-styleの負例は`FixTyping`の不存在まで確認した．

`elaborateFixUsing`と`FixElaboratesUsing`は本体のelaborationを引数に取る合成用の規則である．現在検証した
`elaborateFix`はM3 elaboratorを本体に使うため，直接自己使用の検査を通るmatcher literalを本体に置いても
`none`となる．matcher literal側には実行可能・関係的な合成用APIがあるが，再帰的なM4 dispatcherを組み，
その全体の関係的健全性を
証明するまでは，一般multiset matcherやmatcher-root再帰が型付け済みとは主張しない．

## 論文の番号付き結果5.1--5.8との対応目標

対象は`type-pm-paper/type-pm-paper1.pdf`の第5節である．5.3は定理ではなく系であるが，
論文中の番号順に含める．新体系では旧`SourceTyping`を使わず，独立した`Typing`をsource
programの受理判断とする．予定名は実装開始前にも参照できる安定した目標名であり，実装時に
変更する場合はこの表も同時に更新する．
fuelは，評価器が再帰的な計算を進められる回数を制限する自然数である．

| 番号 | 論文の結果 | 新体系での対応目標 | 現状 | module／theorem |
|---|---|---|---|---|
| 5.1 | Acceptance soundness | 公開`infer`が返した型に`Typing`導出が存在する | partial：M1断片に加え，M2のschemeと`letE`，M3のconstructor／primitive／`ifE`を含む`Source.infer`について`Source.Inference.infer_success_typing`を証明済み．M4への拡張が未完了である | `TypePM/Inference.lean`／`Inference.infer_success_typing`，`TypePM/Source/Elaboration.lean`／`Source.Inference.infer_success_typing` |
| 5.2 | Acceptance completeness | `Typing`が存在するprogramを公開`infer`が必ず受理する | partial：M1断片に加え，M2--M3の`letE`を含まない断片で`Source.Typing.infer_isSome_of_letFree`を証明済み．一般の`letE`は，公開推論が満たすfreshness条件を含む`WellFormedElaborationAcceptanceComplete`を仮定した形まで証明済みである | `TypePM/InferenceCompleteness.lean`／`Typing.infer_isSome`，`TypePM/Source/ElaborationCompleteness.lean`／`Source.Typing.infer_isSome_of_letFree`，`TypePM/Source/SupplyWellFormed.lean` |
| 5.3 | Acceptance equivalence and annotation-freeness | `Typing`の存在と公開`infer`の成功が同値であり，受理を計算で判定できる | partial：M1断片に加え，M2--M3の`letE`を含まない断片で受理同値と決定可能性を証明済み．一般の`letE`は`WellFormedElaborationAcceptanceComplete`を仮定した受理同値・決定可能性まで証明済みである | `TypePM/InferenceExactness.lean`／`Inference.typable_iff_infer_isSome`，`Inference.typableDecidable`，`TypePM/Source/ElaborationCompleteness.lean`，`TypePM/Source/SupplyWellFormed.lean` |
| 5.4 | Target uniqueness modulo renaming | 同じprogramに対する二つの**主要な代表型**が，残った型変数の付け替えを除いて一致する | partial：M1断片に加え，M2--M3の`letE`を含まない断片で，通常の型変数とcapability変数の有限な出現集合上の変数名変更による一意性を証明済み．一般の`letE`では`WellFormedElaborationPrincipalityComplete`から同じ結論が従う条件付き定理まで証明済みである | `TypePM/RenamingUniqueness.lean`／`PrincipalTyping.finiteRenaming_unique`，`TypePM/Source/Principality.lean`／`Source.PrincipalTyping.finiteRenamingEq_of_letFree`，`TypePM/Source/ConditionalPrincipality.lean`／`finiteRenamingEq_of_wellFormedElaborationPrincipalityComplete` |
| 5.5 | Principality of the returned type | 公開`infer`の返す型が，すべての`Typing`結果の最も一般的な型である | partial：M1断片に加え，M2--M3の`letE`を含まない断片で`Source.Inference.infer_success_principalResult_of_letFree`を証明済み．一般の`letE`では`WellFormedElaborationPrincipalityComplete`から主要性が従う条件付き定理まで証明済みだが，条件自体が未証明である | `TypePM/Principality.lean`／`Inference.infer_principal`，`TypePM/Source/Principality.lean`／`Source.Inference.infer_success_principalResult_of_letFree`，`TypePM/Source/ConditionalPrincipality.lean`／`infer_success_principalResult_of_wellFormedElaborationPrincipalityComplete` |
| 5.6 | State erasure | 推論状態の消去ではなく，最初から状態を含まない`Typing`を実行時型付けへ写す | partial：閉じた整数と再帰的tupleについて，値・環境・式の構文的な実行時型付けを定義し，`Source.Typing`からの写像を証明した．closure，matcherとその探索状態は未接続である | `TypePM/RuntimeTyping.lean`／`Source.Typing.toRuntimeTyping` |
| 5.7 | Conditional core safety | 型付き評価，matching状態，有限探索が型を保存し，必要な評価が終了した状態は一歩進むか正常に不一致となる | partial：上記の整数・tuple coreで，式と式列の相互保存を証明した．各fuelの結果はtimeoutまたは型付き値である．matching状態と探索の型保存は未定義である | `TypePM/CoreSafety.lean`／`Runtime.RuntimeTyping.coreSafety`，`Source.Typing.coreSafety` |
| 5.8 | No stuck states | 型付きclosed programは，任意のfuelで規則の適用不能を表す`stuck`を返さない | partial：上記の整数・tuple coreで，関係的な`Typing`と公開`infer`成功の両方から，任意のfuelに対するno-stuckを証明した．`matchFirst`の空arm列が`stuck`になる実行時境界も固定し，静的な網羅性検査が必要であることを明示した | `TypePM/NoStuck.lean`／`Source.Typing.neverStuck`，`Source.Inference.infer_neverStuck`，`RuntimeTypingRegression.matchFirst_empty_arms_is_stuck` |

一般の`Typing`結果は，主要な型をさらに具体化した型も含むため，互いに変数名の付け替えだけで
一致するとは限らない．5.4の対応目標は，5.5で特徴付ける主要な代表型どうしに限定する．
5.6は，新体系では旧推論状態を消す定理ではない．独立した静的型付けを，実行時のvalue，環境，
matching状態の型付けへ結ぶ定理として再定式化する．5.7と5.8はM5で初めて完了できる．

`RuntimeTyping`は`evalFuel ≠ stuck`として定義せず，source式とruntime valueの構造を型で索引する
独立な帰納的関係として定義した．現在の完全な証明範囲は，閉じた整数とそれらの再帰的tupleである．
一般形に必要な追加証明は，closureの定義環境と本体の型保存，Paper 1の固定signatureの
primitive schemeとprimitive実行の型保存，matcher clauseの実行時shape保存，atom reducerの全入力処理，matching状態と
探索の保存である．`matchFirst`については，実装済みの評価規則とM4の静的な網羅性検査を
接続し，空arm列や全arm不一致による`stuck`が型付きprogramでは起きないことの証明が残っている．

## Egison機能の一貫確認ロードマップ

ここで一貫確認とは，同じsource programを推論から実行時安全性まで通して確認することである．
正例の完了条件は次の鎖をすべて同じprogramについて証明することである．
adequacyとは，実行可能な評価器が返した結果を，独立に定義した関係的評価でも導出できることを
いう．

```text
public infer succeeds
  -> independent Typing holds
  -> evalFuel returns the intended exact value
  -> adequacy gives a relational Eval derivation
  -> every fuel is proved not stuck
```

静的な負例は`infer = none`だけでは完了とせず，`Typing`が存在しないことも証明する．
正常なmatch failureは静的拒否ではなく，型が付き，評価結果として空の結果列を返し，
`stuck`にならない場合である．

| 優先度 | 機能と必須例 | 主に実装する段階 | 状態 |
|---|---|---|---|
| P0 | 非線形pattern：`pair $x #x`の一致例は1結果，不一致例は正常な空結果を返す | M3で`pair`，M4でpatternと型付け，M5で実行と安全性 | not-started |
| P0 | multiset matcher：実際のListのsingletonを`(1, [])`へ分解し，二要素の有限入力から`(1,2)`と`(2,1)`を順序込みで返す | M3--M5 | not-started |
| P1 | 入力長に依存しない再帰的multiset matcher：空，一要素，三要素，重複，入れ子`cons`，`join`，現在の探索順を確認する | M3，M4のmatcher literalと`fix`，M5 | not-started |
| P1 | pattern function：引数なしの正例を全段階へ接続し，引数展開を含むprogramの型付けと正確な実行を確認する | M2--M5 | partial：検査済みinline断片について，引数なし`unit`と引数を渡す`pass`の全source展開，正確な実行，関係的健全性，有限完全性を確認済み．統合M4公開推論とprivate bindingを持つ一般pattern functionは未完了 |
| P2 | multiset matcher，非線形pattern，pattern functionを同じ`matchAll`で組み合わせ，相互作用を確認する | M2--M5 | not-started |
| 将来 | 幅優先探索がすべての有限なmatching結果を列挙できること | M5の型安全性とは別の追加目標 | not-started |

pattern functionの引数付き例を旧実装が拒否したという事実は，新仕様の拒否条件として引き継がない．
新しい`Typing`で安全に型が付くなら受理し，拒否するなら独立した宣言的理由を証明する．
一般のprogramの停止性，型のないprogramの安全な実行，Egison標準multiset matcherの全機能は
このロードマップの完了条件に含めない．

## Multiset matcherの7 clause

clauseは，matcherを構成する一つの分岐である．catch-allは，それ以前のどの専用clauseにも
限定されない最後の一般分岐である．
値が同じでも出現位置が異なる分岐は統合しない．`join`は末尾の分割を再帰的に列挙し，現在の
要素を右側へ置く全結果を，左側へ置く全結果より先に返す．深さ優先探索とは，一つの分岐を
先へ進めてから次の分岐へ移る探索方法である．幅優先探索は同じ深さの分岐を先に列挙する方法
であり，別の将来課題である．

| clause | 具体的な確認program | 期待結果 | 状態 | 予定回帰theorem |
|---|---|---|---|---|
| `nil` | `matchAll [] as multiset something with [] -> 0`と，対象を`[1]`にした負例 | 空対象は`[0]`，非空対象は`[]` | partial：実際のclauseを通るatomic dispatchは検証済み．`matchAll`全体は未完了 | `Runtime.ClauseDispatchRegression.nil_clause_complete_dispatch_exact`，`MultisetExecution.nil_empty_exact`，`nil_nonempty_is_match_failure` |
| `$ :: _` | `matchAll [1,2,3] as multiset something with $x :: _ -> x` | `[1,2,3]` | partial：atomic dispatchと，単純なhead matcher closureの`matchAll`統合は検証済み．論文のmultiset bodyにる3要素回帰は未完了 | `Runtime.ClauseDispatchRegression.head_only_clause_complete_dispatch_exact`，`Runtime.MatchAllRegression.matcher_closure_head_preserves_duplicate_branches`，`MultisetExecution.head_only_target_order` |
| `#$val :: $` | `#1 :: $xs`を`[1,1,2]`と`[2,3]`へ適用する | `[[1,2]]`と`[]`．最初の出現だけを除く | partial：captureとarmを含むatomic dispatchは検証済み．具体的なbodyとの接続は未完了 | `Runtime.ClauseDispatchRegression.value_cons_clause_complete_dispatch_exact`，`MultisetExecution.value_cons_removes_first`，`value_cons_absent_is_match_failure` |
| `$ :: $` | `$x :: $xs`を`[1,2,3]`へ適用する | `[(1,[2,3]),(2,[1,3]),(3,[1,2])]` | partial：2 holeのbranch構築は検証済み．具体的な選択bodyとの接続は未完了 | `Runtime.ClauseDispatchRegression.general_cons_clause_complete_dispatch_exact`，`MultisetExecution.cons_three_search_order` |
| `$ ++ $` | `$xs ++ $ys`を`[1,2,3]`へ適用する | `([], [1,2,3])`，`([3], [1,2])`，`([2], [1,3])`，`([2,3], [1])`，`([1], [2,3])`，`([1,3], [2])`，`([1,2], [3])`，`([1,2,3], [])` | partial：論文どおりのnil／consの2 armを通るatomic dispatchは両方検証済み．具体的な再帰分割bodyとの接続は未完了 | `Runtime.ClauseDispatchRegression.join_clause_first_arm_dispatch_exact`，`join_clause_second_arm_dispatch_exact`，`MultisetExecution.join_three_split_order` |
| `#$val` | `#[1,2]`をmultiset対象`[2,1]`と`[1,3]`へ適用する | 一つの成功`[()]`と正常な不一致`[]` | partial：0 holeとcaptureを含むatomic dispatchは検証済み．構造的multiset等価性との接続は未完了 | `Runtime.ClauseDispatchRegression.whole_value_clause_complete_dispatch_exact`，`MultisetExecution.value_whole_permutation`，`value_whole_mismatch` |
| catch-all `$` | `matchAll [1,2,3] as multiset something with $xs -> xs` | 対象全体を一度だけ返す`[[1,2,3]]` | partial：atomic dispatchと，head不一致からcatch-allへ進む単純な`matchAll`統合は検証済み．論文のmultiset全clause定義は未完了 | `Runtime.ClauseDispatchRegression.catch_all_clause_complete_dispatch_exact`，`Runtime.MatchAllRegression.matcher_closure_falls_through_to_catch_all`，`MultisetExecution.catch_all_once` |

重複入力については，`$ :: $`で`[1,1,2]`から同じ値を持つ二つの先頭分岐を残すこと，
`$ ++ $`で`[1,1]`から同じ値を持つ二つの中間分割を残すことも検査する．入れ子`cons`は
`[1,2,3]`から異なる二要素を選ぶ6結果を深さ優先順で返すことを検査する．

`Runtime/OrderedChoice.lean`では，完全なmatcher評価器に先立ち，`$ :: $`が使う位置ごとの
要素選択，`$ ++ $`が使う8通りの順序付き分割，`#$val :: $`が使う最初の出現の除去を
実装した．三要素の正確な列挙順と，重複値を持つ別位置の分岐を統合しないことはkernel proofで
固定済みである．さらに，位置を一つ除く関係`RemovesOne`と，入力位置を左右へ割り当てる関係
`Splits`を独立に定義し，実行可能な列挙中のmembershipとこれらの関係が同値であることを双方向に
証明した．最初の等しい値だけを除く関係`DeletesFirst`についても，成功時と不在時の実行結果を
特徴付けた．上表の各clauseは具体的なclause dispatchまで接続したため`partial`とした．ただし，
上表の7 clause用atomic fixtureではbody式の値を評価callbackから供給している．一方，
`Runtime.MatchAllRegression`では実際のsource bodyを持つ単純なhead／catch-all matcher closureを
`evalFuel`から終点まで実行している．論文どおりの7 clause本体すべての回帰が通るまでは`done`としない．

`Runtime/GroundValue.lean`は，整数，data constructor適用，tupleを再帰的に持つ`GroundValue`を
定義する．BoolとListにはcanonicalな構築関数と，全入力に`some`または`none`を返すlist viewを与えた．
この型はclosureとmatcherを意図的に含まず，完全なruntime valueではない．
`Runtime/DataPattern.lean`は，matcher clauseのarmが使う`DPat`をこのground dataへ照合する．
data constructor名とconstructor／tupleの要素数を正確に検査し，variable bindingを左から右の
source順で返す．実行関数とは独立した構造的な関係を定義し，実行成功との双方向対応と，返る
binding数が静的な`DPat.bindingCount`に一致することを証明した．multiset定義で使うnil，cons，
tuple-list，variable，wildcardのarmと，constructor／要素数不一致を個別のkernel proofで固定した．
`Runtime/PatternPattern.lean`は，clause headerの`PPat`を利用者のsource `Pattern`へ照合する
構文上のdispatchを実装する．holeは元のpatternを一度保持し，captureはvalue pattern内部の式を
保持し，constructor fieldは左から右へ処理する．header内のliteralなwildcardはuser patternの
wildcardだけに一致し，構造を持つ後続patternを早い`$ :: _` clauseが飲み込まない．capture式の評価は後続の式評価器へ分離した．
実行関数と独立した関係仕様の双方向対応と，抽出するhole／capture数が静的なcountに一致することを
証明した．multisetの7個のheaderをそれぞれ独立に実行し，nil，head-only，value-cons，general cons，
join，whole-value，catch-allの抽出結果を固定した．これはheader dispatchだけであり，各clauseの
decompositionや`matchAll`全体が動作済みであるとはまだ数えない．
`Runtime/OrderedDispatch.lean`は，clause列とarm列に共通するfirst-success制御を定義する．
通常の不一致`miss`だけが次の候補へ進み，最初の`hit`で停止する．`timeout`と`stuck`は後の候補を
試さずそのまま伝播する．独立した順序付き関係との双方向対応，候補ごとの一歩がstuckしなければ
dispatch全体もstuckしないこと，先の成功を後の成功より優先する正確な順序を証明した．具体的な
clause／arm評価はこの制御へ後続moduleで接続する．
`Runtime/GroundPrimitive.lean`はこの範囲で5個の`PrimOp`を実行し，不正な個数・形の引数を
`stuck`として明示する．`map`だけは将来の関数適用をcallbackとして受け取り，左から右の順序と
`timeout`／`stuck`を保存する．`Runtime/GroundPrimitiveAdequacy.lean`では各操作の独立した関係仕様を
定義し，実行成功とのadequacyとcompletenessを双方向に証明した．append，memberの在／不在，重複を
含むdeleteFirst，map順序，Bool/List encoding，異常引数とcallback失敗はexact regressionで固定済みである．
ただし，これはground fragment単体の仕様であり，後続の一般value上の式評価とは別に監査する．

`Runtime/Values.lean`は，論文の型消去されたruntime valueを直接定義する．function closureは通常／再帰の
区別，定義時環境，bodyを保持する．matcher closureは定義時環境，元のsource順clause列，未試行suffixを
保持し，初期cursorと一clause進めたcursorが常に元の列のsuffixであることを証明した．value pattern用の
構造的比較は整数・data constructor・tupleだけを再帰的に比較し，closure，matcher value，`something`では
同じLean項どうしでも`false`を返す．`GroundValue`の順序を保つ埋込みと部分射影は往復し，埋込みが単射で
あることも証明済みである．
`Runtime/ValueDataPattern.lean`は，先行するground data-pattern照合をこの一般valueへ接続する．
variableとwildcardはclosure，matcher value，`something`を含む任意の値を受け取り，data constructorと
tupleだけが厳密なconstructor名・要素数で構造分解される．実行関数と独立した関係仕様の双方向対応，
静的binding数との一致，closure／matcherを束縛する正例と構造不一致の負例を検証済みである．
`Runtime/ValueShape.lean`はclause bodyと次matcher式が共有するruntime表現を固定する．候補列は
canonicalなList constructorで表し，holeが0個なら空tuple，1個ならscalar，2個以上なら正確な
要素数のtupleとして復号する．候補順を保存し，不正なlist spineやtuple要素数を明示的に拒否する．
`Runtime/MatchingState.lean`は，一のpattern，matcher value，target valueを持つmatching atomと，
順序付き後続atom分岐を定義する．`something`のvariable／wildcard／value pattern，
tupleの同じ要素数での子atom化，product matcherから`something`への1回の委譲を実行する．
実行と独立した関係仕様との双方向対応を証明し，埋め込み式評価が`stuck`しなければ
これらの構文上の還元も`stuck`しないことを証明済みである．pattern functionのatom規則は
後続moduleに残る．
`Runtime/ClauseDispatch.lean`はこれらを論文のA-MATCHER境界へ接続する．pattern-patternのcapture式は
照合を開始した側の環境で左から右へ評価し，選択armのbodyはdata binding，capture値，matcher定義環境を
この順に連結した環境で評価する．次matcher式だけはmatcher定義環境で評価する．headerのpattern-pattern
（patternを対象にするpattern）が不一致の場合だけ次clauseへ進む．headerが一致したclauseでは，全data armが
不一致でも正常な空候補列としてclause選択を確定し，後続clauseへ進まない．選択armが空候補列を返した場合も
同様である．timeoutとstuckの伝播，不正なlist／tuple形，未試行suffixを持つmatcher cursor，branchの
source順を回帰で固定した．実行成功と，実行関数から独立して定義したclause／arm関係の双方向対応も
証明済みである．multisetの7 clauseは，captureをdata patternへ混ぜず，論文に掲載された`$tgt` armと
nil／cons armの個数・順序を保った完全な`MatcherClause`としてatomic dispatchを通る．
この7 clause fixtureのbodyは評価callbackで与えるが，別の統合回帰は実際のsource bodyを持つ
head／catch-all matcher closureを`evalFuel`と関係`Eval`の両方で終点まで確認する．
`reduceMatcherAtom`は同じ`MatchingAtom`を直接受け取り，matcher valueの未試行clause suffixをdispatch
して，共通の`AtomReduction`へ変換する．matcher value以外では正常な`miss`を返すため，built-in規則との
合成順は別moduleで明示できる．
`Runtime/MatchingSearch.lean`は，atom還元の順序付き分岐を「その分岐のworkの後ろに
元の残りworkを続ける」状態列へ変換し，先行の深さ優先探索に接続する．新しいbindingは
型付けの`Pattern.extendContext`と同じ左から右のsource順で追加する．通常の不一致は後続状態0個となり，同じ結果を持つ二つの
位置別分岐は二つの答えとして残る．実行と独立したstate-step関係との対応，全atomを
扱うreducerがstuckしないときの任意fuelでのsearch no-stuckを証明した．
各atomの埋め込み式は`bindings ++ environment`で評価するため，後ろのvalue patternが左側のbinderを
静的型付けと同じindexで参照できることもexact回帰で固定した．
`Runtime/CombinedAtomReducer.lean`は，構文上のatom規則を先に試し，通常の`miss`のときだけ
user-defined matcher規則へ進む合成を定義する．先行のhit，timeout，stuckは後続規則で隠さない．
両方のno-stuckとfallbackの全atom処理から，合成後のreducerとbounded searchのno-stuckを得る．
`Runtime/Evaluation.lean`と`Runtime/EvalFuel.lean`は，通常のcore式に加えて`matchAll`と
派生surface `matchFirst`のcall-by-value意味を定義する．`matchAll`はtarget，matcherの順に評価し，builtin規則を先に試す
atom reducerで深さ優先探索を行い，各binding groupを元の環境の前に置いてbodyを評価する．
関係`Eval`はclause，arm，atom，探索の順序を実行関数と独立な帰納的関係で保持する．
実行成功からの健全性，有限な`Eval`導出から十分なfuelを得る完全性，成功値のfuel単調性を
両形式を含めて検証した．`matchFirst`はtargetとmatcherを一度ずつ評価し，armをsource順に試す．
各armは`searchPatternFuel`により`matchAll`と同じ順序付き探索を行い，結果が空なら次へ進み，
非空なら先頭binding groupだけを選ぶ．この対応は
`evalMatchFirstArmsFuel_orderedMatchAll_firstResult`で定義上の等式として固定し，後続結果が重複を
含んでも並べ替えも重複除去もしない．空arm列まで到達した場合は`stuck`であり，静的elaboratorの
網羅性検査が受理済みprogramからこの場合を除く．tuple-pattern lambdaとwhole-value形式の複数armを
実行回帰で確認した．pattern function atomは未実装で`stuck`を保持する．

## 論文1のcode listing inventory

inventoryとは，論文に掲載したすべてのcode例を漏れなく追跡する一覧である．IDは
`type-pm-paper1.tex`中の`lstlisting`出現順で固定する．M4のsource構文は定義済みだが，型付けとM5の
評価器と型付けの統合はlistingごとに進捗が異なる．実行例はsource定義をそのまま評価する回帰と，独立した
評価関係`Eval`への接続を別々に記録する．15個のlisting環境には，正負の対を分けると
19個の独立したprogramまたは宣言が含まれる．一つの行に複数のprogramがある場合も，各々を
別の回帰として検証する．

| ID | 掲載内容 | 新体系で固定する結果 | 段階 | 状態 | 予定回帰theorem |
|---|---|---|---|---|---|
| P1-L01 | listとmultisetによる`$x :: $xs` | listは先頭だけ，multisetは三つの選択を正確な順で返す | M3--M5 | partial：隠れたruntime primitiveではなくsource matcherとして定義し，shape検査を固定済み．exact 7-clause multisetを評価し，`[1,2,3]`から`(1,[2,3])`，`(2,[1,3])`，`(3,[1,2])`をこの順で得ることと独立した`Eval`導出をkernel proofで検証済み．listing全体の統合型付けは未完了 | `Source.Paper1Programs.listMatcherDefinition`，`list_matcher_clause_shapes_checked`，`Runtime.Paper1ExecutionRegression.multiset_cons_preserves_three_source_order_choices_exact`，`multiset_cons_has_independent_derivation` |
| P1-L02 | `$x :: #(x + 1) :: _` | `[1,2,5,6]`から`[1,5]`を返す | M3--M5 | partial：exact source multiset上の実行結果，独立した`Eval`導出，有限fuelの存在をkernel proofで検証済み．listing全体の統合型付けは未完了 | `Runtime.Paper1ExecutionRegression.successor_pairs_exact`，`successor_pairs_has_independent_derivation`，`successor_pairs_has_finite_fuel` |
| P1-L03 | `inductive pattern [a]`宣言 | `[]`，`::`，`++`のpattern signatureを受理する | M3 | done（宣言）：Listの3 pattern schemeのwell-scopedness，閉性，正確な具体化，Paper 1 signature全体の整合性をkernel proofで検証済み | `Source.M3DeclarationsRegression.list_pattern_wellFormed`，`list_pattern_closed`，`list_cons_dual_instantiation_exact`，`paper1_signature_wellFormed` |
| P1-L04 | 7 clauseの`multiset`定義 | 定義が型を持ち，各clauseが上表の意味を持つ | M3--M5 | partial：7個すべてを実際の`MatcherClause`として保持し，順序・環境・shapeを検証済み．さらに`member`／`deleteFirst`，nested `matchAll`，2本の`map`，tuple-pattern lambda，whole-value `match`を含む論文本体を省略なしのsource ASTとして固定した．このexact定義でcons，join，successor value patternを終端まで評価済みだが，定義全体の統合型付けは未完了 | `Source.Paper1Programs.multisetDefinition`，`multiset_clause_shapes_checked`，`Runtime.Paper1ExecutionRegression` |
| P1-L05 | 直接のmultiset `matchAll` | 三要素の`cons`結果を返し，全一貫確認を通る | M3--M5 | partial：exact 7-clause source multisetを使う`evalFuel`等式と独立した`Eval`導出で，三つの結果とsource順を検証済み．統合型付けと型安全性への接続は未完了 | `Runtime.Paper1ExecutionRegression.multiset_cons_preserves_three_source_order_choices_exact`，`multiset_cons_has_independent_derivation` |
| P1-L06 | `unconsWith m target` | matcher要求をslotとして持つ主要型を推論する | M4 | not-started | `MatcherDemand.unconsWith_infer_principal` |
| P1-L07 | `unconsWith`の正負二呼出し | `multiset something`は受理し，bare `something`は宣言的に拒否する | M4 | not-started | `MatcherDemand.unconsWith_multiset_accepted`，`unconsWith_something_not_typable` |
| P1-L08 | 共有lambda domainの二順序 | **新仕様では両順序を受理する**．旧論文の片方拒否は更新対象である | M1 | done：両順序が同じ型で受理される実行結果と`Typing`導出をkernel proofで固定済み | `M1BoundaryRegression.infer_useFirst_exact`，`infer_applicationFirst_exact`，`accepted_orders_same_target` |
| P1-L09 | `let`で順序を明示した回避例 | M2でも受理する．M1の両順序受理後は必須の回避策ではない | M2 | done（静的）：公開`Source.infer`の正確な成功結果と独立した`Source.Typing`をkernel proofで固定済み．このlistingは評価結果を示す例ではなく，M5の実行回帰の対象外である | `Source.M2Regression.infer_explicitLet_exact`，`Source.M2Regression.explicitLetTyping` |
| P1-L10 | value pattern内部の`x ++ [1]` | `Integer`と`[Integer]`の不一致で宣言的に拒否する | M3--M4 | partial：List／Integerの最小制約をunifierが拒否することを確認済み．listing全体と宣言的非導出は未接続 | `M4PatternTypingRegression.value_expression_int_list_mismatch_rejected` |
| P1-L11 | `$x :: #x` | occurs checkによる無限型を検出し，宣言的に拒否する | M4 | partial：実際のpattern生成と`inferPattern = none`を確認済み．公開式の宣言的非導出は未接続 | `M4PatternTypingRegression.occurs_check_tail_rejected` |
| P1-L12 | `#x :: $x :: _` | 左でまだ束縛されていない`x`を検出し，宣言的に拒否する | M4 | partial：左から右のcontextと`inferPattern = none`を確認済み．公開式の宣言的非導出は未接続 | `M4PatternTypingRegression.value_before_binder_rejected` |
| P1-L13 | `something`でvariable patternと`cons` pattern | variable patternは受理して対象全体を返し，`cons`はcapability不足で拒否する | M4--M5 | partial：variable patternの`inferMatchAll`結果と関係的導出，cons要求が作る不可能なcapability等式を確認済み．実行と公開式の非導出は未接続 | `M4PatternTypingRegression.infer_variable_match_exact`，`something_cons_capability_rejected` |
| P1-L14 | `matchAll 5 as something with #1` | 型が付き，正常な不一致として`[]`を返す | M4--M5 | partial：論文と同じ式を`evalFuel`で終端まで実行し，`stuck`ではなく空listを返すことをkernel proofで固定済み．統合M4型付けは未接続 | `Runtime.MatchAllRegression.paper_integer_value_mismatch_is_empty_not_stuck` |
| P1-L15 | Bool対象とinteger matcher | matcher targetの`Integer`と対象の`Bool`が一致せず，宣言的に拒否する | M3--M4 | not-started | `MatcherDemand.matcher_target_mismatch_not_typable` |

inventoryの状態は，次の規則で更新する．

1. 論文の例を新構文で表しただけでは`done`にしない．
2. 静的正例は公開`infer`の成功と独立した`Typing`の両方を証明する．
3. 静的負例は`Typing`の不存在を証明し，推論健全性から公開`infer`の拒否へ接続する．
4. 実行正例と正常な不一致は，正確な`evalFuel`結果，関係的`Eval`，任意fuelでのno-stuckを証明する．結果の順序と重複も等式に含める．
5. 対応するLean fileが個別にcompileし，公理監査に追加公理が現れない場合だけ`done`へ変更する．
6. 論文のlistingを追加，削除，変更した場合は，同じ変更でinventoryと回帰を更新する．

旧リポジトリの回帰は期待結果を調べる外部資料としてだけ用いる．新しい回帰moduleは新体系の
構文，`Typing`，評価関係だけに依存する．

## 詳細設計

段階ごとの定義，完了条件，予定moduleの依存関係は[DESIGN.md](DESIGN.md)に記載する．

## Build

```sh
lake build
```
