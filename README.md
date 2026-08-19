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
| M3 | data constructor，pattern constructor，primitive，signature | partial | 4種類の宣言名，5 primitive，`Ty.data`／`Cap.con`，Bool/List constructor scheme，5 primitiveのscheme，Listの3 pattern scheme，有限signatureとその整合性検査を実装済みである．sourceのconstructor／primitive／if構文とelaborationは未実装である |
| M4 | pattern，`matchAll`，matcher literal，`fix`，pattern function | not-started | patternとmatcher固有のsource構文は未定義である |
| M5 | 動的意味論，実行可能評価器，型安全性 | not-started | value，評価関係，fuel付き評価器，非停止状態の不在は未定義である |

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
共通blockの構成へ接続する完全性証明はまだ完了していない．一般の
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
`Source/ElaborationCompleteness.lean`，
`Source/Principality.lean`，`Source/ConditionalPrincipality.lean`である．

## M3の宣言基盤

M3の宣言を実装する前段として，data型を作る名前，data値を作るconstructor名，patternの能力を表す
名前，pattern constructor名をLean上でも別々の型にした．たとえばdataの`nil`とpatternの`nil`は
同じ綴りを持てるが，誤って互いのlookupに渡せない．また，論文のmultiset matcherが使う
`add`，`append`，`member`，`deleteFirst`，`map`を有限な`PrimOp`として列挙した．この段階では名前だけを
固定している．さらに，data型の引数付き適用`Ty.data`と，patternが提供する能力の引数付き適用`Cap.con`を
追加した．この二つの構造は，二種類の変数への代入，多相scheme，単一化，有限support，変数名変更の
全経路で扱われる．同じ名前で引数数も同じなら各引数を単一化し，名前または引数数が違えば拒否することを
正負6件の回帰で確認した．

BoolとListのdata constructor，`add`，`append`，`member`，`deleteFirst`，`map`，Listのpattern constructor
`nil`，`cons`，`join`には，量化変数を含む正確なschemeを定義した．有限signatureの整合性検査は，名前の
重複がないこと，schemeが閉じていること，data resultとpattern resultの名前・引数数がformer宣言と一致すること，
primitive名とcanonical schemeが一致することを確認する．古い誤ったList capabilityの引数数を持つsignatureを
拒否する負例もkernel proofで固定した．source構文，elaboration，評価規則は次のM3作業である．

## 論文の番号付き結果5.1--5.8との対応目標

対象は`type-pm-paper/type-pm-paper1.pdf`の第5節である．5.3は定理ではなく系であるが，
論文中の番号順に含める．新体系では旧`SourceTyping`を使わず，独立した`Typing`をsource
programの受理判断とする．予定名は実装開始前にも参照できる安定した目標名であり，実装時に
変更する場合はこの表も同時に更新する．
fuelは，評価器が再帰的な計算を進められる回数を制限する自然数である．

| 番号 | 論文の結果 | 新体系での対応目標 | 現状 | module／theorem |
|---|---|---|---|---|
| 5.1 | Acceptance soundness | 公開`infer`が返した型に`Typing`導出が存在する | partial：M1断片に加え，M2のschemeと`letE`を含む`Source.infer`について`Source.Inference.infer_success_typing`を証明済み．M3--M4への拡張が未完了である | `TypePM/Inference.lean`／`Inference.infer_success_typing`，`TypePM/Source/Elaboration.lean`／`Source.Inference.infer_success_typing` |
| 5.2 | Acceptance completeness | `Typing`が存在するprogramを公開`infer`が必ず受理する | partial：M1断片に加え，M2の`letE`を含まない断片で`Source.Typing.infer_isSome_of_letFree`を証明済み．一般の`letE`は，公開推論が満たすfreshness条件を含む`WellFormedElaborationAcceptanceComplete`を仮定した形まで証明済みである | `TypePM/InferenceCompleteness.lean`／`Typing.infer_isSome`，`TypePM/Source/ElaborationCompleteness.lean`／`Source.Typing.infer_isSome_of_letFree`，`TypePM/Source/SupplyWellFormed.lean` |
| 5.3 | Acceptance equivalence and annotation-freeness | `Typing`の存在と公開`infer`の成功が同値であり，受理を計算で判定できる | partial：M1断片に加え，M2の`letE`を含まない断片で受理同値と決定可能性を証明済み．一般の`letE`は`WellFormedElaborationAcceptanceComplete`を仮定した受理同値・決定可能性まで証明済みである | `TypePM/InferenceExactness.lean`／`Inference.typable_iff_infer_isSome`，`Inference.typableDecidable`，`TypePM/Source/ElaborationCompleteness.lean`，`TypePM/Source/SupplyWellFormed.lean` |
| 5.4 | Target uniqueness modulo renaming | 同じprogramに対する二つの**主要な代表型**が，残った型変数の付け替えを除いて一致する | partial：M1断片に加え，M2の`letE`を含まない断片で，通常の型変数とcapability変数の有限な出現集合上の変数名変更による一意性を証明済み．一般の`letE`では`WellFormedElaborationPrincipalityComplete`から同じ結論が従う条件付き定理まで証明済みである | `TypePM/RenamingUniqueness.lean`／`PrincipalTyping.finiteRenaming_unique`，`TypePM/Source/Principality.lean`／`Source.PrincipalTyping.finiteRenamingEq_of_letFree`，`TypePM/Source/ConditionalPrincipality.lean`／`finiteRenamingEq_of_wellFormedElaborationPrincipalityComplete` |
| 5.5 | Principality of the returned type | 公開`infer`の返す型が，すべての`Typing`結果の最も一般的な型である | partial：M1断片に加え，M2の`letE`を含まない断片で`Source.Inference.infer_success_principalResult_of_letFree`を証明済み．一般の`letE`では`WellFormedElaborationPrincipalityComplete`から主要性が従う条件付き定理まで証明済みだが，条件自体が未証明である | `TypePM/Principality.lean`／`Inference.infer_principal`，`TypePM/Source/Principality.lean`／`Source.Inference.infer_success_principalResult_of_letFree`，`TypePM/Source/ConditionalPrincipality.lean`／`infer_success_principalResult_of_wellFormedElaborationPrincipalityComplete` |
| 5.6 | State erasure | 推論状態の消去ではなく，最初から状態を含まない`Typing`を実行時型付けへ写す | not-started：`Typing`は状態非依存であるが，実行時型付けが未定義である | `TypePM/RuntimeTyping.lean`／`Typing.toRuntimeTyping` |
| 5.7 | Conditional core safety | 型付き評価，matching状態，有限探索が型を保存し，必要な評価が終了した状態は一歩進むか正常に不一致となる | not-started | `TypePM/CoreSafety.lean`／`Typing.coreSafety` |
| 5.8 | No stuck states | 型付きclosed programは，任意のfuelで規則の適用不能を表す`stuck`を返さない | not-started | `TypePM/NoStuck.lean`／`Typing.neverStuck`，`Inference.infer_neverStuck` |

一般の`Typing`結果は，主要な型をさらに具体化した型も含むため，互いに変数名の付け替えだけで
一致するとは限らない．5.4の対応目標は，5.5で特徴付ける主要な代表型どうしに限定する．
5.6は，新体系では旧推論状態を消す定理ではない．独立した静的型付けを，実行時のvalue，環境，
matching状態の型付けへ結ぶ定理として再定式化する．5.7と5.8はM5で初めて完了できる．

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
| P1 | pattern function：引数なしの正例を全段階へ接続し，引数展開を含むprogramの型付けと正確な実行を確認する | M2--M5 | not-started |
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
| `nil` | `matchAll [] as multiset something with [] -> 0`と，対象を`[1]`にした負例 | 空対象は`[0]`，非空対象は`[]` | not-started | `MultisetExecution.nil_empty_exact`，`nil_nonempty_is_match_failure` |
| `$ :: _` | `matchAll [1,2,3] as multiset something with $x :: _ -> x` | `[1,2,3]` | not-started | `MultisetExecution.head_only_target_order` |
| `#$val :: $` | `#1 :: $xs`を`[1,1,2]`と`[2,3]`へ適用する | `[[1,2]]`と`[]`．最初の出現だけを除く | not-started | `MultisetExecution.value_cons_removes_first`，`value_cons_absent_is_match_failure` |
| `$ :: $` | `$x :: $xs`を`[1,2,3]`へ適用する | `[(1,[2,3]),(2,[1,3]),(3,[1,2])]` | not-started | `MultisetExecution.cons_three_search_order` |
| `$ ++ $` | `$xs ++ $ys`を`[1,2,3]`へ適用する | `([], [1,2,3])`，`([3], [1,2])`，`([2], [1,3])`，`([2,3], [1])`，`([1], [2,3])`，`([1,3], [2])`，`([1,2], [3])`，`([1,2,3], [])` | not-started | `MultisetExecution.join_three_split_order` |
| `#$val` | `#[1,2]`をmultiset対象`[2,1]`と`[1,3]`へ適用する | 一つの成功`[()]`と正常な不一致`[]` | not-started | `MultisetExecution.value_whole_permutation`，`value_whole_mismatch` |
| catch-all `$` | `matchAll [1,2,3] as multiset something with $xs -> xs` | 対象全体を一度だけ返す`[[1,2,3]]` | not-started | `MultisetExecution.catch_all_once` |

重複入力については，`$ :: $`で`[1,1,2]`から同じ値を持つ二つの先頭分岐を残すこと，
`$ ++ $`で`[1,1]`から同じ値を持つ二つの中間分割を残すことも検査する．入れ子`cons`は
`[1,2,3]`から異なる二要素を選ぶ6結果を深さ優先順で返すことを検査する．

## 論文1のcode listing inventory

inventoryとは，論文に掲載したすべてのcode例を漏れなく追跡する一覧である．IDは
`type-pm-paper1.tex`中の`lstlisting`出現順で固定する．現在はM4とM5の構文がないため，
M1の境界例とM2の明示的`let`例を除いて`not-started`である．15個のlisting環境には，正負の対を分けると
19個の独立したprogramまたは宣言が含まれる．一つの行に複数のprogramがある場合も，各々を
別の回帰として検証する．

| ID | 掲載内容 | 新体系で固定する結果 | 段階 | 状態 | 予定回帰theorem |
|---|---|---|---|---|---|
| P1-L01 | listとmultisetによる`$x :: $xs` | listは先頭だけ，multisetは三つの選択を正確な順で返す | M3--M5 | not-started | `MultisetExecution.list_and_multiset_cons_exact` |
| P1-L02 | `$x :: #(x + 1) :: _` | `[1,2,5,6]`から`[1,5]`を返す | M3--M5 | not-started | `NonLinearPatternExecution.successor_pairs_exact` |
| P1-L03 | `inductive pattern [a]`宣言 | `[]`，`::`，`++`のpattern signatureを受理する | M3 | done（宣言）：Listの3 pattern schemeのwell-scopedness，閉性，正確な具体化，Paper 1 signature全体の整合性をkernel proofで検証済み | `Source.M3DeclarationsRegression.list_pattern_wellFormed`，`list_pattern_closed`，`list_cons_dual_instantiation_exact`，`paper1_signature_wellFormed` |
| P1-L04 | 7 clauseの`multiset`定義 | 定義が型を持ち，各clauseが上表の意味を持つ | M3--M5 | not-started | `GeneralMultiset.multiset_definition_typing`と7 clause回帰 |
| P1-L05 | 直接のmultiset `matchAll` | 三要素の`cons`結果を返し，全一貫確認を通る | M3--M5 | not-started | `MultisetExecution.cons_three_end_to_end` |
| P1-L06 | `unconsWith m target` | matcher要求をslotとして持つ主要型を推論する | M4 | not-started | `MatcherDemand.unconsWith_infer_principal` |
| P1-L07 | `unconsWith`の正負二呼出し | `multiset something`は受理し，bare `something`は宣言的に拒否する | M4 | not-started | `MatcherDemand.unconsWith_multiset_accepted`，`unconsWith_something_not_typable` |
| P1-L08 | 共有lambda domainの二順序 | **新仕様では両順序を受理する**．旧論文の片方拒否は更新対象である | M1 | done：両順序が同じ型で受理される実行結果と`Typing`導出をkernel proofで固定済み | `M1BoundaryRegression.infer_useFirst_exact`，`infer_applicationFirst_exact`，`accepted_orders_same_target` |
| P1-L09 | `let`で順序を明示した回避例 | M2でも受理する．M1の両順序受理後は必須の回避策ではない | M2 | done（静的）：公開`Source.infer`の正確な成功結果と独立した`Source.Typing`をkernel proofで固定済み．このlistingは評価結果を示す例ではなく，M5の実行回帰の対象外である | `Source.M2Regression.infer_explicitLet_exact`，`Source.M2Regression.explicitLetTyping` |
| P1-L10 | value pattern内部の`x ++ [1]` | `Integer`と`[Integer]`の不一致で宣言的に拒否する | M3--M4 | not-started | `PatternTyping.value_expression_type_mismatch` |
| P1-L11 | `$x :: #x` | occurs checkによる無限型を検出し，宣言的に拒否する | M4 | not-started | `PatternTyping.nonlinear_occurs_check_rejected` |
| P1-L12 | `#x :: $x :: _` | 左でまだ束縛されていない`x`を検出し，宣言的に拒否する | M4 | not-started | `PatternTyping.value_before_binding_rejected` |
| P1-L13 | `something`でvariable patternと`cons` pattern | variable patternは受理して対象全体を返し，`cons`はcapability不足で拒否する | M4--M5 | not-started | `MatcherDemand.something_variable_accepted`，`something_cons_not_typable` |
| P1-L14 | `matchAll 5 as something with #1` | 型が付き，正常な不一致として`[]`を返す | M4--M5 | not-started | `ValuePatternExecution.integer_mismatch_is_empty` |
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
