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
| M1 | lambda，application，順序に依存しない制約block，宣言的受理，推論 | partial | 関係的制約生成，freshness，必ず停止する`unify`，宣言的飽和，audit非依存の`Typing`，公開`infer`の健全性・完全性・受理同値・主要性，昇格した通常等式が後で特殊変換に変わらずslot構造を推測しないことまで実装済みである．主要な代表型どうしの有限な変数名の付け替えもM1断片で証明済みである．fresh変数の付け替えを含む一般のsource順序不変性が未完了である |
| M2 | 多相型を表すscheme，`let`，value blockの一般化 | not-started | schemeと`let`はsource構文に存在しない |
| M3 | data constructor，pattern constructor，primitive，signature | not-started | data型，constructor，primitive，signatureは未定義である |
| M4 | pattern，`matchAll`，matcher literal，`fix`，pattern function | not-started | patternとmatcher固有のsource構文は未定義である |
| M5 | 動的意味論，実行可能評価器，型安全性 | not-started | value，評価関係，fuel付き評価器，非停止状態の不在は未定義である |

M1の`Typing`は，実行可能な生成器，単一化手続き，`infer`，terminal auditを定義に含まない．
実行側では，必ず停止する`unify`について健全性，完全性，最も一般的な解を返す性質を証明し，
これを使う公開`infer`を定義した．M1断片については，公開`infer`の健全性，完全性，受理同値，
受理可能性の決定可能性，返却型の主要性を証明済みである．特殊変換が選ばれるときは，要求型の
最外にmatcherまたはslotが既に現れていることを`Resolution.special_expected_head`で証明している．
M1全体は，fresh変数名の付け替えを含む一般のsource順序不変性が未完了なので`partial`とする．

## 論文の番号付き結果5.1--5.8との対応目標

対象は`type-pm-paper/type-pm-paper1.pdf`の第5節である．5.3は定理ではなく系であるが，
論文中の番号順に含める．新体系では旧`SourceTyping`を使わず，独立した`Typing`をsource
programの受理判断とする．予定名は実装開始前にも参照できる安定した目標名であり，実装時に
変更する場合はこの表も同時に更新する．
fuelは，評価器が再帰的な計算を進められる回数を制限する自然数である．

| 番号 | 論文の結果 | 新体系での対応目標 | 現状 | module／theorem |
|---|---|---|---|---|
| 5.1 | Acceptance soundness | 公開`infer`が返した型に`Typing`導出が存在する | partial：M1断片では`Inference.infer_success_typing`を証明済み．M2--M4の構文への拡張が未完了である | `TypePM/Inference.lean`／`Inference.infer_success_typing` |
| 5.2 | Acceptance completeness | `Typing`が存在するprogramを公開`infer`が必ず受理する | partial：M1断片では`Typing.infer_isSome`を証明済み．M2--M4の構文への拡張が未完了である | `TypePM/InferenceCompleteness.lean`／`Typing.infer_isSome` |
| 5.3 | Acceptance equivalence and annotation-freeness | `Typing`の存在と公開`infer`の成功が同値であり，受理を計算で判定できる | partial：M1断片では受理同値と`Inference.typableDecidable`を証明済み．M2--M4の構文への拡張が未完了である | `TypePM/InferenceExactness.lean`／`Inference.typable_iff_infer_isSome`，`Inference.typableDecidable` |
| 5.4 | Target uniqueness modulo renaming | 同じprogramに対する二つの**主要な代表型**が，残った型変数の付け替えを除いて一致する | partial：M1断片では，通常の型変数とcapability変数の有限な出現集合上で双方向に逆となる付け替えを`PrincipalTyping.finiteRenaming_unique`で証明済み．M2--M4の構文への拡張が未完了である | `TypePM/RenamingUniqueness.lean`／`PrincipalTyping.finiteRenaming_unique` |
| 5.5 | Principality of the returned type | 公開`infer`の返す型が，すべての`Typing`結果の最も一般的な型である | partial：M1断片では`Inference.infer_principal`と`Inference.infer_success_principalTyping`を証明済み．M2--M4の構文への拡張が未完了である | `TypePM/Principality.lean`／`Inference.infer_principal` |
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
M1の境界例を除いてすべて`not-started`である．15個のlisting環境には，正負の対を分けると
19個の独立したprogramまたは宣言が含まれる．一つの行に複数のprogramがある場合も，各々を
別の回帰として検証する．

| ID | 掲載内容 | 新体系で固定する結果 | 段階 | 状態 | 予定回帰theorem |
|---|---|---|---|---|---|
| P1-L01 | listとmultisetによる`$x :: $xs` | listは先頭だけ，multisetは三つの選択を正確な順で返す | M3--M5 | not-started | `MultisetExecution.list_and_multiset_cons_exact` |
| P1-L02 | `$x :: #(x + 1) :: _` | `[1,2,5,6]`から`[1,5]`を返す | M3--M5 | not-started | `NonLinearPatternExecution.successor_pairs_exact` |
| P1-L03 | `inductive pattern [a]`宣言 | `[]`，`::`，`++`のpattern signatureを受理する | M3 | not-started | `PatternDeclaration.list_pattern_wellFormed` |
| P1-L04 | 7 clauseの`multiset`定義 | 定義が型を持ち，各clauseが上表の意味を持つ | M3--M5 | not-started | `GeneralMultiset.multiset_definition_typing`と7 clause回帰 |
| P1-L05 | 直接のmultiset `matchAll` | 三要素の`cons`結果を返し，全一貫確認を通る | M3--M5 | not-started | `MultisetExecution.cons_three_end_to_end` |
| P1-L06 | `unconsWith m target` | matcher要求をslotとして持つ主要型を推論する | M4 | not-started | `MatcherDemand.unconsWith_infer_principal` |
| P1-L07 | `unconsWith`の正負二呼出し | `multiset something`は受理し，bare `something`は宣言的に拒否する | M4 | not-started | `MatcherDemand.unconsWith_multiset_accepted`，`unconsWith_something_not_typable` |
| P1-L08 | 共有lambda domainの二順序 | **新仕様では両順序を受理する**．旧論文の片方拒否は更新対象である | M1 | done：両順序が同じ型で受理される実行結果と`Typing`導出をkernel proofで固定済み | `M1BoundaryRegression.infer_useFirst_exact`，`infer_applicationFirst_exact`，`accepted_orders_same_target` |
| P1-L09 | `let`で順序を明示した回避例 | M2でも受理する．M1の両順序受理後は必須の回避策ではない | M2 | not-started | `M2Boundary.let_ordered_typable` |
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
