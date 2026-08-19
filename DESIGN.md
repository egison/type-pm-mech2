# 独立した Type-PM 型付けの設計

## 目標

型付け可能性を，実行可能な制約解決手続き（solver）の状態，source 順の履歴，推論終了後の
再検査（terminal audit）に依存しない
帰納的な判断で定義する．その後で，独立判断に対する推論器の健全性・完全性と主要性を
証明する．

**双方向型付け**とは，式自身から周囲の要求を適用する前の型（raw 型）を求める synthesis と，既知の
要求型（expected type）として
式を使えるかを調べる checking を分ける方法である．暗黙の matcher 変換は checking に
だけ置き，synthesis の型を複数の異なる最外型構成子へ分岐させない．

## 段階

### M0: 独立した基礎

必要最小限の構文に対して，型，代入，raw synthesis，checking 変換を定義する．
`(something, something)` は raw には product of matchers だけを synthesize し，外から
matcher または slot の expected 型が明示された場合にだけ checking 変換を使える．

M0 の `RootChecks` は expected 型の由来をまだ証明しないため，source acceptance ではない．
checking 変換も，恒等変換，matcher-to-slot，空でない product of matchers から
matcher／slot への変換に限定する．product of slots などは必要になる段階で追加する．

### M1: 順序に依存しない制約 block

ここで block とは，同じ変数の有効範囲に属する式から制約をまとめて生成し，一括して
解いてから結果を外へ出す単位である．lambda と application を追加し，一つの block から
次を純粋に生成する．

1. coercion の選択に依存しない型等式（確定制約）
2. raw 型と expected 型を後で対応させる保留中の checking 要求（obligation）
3. context，root の expected 型，または構文から直接生じる matcher／slot 要求の根

確定制約を最も一般的に解き，通常の等式にするしかない obligation を確定制約へ移して
再び解く操作（確定制約の飽和）を繰り返した後，全 obligation を同じ解で一度に分類する．一つの obligation の解を
別の obligation の分類根拠にはしない．これにより source 順序への依存と，型を付けるため
だけに slot 構造を推測することを同時に避ける．

M1 の完了条件は，制約生成と solver の正確性，宣言的受理と `infer2` の健全性・完全性，
raw synthesis の主要性，および順序を入れ替えた境界 program の回帰である．

### M2 以降

- M2: scheme，`let`，value block の一般化
- M3: constructor と primitive，および signature 由来の要求
- M4: pattern，`matchAll`，matcher literal，`fix`
- M5: 動的意味論，型安全性，旧実装との差分分類

旧実装の定義は，対応する milestone で意味が確定してから必要なものだけ再実装する．
旧 `SourceTyping`，trace，validator，terminal audit を互換層として持ち込まない．

## terminal audit を除く条件

全構文について独立した型付けを定義し，`infer2` の健全性・完全性と型安全性を追加公理なし
で証明した後に限り，terminal audit を公開仕様から除けたと主張する．M0 はその主張を行わない．
