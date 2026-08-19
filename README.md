# type-pm-mech2

`type-pm-mech2` は，Type-PM の source program に直接型を与える判断を，推論終了後の
再検査（terminal audit）や推論履歴に依存しない形で定義し直す Lean 4 プロジェクトである．既存実装
[`type-pm-mech`](../type-pm-mech/) は比較用の別リポジトリとして扱い，そのソースを
このリポジトリへ一括移植しない．

## 現在の範囲: M0

M0 は，新設計の最小の独立基盤である．capability は matcher が入力値のどの形を
観察するかを表す型情報である．raw synthesis は，周囲から要求される型や暗黙変換を
まだ適用せず，式自身から型を求める判断である．

- capability と型
- 2種類の変数に対する同時代入と基本法則
- `var`，整数，`something`，tuple の raw synthesis
- raw 型を明示された要求型（expected type）として使うための checking 変換．変換の
  推移規則は置かず，必要な合成形を直接定義する
- `(something, something)` の raw product 型に関する主要性

ここでいう**主要性**とは，他のすべての raw synthesis 結果が，一つの代表型への
代入で得られることである．checking 後の matcher／slot 型は raw synthesis 結果には
数えない．

現在の checking 変換は，恒等変換，matcher-to-slot，および空でない product of matchers
から matcher／slot への変換だけを扱う M0 部分系である．

M0 は program 全体の受理判断，制約生成，制約を解く手続き（solver），`infer2`，型安全性，terminal audit の
除去をまだ定義・証明しない．明示された expected 型に対する `RootChecks` は局所的な
補助関係であり，program 全体の受理判断ではない．

## 次の開発段階

M1 では lambda と application を追加し，source 構文・context・明示された root の要求だけに基づく
制約生成，確定制約の
飽和，最も一般的な解，要求型の由来，宣言的受理，`infer2` の健全性・完全性を一つの
まとまりとして実装する．この段階で初めて，兄弟式の順序を変えても受理結果が変わらない
ことと，外部根拠のない matcher slot を推測しないことを source program 上で検証する．

詳しい段階分けは [DESIGN.md](DESIGN.md) に記載する．

## Build

```sh
lake build
```
