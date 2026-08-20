# 再開チェックポイント

この文書は，作業を中断した後に，現在の確定範囲と次の着手点を会話履歴なしで確認するための索引である．

## 現在の確定状態

- M2は完了している．一般の入れ子`letE`を含むM2--M3 sourceについて，公開推論の完全性，受理同値，決定可能性，公開推論結果の主要性，主要型の有限な変数名変更による一意性を証明済みである．完全性とは，宣言的な型付けがある式を公開推論が取りこぼさない性質である．主要性とは，公開推論が返す型から代入によってほかの型付け結果を得られる性質である．
- 無条件のM2証明経路は`TypePM/Source/FullM2Completion.lean`に集約されている．M2の定義域は`supply.WellFormedFor context`である．これは，新しい変数番号を割り当てる開始位置がcontext内の既存変数と衝突しない条件である．公開推論は`context.initialSupply`から始めるため，この条件を常に満たす．条件を満たさない開始supplyは未完の課題ではなく仕様外である．
- M4では，再帰matcherを含む統合elaborationと小さい公開推論回帰，Paper 1の静的負例6件の非型付けを検証済みである．elaborationとは，source構文から型と制約を生成する処理である．
- M4のsupport provenanceは公開`M4.Elaborates`まで完了した．support provenanceとは，生成結果に現れる各変数が，入力contextにすでにあったか，開始supplyから終了supplyまでに新しく割り当てられたことを示す性質である．`TypePM.Source.M4.Elaborates.supportProvenance`と，supply増加もまとめた`TypePM.Source.M4.supplyAndSupport`を監査一覧へ接続済みである．
- 一般pattern functionでは，本体内だけのprivate bindingを外へ漏らさず，引数patternのbindingだけを返すMNodeを実装済みである．MNodeは，pattern function本体の照合を外側から隔離する実行時nodeである．`Pattern.app`はuser-defined matcherのcatch-all clauseより先にMNodeへ展開される．
- `PatternFunctionDefinitions.Agree`はsource宣言とruntime本体表の双方向対応を表す．具体的には，全runtime本体が保存schemeの標準的な一つの具体化についてsource側の検査証拠を持ち，全source宣言に対応するruntime実装があることを要求する．この証拠だけでは全具体化に対するinterface一致や主要性を主張しない．Paper 2の`pair`定義表はこの条件を満たす．
- `evalCheckedPatternFunctionNodesFuel`は上記の対応証明を必須にして，全`Expr`を再帰評価し，`matchAll`と`matchFirst`でMNode探索を使う公開実行経路である．Paper 2の`pair`と正確な7節source `multiset`を組み合わせた全`matchAll`式は，`[1,2,1,3]`から`[[1,2],[1,2],[1,3],[1,3]]`を順序と重複を保って返す．`matchFirst`の先頭結果と，成功した`matchAll`内部探索について実行可能な一歩関数を使う帰納的な順序付き深さ優先導出も証明済みである．
- M5の直接の実行時型付けは，型付き環境，通常・再帰closure，任意の型付き関数位置を持つapplication，`map`まで型保存とno-stuckを証明済みである．no-stuckとは，型の付いた実行が型の不整合を理由に停止しない性質である．ただしsourceの多相`let`からこの実行時型付けを再構成する橋は未完成である．

## 次に着手する作業

次の作業はM2の続きではない．優先順は次のとおりである．

1. 大きいPaper 1正例について，公開`M4.infer`の正確な結果と対応する`M4.Typing`をLean kernelが確認できる回帰として固定する．ここでPaper 1とは，隣接する`../type-pm-paper/type-pm-paper1.tex`を指す．対象は`Paper1Programs.listMatcherDefinition`，`multisetDefinition`，`closedMultisetDefinition`である．
2. READMEのPaper 1 inventoryを実装と照合し，統合静的型付けまで通った項目を更新する．
3. M4全構文について公開推論の完全性と主要性を証明する．生成変数の由来証明は完成したが，これは完全性・主要性そのものではないため，完了と主張しない．
4. MNode評価器全体に対応する独立な関係的評価を定義し，実行可能評価との対応を証明する．現在ある関係証明は`matchAll`内部の順序付き探索までであり，全式評価の関係証明ではない．
5. 一般pattern functionのMNodeとuser-defined matcher clauseを実行時型付けへ接続し，型保存とno-stuckを証明する．
6. sourceの多相`let`から，すでに任意の型付き関数適用と`map`を扱える実行時型付けへの橋を作る．

最初に読むファイルは次のとおりである．

- `TypePM/Source/M4SupplySupport.lean`
- `TypePM/Source/M4CompletenessArchitecture.lean`
- `TypePM/Source/M4PatternFunctionPairRegression.lean`
- `TypePM/Runtime/PatternFunctionMatching.lean`
- `TypePM/Runtime/PatternFunctionNodeEvaluation.lean`
- `TypePM/Runtime/PatternFunctionNodeEvaluationRegression.lean`
- `TypePM/RuntimeTyping.lean`
- `TypePM/CoreSafety.lean`
- `TypePM/Source/Paper1Programs.lean`
- `README.md`のPaper 1 inventory

## ブランチと作業ツリー

このチェックポイントは，作業ツリーがcleanであることや，過去の作業branchを再mergeすべきことを保証しない．再開時にはまず`git status --short --branch`と`git worktree list`を確認し，mainにすでに入った変更を古いbranchから重ねてmergeしない．未commit変更がある場合は，所有者と内容を確認してから編集する．

## 検証

変更後はリポジトリ直下で次を実行する．

```sh
lake build
git diff --check
```

公理依存の一覧は`TypePM/AxiomAudit.lean`にある．M2の公開入口，M4の公開support provenance，MNodeのchecked公開評価器とPaper 2全式回帰をここで監査する．
