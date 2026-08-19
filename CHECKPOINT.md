# 再開チェックポイント

この文書は，作業を中断した後に，現在の確定範囲と次の着手点を会話履歴なしで確認するための索引である．

## 現在の確定状態

- M2は完了している．一般の入れ子`letE`を含むM2--M3 sourceについて，公開推論の完全性，受理同値，決定可能性，公開推論結果の主要性，主要型の有限な変数名変更による一意性を証明済みである．
- 無条件の証明経路は`TypePM/Source/FullM2Completion.lean`に集約されている．入口は`fullM2CoherenceComplete`と`wellFormedElaborationPrincipalityComplete`であり，公開APIは`Typing.infer_isSome`，`Inference.typable_iff_infer_isSome`，`Inference.typableDecidable`，`Inference.infer_success_principalResult`，`Inference.infer_principalResult`，`PrincipalTyping.finiteRenamingEq`である．
- M2の定義域は`supply.WellFormedFor context`である．公開推論は`context.initialSupply`から開始し，この条件を常に満たす．well-formedでない開始supplyは未完の課題ではなく，仕様上の範囲外である．
- 再帰matcherの型形状をslotからmatcherへ閉じる修正と，next-matcherのcapture位置の修正をmainへ統合済みである．小さいvalue patternと`matchFirst`には，公開`M4.infer`の正確な結果と`M4.Typing`のkernel proofがある．
- 5個のprimitiveとconditionalについて，canonical schemeの具体化結果を固定する補題をmainへ統合済みである．

## 次に着手する作業

次のまとまりは，M2の続きではなくM4の静的型付け回帰である．ここでPaper 1または論文1とは，隣接する
`../type-pm-paper/type-pm-paper1.tex`（生成物は`../type-pm-paper/type-pm-paper1.pdf`）を指す．優先順は次のとおりである．

1. `Paper1Programs.listMatcherDefinition`について，公開`M4.infer`の正確な成功結果と対応する`M4.Typing`をkernel theoremとして追加する．
2. 同じ形式で`Paper1Programs.multisetDefinition`と`closedMultisetDefinition`を固定する．実行確認だけでなく，具体的な推論結果と関係的型付けを証明する．
3. READMEのPaper 1 inventoryにあるP1-L01からP1-L15を順に見直し，統合型付けが通った項目を更新する．特にP1-L07と残りの負例を静的回帰へ接続する．
4. 一般のprivate bindingを持つpattern functionを公開M4推論へ接続する．
5. その後，M5の実行時型付けと型安全性をdata，closure，user-defined matcher clause，一般pattern functionへ拡張する．

最初に読むファイルは次のとおりである．

- `TypePM/Source/M4FixTyping.lean`
- `TypePM/Source/M4RecursiveElaborationRegression.lean`
- `TypePM/Source/Paper1Programs.lean`
- `README.md`のPaper 1 inventory

## ブランチ整理

監査時点の全worktreeはcleanである．mainに未反映だった実質的な変更は，再帰matcher修正とcanonical scheme具体化補題の2件だけであり，どちらもmainへmerge済みである．ほかの作業branchはmainと変更内容が同じか，main上の後続修正に置き換えられているため，再mergeしない．古いbranchとworktreeは履歴確認用に残してあり，作業再開時の統合対象ではない．

## 検証

変更後はリポジトリ直下で次を実行する．

```sh
lake build
git diff --check
```

公理依存の一覧は`TypePM/AxiomAudit.lean`にあり，M2の公開入口はLean標準の`propext`，`Classical.choice`，`Quot.sound`以外の追加公理に依存しない．
