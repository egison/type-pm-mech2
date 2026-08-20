# type-pm-mech2

`type-pm-mech2`は，Type-PMのsource programに直接型を与える判断をLean 4で
機械化するプロジェクトである．推論終了後の再検査（terminal audit）や推論器の
実行履歴を型付けの定義へ含めず，独立した関係`Typing`を先に定義する．その上で，
公開推論器の健全性・完全性・主要性と，評価器の型安全性を証明する．

このREADMEは，設計，現在地，完了条件，次の作業をまとめた唯一のロードマップである．
旧`DESIGN.md`の設計判断と，旧`CHECKPOINT.md`の再開情報はここへ統合した．概念を
順に説明する日本語資料は[`tex/type-pm-mech2-guide.pdf`](tex/type-pm-mech2-guide.pdf)
にあるが，進捗についてはこのREADMEとLeanコードを正本とする．

旧実装は別リポジトリ[`type-pm-mech`](../type-pm-mech/)に保存する．旧推論器，旧
`SourceTyping`，互換層，旧仕様専用の回帰をこのリポジトリへコピーしない．旧実装で
証明済みであることは，このロードマップの項目を完了にする根拠にならない．

## 状態の読み方

ロードマップでは次の状態を使う．

| 状態 | 意味 |
|---|---|
| **done** | その行の完了条件をLean kernelが検査済み．公開入口がある項目では公理監査にも登録済み |
| **in progress** | 必要な定義または補題の一部はあるが，行の完了条件をまだ満たさない |
| **not started** | 行に固有の実装をまだ開始していない |
| **design decision** | 単純な証明追加ではなく，対象範囲または表現を先に決める必要がある |
| **out of scope** | 現行の形式体系の仕様として意図的に対象外 |

「構文がある」，「実行例が動く」，「型安全性がある」は別の状態である．正例を完全と
数えるには，その例に必要な範囲で次を個別に確認する．

1. source構文で表現できる．
2. 公開`infer`の結果と独立した`Typing`を持つ．
3. 実行例なら正確な`evalFuel`等式を持つ．
4. 実行成功が独立した関係`Eval`へ接続される．
5. 型付きclosed programなら任意のfuelで`stuck`にならない．

2026年8月20日の更新時点では，`lake build TypePM.AxiomAudit TypePM`が成功している．
監査対象の推移的な公理依存は`propext`，`Classical.choice`，`Quot.sound`だけである．

## 現在地

### 段階別の要約

| 段階 | 対象 | 状態 | 現在地 |
|---|---|---|---|
| M0 | 型，二種類の変数，raw synthesis，局所checking | **done** | tuple of matchersのraw主要性と，明示された要求型への変換まで証明済み |
| M1 | lambda，application，制約block，公開推論 | **done** | 健全性，完全性，受理同値，決定可能性，主要性，主要型の有限な変数名変更による一意性まで証明済み |
| M2 | bound-index scheme，多相`letE`，value block一般化 | **done** | 一般の入れ子`letE`についてcoherence，replay，公開推論の完全性・主要性まで証明済み |
| M3 | data／pattern constructor，primitive，signature，`ifE` | **done** | M3固有の宣言・elaborationと，M2--M3全域の公開定理を証明済み．論文例のM4/M5部分は別に追跡する |
| M4 | pattern，matcher literal，`matchAll`，`matchFirst`，`fixE`，pattern function | **in progress** | 全構文の推論健全性，fuel標準化，fresh renaming，通常構文と`fixE`のcoherence，Paper 1の大規模exact回帰まで完了．全M4 coherenceとreplayが残る |
| M5 | 評価，matching探索，runtime typing，型安全性 | **in progress** | core評価とmatching基盤，条件付き安全性，限定されたsource-to-runtime橋まで完了．一般user matcher，多相`let`，MNode全体の安全性が残る |

M3を`done`とするのは，M3固有のconstructor／primitive／signature基盤とM2--M3の
静的定理が閉じているためである．Paper 1全体の例が未完であることは，M4/M5と後述の
inventoryで追跡する．

### 直近の重要な到達点

- `M4.infer_success_typing`により，全M4構文で公開推論の成功から独立した`M4.Typing`を
  得られる．論文結果5.1の静的健全性は完了している．
- fuelは上向きに単調であり，任意の導出を`expression.complexity + 1`へ正規化できる．
  公開`M4.Elaborates`と標準fuelの関係は`M4.Elaborates.iff_at_complexity`で固定した．
- matcherの静的検査は宣言的な命題で表し，実行可能なBool検査との同値を証明した．
  `Typing`側がBool計算結果を直接仮定する形にはなっていない．
- 全M4構文についてsupply増加，生成変数の由来，fresh-variable renamingを証明した．
- M2--M3部分構文の再利用に加え，子にM4構文を含む通常構文と`fixE`のcoherenceを証明した．
- Paper 1のsource-defined `list`とclosed `multiset`について，公開`M4.infer`の正確な型と
  `M4.Typing`をkernel計算だけで固定した．open `multiset`は空contextで`none`になることを
  正確に証明した．
- 公理監査は表示用の`#print axioms`ではなく，許可集合外の公理があればbuildを失敗させる
  `#assert_allowed_axioms`で実施し，CIでも`lake build`を実行する．

## 用語と証明の流れ

capabilityは，matcherが入力値のどの形を観察できるかを表す型情報である．matcher
producerは実際のmatcher値の型，matcher slotは使用箇所がmatcherへ課す要求型である．

raw synthesisは，周囲の要求を適用する前に式自身の型を合成する処理である．checkingは，
その型を外から与えられた要求型として使用できるかを確認する処理である．matcher producerから
slotへの暗黙変換はcheckingでだけ選ぶ．

制約blockは，同じ変数の有効範囲で生じる制約をまとめて解く単位である．hard制約は暗黙変換の
選択にかかわらず満たす型等式，pending obligationは解が得られてから変換可能性を確認する要求で
ある．saturation（飽和）は，特殊変換になり得ないpending obligationを通常の型等式へ一括して
移し，それ以上移せなくなるまでhard制約を解き直す操作である．

主要性とは，推論器の返す型から代入によってほかのすべての型付け結果を得られる性質である．
coherenceは，同じsourceに対する二つの正しい関係的elaborationが受理と主要結果について一致する
ことを意味する．replayは，関係的elaborationを公開の決定的な実行経路で再現する証明である．
interfaceは，blockやpatternの内部で使う変数のうち，外側から観測できる型とbindingの対応を
意味する．

fuelは再帰計算を打ち切るための自然数であり，型付けの意味ではない．supplyは新しい通常型変数と
capability変数の次の番号を持つ．support provenanceは，生成結果の変数が入力context由来か，
開始supply以上・終了supply未満で新しく生成されたことを示す．

静的証明の全体像は次のとおりである．

```text
source expression
    │
    ├─ executable elaboration ── solver ── public infer
    │
    └─ relational elaboration ── declarative closure ── Typing
               │                         │
               ├─ coherence             ├─ principality
               └─ executable replay     └─ infer completeness
```

動的側では，`Typing`を値・環境・式に対する`RuntimeTyping`へ移し，評価とmatching探索が
その型を保存し，`stuck`へ到達しないことを証明する．adequacyは実行可能評価の成功から関係的
評価を得る性質，progressは型付きの未完了状態が一歩進むか正常な不一致になる性質，no-stuckは
規則不足を表す`stuck`へ到達しない性質である．`timeout`はfuel切れであり`stuck`とは区別する．

## 設計上の不変条件

以下は将来の証明でも維持する．変更する場合は，コードとこの節を同じcommitで更新する．

1. **宣言的型付けを実行器から独立させる．** `Typing`は関係的制約生成，宣言的飽和，
   制約を満たす代入から定義する．`generate`，`unify`，`infer`，実行結果，terminal auditを
   定義に含めない．
2. **matcher slotの形を推測しない．** producerからslotへの変換は，外側の構文，context，
   signatureから既に得られた要求だけで選ぶ．型を付けるために未知型をmatcher-shapedな型へ
   先回りして固定しない．
3. **一つのblockを同じ解で分類する．** 同じblockのpending obligationは，同じhard制約の解で
   一括して分類する．特殊変換や最後までpendingだった要求を解いた結果を，siblingの分類へ
   フィードバックしない．
4. **全checking要求を追跡する．** sourceから生成した各要求は，最終代入の下で変換があるか，
   通常等式としてhard制約へ移ったことを証明する．この性質をcoverageと呼ぶ．
5. **fresh変数の範囲を守る．** 新しい二種類の変数は開始supply以上・終了supply未満に置き，
   context由来の変数と区別する．公開推論は常にcontextに対してwell-formedなsupplyから始める．
   well-formedでない開始supplyは将来課題ではなく仕様外である．
6. **管理上の違いだけを同一視する．** 同じsourceから生成したblockについて，fresh変数名の
   有限な付け替えとhard／pending worklistの管理的な並べ替えは受理を変えない．source ASTの
   任意の並べ替えは位置の意味を変えるため，一般定理にしない．
7. **`letE`はfull-cut方式とする．** 右辺のblockを完全に閉じて一般化し，右辺の未解決要求を
   bodyへ流さない．周囲のcontextへの効果だけを有限なinterface等式として親blockへ戻す．
8. **fuelを意味論上の仮定にしない．** 関係は必要なfuelの存在を隠し，単調性と構文的な標準fuel
   への正規化を証明する．
9. **構文検査にも宣言的な意味を与える．** 直接自己参照，matcher網羅性，`matchFirst`網羅性は
   帰納的な命題で表し，Bool検査との同値を実行境界で使う．
10. **Paper 1のmatcherを隠れたprimitiveに置き換えない．** 7節の`multiset`と4節の`list`は
    実際のsource ASTとして静的・動的回帰で共有する．最適化primitiveを追加する場合は，先に
    source定義との結果列の一致を証明する．
11. **分岐の順序と重複を保存する．** matching分岐は値ではなく入力中の出現位置で区別する．
    深さ優先探索はsource順を保ち，同じ値になる別分岐を重複除去しない．
12. **追加公理や高速な外部判定に依存しない．** 公開証明で`sorry`，`admit`，追加`axiom`，
    `native_decide`，`unsafe`，`partial def`を使わない．exact回帰もkernelが検査する定義展開と
    equation lemmaだけで閉じる．

## 形式体系として固定している範囲

- `fixE`は単項・単相の直接自己再帰だけを受理する．自己はapplicationの直接のcalleeとして
  使い，bareな値，argument位置，`letE`による別名，内側の`fixE`から外側の自己を参照する
  mutual-styleな形を拒否する．相互`letrec`は現行の形式体系に含めない．
- `matchFirst`はPaper 1 Appendix Aの単一結果`match`を保持する派生surface構文であり，formal
  coreに新しいprimitiveを追加するものではない．
- conjunction pattern `p & q`は同じ対象へ左，右の順で照合し，右側は左側のbindingを参照できる．
- or-pattern `p | q`は左右をsource順で試す．両枝は同じbinding interfaceを持たなければならず，
  位置の対応は生成した等式で記録する．
- `PatternFunctionDefinitions.Agree`は，runtime本体とsource宣言の双方向対応と，保存schemeの
  標準的な一つの具体化に対する検査を表す．全具体化に対するinterface一致や主要性はまだ
  含まない．
- runtime contextは`List Ty`のまま保持する．sourceのschemeをそのままruntime contextへ入れない．
  任意の`IsInstance`を変数規則へ追加するだけでは後続代入に保存されないため，多相`let`の橋には
  量化bindingの由来またはfreshnessを保持する証明が必要である．
- bound-index schemeは束縛変数名の選び方に依存しないが，未使用binderを許すため，scheme全体の
  唯一の標準形ではない．`Source.Context`の自由変数は固定した仮定ではなく，最終代入で具体化
  され得る推論上の未知変数である．
- M2の`letE` coherenceでは，二つの生成結果が一つの大域的な変数名変更だけで一致するという
  強い主張は反例により偽である．閉じたcontextから観測できる対応だけを取り出すvisible closure
  graphと，有限な別名等式を使って比較する．

## 詳細ロードマップ

### M0--M3：完了した静的基盤

| ID | 項目 | 状態 | 証拠／完了内容 |
|---|---|---|---|
| S0.1 | 型と二種類の変数への代入 | **done** | 通常型変数とcapability変数を同時に扱う代入，合成，support |
| S0.2 | raw synthesisと局所checking | **done** | matcher tupleのraw主要性，外部要求がある場合だけの変換 |
| S1.1 | 実行可能生成と関係的生成 | **done** | `GenerationRelation`とfreshness／supply範囲 |
| S1.2 | 停止する単一化 | **done** | `unify`の健全性，完全性，最も一般的な解，fuel版からのtransport |
| S1.3 | 飽和とcoverage | **done** | 宣言的飽和，実行手続きの健全性・完全性，全pending要求の追跡 |
| S1.4 | M1公開定理 | **done** | `Inference.infer_success_typing`，`Typing.infer_isSome`，受理同値，決定可能性，主要性 |
| S1.5 | 順序不変性 | **done** | fresh名とworklist順序の違いを輸送．ASTの並べ替えは個別回帰 |
| S2.1 | bound-index scheme | **done** | well-scopedness，instantiate，generalize，自由変数への代入 |
| S2.2 | full-cut `letE` | **done** | value block closure，一般化，context interface等式 |
| S2.3 | closureの局所性 | **done** | 吸収性からsupport外を変更しないこと，let境界のsupply安定性 |
| S2.4 | entailed alignment | **done** | hard制約の全解の下でpending要求を比較し，飽和・受理・closureを輸送 |
| S2.5 | M2 coherenceとreplay | **done** | visible closure graphと有限別名等式による一般の入れ子`letE`の比較 |
| S2.6 | M2--M3公開定理 | **done** | `Source.Typing.infer_isSome`，受理同値，決定可能性，主要性，`finiteRenamingEq` |
| S3.1 | 宣言名とsignature | **done** | data／pattern former，constructor，primitive名を分離し，有限signatureを検査 |
| S3.2 | data型とcapability | **done** | `Ty.data`，`Cap.con`を代入，scheme，単一化，support，renamingへ接続 |
| S3.3 | 標準宣言 | **done** | Bool/List，`add`，`append`，`member`，`deleteFirst`，`map`，List pattern scheme |
| S3.4 | M3 source elaboration | **done** | constructor，primitive，`ifE`の実行可能・関係的elaborationと健全性 |

主要な公開入口は`TypePM/Source/FullM2Completion.lean`に集約している．M2完全性の
定義域は`supply.WellFormedFor context`であり，公開推論は`context.initialSupply`から始まるため
常にこの条件を満たす．

### M4-A：構文，推論健全性，計算回帰

| ID | 項目 | 状態 | 証拠／残り |
|---|---|---|---|
| M4.1 | 相互再帰source構文 | **done** | `Expr`，`Pattern`，matcher clause／arm，`matchFirst`を直接定義 |
| M4.2 | pattern構文 | **done** | variable，wildcard，value，constructor，tuple，conjunction，or，argument，application |
| M4.3 | matcher header形検査 | **done** | `PPat`／`DPat`，hole／capture順序，constructor arity，catch-all最後尾 |
| M4.4 | 宣言的静的条件 | **done** | DirectSelf，matcher coverage，`matchFirst` exhaustivenessとBool検査の同値 |
| M4.5 | pattern／`matchAll`型生成 | **done** | 左から右のbinding，value式，slotへの一方向checking，実行可能規則の関係的健全性 |
| M4.6 | matcher literal型生成 | **done** | clause／armの環境順，hole積，浅い網羅性，埋め込み式の型生成関係を引数に取る健全性 |
| M4.7 | `fixE`型生成 | **done** | 直接自己再帰検査とmatcher-root専用のdomain／codomain形 |
| M4.8 | `matchFirst`型生成 | **done** | target／matcherの一回だけの生成，arm body型の一致，網羅性 |
| M4.9 | 全構文dispatcher | **done** | `M4.elaborate`，`M4.infer`，`ElaboratesFuel`，`Elaborates`，`Typing` |
| M4.10 | 公開推論の健全性 | **done** | `M4.infer_success_principalTyping`，`M4.infer_success_typing` |
| M4.11 | fuel単調性と標準化 | **done** | `ElaboratesFuel.mono`，`normalize`，`Elaborates.iff_at_complexity` |
| M4.12 | supplyとsupport | **done** | `M4.supplyAndSupport`，全M4構文の生成変数の由来 |
| M4.13 | Paper 1 list exact | **done** | `M4Paper1ListExactRegression.infer_exact`，`typing`，shifted-supply再利用 |
| M4.14 | Paper 1 closed multiset exact | **done** | 7節全部のkernel計算，`M4Paper1ClosedMultisetExactRegression.infer_exact`，`typing` |
| M4.15 | Paper 1 open multiset拒否 | **done** | 空contextで`open_infer_none`．外側のlist依存が供給されていない式を誤って受理しない |
| M4.16 | 静的負例 | **done** | Paper 1の6例で`M4.Typing`不存在と公開`infer = none` |

#### list，open multiset，closed multiset

3つは別の型体系ではなく，共通のfixture（検証用に固定したsource program）である．

| fixture | 依存 | 空contextでの結果 | 検証済みの意味 |
|---|---|---|---|
| `listMatcherDefinition` | なし | `some listMatcherType` | 要素matcherからList matcherを作る4節のclosed constructor |
| `multisetDefinition` | 外側のlist matcher | `none` | 7節の本体を依存先なしでは受理しないopen expression |
| `closedMultisetDefinition` | source-defined listを明示的に適用 | `some closedMultisetType` | list依存を供給したclosed constructor |

依存関係は`multiset → list`の一方向であり，相互再帰ではない．listとmultisetはそれぞれ
個別の`fixE`で自己再帰し，closed版はlambda/applicationで二つを接続する．

### M4-B：完全性と主要性

M4完全性は，coherenceとexecutable replayの二本を別々に完成させてから合成する．coherenceは
二つの関係的elaborationの比較，replayは関係的elaborationを公開実行経路で再現する証明である．
以下の最外構文は式の一番外側にあるconstructor，部分構文はM2--M3だけで表せる式の範囲を
意味する．

| ID | 項目 | 状態 | 証拠／完了条件 |
|---|---|---|---|
| C1 | fuel標準化 | **done** | `CompletenessArchitecture.m4FuelNormalization` |
| C2 | M2--M3部分構文の再利用 | **done** | `fullM4FuelPairProperty_of_m2Fragment` |
| C3 | M4 fresh renaming | **done** | 全構文の`M4FreshRenaming.M4.ElaboratesFuel.rename`と`m4FreshRenamingTransport` |
| C4 | 通常最外構文のcoherence | **done** | lambda，application，tuple，constructor，primitive，`ifE`等を`ordinaryM4CoherenceStep`で合成 |
| C5 | `fixE` coherence | **done** | `fixCoherenceStep` |
| C6 | pattern／pattern-list pair coherence | **in progress** | embedded expression，binding interface，pattern由来等式を相互帰納で比較する |
| C7 | `matchAll` coherence | **not started** | C6とtarget／matcher／bodyの証明書を`Generated.fromMatchAll`へ合成する |
| C8 | matcher literal coherence | **not started** | pattern-pattern，data-pattern，next matcher，arm，clause列を合成する |
| C9 | `matchFirst` coherence | **not started** | patternとbodyをarm列，target／matcherへ合成する |
| C10 | M4 `letE` transport／assembly | **done** | `m4LetTransportAndAssembly`はclosureの代表を揃え，bodyと`Generated.fromLet`へ合成する |
| C11 | `FullM4Coherence` | **in progress** | 合成定理`fullM4Coherence_of_steps`は完成．C6--C10の実体が残る |
| R1 | non-let structural replay | **in progress** | 通常rootと`fixE`のexact/non-exact replay，sibling/callの逐次合成は完成．matcher系3 rootが残る |
| R2 | let closure representative agreement | **in progress** | `letM4FuelReplayStep`は完成．全構文fuel帰納への差し込みはmatcher系3 replay step待ち |
| R3 | `FullM4ExecutableReplay` | **in progress** | `fullM4ExecutableReplay_of_coherence_and_patternSteps`まで完成．Full coherenceとmatcher／`matchAll`／`matchFirst` replayの実体化待ち |
| F1 | M4完全性 | **in progress** | coherence／replayから完全性を得る条件付き定理は完成．C11とR3の実体化が残る |
| F2 | M4受理同値・決定可能性 | **in progress** | 条件付きAPI `typable_iff_infer_isSome_of_principalityComplete`と`typableDecidable_of_principalityComplete`は完成．F1の実体化待ち |
| F3 | M4主要性 | **in progress** | 条件付きの主要性定理は完成．C11とR3の実体化が残る |
| F4 | M4主要型の一意性 | **in progress** | 条件付き`PrincipalTyping.finiteRenamingEq_of_fullM4`は完成．Full M4 coherenceの実体化待ち |

現在の最短経路は，C6 → C7 → C8/C9 → C10 → C11と，R1/R2 → R3を並行して進め，
`wellFormedM4ElaborationPrincipalityComplete_of_coherence_and_replay`へ接続することである．

### M4-C：pattern functionとDamas--Milner対応

Damas--Milnerは，通常のHindley--Milner多相型付けを表す比較用の形式体系である．ここでの対応は，
matcher機能を使わない式を新体系へ埋め込めるかを調べる独立課題である．

| ID | 項目 | 状態 | 証拠／残り |
|---|---|---|---|
| PF1 | frozen interfaceの表現 | **done** | pattern function名，`DualScheme`，手動で与えた表の整合性検査 |
| PF2 | 標準具体化の本体検査 | **done** | `PatternFunctionDefinitions.Agree`とPaper 2 `pair` |
| PF3 | inline展開 | **done** | private binderを持たない断片の全source構文上の展開と評価 |
| PF4 | MNode実行 | **done** | private bindingを隔離し，引数patternのbindingだけを外へ返す探索 |
| PF5 | 公開freeze checker | **not started** | 検査済みsource本体から`FrozenSignature`とruntime定義表を構成する手続き |
| PF6 | 全具体化のinterface一致 | **not started** | 現在の`Agree`より強い独立定理．frozen signatureを仮定する通常のM4主要性F3とは別の主張 |
| DM1 | 独立したDM形式体系 | **done** | DM専用の型，scheme，式，`Typing`，sourceへの埋込み |
| DM2 | 基本的な実Source接続 | **done** | literal，variable，polymorphic identityの公開推論／`Source.Typing` |
| DM3 | 一般DM対応 | **design decision** | lambda/application/let全導出の対応はAlgorithm W完全性に相当する．最終主張へ含めるなら独立した大定理として進める |

### M5-A：評価と探索

| ID | 項目 | 状態 | 証拠／完了内容 |
|---|---|---|---|
| E1 | `FuelResult` | **done** | `ok`，`timeout`，`stuck`を分離し，左から右のtraverseを証明 |
| E2 | 環境とlookup | **done** | de Bruijn lookup，追加によるindex shift，末尾追加の保存 |
| E3 | 深さ優先探索 | **done** | 実行可能探索の健全性，有限完全性，fuel単調性，条件付きno-stuck |
| E4 | ordered choice | **done** | multisetの一要素選択，join分割，位置別の重複とsource順 |
| E5 | runtime value | **done** | data，tuple，function／recursive closure，matcher closure，`something` |
| E6 | pattern dispatch | **done** | `PPat`／`DPat`の実行と独立関係，binding数・順序の一致 |
| E7 | matcher clause dispatch | **done** | header不一致だけが次clauseへ進むfirst-success規則，環境連結順 |
| E8 | matching atom／state | **done** | built-in規則，conjunction，product matcher，user matcher reducerの合成 |
| E9 | `Eval`と`evalFuel` | **done** | `matchAll`／`matchFirst`を含むcall-by-value評価，成功時健全性，有限完全性，fuel単調性 |
| E10 | Paper 1 multiset実行 | **done** | 7節それぞれの正確なsource body結果と独立した`Eval`導出 |
| E11 | checked MNode評価器 | **done** | 定義表の`Agree`を必須にした全式fuel評価器とPaper 2 `pair`全式回帰 |
| E12 | MNode全式の独立関係 | **in progress** | evaluator-independent断片のexact simulationは完了．application／matchingを含む一般の環境・探索simulationが残る |

`ClauseDispatch.lean`と`Evaluation.lean`には形の似た関係が残るが，外部callback関係を相互帰納的な
`Eval`へ直接差し込む統合案は，帰納型が自身を関数引数の負の位置に含まないことを要求するLeanの
strict positivity検査に通らない．これは現在の定理の健全性を
損なう穴ではなく，将来の重複整理で別の表現が必要という実装上の境界である．

### M5-B：runtime typingと型安全性

| ID | 項目 | 状態 | 証拠／完了条件 |
|---|---|---|---|
| T1 | 値・環境・core式の型付け | **done** | 整数，Bool/List，tuple，変数，lambda，通常／再帰closure，application，`letE`，`ifE` |
| T2 | primitive安全性 | **done** | `add`，`append`，`member`，`deleteFirst`，`map`の型保存とno-stuck |
| T3 | signature整合性 | **done** | 固定 evaluator の宣言を`Runtime.StandardSignature`に集約．公開橋はsignature等式だけで使え，内部のlookup契約は無関係な追加宣言も許す |
| T4 | core safety | **done** | `RuntimeTyping.coreSafety`と任意fuelの`RuntimeTyping.neverStuck` |
| T5 | source-to-runtime橋の基本断片 | **done** | closedなtuple/data/primitiveに加え，monomorphic context下のvar/lam/app/map |
| T6 | source多相`let`の橋 | **design decision** | bareなgeneric `Ty` lookupは代入で保存されない．量化bindingの由来またはfreshness-aware transportを追加する |
| T7 | M4を出発点にするruntime橋 | **not started** | M2 `Source.Typing`にない`fixE`／matcher構文をM4 `Typing`から移す |
| T8 | built-in matching safety | **done** | binding／atom／state／有限DFSの型保存，局所progress，no-stuck |
| T9 | matcher closureの型付け部品 | **in progress** | cursor（未試行clauseの現在位置）の不変条件，product/list/slot canonical forms，0／1／複数holeの復号，環境連結順，単一hole clauseの保存は完了 |
| T10 | 一般user matcher safety | **in progress** | 単一hole／variable armの保存は実証済み．全clause／armと静的網羅性を接続し，正常な`.miss`と復号成功を証明する |
| T11 | 共通fuelの強帰納 | **not started** | 式評価とmatcher探索を同じbudgetで帰納し，embedded evaluatorの条件付き仮定を放電する |
| T12 | `matchFirst` no-stuck | **not started** | 宣言的`Exhaustive`から実行時の空arm到達を排除する |
| T13 | MNode／pattern function safety | **not started** | MNode固有application／parameter／nodeDone規則と一般評価を型付けする |
| T14 | Source全体の5.8 | **not started** | M4 bridge，T10--T13を合成し，型付きclosed programの任意fuel no-stuckを得る |

`MatcherSafety`のembedded evaluator契約は「必ず収束する」仮定ではない．型付き式の評価が
`timeout`になるか，型の付いた値を返すことを要求する．user matcher bodyが再び`matchAll`を呼ぶ場合に
この契約を無条件で得るには，T11の共通fuel強帰納が必要である．

## 論文の結果5.1--5.8との対応

5.3は論文では系だが，番号順に記録する．一般の`Typing`結果は主要型の具体化も含むため，5.4は
任意の型付け結果同士ではなく，主要性を満たす代表型同士の一意性として定式化する．

| 番号 | 新体系での意味 | 状態 | 現在の公開入口／残り |
|---|---|---|---|
| 5.1 | 公開`infer`成功なら独立した`Typing`がある | **done** | M1 `Inference.infer_success_typing`，M2--M3 `Source.Inference.infer_success_typing`，M4 `M4.infer_success_typing` |
| 5.2 | `Typing`があれば公開`infer`が成功する | **in progress** | M1とM2--M3は完了．M4はC6--C11とR1--R3が残る |
| 5.3 | `Typing`の存在と推論成功が同値で，受理を決定できる | **in progress** | M1とM2--M3は完了．M4完全性の公開化待ち |
| 5.4 | 二つの主要な代表型が有限な変数名変更を除いて一致する | **in progress** | M1とM2--M3は完了．M4 coherence／主要性待ち |
| 5.5 | 公開`infer`結果がすべての`Typing`結果の最も一般的な型である | **in progress** | M1とM2--M3は完了．M4 coherence／replay待ち |
| 5.6 | 静的型付けを状態を含まないruntime typingへ移す | **in progress** | `Source.Typing.toRuntimeTyping_standard`は固定signatureと`RuntimeSupported`断片を接続．source多相`let`とM4 matcher構文が残る |
| 5.7 | 型付き評価・matching・有限探索が型を保存し，局所的に進む | **in progress** | coreとbuilt-in matchingは完了．一般user matcherとMNode，共通fuel帰納が残る |
| 5.8 | 型付きclosed programは任意fuelで`stuck`にならない | **in progress** | core断片と条件付きmatchingは完了．M4-to-runtime橋とT10--T13の合成が残る |

5.6は旧体系の推論状態を後から消す定理ではない．新体系には初めから状態を含まない`Typing`がある
ため，sourceの型付け導出をruntime value・環境・matching stateの型付けへ移す構造的な定理として
再定式化する．

## Paper 1回帰

### code listing inventory

「静的」は公開`infer`と独立`Typing`を表す．

| ID | 掲載内容 | source | 静的 | 主な根拠／残り |
|---|---|---|---|---|
| P1-L01 | listとmultisetの`$x :: $xs` | done | in progress | matcher constructorはexact型付け済み．最終`matchAll`式の静的接続が残る |
| P1-L02 | `$x :: #(x + 1) :: _` | done | not started | 実行例と同じ最終式の統合M4型付けが残る |
| P1-L03 | List pattern宣言 | done | done | 3 schemeとPaper 1 signatureの整合性を検証済み |
| P1-L04 | 7節`multiset`定義 | done | in progress | closed wrapperはexact，open版の空context拒否も完了．list bindingを持つcontextでopen本体を直接型付けする名前付き定理が残る |
| P1-L05 | 直接のmultiset `matchAll` | done | not started | 実行済みの最終式を統合M4型付けへ接続する |
| P1-L06 | `unconsWith m target` | done | done | slot要求を持つ主要型と`M4.Typing`を固定済み |
| P1-L07 | `unconsWith`の正負呼出し | done | in progress | bare `something`拒否は完了．`multiset something`正例が残る |
| P1-L08 | 共有lambda domainの二順序 | done | done | 新仕様では両順序を同じ型で受理する |
| P1-L09 | 明示的`let` | done | done | M2公開推論と`Source.Typing`を固定済み |
| P1-L10 | value pattern内の`x ++ [1]` | done | done | Integer/List不一致による宣言的拒否 |
| P1-L11 | `$x :: #x` | done | done | occurs checkによる宣言的拒否 |
| P1-L12 | `#x :: $x :: _` | done | done | 左で未束縛の参照を宣言的に拒否 |
| P1-L13 | `something`のvariable／cons | done | done | variable成功とcons capability不足拒否を確認済み |
| P1-L14 | `matchAll 5 ... #1` | done | not started | 正常な不一致式の統合M4型付けが残る |
| P1-L15 | Bool対象とinteger matcher | done | done | target型不一致による宣言的拒否 |

実行を主張するlistingだけを次に分ける．「実行」はexact `evalFuel`，「関係」は`Eval`または
対応する独立関係，「安全」はsource-to-runtime橋を含む任意fuel no-stuckを表す．

| ID | 実行 | 関係 | 安全 | 主な根拠／残り |
|---|---|---|---|---|
| P1-L01 | done | done | not started | list先頭とmultiset三選択をsource順で確認済み |
| P1-L02 | done | done | not started | `[1,2,5,6] → [1,5]`を確認済み |
| P1-L04 | done | done | not started | 7節それぞれのsource bodyを終端まで評価済み |
| P1-L05 | done | done | not started | 三要素consの3結果をsource順で確認済み |
| P1-L13 | done | done | not started | exact評価を一般の`evalFuel_sound`で関係へ接続済み |
| P1-L14 | done | done | not started | 正常な不一致として空Listを返し，`evalFuel_sound`で関係へ接続済み |

論文listingを追加・削除・変更するときは，このinventoryと対応するsource／runtime回帰を同じ変更で
更新する．正確な結果の順序と重複も等式の一部として扱う．

### 7節multisetの実装境界

`multiset`は次の順序でsource定義として検証する．

1. M3でList，pattern宣言，使用するprimitiveの型を定義する．完了済み．
2. M4で7節をmatcher literalとして型付けし，clause順とhole要求を検査する．完了済み．
3. M5で同じ定義を評価し，nil，head-only，value-cons，general-cons，join，whole-value，
   catch-allを個別に固定する．exact評価と関係的導出は完了済み．
4. 静的型付けとruntime typingを一般定理で接続し，各closed利用例のno-stuckを得る．未完了．

joinは末尾の分割を再帰的に列挙し，各段階で現在の要素を右側へ置く結果を，左側へ置く結果より
先に返す．性能上の理由で順序を変える場合は，この説明，回帰，論文を同じ変更で更新する．

## 次に進める作業

依存順に並べると，現在の作業列は次のとおりである．

1. pattern／pattern-list pair coherenceを完成させ，`matchAll` coherenceへ接続する．
2. matcher literalと`matchFirst`のconstructor-local coherenceを並行して証明する．
3. M4 `letE`のclosure representative transportとassemblyを証明し，`FullM4Coherence`を得る．
4. non-let structural replayとlet closure agreementを証明し，`FullM4ExecutableReplay`を得る．
5. M4の5.2--5.5を公開APIとして閉じる．
6. M4 `Typing`を出発点にruntime typingのmatcher規則とbridgeを追加する．
7. 式評価とmatcher探索の共通fuel強帰納で，一般user matcherの安全性を証明する．
8. MNode固有規則を型付けし，一般pattern functionの安全性を接続する．
9. Paper 1 inventoryの残る統合静的例と任意fuel no-stuckを埋める．
10. DM一般対応を最終主張に含めるか決定し，含める場合は独立した完全性定理を証明する．

静的レーンの1--5と，動的基盤の6以降で独立に進められる補題は並行して実装する．ただし論文の
静的結果5.2--5.5を確定するのは5の完了後，型安全性5.6--5.8を確定するのは7--9の完了後とする．

## 完了と主張する条件

M1断片の`Typing`を定義しただけでは，Type-PM全体からterminal auditを除けたとは主張しない．
次をすべて追加公理なしで証明した時点で，プロジェクト全体を完了とする．

- M0--M4の全対象構文に対する独立した`Typing`と，公開`infer`の健全性，完全性，受理同値，
  主要性，主要な代表型の一意性．
- M5の静的型付けからruntime typingへの橋，型保存，局所progress，任意fuelのno-stuck．
- 対象に含める一般pattern functionについて，独立した実行関係と型安全性．
- このREADMEのPaper 1 inventoryで必要とした各段階．
- `TypePM/AxiomAudit.lean`の強制監査とCIを含む全build．

一般の停止性，幅優先探索の完全性，相互`letrec`，旧実装との後方互換性は現行の完了条件に
含めない．DM一般対応と全具体化のpattern-function主要性は，論文の最終主張へ含めると決めた場合に
完了条件へ昇格する．

## 主なファイル

| 目的 | 入口 |
|---|---|
| M1公開推論と型付け | [Inference.lean](TypePM/Inference.lean)，[InferenceCompleteness.lean](TypePM/InferenceCompleteness.lean)，[Principality.lean](TypePM/Principality.lean) |
| M2--M3完全性・主要性 | [FullM2Completion.lean](TypePM/Source/FullM2Completion.lean) |
| M4実行可能／関係的elaboration | [M4RecursiveElaboration.lean](TypePM/Source/M4RecursiveElaboration.lean) |
| M4 fuelとsupport | [M4ElaborationFuelMonotonicity.lean](TypePM/Source/M4ElaborationFuelMonotonicity.lean)，[M4SupplySupport.lean](TypePM/Source/M4SupplySupport.lean) |
| M4完全性の境界と公開系 | [M4CompletenessArchitecture.lean](TypePM/Source/M4CompletenessArchitecture.lean)，[M4StructuralReplay.lean](TypePM/Source/M4StructuralReplay.lean)，[M4CompletionConsequences.lean](TypePM/Source/M4CompletionConsequences.lean) |
| M4 renaming／coherence | [M4FreshRenamingTransport.lean](TypePM/Source/M4FreshRenamingTransport.lean)，[M4OrdinaryCoherence.lean](TypePM/Source/M4OrdinaryCoherence.lean)，[M4FixCoherence.lean](TypePM/Source/M4FixCoherence.lean)，[M4LetCoherence.lean](TypePM/Source/M4LetCoherence.lean) |
| Paper 1 source | [Paper1Programs.lean](TypePM/Source/Paper1Programs.lean) |
| Paper 1 exact静的回帰 | [M4Paper1ListExactRegression.lean](TypePM/Source/M4Paper1ListExactRegression.lean)，[M4Paper1ClosedMultisetExactRegression.lean](TypePM/Source/M4Paper1ClosedMultisetExactRegression.lean) |
| 評価とmatching | [Evaluation.lean](TypePM/Runtime/Evaluation.lean)，[EvalFuel.lean](TypePM/Runtime/EvalFuel.lean)，[MatchingState.lean](TypePM/Runtime/MatchingState.lean)，[MatchingSearch.lean](TypePM/Runtime/MatchingSearch.lean) |
| runtime typingと安全性 | [RuntimeTyping.lean](TypePM/RuntimeTyping.lean)，[CoreSafety.lean](TypePM/CoreSafety.lean)，[MatcherSafety.lean](TypePM/MatcherSafety.lean)，[NoStuck.lean](TypePM/NoStuck.lean) |
| user matcherの型付け部品 | [UserMatcherSafety.lean](TypePM/UserMatcherSafety.lean) |
| pattern function／MNode | [PatternFunctionNodeEvaluation.lean](TypePM/Runtime/PatternFunctionNodeEvaluation.lean) |
| 公理監査 | [AxiomAuditCommand.lean](TypePM/AxiomAuditCommand.lean)，[AxiomAudit.lean](TypePM/AxiomAudit.lean) |

## Buildと監査

リポジトリ直下で実行する．

```sh
lake build
lake build TypePM.AxiomAudit TypePM
git diff --check
```

`TypePM/AxiomAudit.lean`では，重要な公開定理を`#assert_allowed_axioms`へ登録する．このcommandは
推移的な公理依存を収集し，許可集合`{propext, Classical.choice, Quot.sound}`以外があればbuildを
失敗させる．新しい公開定理をロードマップで`done`にするときは，対応するassertionも追加する．

新しい正例回帰には，可能な範囲で`*_infer_exact`，`*_typing`，`*_eval_exact`，
`*_eval_relational`，`*_never_stuck`を分けて置く．静的負例は先に`*_not_typable`を証明し，
推論健全性から`*_infer_none`を導く．正常な不一致は`stuck`ではなく空の結果列として固定する．

## READMEの更新規則

- 完了した項目は，完了条件を満たす公開定理と公理監査を追加したcommitで`done`へ変更する．
- 大きな段階の状態だけでなく，対応する詳細ロードマップと論文表も同時に更新する．
- 実装途中の一時的なbranch名，worktree名，担当者名は記録しない．再開時は
  `git status --short --branch`と`git worktree list`で実際の状態を確認する．
- 過去の予定module名を先に固定しない．実在するmodule／theoremだけを証拠欄に記す．
- 設計判断を変更するときは「形式体系として固定している範囲」と，影響する完了条件を同時に
  更新する．
