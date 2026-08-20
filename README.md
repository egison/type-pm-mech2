# type-pm-mech2

`type-pm-mech2`は，Type-PMの入力プログラム（source program）へ直接型を与える規則を
Lean 4で機械的に検証するプロジェクトである．推論終了後の再検査（terminal audit）や
推論器の実行履歴を型付けの定義へ含めない．代わりに，「この式にこの型を与えてよい」
という条件を，推論器とは独立した規則`Typing`として定義する．

公開推論器`infer`について，成功した結果が必ず`Typing`を満たすことを**健全性**，
`Typing`を満たす結果があれば`infer`も成功することを**完全性**という．さらに，`infer`が
ほかのすべての型付け結果を具体化できる最も一般的な型を返すことを**主要性**という．
本プロジェクトでは，これらに加えて，型の付いたプログラムが評価中に型に合わない状態へ
進まないことも証明する．

このREADMEは，設計，現在地，完了条件，次の作業をまとめた唯一のロードマップである．
旧`DESIGN.md`の設計判断と，旧`CHECKPOINT.md`の再開情報はここへ統合した．概念を
順に説明する日本語資料は[`tex/type-pm-mech2-guide.pdf`](tex/type-pm-mech2-guide.pdf)
にあるが，進捗についてはこのREADMEとLeanコードを正本とする．

旧実装は別リポジトリ[`type-pm-mech`](../type-pm-mech/)に保存する．旧推論器，旧
`SourceTyping`，互換層，旧仕様専用の回帰をこのリポジトリへコピーしない．旧実装で
証明済みであることは，このロードマップの項目を完了にする根拠にならない．

## 最初に読む用語

### 二つのelaborationと`Typing`

このREADMEで**elaboration（型付け情報の生成）**とは，入力式から型変数と型制約を作る
段階を指す．プログラムを別の実行用コードへ変換するという意味ではない．同じ型付け規則を，
目的の異なる二つの形で定義する．

| 名前 | 何であるか | 何のために使うか |
|---|---|---|
| 実行可能なelaboration（executable elaboration） | Leanの関数として実際に走る決定的な処理 | 公開`infer`が型と制約を計算する |
| 関係として定義したelaboration（relational elaboration） | 正しい入力と出力の組を帰納規則で記述した仕様 | 特定の実装を呼ばずに，正しい型付け生成とは何かを定める |
| `Typing` | 関係として定義したelaborationと，生成した制約を満たす代入から作る判断 | 「推論器がそう答えたから正しい」という循環を避ける |

関係として定義するとは，たとえば「変数ならcontextから型を読む」「applicationなら関数部と
引数部の規則を満たし，両者の型が整合する」といった規則をLeanの帰納型で列挙することである．
`generate`，`unify`，`infer`の実行結果は，この規則の前提に入れない．

### coherenceとexecutable replay

関係的elaborationには，使用したfuelや`letE`で選ぶ一般化済みclosureの代表など，プログラムの
意味に影響しない管理上の選択がある．また，開始supplyが違えばfresh変数の番号も変わる．そのため，
正しい導出が二つあっても，中間の型変数名や制約blockが文字どおり同じとは限らない．この違いは，
fresh変数の名前変更を扱う定理と，次の二つの証明を組み合わせて扱う．

- **coherence（正しい導出同士の整合性）**は，同じ入力に対する二つの正しい関係的elaborationが，
  fresh変数の名前や`letE`の代表の違いを除けば，受理結果と外から見える主要な型について一致する
  ことを保証する．中間データ全体の文字列としての等しさを要求する証明ではない．
- **executable replay（公開手続きとの対応）**は，関係的elaborationで認められた導出から，
  公開`infer`が使う決定的なelaborationも成功し，意味の同じ代表結果へ到達することを保証する．
  とくに`letE`では，元のclosureを一字一句再現するのではなく，公開手続きが選ぶ代表へ対応付ける．

小さな例として恒等関数`fun x => x`を考える．開始番号10から型変数を作る実行では
`α10 → α10`が得られ，別の正しい開始番号37からは`α37 → α37`が得られる．fresh変数の
名前変更を扱う定理は，`α10`と`α37`を対応させれば両者が同じ型付けを表すことを保証する．
`let id = (fun x => x) in ...`では，一般化済みclosureの異なる正しい代表があり得るが，
coherenceはbodyから観測できる型付け結果が一致することを保証する．executable replayは，
これら関係的な規則で認められた導出を，公開`infer`が実際に計算する代表結果へ結び付ける．
`Integer → Integer`や`Bool → Bool`は`α10 → α10`への代入で得られるので，
`α10 → α10`が主要な型である．

二つを分けて証明する理由は次のとおりである．

| 証明 | それだけで分かること | それだけでは分からないこと |
|---|---|---|
| 健全性 | `infer`が返した結果は正しい | 正しい型付けがあるとき`infer`が成功するか |
| coherence | 関係的な正しい導出をどれに選んでも，外から見える意味は一致する | 公開の実行手続きが成功するか |
| executable replay | 関係的導出を公開の実行手続きへ対応付けられる | 別の正しい導出が異なる主要結果を表さないか |
| coherenceとreplayの合成 | `Typing`があれば`infer`が成功し，公開結果が主要である | ― |

静的証明の流れを短く書くと，次のようになる．

```text
入力式
  ├─ 実行可能なelaboration ─ 制約を解く関数 ─ 公開 infer
  └─ 関係として定義したelaboration ─ 宣言的な制約解釈 ─ Typing
             │
             ├─ coherence：正しい導出同士を比較する
             └─ replay：公開 infer の経路へ結び付ける
```

### 証明を管理するための情報

次の情報はLean上の再帰計算とfresh変数を安全に管理するために使う．プログラムの型の意味には
含めない．

- **fuel（計算量の上限）**は，再帰計算をどこで打ち切るかを指定する自然数である．評価器では
  fuel不足を`timeout`として型エラーと区別する．静的型付け関係では必要なfuelの存在を外から隠し，
  構文から決まる標準fuelへ揃えられることを証明する．
- **supply（次の未使用番号）**は，新しい通常型変数とcapability変数へ割り当てる次の番号を持つ．
- **support（実際に現れる変数）**は，型や制約に含まれる変数を表す．
- **support provenance（変数の由来の証明）**は，各変数が入力contextから来たか，開始supply以上・
  終了supply未満の範囲で新しく作られたかを記録する．
- **interface（外から見える対応）**は，blockやpatternの内部変数のうち，外側から観測できる型と
  bindingの対応である．

### matcherと制約の用語

- **capability**は，matcherが入力値のどの形を観察できるかを表す型情報である．
- **matcher producer**は実際にmatcher値を作る式の型，**matcher slot**は利用箇所がmatcherへ
  要求する型である．
- **raw synthesis**は外側の要求をまだ使わず式自身の型を作る処理，**checking**はその型を要求型として
  使用できるか確認する処理である．producerからslotへの暗黙変換はcheckingでだけ選ぶ．
- **制約block**は，同じ変数の有効範囲で生じた制約をまとめて解く単位である．
- **hard制約**は必ず満たす型等式，**pending obligation（保留中の検査要求）**は，制約の解が
  得られた後で変換可能か確認する要求である．
- **saturation（飽和）**は，特殊変換にならない保留中の要求を通常の型等式へ移し，それ以上
  移せなくなるまで制約を解き直す操作である．

動的な証明では，`Typing`を値・環境・式の型付け`RuntimeTyping`へ結び付ける．
**adequacy（実行結果との対応）**は，実行可能な評価の成功から関係として定義した評価を得る性質，
**progress（行き詰まらず進めること）**は，型の付いた未完了状態が一歩進むか正常な不一致になる性質，
**no-stuck**は，評価規則が足りない状態`stuck`へ到達しない性質である．fuel切れの`timeout`は
`stuck`と区別する．

## 状態の読み方

ロードマップでは次の状態を使う．

| 状態 | 意味 |
|---|---|
| **done** | その行の完了条件をLean kernelが検査済み．公開入口がある項目では公理監査にも登録済み |
| **in progress** | 必要な定義または補題の一部はあるが，行の完了条件をまだ満たさない |
| **not started** | 行に固有の実装をまだ開始していない |
| **scope decision** | Type-PM本体の完成には不要だが，論文で追加の強い主張をするなら，その前にユーザーが対象へ含めるか決める |
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
| M4 | pattern，matcher literal，`matchAll`，`matchFirst`，`fixE`，pattern function | **in progress** | 全対象構文で公開推論の健全性・完全性・受理同値・決定可能性・主要性・主要型一意性を証明済み．公開freeze checker PF5だけがこの段階に残る |
| M5 | 評価，matching探索，runtime typing，型安全性 | **in progress** | core評価とmatching基盤に加え，解決済みruntime型を前提に任意長のuser matcher arm／clause列の型保存と進行を証明済み．M4静的型付けとの接続，多相`let`，共通fuel帰納，MNode全体が残る |

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
- M2--M3部分構文の再利用に加え，子にM4構文を含む通常構文，`fixE`，全pattern，
  matcher literal，`matchAll`，`matchFirst`のcoherenceを証明した．全最外構文の局所証明が揃った．
- 全最外構文のcoherenceとreplayを全構文帰納へ接続し，`FullM4Coherence`，
  `FullM4ExecutableReplay`，`M4.Typing.infer_isSome`を無条件の公開定理にした．これにより
  論文結果5.2--5.5のM4静的部分は完了した．
- Paper 1のsource-defined `list`とclosed `multiset`について，公開`M4.infer`の正確な型と
  `M4.Typing`をkernel計算だけで固定した．open `multiset`は空contextで`none`になることを
  正確に証明した．
- user matcherのnext matcher式をcapture値とmatcher定義環境の連結上で評価するよう，実行可能評価と
  関係的評価の環境順を静的規則へ一致させた．0／1／複数hole，constructor header，capture参照，
  arm列，clause列について，`timeout`または型付きの正常結果になることを証明した．
- 公理監査は表示用の`#print axioms`ではなく，許可集合外の公理があればbuildを失敗させる
  `#assert_allowed_axioms`で実施し，CIでも`lake build`を実行する．

## 設計上の不変条件

以下は判断待ちの候補ではなく，このプロジェクトの目的を守るために既に固定した原則である．
将来の証明でも維持し，変更する場合はコードとこの節を同じcommitで更新する．

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

以下も現在の仕様として固定済みであり，証明を続けるためのユーザー判断は不要である．

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

## ユーザー判断が必要になる項目

現在のType-PM本体の健全性・完全性・型安全性を完成させるために，今すぐ選ぶ必要がある項目はない．
次の二件だけは，論文でType-PM本体より強い追加主張をする場合に，その論文を確定する前に
対象へ含めるかを判断する．判断があるまでは，どちらも本体完成の後に行う独立課題として扱う．

| 項目 | 含める場合に得られる主張 | 必要になる追加証明 | 現在の推奨 |
|---|---|---|---|
| 一般Damas--Milner対応（DM3） | matcherを使わない任意の通常Hindley--Milner導出がType-PMと一般に対応する | lambda，application，多相`let`を含む全導出について，Algorithm Wの完全性に相当する大きな証明 | 論文が一般対応を主要結果として主張しない限り，将来課題とする |
| pattern functionの全具体化でのinterface一致・主要性（PF6） | 一つの標準的な型具体化だけでなく，すべての型具体化で保存interfaceが一致し，主要である | 現在の`PatternFunctionDefinitions.Agree`より強い，全具体化を量化した独立定理 | pattern functionを中心に扱う論文で必要になった時点まで将来課題とする |

source多相`let`をruntime typingへ接続するT6は，ユーザーの対象範囲判断ではない．目標は既に
5.6の一部として固定しており，状態は`in progress`である．難点は，source contextでは一つの
多相schemeを利用ごとに別の型へ具体化できる一方，runtime contextを単相型の`List Ty`として
保持していることにある．変数規則へ単純に「任意の具体化」を足すだけでは，後から型代入を行うと
その証明が保存されない．runtime contextをscheme入りへ変更せず，量化されたbindingの由来と
freshnessを外部の証明関係で記録して接続する方針で進める．別方式へ変える判断は，この方針で
矛盾が見つかった場合にだけ改めて求める．

相互`letrec`，幅優先探索，旧実装との後方互換性などは「判断待ち」ではなく，現行仕様では
明示的に対象外である．対象へ戻す場合は新しい機能追加として，完了条件とロードマップを先に更新する．

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

M4完全性では，任意の`Typing`導出を受け取り，公開`infer`も成功することを示す．関係として
定義したelaborationには管理上の選択があるため，まずcoherenceで「どの正しい導出を選んでも
外から見える結果は同じ」と証明する．次にexecutable replayで，その導出を公開`infer`の決定的な
経路へ対応付ける．最後に二本を合成して，完全性と主要性を得る．

以下で「最外構文」は式の一番外側にあるconstructor，「部分構文」はM2--M3だけで表せる式の
範囲を意味する．`constructor-local`は，lambdaや`matchAll`など一種類の最外構文について，
子式で既に得た証明を親式へ組み立てる局所補題という意味である．

| ID | 項目 | 状態 | 証拠／完了条件 |
|---|---|---|---|
| C1 | fuel標準化 | **done** | `CompletenessArchitecture.m4FuelNormalization` |
| C2 | M2--M3部分構文の再利用 | **done** | `fullM4FuelPairProperty_of_m2Fragment` |
| C3 | M4 fresh renaming | **done** | 全構文の`M4FreshRenaming.M4.ElaboratesFuel.rename`と`m4FreshRenamingTransport` |
| C4 | 通常最外構文のcoherence | **done** | lambda，application，tuple，constructor，primitive，`ifE`等を`ordinaryM4CoherenceStep`で合成 |
| C5 | `fixE` coherence | **done** | `fixCoherenceStep` |
| C6 | pattern／pattern-list pair coherence | **done** | 全pattern構成子のsupply／binding interfaceと意味的証明書を`PatternElaboratesUsing.supportedFuelPairCoherence`で相互帰納的に比較 |
| C7 | `matchAll` coherence | **done** | target，pattern，matcher，bodyの4段階を比較し，pattern bindingと`Generated.fromMatchAll`の制約を`matchAllCoherenceStep`へ合成 |
| C8 | matcher literal coherence | **done** | pattern-pattern／data-patternの決定性，固定した外側境界を保つsupport，next matcher／arm／clause列，evidence等式を`matcherCoherenceStep`へ合成 |
| C9 | `matchFirst` coherence | **done** | 各armのpattern／body証明書を順序付きtailへ畳み込み，target／matcherと`matchFirstCoherenceStep`へ合成 |
| C10 | M4 `letE` transport／assembly | **done** | `m4LetTransportAndAssembly`はclosureの代表を揃え，bodyと`Generated.fromLet`へ合成する |
| C11 | `FullM4Coherence` | **done** | 全constructor-local stepを`fullM4Coherence_of_steps`へ渡し，公開`CompletenessArchitecture.fullM4Coherence`を実体化 |
| R1 | non-let structural replay | **done** | 通常root，`fixE`，matcher literal，`matchAll`，`matchFirst`を全構文fuel帰納へ合成し，`m4StructuralReplay_of_fuelReplay`へ接続 |
| R2 | let closure representative agreement | **done** | `letM4FuelReplayStep`を同じ全構文fuel帰納へ組み込み，`m4LetClosureRepresentativeAgreement_of_fuelReplay`へ接続 |
| R3 | `FullM4ExecutableReplay` | **done** | `CompletenessArchitecture.fullM4ExecutableReplay` |
| F1 | M4完全性 | **done** | 任意の`M4.Typing`から公開推論成功を得る`M4.Typing.infer_isSome` |
| F2 | M4受理同値・決定可能性 | **done** | `M4.typable_iff_infer_isSome`，`M4.typableDecidable` |
| F3 | M4主要性 | **done** | `M4.infer_success_principalResult` |
| F4 | M4主要型の一意性 | **done** | `M4.PrincipalTyping.finiteRenamingEq` |

M4-Bの静的完全性と主要性は完了した．今後のM4作業は，PF5の公開freeze checkerと，M5へ渡す
runtime typingの橋である．

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
| PF6 | 全具体化のinterface一致 | **scope decision** | 現在の`Agree`より強い独立定理．本体完成には含めず，pattern functionを中心に扱う論文で主張する場合に対象へ加える |
| DM1 | 独立したDM形式体系 | **done** | DM専用の型，scheme，式，`Typing`，sourceへの埋込み |
| DM2 | 基本的な実Source接続 | **done** | literal，variable，polymorphic identityの公開推論／`Source.Typing` |
| DM3 | 一般DM対応 | **scope decision** | lambda/application/let全導出の対応はAlgorithm W完全性に相当する．本体完成には含めず，論文の主要結果にする場合に対象へ加える |

### M5-A：評価と探索

| ID | 項目 | 状態 | 証拠／完了内容 |
|---|---|---|---|
| E1 | `FuelResult` | **done** | `ok`，`timeout`，`stuck`を分離し，左から右のtraverseを証明 |
| E2 | 環境とlookup | **done** | de Bruijn lookup，追加によるindex shift，末尾追加の保存 |
| E3 | 深さ優先探索 | **done** | 実行可能探索の健全性，有限完全性，fuel単調性，条件付きno-stuck |
| E4 | ordered choice | **done** | multisetの一要素選択，join分割，位置別の重複とsource順 |
| E5 | runtime value | **done** | data，tuple，function／recursive closure，matcher closure，`something` |
| E6 | pattern dispatch | **done** | `PPat`／`DPat`の実行と独立関係，binding数・順序の一致 |
| E7 | matcher clause dispatch | **done** | header不一致だけが次clauseへ進むfirst-success規則．capture式はatom環境，next matcherはcapture値＋定義環境，arm bodyはdata binding＋capture値＋定義環境で評価 |
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
| T6 | source多相`let`の橋 | **in progress** | bareなgeneric `Ty` lookupは代入で保存されない．runtime contextは`List Ty`のまま，量化bindingの由来とfreshnessを外部の証明関係で保持する |
| T7 | M4を出発点にするruntime橋 | **in progress** | 共有M2--M3構文に加え，bodyがその断片に属する通常の`fixE`をruntime typingとno-stuckへ接続済み．matcher-rootの`fixE`とmatcher構文が残る |
| T8 | built-in matching safety | **done** | binding／atom／state／有限DFSの型保存，局所progress，no-stuck |
| T9 | matcher closureとdispatchの型付け部品 | **done** | cursor不変条件，product/list/slot canonical forms，0／1／複数holeの復号，pattern-pattern constructor，環境連結順，任意長arm／clause列の条件付き型保存と進行 |
| T10 | 一般user matcher safety | **in progress** | runtime側はdata patternのvariable／wildcard断片で`tryMatcherArm_typedSafe`から`dispatchMatcherClauses_typedSafe`まで完成．data constructor／tuple，M4 signature／clause型付けとの橋，静的網羅性による最終`.miss`排除，任意source patternのatom型付けが残る |
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
| 5.2 | `Typing`があれば公開`infer`が成功する | **done** | M1，M2--M3，M4の全対象構文で完了．M4入口は`M4.Typing.infer_isSome` |
| 5.3 | `Typing`の存在と推論成功が同値で，受理を決定できる | **done** | M4入口は`M4.typable_iff_infer_isSome`，`M4.typableDecidable` |
| 5.4 | 二つの主要な代表型が有限な変数名変更を除いて一致する | **done** | M4入口は`M4.PrincipalTyping.finiteRenamingEq` |
| 5.5 | 公開`infer`結果がすべての`Typing`結果の最も一般的な型である | **done** | M4入口は`M4.infer_success_principalResult` |
| 5.6 | 静的型付けを状態を含まないruntime typingへ移す | **in progress** | 固定signatureのsource橋，共有M2--M3構文，通常のM4 `fixE`は完了．source多相`let`，matcher-rootの`fixE`，M4 matcher構文が残る |
| 5.7 | 型付き評価・matching・有限探索が型を保存し，局所的に進む | **in progress** | core，built-in matching，runtime証明書を持つuser matcherの任意長arm／clause列は完了．data-pattern全形，M4静的規則との橋，MNode，共通fuel帰納が残る |
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

1. M4 `Typing`からruntime typingへの橋をmatcher-rootの`fixE`，matcher literal，
   `matchAll`，`matchFirst`へ広げる．
2. 完成したuser matcherのruntime arm／clause安全性をM4のconstructor signatureと静的clause型付けへ
   接続し，宣言的な網羅性から最終的な`.miss`を排除する．
3. source多相`let`の量化bindingの由来を保持する証明関係を追加し，T6のruntime橋を閉じる．
4. 式評価とmatcher探索を共通fuelで強帰納し，embedded evaluatorへの条件付き仮定を外す．
5. `matchFirst`とMNode固有規則のno-stuckを証明し，公開freeze checkerが受理した
   source-defined pattern functionの型安全性へ接続する．
6. Paper 1 inventoryの残る統合静的例と任意fuel no-stuckを埋める．

静的結果5.1--5.5は確定した．動的レーンの1--5で独立に進められる補題と，PF5の公開freeze
checkerを並行して実装する．型安全性5.6--5.8を確定するのは1--6の完了後とする．
DM3とPF6はこの作業列を止めず，「ユーザー判断が必要になる項目」に書いた論文上の判断時点まで
将来課題として保持する．

## 完了と主張する条件

M1断片の`Typing`を定義しただけでは，Type-PM全体からterminal auditを除けたとは主張しない．
次をすべて追加公理なしで証明した時点で，プロジェクト全体を完了とする．

- M0--M4の全対象構文に対する独立した`Typing`と，公開`infer`の健全性，完全性，受理同値，
  主要性，主要な代表型の一意性．
- M5の静的型付けからruntime typingへの橋，型保存，局所progress，任意fuelのno-stuck．
- 公開freeze checkerが受理したsource-defined pattern functionについて，独立した実行関係と
  型安全性．全具体化でのinterface主要性PF6は含めない．
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
| M4完全性の境界と公開系 | [M4CompletenessArchitecture.lean](TypePM/Source/M4CompletenessArchitecture.lean)，[M4StructuralReplay.lean](TypePM/Source/M4StructuralReplay.lean)，[M4PatternReplay.lean](TypePM/Source/M4PatternReplay.lean)，[M4MatchAllReplay.lean](TypePM/Source/M4MatchAllReplay.lean)，[M4MatchFirstReplay.lean](TypePM/Source/M4MatchFirstReplay.lean)，[M4CompletionConsequences.lean](TypePM/Source/M4CompletionConsequences.lean)，[FullM4Completion.lean](TypePM/Source/FullM4Completion.lean) |
| M4からruntimeへの橋 | [M4RuntimeBridge.lean](TypePM/Source/M4RuntimeBridge.lean) |
| M4 renaming／coherence | [M4FreshRenamingTransport.lean](TypePM/Source/M4FreshRenamingTransport.lean)，[M4OrdinaryCoherence.lean](TypePM/Source/M4OrdinaryCoherence.lean)，[M4PatternCoherence.lean](TypePM/Source/M4PatternCoherence.lean)，[M4MatcherCoherence.lean](TypePM/Source/M4MatcherCoherence.lean)，[M4MatchAllCoherence.lean](TypePM/Source/M4MatchAllCoherence.lean)，[M4MatchFirstCoherence.lean](TypePM/Source/M4MatchFirstCoherence.lean)，[M4FixCoherence.lean](TypePM/Source/M4FixCoherence.lean)，[M4LetCoherence.lean](TypePM/Source/M4LetCoherence.lean) |
| Paper 1 source | [Paper1Programs.lean](TypePM/Source/Paper1Programs.lean) |
| Paper 1 exact静的回帰 | [M4Paper1ListExactRegression.lean](TypePM/Source/M4Paper1ListExactRegression.lean)，[M4Paper1ClosedMultisetExactRegression.lean](TypePM/Source/M4Paper1ClosedMultisetExactRegression.lean) |
| 評価とmatching | [Evaluation.lean](TypePM/Runtime/Evaluation.lean)，[EvalFuel.lean](TypePM/Runtime/EvalFuel.lean)，[MatchingState.lean](TypePM/Runtime/MatchingState.lean)，[MatchingSearch.lean](TypePM/Runtime/MatchingSearch.lean) |
| runtime typingと安全性 | [RuntimeTyping.lean](TypePM/RuntimeTyping.lean)，[CoreSafety.lean](TypePM/CoreSafety.lean)，[MatcherSafety.lean](TypePM/MatcherSafety.lean)，[NoStuck.lean](TypePM/NoStuck.lean) |
| user matcherの型付けと条件付き安全性 | [UserMatcherSafety.lean](TypePM/UserMatcherSafety.lean)，[UserMatcherGeneralSafety.lean](TypePM/UserMatcherGeneralSafety.lean) |
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
