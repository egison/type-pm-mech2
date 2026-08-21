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
旧`DESIGN.md`の設計判断と，旧`CHECKPOINT.md`の再開情報はここへ統合し，両ファイルは削除した．概念を
順に説明する日本語資料は[`tex/type-pm-mech2-guide.pdf`](tex/type-pm-mech2-guide.pdf)
にあるが，進捗についてはこのREADMEとLeanコードを正本とする．

旧実装は別リポジトリ[`type-pm-mech`](../type-pm-mech/)に保存する．旧推論器，旧
`SourceTyping`，互換層，旧仕様専用の回帰をこのリポジトリへコピーしない．旧実装で
証明済みであることは，このロードマップの項目を完了にする根拠にならない．

## 最初に読む用語

### READMEで繰り返し使う基本語

- **context**は，その場所で参照できる変数の型を順番に並べたものである．
- **arm**は，patternと，そのpatternが結果を返したときに評価する式を組にした分岐である．
- **decomposition（候補分解）**は，matcherが一つの対象から返す照合候補の列である．0件でも
  正常な結果であり，型エラーや`stuck`ではない．
- **closedな式**は自由変数を持たない式，**openな式**は外側のcontextにある変数を参照する式である．
- **certificate（証明書）**は，ある前提や実行結果が型を保つことをLean内で記録した証明データである．
  外部ツールが発行する証明書という意味ではない．
- **exact regression（結果を等式で固定した回帰）**は，具体例が特定の値を返すことをLeanの等式で
  検査するテストである．具体例の動作は保証するが，それだけでは任意のプログラムに対する一般定理にならない．

### 型推論を二つの経路で記述する理由

まず`fun x => x`を例に，全体の流れを示す．このREADMEで
**elaboration（型付け情報の生成）**とは，入力式から型変数と型制約を作る処理である．

```text
入力 `fun x => x`
  ├─ 実行可能なelaboration ── 実際に関数を走らせる ── `α10 → α10`を返す
  └─ 関係として定義したelaboration ── 規則から導出を組み立てる ── `α37 → α37`も認める
                                  │
                                  ├─ coherence：α10とα37は名前が違うだけと示す
                                  └─ executable replay：下側の導出を上側の実行で再現する
```

- **実行可能なelaboration（executable elaboration）**は，入力を受け取り，Lean上で実際に
  実行して型と制約を返す関数である．公開`infer`はこの関数を使う．
- **関係として定義したelaboration（relational elaboration）**は，同じ型付け規則を
  Leanの命題`Prop`として書いた独立仕様である．「変数ならcontextから型を読む」などの
  規則から正しい入出力の組を記述し，`generate`，`unify`，`infer`の実行結果を前提にしない．
- **`Typing`**は，関係として定義したelaborationと，生成した制約を満たす代入から作る判断である．
  これにより「推論器が返したから正しい」という循環を避ける．ただし，ここで完全性の対象にする
  `M4.Typing`は，`letE`ごとに主要な制約blockを閉じる関係的elaborationの判断である．教科書で使う
  Damas–Milner型付け判断を別に定義し，それに対する完全性まで証明した，という意味ではない．
- **coherence（導出同士の意味の一致）**は，同じ式について二つの関係的な導出があるとき，
  fresh変数の番号や`letE`で選んだ代表が違っても，名前を対応させれば同じ受理結果と型を表す
  ことを示す．中間データが文字どおり同じ，という意味ではない．
- **executable replay（実行関数による再現）**は，関係的な導出があるなら，公開`infer`が使う
  実行可能なelaborationも成功し，同じ意味の代表結果を返すことを示す．ここでいうreplayは
  推論器が過去に残した実行履歴を再生することではなく，規則版で認めた型付けを関数版でも再現できる
  という定理を指す．

たとえば`α10 → α10`と`α37 → α37`は，型変数の名前だけが違う．coherenceはこの二つを
同じ型付けとして結び付ける．executable replayは，関係的な規則で`α37 → α37`という導出を
作れたとき，実行関数も自分のfresh変数`α10`を使って対応する結果を返すことを保証する．

これらを分けるのは，役割が異なるためである．健全性は「`infer`の答えは正しい」，coherenceは
「正しい導出をどれに選んでも意味は同じ」，replayは「独立仕様で認めた導出を実行関数でも
再現できる」をそれぞれ示す．coherenceとreplayを合成して初めて，`Typing`があるとき公開
`infer`も成功し，主要な型を返すという完全性・主要性へ進める．

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
`stuck`と区別する．`matchFirst`は必須の`else`を持つため，すべてのarmの探索結果が空でも
`stuck`にはならず，元の環境で`else`を評価する．sourceでは通常armを1本以上要求する．静的に
受理されたsource式のruntimeでは，空arm caseを全armの試行後を表す内部状態としてだけ使う．

```text
matchFirst target matcher
| pattern1 -> body1
| pattern2 -> body2
else fallback
```

型推論はtargetとmatcher，各body，fallbackを型検査し，すべてのbodyとfallbackが同じ結果型を
持つことを確認する．通常armが実際に結果を返すことは保証しない．すべての候補分解が空なら，
arm内でだけ使える変数を含まない元の環境でfallbackを評価する．したがって`else`が
「現在のarmに依存しない」とは，そのarm内で導入された変数を参照しないという意味である．
`else`は元のcontextで型付けする任意の式なので，内部に別の`matchAll`や`matchFirst`を含めてもよい．

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

必須`else`付き`matchFirst`への変更後も，`lake build TypePM.AxiomAudit TypePM`が成功している．
推移的な公理依存は許可集合`{propext, Classical.choice, Quot.sound}`だけであり，それ以外を検出すると
監査commandがbuildを失敗させる．

## 現在地

### 段階別の要約

| 段階 | 対象 | 状態 | 現在地 |
|---|---|---|---|
| M0 | 型，二種類の変数，raw synthesis，局所checking | **done** | tuple of matchersのraw主要性と，明示された要求型への変換まで証明済み |
| M1 | lambda，application，制約block，公開推論 | **done** | 健全性，完全性，受理同値，決定可能性，主要性，主要型の有限な変数名変更による一意性まで証明済み |
| M2 | bound-index scheme，多相`letE`，value block一般化 | **done** | 一般の入れ子`letE`についてcoherence，replay，公開推論の完全性・主要性まで証明済み |
| M3 | data／pattern constructor，primitive，signature，`ifE` | **done** | M3固有の宣言・elaborationと，M2--M3全域の公開定理を証明済み．論文例のM4/M5部分は別に追跡する |
| M4 | pattern，matcher literal，`matchAll`，`matchFirst`，`fixE`，pattern function | **done** | 必須`else`付き`matchFirst`を含む全構文で健全性，完全性，受理同値，決定可能性，主要性，主要型の一意性を再検証し，Paper 1の大規模exact回帰も新仕様へ固定済み |
| M5 | 評価，matching探索，runtime typing，型安全性 | **in progress** | core評価とmatching基盤，`matchAll`／`matchFirst`を含む共通fuel安全性まで進んだ．M4静的型付けとの一般接続，多相`let`の一般橋，user matcher branch，MNode全体が残る |

M3を`done`とするのは，M3固有のconstructor／primitive／signature基盤とM2--M3の
静的定理が閉じているためである．Paper 1全体の例が未完であることは，M4/M5と後述の
inventoryで追跡する．

### 直近の重要な到達点

- `M4.infer_success_typing`により，必須`fallback`付き`matchFirst`を含む全M4構文で，
  公開推論の成功から独立した`M4.Typing`を得られる．論文結果5.1の静的健全性は完了している．
- fuelは上向きに単調であり，任意の導出を`expression.complexity + 1`へ正規化できる．
  公開`M4.Elaborates`と標準fuelの関係は`M4.Elaborates.iff_at_complexity`で固定した．
- matcherの形状条件（pattern-pattern／data-patternのconstructorとarity，captureとholeの順序，
  armのbinding順序，clause列の最終catch-all）を帰納的な命題で表し，各実行可能Bool検査との
  同値を証明した．`StaticChecksHold`と関係的なmatcher clause elaborationはBool計算結果を
  直接仮定せず，Boolとの変換は実行可能elaborator／runtime bridgeの境界で行う．
- 必須`fallback`を含む全M4構文について，supply増加，生成変数の由来，fresh-variable renamingを
  証明した．
- 全M4構文で最外構文ごとのcoherenceとreplayを全構文帰納へ接続した．`FullM4Completion`から
  完全性，受理同値，決定可能性，主要性，主要型の一意性を公開する．構成要素を列挙した二つの
  architecture boundaryも，実装が連言全体を満たす定理として監査する．また，主要型付けを前提に
  公開`infer`の主要な結果を得る`M4.infer_principalResult`を公開した．
- `PatternFunctionFreeze.freezePatternFunctions`はsourceのinterfaceとbody列から検査済みの
  `FrozenSignature`，runtime定義表，`PatternFunctionDefinitions.Agree`を構成する．Paper 2の
  `pair`をfreeze結果からchecked MNode evaluatorへ直接渡す回帰を固定した．
- `FrozenSignature.WellFormed`は通常のconstructor／primitive宣言に対する
  `Signature.WellFormed`より強く，pattern function宣言の整合性も検査する．M4の公開完全性定理が
  前提にするのはこの強い方の条件である．
- Paper 1のsource-defined `list`，open `multiset`，closed `multiset`は，必須`else`と
  全域的なpair destructuringへの変更後の構造fuel，生成block，公開推論型，open版の拒否を
  kernel回帰として再固定した．
- user matcherのnext matcher式をcapture値とmatcher定義環境の連結上で評価するよう，実行可能評価と
  関係的評価の環境順を静的規則へ一致させた．0／1／複数hole，constructor header，capture参照，
  arm列，clause列について，`timeout`または型付きの正常結果になることを証明した．data patternは
  variable，wildcard，Bool/List constructor，tupleと，入れ子の場合まで扱う．
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
9. **構文検査にも宣言的な意味を与える．** matcherの形状・網羅性は帰納的な命題で表す．
   直接自己参照の`DirectSelf.Holds`は固定fuelでの証明レベルの検査関係として表し，いずれも
   Bool検査との同値を実行境界で使う．
10. **Paper 1のmatcherを隠れたprimitiveに置き換えない．** 7節の`multiset`と4節の`list`は
    実際のsource ASTとして静的・動的回帰で共有する．最適化primitiveを追加する場合は，先に
    source定義との結果列の一致を証明する．
11. **分岐の順序と重複を保存する．** matching分岐は値ではなく入力中の出現位置で区別する．
    現在のfuel付き深さ優先探索はsource順を保ち，同じ値になる別分岐を重複除去しない．
12. **追加公理や高速な外部判定に依存しない．** 公開証明で`sorry`，`admit`，追加`axiom`，
    `native_decide`，`unsafe`，`partial def`を使わない．exact回帰もkernelが検査する定義展開と
    equation lemmaだけで閉じる．

## 形式体系として固定している範囲

以下も現在の仕様として固定済みであり，証明を続けるためのユーザー判断は不要である．

- `fixE`は単項・単相の直接自己再帰だけを受理する．自己はapplicationの直接のcalleeとして
  使い，bareな値，argument位置，`letE`による別名，内側の`fixE`から外側の自己を参照する
  mutual-styleな形を拒否する．相互`letrec`は現行の形式体系に含めない．
- `matchFirst`はcore構文`.matchFirst target matcher arms fallback`として保持する．target，matcherを
  この順で先に評価し，通常armをsource順に試す．最初の非空結果の先頭だけを使い，すべて空なら
  通常armが導入する変数に依存しない必須の`fallback`（表面構文では`else`）を元のcontext・元の
  実行環境で評価する．
  静的に受理するsource式には通常armを1本以上要求する．runtime helperの空arm caseは，受理済みの
  通常armをすべて空結果として消費した後に`fallback`へ進む内部終端である．最初からarmが不要なら
  sourceでは`fallback`自体を書けばよく，target／matcherの先行評価も残す必要があれば`letE`で書ける
  ため，表現力は落ちない．wildcardもuser matcher次第で空結果になり得るため，全域性の根拠にしない．
  targetまたはmatcher自身が`stuck`／`timeout`なら，`fallback`より先にその結果を返す．
- tuple pattern lambdaは`matchFirst`で表さない．pairを必ず二要素へ分解する用途は，型付きの
  `pairFirst`／`pairSecond` primitiveを使う全域的なpair destructuringとして分離する．
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
  強い主張は反例により偽である．そのため，外から観測できる型変数の対応だけを記録する
  **visible closure graph**と，有限な別名等式を使って比較する．

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

相互`letrec`，完全なEgison処理系との後方互換性などは「判断待ち」ではなく，現行仕様では
明示的に対象外である．対象へ戻す場合は新しい機能追加として，完了条件とロードマップを先に更新する．

### `matchAllDFS`と公平な`matchAll`

現行の`depthFirstFuel`／`searchPatternFuel`／`evalFuel`にある`.matchAll` caseは，後続の状態より
先頭branchを優先するfuel付き深さ優先探索であり，探索完了後に有限なanswer列を一括して返す．
探索部分はAPLAS 2018論文の付録にある`match-all-dfs`に対応し，同論文で既定とされる
`match-all`の意味論ではない．型保存とno-stuckはこのbounded DFS laneについて有効だが，公平な
列挙完全性は含まない．`timeout`は探索未完了を表し，正常な不一致`[]`や`stuck`ではない．

たとえば左branchが自分自身を無限に展開し，右branchが直ちに成功する探索では，右の成功は
有限深さに存在していてもDFSの任意fuelで観測できない．この境界は
`left_recursive_branch_starves_later_success`で実行可能な回帰として固定する．

APLAS 2018の既定`match-all`は，状態列をnodeとする二分の簡約木を幅優先に走査し，各有限位置の
nodeへ有限回で探索機会を与える．無限個の結果を扱うには，単に探索順を幅優先へ変えるだけでなく，
完成した有限リストではなく遅延列または有限prefixとして結果を観測する必要がある．そのためLean側でも，
現在のbounded `matchAllDFS`を残したまま，有限prefixと未探索frontierを返す公平な`matchAll` laneを
別に追加し，両方について型安全性を証明する．公平性の正確な主張は「各局所stepが完了し，有限個の
局所stepで到達できる成功は，ある有限roundのprefixに現れる」であり，一般停止性は要求しない．

`matchFirst`の通常armに結果があるかを型推論で判定しないことも固定済みである．user matcherは
型の正しい空decomposition列を返せるため，wildcard armでも照合結果がない場合がある．この場合は
通常armが導入した変数から独立した必須`else`へ進む．全matcherの意味的な全域性を型検査で要求する案は採用しない．
この設計について追加のユーザー判断は不要である．

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
| M4.1 | 相互再帰source構文 | **done** | `Expr`，`Pattern`，matcher clause／arm，必須`fallback`付き`matchFirst`を直接定義 |
| M4.2 | pattern構文 | **done** | variable，wildcard，value，constructor，tuple，conjunction，or，argument，application |
| M4.3 | matcher header形検査 | **done** | `PPat`／`DPat`，hole／capture順序，constructor arity，catch-all最後尾 |
| M4.4 | 宣言的静的条件 | **done** | matcherの形状・coverageを帰納的命題，DirectSelfを固定fuelの証明レベルの検査関係で表し，各Bool検査との同値を証明 |
| M4.5 | pattern／`matchAll`型生成 | **done** | 左から右のbinding，value式，slotへの一方向checking，実行可能規則の関係的健全性 |
| M4.6 | matcher literal型生成 | **done** | clause／armの環境順，hole積，浅い網羅性，埋め込み式の型生成関係を引数に取る健全性 |
| M4.7 | `fixE`型生成 | **done** | 直接自己再帰検査とmatcher-root専用のdomain／codomain形 |
| M4.8 | `matchFirst`型生成 | **done** | 1本以上の通常arm，target／matcher，同じ結果型を持つ必須`fallback`を実行可能規則と関係規則の両方で検査 |
| M4.9 | 全構文dispatcher | **done** | `M4.elaborate`，`M4.infer`，`ElaboratesFuel`，`Elaborates`，`Typing`を必須`fallback`へ同期 |
| M4.10 | 公開推論の健全性 | **done** | `M4.infer_success_principalTyping`と`M4.infer_success_typing`を全M4構文について証明 |
| M4.11 | fuel単調性と標準化 | **done** | 関係版の`ElaboratesFuel.mono`／`normalize`／`Elaborates.iff_at_complexity`に加え，成功した実行結果を同じ生成blockのまま大きいfuelへ運ぶ`M4.elaborateFuelUsing_success_mono` |
| M4.12 | supplyとsupport | **done** | `M4.supplyAndSupport`と`M4FreshRenaming.M4.ElaboratesFuel.rename`により，生成変数の由来とfresh renamingを全構文で証明 |
| M4.13 | Paper 1 list exact | **done** | 全域的pair destructuringへ移行後の4節をkernel計算で固定し，公開`infer`結果と`M4.Typing`へ接続 |
| M4.14 | Paper 1 closed multiset exact | **done** | list依存を供給した7節全部のkernel計算，公開`infer`結果，`M4.Typing`を固定 |
| M4.15 | Paper 1 open multiset拒否 | **done** | list依存のない空contextで，構造的elaborationと公開`infer`がともに失敗することを固定 |
| M4.16 | 静的負例 | **done** | Paper 1の型不一致，未束縛参照，capability不足等を新構文で再検証 |

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
| C3 | M4 fresh renaming | **done** | `m4FreshRenamingTransport`が必須`fallback`を含む全構文の導出を有限な変数名変更で輸送 |
| C4 | 通常最外構文のcoherence | **done** | lambda，application，tuple，constructor，primitive，`ifE`等を`ordinaryM4CoherenceStep`で合成 |
| C5 | `fixE` coherence | **done** | `fixCoherenceStep` |
| C6 | pattern／pattern-list pair coherence | **done** | 全pattern構成子のsupply／binding interfaceと意味的証明書を`PatternElaboratesUsing.supportedFuelPairCoherence`で相互帰納的に比較 |
| C7 | `matchAll` coherence | **done** | target，pattern，matcher，bodyの4段階を比較し，pattern bindingと`Generated.fromMatchAll`の制約を`matchAllCoherenceStep`へ合成 |
| C8 | matcher literal coherence | **done** | pattern-pattern／data-patternの決定性，固定した外側境界を保つsupport，next matcher／arm／clause列，evidence等式を`matcherCoherenceStep`へ合成 |
| C9 | `matchFirst` coherence | **done** | `matchFirstCoherenceStep`がtarget／matcher，1本以上の通常arm，arm-local bindingから独立して元contextで型付けする`fallback`の二導出を比較 |
| C10 | M4 `letE` transport／assembly | **done** | `m4LetTransportAndAssembly`はclosureの代表を揃え，bodyと`Generated.fromLet`へ合成する |
| C11 | `FullM4Coherence` | **done** | `CompletenessArchitecture.fullM4Coherence`が全constructor-local証明を合成 |
| R1 | non-let structural replay | **done** | `m4StructuralReplay_of_fuelReplay`が必須`fallback`を含む全構文fuel帰納を公開elaboratorへ接続 |
| R2 | let closure representative agreement | **done** | `letM4FuelReplayStep`を同じ全構文fuel帰納へ組み込み，`m4LetClosureRepresentativeAgreement_of_fuelReplay`へ接続 |
| R3 | `FullM4ExecutableReplay` | **done** | `CompletenessArchitecture.fullM4ExecutableReplay` |
| F1 | M4完全性 | **done** | `M4.Typing.infer_isSome` |
| F2 | M4受理同値・決定可能性 | **done** | `M4.typable_iff_infer_isSome`と`M4.typableDecidable` |
| F3 | M4主要性 | **done** | `M4.infer_success_principalResult` |
| F4 | M4主要型の一意性 | **done** | `M4.PrincipalTyping.finiteRenamingEq` |

M4-Bは必須`fallback`付き`matchFirst`を含めて完了している．局所補題だけでなく，それらを合成した
`FullM4Completion.lean`の公開定理までkernelで検査する．

### M4-C：pattern functionとDamas--Milner対応

Damas--Milnerは，通常のHindley--Milner多相型付けを表す比較用の形式体系である．ここでの対応は，
matcher機能を使わない式を新体系へ埋め込めるかを調べる独立課題である．

| ID | 項目 | 状態 | 証拠／残り |
|---|---|---|---|
| PF1 | frozen interfaceの表現 | **done** | pattern function名，`DualScheme`，手動で与えた表の整合性検査 |
| PF2 | 標準具体化の本体検査 | **done** | `PatternFunctionDefinitions.Agree`とPaper 2 `pair` |
| PF3 | inline展開 | **done** | private binderを持たない断片の全source構文上の展開と評価 |
| PF4 | MNode実行 | **done** | private bindingを隔離し，引数patternのbindingだけを外へ返す探索 |
| PF5 | 公開freeze checker | **done** | `freezePatternFunctions`が全interfaceを先に凍結し，各bodyの標準具体化を検査してsignature，runtime定義表，`Agree`証明を返す |
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
| E9 | `Eval`と`evalFuel` | **done** | `matchAll`／`matchFirst`を含むcall-by-value評価，成功時健全性，有限完全性，fuel単調性．さらに，一度`ok`または`stuck`まで計算が完了した結果はfuelを増やしても変わらない．したがって，あるfuelで`ok`になった式や関数適用は，それより小さいfuelでは`timeout`の可能性があるが，どのfuelでも`stuck`にはならない |
| E10 | Paper 1 multiset実行 | **done** | 7節それぞれの正確なsource body結果と独立した`Eval`導出．成功を確認したnil，head-only，value-cons，general-cons，join，whole-value，catch-allの7例は，E9から任意fuelで`stuck`にならないことも固定済み |
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
| T3 | signature整合性 | **done** | 固定 evaluator の宣言を`Runtime.StandardSignature`に集約．基本のlookup契約は無関係な追加宣言を許す．data-pattern橋向けには，frozen signatureでlookup可能な各data constructorがruntimeのconstructor型付けを持つことを要求する一般契約を追加し，Paper 1の閉じた宣言表による証拠をfixture側へ分離した．M4の一般runtime橋もこの契約を明示引数に取るようparameter化し，一般moduleからPaper 1 signatureへの依存を除いた．Paper 1の証拠はfixture moduleだけが直接importする．公開infer endpointでは，runtime整合性とは別に`FrozenSignature.WellFormed`も要求する |
| T4 | core safety | **done** | `RuntimeTyping.coreSafety`と任意fuelの`RuntimeTyping.neverStuck` |
| T5 | source-to-runtime橋の基本断片 | **done** | closedなtuple/data/primitiveに加え，monomorphic context下のvar/lam/app/map |
| T6 | source多相`let`の実行時型付け | **in progress** | ここでいう橋は，sourceの型付け導出から，評価器が使う値・環境・式の型付けを自動で組み立てる定理である．多相bindingだけを証明用の印で追跡し，実行時contextは`List Ty`のまま保つ．入れ子`letE`の値はidentity限定ではなく，実際のvalue elaborationと，その`let`が採用した同じprincipal closureに結び付いたcertificateがあれば任意の構文を扱える．非identityのclosed tuple `(1, 2)`，入れ子identity，外側lambdaが多相identityを捕捉する三回帰では，公開`infer`成功だけからruntime typingと任意fuel no-stuckを得られる．var／literal／`something`／lambda／application／tuple／nested letに加え，複数引数のconstructor・primitive・`ifE`について，実際の関係的elaboration導出に沿って各残存検査の由来を記録する構造的certificateを追加した．一つの実elaboration導出と代入に固定した実行可能checkerも追加し，受理と同じ導出の構造的certificateが同値であることを証明した．さらに，引数位置をliteral／lambdaに制限して型の最外形を`Int`／関数型に固定する明示的な`RootOrdinarySourceFragment`では，構文証明と実際のelaboration成功からchecker受理を自動導出する．関数位置とtupleの子では入れ子applicationを許し，`letE`右辺の内部検査はroot列に現れないためbodyだけを調べる．この断片のlambda application＋tuple＋二引数`add`回帰も，公開`infer`からruntime typingと任意fuel no-stuckへ接続した．matcher-to-slotはrootの残存検査列に現れる限り通常等式として隠せない．公開root checkerについては受理からcertificateを作る向きだけを主張し，任意の`infer`成功からchecker成功が従うとはしていない．matcher構文，引数位置の一般化，同じclosureのcertificateをさらに一般の値へ広げる作業が残る |
| T7 | M4型付けから実行時型付けを作る定理 | **in progress** | M2--M3と共有する構文，通常の`fixE`，解決済みのmatcher header／arm／clauseは接続済み．arm bodyが`matchAll`を含む最小の再帰matcherでも，M4の導出から実行時のclause証明書を作り，任意fuel no-stuckへ接続した．built-in matcher上のvar／wild／value／tuple／and／or patternを使う，必須`fallback`付き`matchFirst`も，M4 fuel導出から`TotalCoreTyping`（共通fuel安全性が使える式型付け）を自動構成する．具体的なuser matcher literal＋wildcard armで実dispatchが0 branchを返し`fallback`へ進むclosed回帰も，入力に添字を付けたM4 matcher導出からruntime証明へ接続した．Paper 1のlist／multisetについては，公開主要導出を実call siteへ具体化して両再帰matcher本体の証明書を抽出し，実matcher値をすべてのfuel indexで型付けした．P1-L01の実cons-arm本体とP1-L02／L05の掲載式全体も値に固定して型保存・no-stuckへ接続済みである．P1-L02／L05と従来のP1-L01経路では，target／matcher値の同定と探索証明を具体的なexact実行から作る．一方，P1-L01の環境添字付き経路は，三種類の到達可能atomを記録する関係と局所保存則を使い，callback fuel 0--12の局所timeout，13の局所dispatch成功，それ以上のcallback単調性から内側探索を任意のsearch fuelで型付けし，full cons-armまで構成する．whole-search exact，再帰closure環境に対する従来の構造的`EnvironmentTyping`の証拠，明示的な有限遷移木は使わない．ただし関係と保存則は具体例に固有で，一般のM4 clause bridgeではない．これらを任意のclause body環境へ運ぶ規則，matcherを返す`fixE`全般，任意user matcher／constructorを使う`matchFirst`，存在だけが与えられた一般のM4 `Typing`が残る |
| T8 | built-in matching safety | **done** | binding／atom／state／有限DFSの型保存，局所progress，no-stuck |
| T9 | matcher closureとdispatchの型付け部品 | **done** | cursor不変条件，product/list/slot canonical forms，0／1／複数holeの復号，pattern-pattern constructor，全data-pattern形，環境連結順，任意長arm／clause列の条件付き型保存と進行 |
| T10 | user matcherの型安全性 | **in progress** | runtime側の任意長arm／clause，最終catch-allによる`.miss`排除，M4のvar／wild／value／tuple／and／or patternから実dispatchが返した枝への接続は証明済み．再帰closure専用の`TotalValueTyping`／`TotalEnvironmentTyping`も追加し，Paper 1で実際に使うlist closure，multiset closure，それらを捕捉する環境，最終的なmatcher値をM4導出から構造的に型付けした．nil入力の無条件探索に加え，実multisetの第2節`$ :: _`は，`Value.buildList values`で表せる空を含む任意の有限runtime listについて，単一fuelの成功結果とfuel単調性を種にせず，全callback／search fuelを直接分類した．空入力では探索が正常終了して回答0件，非空入力では入力順と重複を保ち，各回答が1要素だけを含む回答列になる．実第4節`$ :: $`も固定target `[1,2,3]`について，callback fuel 0--25のtimeoutと26の最初のdispatch成功を直接計算し，26以上はdispatch結果だけのfuel単調性で同じ三branchを保つことを証明した．各branchのsource patternと再帰atom型付けを同じ実dispatchに結び付け，全callback／search fuelの型保存・no-stuckを得た．whole-searchのexact成功やsearch fuel単調性は使わないが，26以上のdispatchはfuel 26の実行結果を種にする．さらに，探索で残る状態訪問回数を添字にした再帰branch型付けを追加した．user matcherのdispatchが返した実branchだけを一段小さい添字で検査するため，P1-L05の三branchと各branch内の再帰variable dispatchを，matcher値が捕捉する再帰closure環境へ従来の構造的`ValueTyping`／`EnvironmentTyping`や無制限の再帰証明書を要求せず，全callback／search fuelの型保存へ接続できる．このM4由来のfuel添字付き経路では，初期の通常環境に従来の構造的`EnvironmentTyping`が残る．別のP1-L01経路では，callerが選ぶ環境不変条件と三種類の到達可能atomの関係を使い，再帰closure環境にその証拠を要求せず，明示的な有限遷移木なしでfull cons-armまで証明する．ただしこの関係と局所保存則もM4導出から自動生成される一般bridgeやmatcher closure型付けの代替ではない．残りは任意target／clause body／field／captureを扱う一般規則と，証明書の自動構成である |
| T11 | 式評価と探索を同じfuelで証明する安全性 | **in progress** | `TotalCoreTyping`に対しては，式評価とmatching探索を同じfuelで同時に追い，`matchAll`と必須`fallback`付き`matchFirst`を含む型保存・任意fuel no-stuckまで完了した．通常lambdaが再帰matcherを捕捉する場合も扱う`TotalPlainEnvironmentSafe`を追加した．値に固定した`matchAll`規則は，target／matcher式が実際に返した値，その値に対する探索，bindingを受け取るbodyを同じfuelで合成する．P1-L01の実join cons-armではself適用，内側探索，`letE`，pair分解，`map`，`append`まで，P1-L02／L05では掲載式全体まで型保存・no-stuckを証明した．P1-L02／L05と従来のP1-L01経路は，target／matcher値の固定と探索certificateにexact実行とfuel単調性を使う．P1-L01の関係ベースの環境添字付き経路は，callback fuel 0--12の局所timeout，13の局所dispatch成功，それ以上のcallback単調性から内側探索を任意のsearch fuelで型付けし，同じfull cons-armまで構成する．whole-search exact，search fuel単調性，明示的な有限遷移木は使わない．multisetの`$ :: _`探索は空を含む任意長のruntime listについて全fuelを直接場合分けした．固定したP1-L05の`$ :: $`探索も，全callback／search fuelの型保存まで広げたが，26以上のdispatchはfuel 26の結果を単調性で運ぶ．残る中心課題は，節固有・値固有の関係と保存則を任意の型付きtargetとM4 clause導出から自動構成するT10の接続である |
| T12 | explicit-else `matchFirst` no-stuck | **in progress** | runtime armループと`TotalCoreTyping.matchFirst`では，空探索が通常armを飛ばし，全armが空なら元の環境で`fallback`を評価する型保存・no-stuckを証明済み．built-in `.something` matcherと，それで実行できるvar／wild／value／and／or pattern断片では，公開M4 `infer`成功からfuel導出・semantic solutionを取り出し，target・各arm body・fallback・patternの動的support証明と合わせて`TotalCoreTyping`を構成した．open contextでも，そのinfer導出が実際に選んだsubstitutionと明示的なruntime contextの対応をcertificateで保持し，`[mono Int]`／実行環境`[19]`の回帰をexact評価・関係的な`Eval`・任意fuel no-stuckまで接続した．さらにfinal catch-all節を1本持つ具体的なuser matcher literal＋wildcard armのclosed回帰では，公開M4 `infer = some Int`とruntime証明書を別々に構成した．runtime側は実dispatch結果を添字として保持し，成功時のbranch列が任意fuelで空であることを示すため，fuel 30で`fallback`の`7`を返すexact評価，対応する`Eval`，任意fuel no-stuckまで得た．対照となる`cons [var,wild]`回帰では，実user matcherが1件のbranchと`Int` bindingを返し，通常armの`99`がelseの`7`を抑制するruntime型保存・`Eval`・no-stuckを証明した．ただしこの二節matcherは，shape・arm coverage・final catch-allには合格する一方，Listの一般`nil`／`cons`／`join`節をそろえるroot coverageに失敗するため，どの結果型にも独立した`M4.Typing`を持たず，推論健全性から公開M4 `infer = none`が従う．したがって後者は受理済みsource橋ではなく，非空branchと静的coverageの境界を固定するruntime回帰である．任意contextの対応certificate，完全なcoverageを持つ任意user matcher／constructor arm，任意matcher producer，存在量化された一般のM4 `Typing`からの自動構成が残る |
| T13 | MNode／pattern function safety | **in progress** | MNodeは，pattern functionの内部bindingを呼出し側から分離して探索するnodeである．application，parameterの受渡し，node終了の型付けと，有限の深さ優先探索の型保存・no-stuckは証明済み．body-plan compilerは，埋め込み引数，conjunction，任意長tuple，private `.var`／`.wild`，証明付き`.value`／`.or`，証明付きnested applicationに加え，証明付きconstructorを扱う．constructor resolverは具体的なconstructor・子pattern・matcher・targetに対応する通常atomの証明を返し，外側frameを変えずprivate frameだけを証明どおり更新する．Paper 1のnil節とは別の検証用最小回帰では，patternとtargetの形はともにnilだが，final catch-all user matcherが分解を0件返すため正常な不一致となる．さらに固定した`cons [.var, .wild]`／target `cons(7, nil)`回帰では，source順の二節user matcherが先頭節を選び，`[var, something, 7]`だけを返してprivate `Int` bindingを1件増やす．public freezeから専用reducerでfuel 20のexact結果と任意search fuelのtyped・no-stuckを証明した．実`evaluationAtomReducer`についてはcallback fuel 0／1がuser-matcher atomでtimeoutし，2以上が同じsingleton branchを返すことを直接分類した．成功範囲ではapplication展開からyieldまでの固定5状態だけで専用reducerとの探索結果が任意search fuelで一致する．したがって全callback／search fuelでtyped・no-stuckとなり，callback 2以上ではsearch fuel 5でexact結果を得る．専用reducerのbranch型付け証明書はcallback 4のexact dispatchを種にしており，global reducer等式や一般のconstructor／user matcherは主張しない．残りはM4と実dispatchからresolver証明を自動生成する橋と一般checked evaluatorへの接続である |
| T14 | 全域的Source断片の5.8 | **in progress** | `TotalCoreTyping`では`matchAll`／`matchFirst`込みの任意fuel no-stuckまで到達．M4 bridge，T6，T10，T13を合成して任意の対象source導出から証明書を作る作業が残る |

T6の`RootOrdinarySourceFragment`には，式・tuple要素列・call引数列を構文だけで調べるBoolean判定器もある．
判定成功と構文certificateは正確に同値であり，判定成功と独立した公開`infer`成功を合わせて
root checkerまで一般に進む．固定回帰では，さらに構文support，signature整合性，runtime contextの型付けと合成して
runtime typingと任意fuel no-stuckを得た．判定器単独で推論成功を主張せず，任意の`infer`成功から
判定成功が従うとも主張しない．

T10のM4由来のfuel添字付き経路では，初期の通常環境に従来の構造的`EnvironmentTyping`が残る．
別の環境添字付きDFSでは，callerが環境の不変条件を与えることでこの制約を外し，
実P1-L01の再帰closure環境を扱う．この一般DFSは，明示的な局所reducer遷移の証明書から
探索安全性を作る．先行回帰では，その有限な遷移木を具体計算で構成した．

環境添字付きDFSには，fuel添字付きの未処理atom列と，callerが選んだ環境不変条件の下での
一段のreducer保存則から，探索用の状態証明を組み立てる一般生成定理も追加した．保存則は
`bindings ++ environment`の実行順でreducerを一度だけ分類し，成功時の各branchを一段小さい
探索fuelで型付けする．そのため，この一般定理は有限な遷移木や探索全体の結果を前提にしない．
さらに，各fuelで到達できるatomと，そのatomが追加するbinding型を記録する関係をcallerが選べる
形に一般化した．実P1-L01では，初期join，委譲されたvariable，built-in `something` variableの
三種類だけをこの関係に含め，その関係と一段のreducer保存則から任意callback／探索fuelの内側探索と
full cons-armの安全性を構成した．この新経路は明示的な有限遷移木に依存しない．ただし三種類の関係と
局所reducer等式はこの具体例に固有で，M4 clause導出から自動生成される一般bridgeではない．既存の
M4 workからのadapterはuser matcherのatom環境に従来の構造的`EnvironmentTyping`を残し，束縛と回答も
引き続き従来の構造的`ValueTypings`で型付けする．

T6でいう「同じclosureのcertificate」は，`let`の値を型生成した導出と，その導出から実際に選ばれた
principal closureを一組として記録する証明である．一般化後のschemeはこのclosureの代入とtargetから
作られるため，sourceの構文だけを見てもruntimeで必要な具体型は決まらない．また，ある一つの型で値を
型付けできても，それだけで一般化後の任意の具体化に使えるとは限らない．このため，syntaxだけを前提に
任意valueを受け入れる定理は偽であり，実際のclosureに結び付いたcertificateを要求する現在の形を維持する．

root closureに残る検査については，実際のelaboration結果と制約解を入力に，すべて通常の型等式として
処理されたかを確認する実行可能な検査を証明した．これは`Typing`の定義へ検査器を混ぜるものではなく，
source導出をruntime証明へ移す入口だけで用いる．matcher-to-slotなどの特殊変換が残る場合はfalseになり，
通常等式だったと仮定して先へ進むことはない．現在は上記三回帰でこの検査の成功をkernelが確認している．

さらに，この検査結果を単なる検査要求の列として扱うだけでなく，実際の関係的elaboration導出の
どのapplication／constructor引数／primitive引数／条件分岐から生じたかを保持する相互帰納的な証明へ
分解した．逆向きに，この構造的な証明から元のroot残存検査列がすべて通常等式であることも復元できる．
`elaborationResolutionsOrdinaryCheckAt`は，一つの関係的elaboration導出が生成したroot残存検査列を，
指定した代入の下で実行可能に走査する．trueになることと，同じ導出に対する構造的certificateを構成できる
ことは同値である．一方，公開root checkerについて証明したのはtrueならcertificateを作れる向きであり，
任意の`infer`成功だけからchecker成功が従うわけではない．`letE`の値側でprincipal closure内部に処理された
検査要求はroot列にもこのcertificateにも含まれず，root列にmatcher-to-slotが残ればcheckerはfalseになる．

`sourceStructuralOrdinaryCheckAt`は，同じ判定を生成後の平らな列だけでなく，元のsource式の構造を
たどって行う実行可能checkerである．成功した同一のelaborationから各節点の型とsupplyを再取得し，
applicationが追加した検査要求をその場で確認する．一つの成功したelaborationと一つの固定した代入について，
この構造走査の結果がroot残存検査列の全件検査と等しいことを証明した．source構文だけから通常変換を保証する
定理でも，任意の`infer`成功からchecker成功を導く定理でもない．`letE`の値側の検査要求はclosure内部で
処理されroot列へ出ないため，構造走査の対象外である．新しい混合回帰は公開`infer`からruntime typingと
任意fuel no-stuckへ進むが，構文support，context対応，初期環境の型付けは回帰固有の証明として残る．

Paper 1の実closed multiset環境は，従来の`EnvironmentTyping`では型付けできない．これは未証明な
だけではなく，`closedMultisetMatcherEnvironment_not_environmentTyping`で不可能だと証明している．
捕捉されたlist／multiset再帰closureの本体がmatcher literalであり，arm bodyに`matchAll`を含むのに対し，
従来の`ValueTyping.recursiveClosure`が古い`RuntimeTyping`だけを要求するためである．

この問題に対して，再帰closure本体も扱う`TotalValueTyping`／`TotalEnvironmentTyping`を別に定義した．
現在は，Paper 1で実際に評価されるlist closure，multiset closure，3値からなるcaptured environment，
closed multiset matcher値を，公開M4導出から構造的に型付けできる．さらに同じ主要導出と具体化代入から，
list／multiset双方の再帰matcher本体を正確なcaptured contextで型付けする証明書を抽出し，実closed matcher値を
すべてのfuel indexで型付けした．この証明書を値に固定した`matchAll`規則へ渡し，P1-L02／L05の掲載式全体を
型保存・no-stuckへ接続している．ただしtarget／matcher値の同定と探索certificateは具体的なexact実行を
fuel単調性で広げたものであり，任意のM4 clauseやconstructor branchを扱う一般定理ではない．本体先頭の
matcher literalだけを評価する一般`TotalEnvironmentSafe`も別に残しており，これはclause選択やarm body評価を
始めない．nil入力はbindingも再帰atomも返さない実dispatchを直接検証した無条件の全fuel no-stuckである．
また，実7節matcherの第2節`$ :: _`については，`Value.buildList values`で作られる空を含む
任意長の有限runtime listへ一般化した．nil節のmiss，第2節のtimeoutまたは成功，後続探索を
全fuelで直接分類する．空入力は回答0件で正常終了し，非空入力は順序と重複を保つ．この証明は
固定fuelの成功結果をfuel単調性で広げない．ただし実第2節に固定した証明であり，静的本体証明と
組み合わせた回帰用certificateも，一般のtargetやconstructor節に対するsource-to-runtime定理ではない．

実第4節`$ :: $`については，P1-L05のtarget `[1,2,3]`と三つのbranchに固定し，callback fuel
0--25のtimeoutと26の最初のdispatch成功を直接計算した．26以上では，評価callbackを一段増やしても
完了済みdispatch結果が変わらない定理だけを使って，同じbranchを保つ．各branchの先頭の整数と，
残りのlistを実第7節catch-allへ委譲する再帰atomを型付けし，任意のcallback／search fuelで探索が
型を保存して`stuck`にならないことを得た．whole-searchの固定成功やsearch fuel単調性には依存しないが，
26以上のdispatchにはfuel 26の具体的な成功を種として使う．任意targetやM4 clauseへ広げた一般定理ではない．

再帰matcherを捕捉する通常lambdaについては，従来の値型付けを無理に変更せず，証明専用の
`TotalPlainEnvironmentSafe`を追加した．lambda，application，`letE`，`map`，tuple，List constructor，
pair projection，`append`，`matchAll`をこの層で組み合わせられる．さらに，通常環境の型付けを
callerが選ぶ不変条件に置き換え，各reducer遷移と後続状態だけを一段小さい探索fuelで検査する
環境添字付きDFSを追加した．Paper 1の`listJoinConsBody`では，再帰closureを含む実cons-arm環境を
従来の構造的`EnvironmentTyping`の証拠を要求せず，callback fuel 0--12の局所timeout，13の局所dispatch成功，それ以上の
callback単調性と後続atomの局所遷移から，全callback／探索fuelの内側`matchAll`を証明した．
その後の`letE`／pair分解／`map`／`append`も同じ新しい前提から合成し，arm本体全体の型保存・no-stuckまで
探索全体のexact結果なしで得た．新しい関係ベースの生成定理により，この具体例も明示的な有限遷移木を
使わずに同じ結論へ到達する．ただし三種類のatom関係と局所reducer保存則は具体例に固有で，M4導出から
自動構成する一般橋ではない．

環境添字付きDFSの一般層では，固定環境だけでなく，探索中に蓄積するbindingと完了したanswerにも
callerが別の関係を選べるようにした．従来の`ValueTypings`を使う入口はその特殊化である．さらに，
探索fuelと成功answerに残す論理indexを分けたDFS定理を追加した．状態証明は探索で訪問しうる状態数に
応じた入力indexを予約し，完了時には指定した残余indexのanswerを返す．callbackがより多くのindexを
必要とする場合は，callerが選ぶ関係にその余裕を含める．この定理は探索全体の結果を前提にせず，
各reducer呼出しのtimeoutまたは直後のsuccessorだけを一段小さい探索fuelで要求する．最小回帰では，
Paper 1の実list再帰closureを固定環境と完了answerの両方に置き，fuel付き環境関係では型付けできる一方，
従来の`EnvironmentTyping`と`ValueTypings`では型付けできないことを同時に固定した．これは探索結果側の
関係を一般化した実証であるが，任意のuser matcherについて局所reducer保存則をM4導出から生成する橋や，
式評価全体の`commonFuelSafety` companion theoremを完成させたものではない．

M4の実dispatchと二index DFSの間には，callerが選ぶatom関係を使うuser-matcher bridgeも追加した．実際の
`dispatchMatcherClauses`がtimeoutまたはhitを返す証明は，返された各branchのpattern列と，そのbranchを
一段小さい探索fuelで構造的に型付けする証拠を同じ実行結果に結び付ける．一段のreducer保存則は実runtime環境での
built-in miss，直後に追加されるbinding，後続branchだけを扱い，探索全体の結果や式評価全体の安全性を前提にしない．
Paper 1の実multiset variable節では，再帰list closureをatom環境・target・最終answerに置き，user dispatch，
委譲された`.something` atom，yieldの三状態をこのbridgeから型付けした．成功answerはfuel付き関係で型付けできる一方，
従来の構造的`EnvironmentTyping`／`ValueTypings`では型付けできない．探索のexact結果は独立した回帰であり，
二index安全性証明には使わない．従来の構造的M4 branch-workでは同じdelegated atomを正の探索indexで型付けできないことも
残している．さらに，M4のpattern elaborationが決めたbinding型とpattern順を，有限のatom義務を介して二index branch-workへ
運ぶproducerを追加した．この回帰では独立した`.var` elaborationとその解から，再帰list closureの関数型
`recursiveClosureType`をbinding型として導出し，手組みのdispatch certificateを置き換えた．ただしcallerのatom関係，
一段のreducer保存則，実dispatch等式は具体例ごとの証明であり，
完全なM4 matcher-clause導出からそれらを自動生成する一般producerは未完である．

`MatcherSafety`のembedded evaluator契約は「必ず収束する」仮定ではない．型付き式の評価が
`timeout`になるか，型の付いた値を返すことを要求する．T11はこの契約を`TotalCoreTyping`について
内部の共通fuel帰納で放電した．user matcherが生成する実branchには，残る探索回数を指標にした
型付けまで拡張した．残る問題は，任意のM4導出からこの証明書を自動構成し，
再帰closureを含む通常環境へ運ぶ一般接続である．

## 論文の結果5.1--5.8との対応

5.3は論文では系だが，番号順に記録する．一般の`Typing`結果は主要型の具体化も含むため，5.4は
任意の型付け結果同士ではなく，主要性を満たす代表型同士の一意性として定式化する．

| 番号 | 新体系での意味 | 状態 | 現在の公開入口／残り |
|---|---|---|---|
| 5.1 | 公開`infer`成功なら独立した`Typing`がある | **done** | M1，M2--M3，M4の公開健全性を証明．M4入口は`M4.infer_success_typing` |
| 5.2 | `Typing`があれば公開`infer`が成功する | **done** | M4入口はcoherenceとreplayから得た`M4.Typing.infer_isSome` |
| 5.3 | `Typing`の存在と推論成功が同値で，受理を決定できる | **done** | `M4.typable_iff_infer_isSome`と`M4.typableDecidable` |
| 5.4 | 二つの主要な代表型が有限な変数名変更を除いて一致する | **done** | `M4.PrincipalTyping.finiteRenamingEq` |
| 5.5 | 公開`infer`結果がすべての`Typing`結果の最も一般的な型である | **done** | 成功結果からの`M4.infer_success_principalResult`と，主要型付けを前提に成功結果を得る`M4.infer_principalResult` |
| 5.6 | 静的型付けを状態を含まないruntime typingへ移す | **in progress** | runtimeと整合する任意のfrozen signatureに対するsource橋，共有M2--M3構文，通常のM4 `fixE`，解決済みM4 matcher clause，`.something` matcherで実行できる直接pattern断片の必須`fallback`付き`matchFirst`からruntime証明書への橋は完了．`matchFirst`はclosed contextに加え，公開infer導出が選んだsubstitutionと実行時の型の並びを明示的に対応付けたopen contextを扱い，具体的なuser matcher literalがwildcardへ0 branchを返すclosed回帰も入力添字付きM4導出からruntimeへ接続した．source多相`let`は，実際のvalue elaborationと同じprincipal closureに対するcertificateがあれば任意valueを扱う．実elaborationに添字を付けた構造的certificateをapplication，tuple，nested let，複数引数constructor／primitive／`ifE`まで定義し，固定導出と代入に対する実行可能checkerからcertificateを構成する橋も追加した．引数位置をliteral／lambdaに限定する明示的なsource断片では，構文だけを読むBoolean判定器と構文certificateが正確に同値である．判定成功と独立したpublic infer成功からroot checkerまで一般に接続し，runtime typingと任意fuel no-stuckまでは回帰固有の構文support，signature整合性，runtime context型付けと合成した．任意の`infer`成功からchecker成功を導くわけではない．context対応certificateの自動構成，matcher-rootの`fixE`，引数形の一般化，任意user matcher／constructorを含む再帰的M4式が残る |
| 5.7 | 型付き評価・matching・有限探索が型を保存し，局所的に進む | **in progress** | core，built-in matching，`TotalCoreTyping`の共通fuel安全性，再帰matcherの実dispatchを使う最小回帰まで進んだ．Paper 1の実再帰closureと環境はM4導出から型付け済みである．値に固定した`matchAll`規則により，P1-L01のtop-level掲載式と実join cons-arm本体，P1-L02／L05の掲載式全体を全fuel型保存／no-stuckへ統合した．P1-L01の新しい環境添字付き経路は実clause-body環境をcaller不変条件で保持し，三種類の到達可能atomの関係と局所保存則から内側探索を全callback／search fuelで型付けし，明示的な有限遷移木やwhole-search exactなしでfull cons-armまで証明する．探索一般層は固定環境と完了answerの関係を独立に選べるようになり，探索fuelとanswerの論理indexを分けたDFS定理も持つ．実list再帰closureを環境とanswerの双方に置く回帰は，従来の構造的関係を経由せずfuel付きanswerを返す．さらに，caller指定のatom関係と構造的branch-workを実M4 dispatchへ結ぶbridgeにより，実multiset variable節のuser dispatch，delegated `.something` atom，yieldからなる三状態探索も，従来の環境／値型付けを使わず成功answerまで型付けした．exact探索結果は独立した回帰である．二index探索を`.matchAll`式全体のfuel付き結果安全性へ上げる一般合成定理も追加し，実list再帰closure回帰では探索answerと式結果の論理indexを分離した．ただしatom関係・局所reducer保存則・初期state証明はfixture固有で，M4 clause導出からの一般producerは未完である．具体的なtarget／matcher値の同定と多くの探索certificateはexact実行から作るが，multisetの実`$ :: _`節では任意の有限runtime listに対して全fuelを直接分類し，実`$ :: $`節では固定targetの全callback／search fuelをdispatch単調性と，残る探索状態数を添字にした再帰atom型付けから証明した．このP1-L05のM4由来fuel添字付き経路では，actual三branchと内側の同じmatcherへのvariable dispatchを直接構成し，matcherが捕捉する再帰closureに従来の構造的`EnvironmentTyping`の証拠を要求しない一方，初期の通常環境はその関係で型付けされており，一般のM4 bridgeでもない．再帰matcherの任意target・clause環境へ運ぶ接続が残る．MNodeはouter/privateの二frameでtuple／conjunction，private variable，証明付きvalue/or，証明付きnested applicationを同時に扱う．constructorは，固定nilの空分解と，固定`cons [.var,.wild]`の非空分解・private binding追加まで証明付きresolverで扱う．後者は実評価器をcallback 0／1のtimeoutと2以上の同一branchに分け，全callback／search fuelの型保存まで接続した．任意constructor／user matcher，resolver証明の自動生成が残る |
| 5.8 | 全域的断片の型付きclosed programは任意fuelで`stuck`にならない | **in progress** | `TotalCoreTyping`では`matchAll`と必須`else`付き`matchFirst`を含めて完了．P1-L01／L02／L05は値に固定したruntime合成による型保存／no-stuck証明を持つ．target／matcher評価と多くの探索は一度のexact成功からfuel単調性で広げるfixture固有の証明である．ただしP1-L01の関係ベースの環境添字付き経路は，実再帰closure環境に従来の構造的`EnvironmentTyping`の証拠を要求せず，callback 0--12のtimeout，13のdispatch成功，それ以上のcallback単調性からfull cons-armの任意fuel no-stuckをwhole-search exactや明示的な有限遷移木なしで導く．一方，Paper 1のnil constructorと実`$ :: _`節の任意有限runtime listは，固定成功を種にせず全fuelを直接解析した．実`$ :: $`節の固定targetも全callback／search fuelでno-stuckであり，残る探索状態数を添字にした証明により，再帰closureにその環境型付けや無制限の再帰証明書を要求しない．ただし26以上の外側dispatchはfuel 26の成功から単調性で運ぶ．MNodeの固定`cons` constructor回帰は実評価器でも全callback／search fuelでno-stuckである．ただし成功範囲の型付けはcallback 4の具体dispatchから得た同一branch証明書を使い，一般constructorには広げない．任意のM4 source導出からT6／T10／T13の証明書を自動構成し，任意targetと再帰closureを含むclause-body環境を覆う一般定理が残る |

5.6--5.8が最終的に満たすinterfaceは，`M5CompletionArchitecture.lean`の
`ConditionalCompletionSchema`として機械的に固定した．これは，実際の
`M4.PrincipalTypingDerivation`に添字を付けたruntime certificate，source contextとruntime contextの
対応，主要型から結果型への具体化，式評価の型保存，source由来のmatching taskに対する探索型保存，
closed programのno-stuckを一つに束ねる．式評価fuel，matcher callback fuel，探索fuel，論理的な
安全性indexは別々の引数であり，入力側に必要なindexを明示的に計算する．matching側では，runtime
certificateと，その評価から生じたtaskであることの証拠から探索certificateを作る
`MatchingStateErasure`を要求し，無関係な具体回帰を5.7のsource bridgeとして数えない．

通常式用のspecializationは，再帰的にMNodeを含まない式を`evalFuel`で評価し，探索taskのpatternにも
MNodeがないことを証拠として保持して，実際の`searchPatternFuel`を使うlaneだけを固定する．
pattern functionを含む全M4には，frozen runtime定義と
`PatternFunctionDefinitions.Agree`，checked MNode evaluatorを保持する別のlaneが必要である．また，
現段階のcertificate family，context relation，search originは抽象parameterであり，全M4からそれらを
構成する具体的な帰納的certificateは未完である．したがってこのschema自体を5.6--5.8の完成証拠とは
数えず，今後の一般定理が満たす型と依存関係を固定する回帰として使う．

`M4CanonicalCertificateTransport.lean`では，closed programについて，任意に選んだ
`M4.PrincipalTypingDerivation`を，公開`infer`の成功から選んだ代表導出へ，
`FullM2PairCoherence`とclosureの対応証拠を保ったまま結び付ける．runtime certificateの輸送は
無条件ではなく，certificate familyがこの対応を尊重する
`ClosedRuntimeCertificateRespectsCoherence`を明示的な前提とする．open contextではruntime型列の
輸送，多相contextではより強いcontext関係が別に必要であり，ここでは主張しない．

既存の`TotalCoreTyping.commonFuelSafety`は，現在の`type-pm-mech2`内で先に定義した構造的な
`EnvironmentTyping`を入力に取り，成功結果も`ValueTyping`を使う`TypedResult`で返す．これは別の
リポジトリ`type-pm-mech`を参照するという意味ではない．入力だけを`FuelEnvironmentSafe`へ替えても
結果側が対応しないため，環境・結果・探索の関係を同時に一般化する必要がある．さらに高階値の
安全性indexは関数適用で減るので，実行fuelと同じ自然数をそのまま出力indexにすることも仮定しない．

`TwoIndexMatchAllSafety.lean`は，target／matcherのfuel付き評価，二indexの初期探索state証明，bindingを受け取る
bodyの安全性を合成し，`.matchAll`式全体の`FuelResultSafe`を返す．探索answerのindexと最終結果のindexは独立で，
構造的`EnvironmentTyping`／`ValueTyping`や完了探索結果の等式を要求しない．ただし初期state証明は，実reducerが返す
各後続stateの局所安全性を再帰的に含む．実list再帰closureを環境・target・bindingに置く回帰ではこの経路を
実行fuel 2，answer index 2，result index 1で実行し，別証明のexact結果と構造的型付け不能性も固定した．
これは探索から式評価への合成規則であり，M4導出から初期state証明や局所reducer保存則を自動生成する最終
`commonFuelSafety` companionではない．

5.7の「初期の通常環境に従来の構造的`EnvironmentTyping`が残る」という制限は，M4由来のfuel添字付き経路のものである．
環境添字付きDFSではP1-L01の実clause-body環境にその証拠を要求せず，全callback／探索fuelの内側join探索を
型付けた．その証明を周囲の`letE`／pair分解／`map`／`append`へ渡し，full cons-armのno-stuckまで合成した．
この新経路はwhole-search exactを使わないが，callback 0--12の局所timeoutと13の局所dispatch成功を直接計算し，
それ以上はcallback単調性を使う．現在の三種類のatom関係と局所保存則は具体例に固有であり，M4導出から
それらを自動構成する定理は未完である．

5.6は以前の推論状態表現を後から消す定理ではない．新体系には初めから状態を含まない`Typing`がある
ため，sourceの型付け導出をruntime value・環境・matching stateの型付けへ移す構造的な定理として
再定式化する．

## Paper 1回帰

### code listing inventory

「静的」は公開`infer`と独立`Typing`を表す．

| ID | 掲載内容 | source | 静的 | 主な根拠／残り |
|---|---|---|---|---|
| P1-L01 | listとmultisetの`$x :: $xs` | done | done | listのjoin分解を使う掲載`matchAll`式について，任意の開始supply用に巨大な生成blockを複製せず，公開`infer`のexact結果と`M4.Typing`を固定済み |
| P1-L02 | `$x :: #(x + 1) :: _` | done | done | 7節multisetと入れ子のlist matcherを開始supplyの変換で再利用し，掲載式の公開`infer` exact結果と`M4.Typing`を固定済み |
| P1-L03 | List pattern宣言 | done | done | 3 schemeとPaper 1 signatureの整合性を検証済み |
| P1-L04 | 7節`multiset`定義 | done | done | closed wrapperと空contextでのopen版拒否に加え，source-defined list matcherを多相library bindingとして持つcontextでopen本体を直接推論し，exact結果と`M4.Typing`を固定済み |
| P1-L05 | 直接のmultiset `matchAll` | done | done | 7節matcher，入れ子のlist matcher，closed wrapperを開始supplyの変換で再利用し，掲載式の公開`infer` exact結果と`M4.Typing`を固定済み |
| P1-L06 | `unconsWith m target` | done | done | slot要求を持つ主要型と`M4.Typing`を固定済み |
| P1-L07 | `unconsWith`の正負呼出し | done | done | bare `something`拒否に加え，多相library bindingからの`multiset something`と，正しい`List Int` slotを使う`unconsWith`呼出しのexact推論／`M4.Typing`を固定済み |
| P1-L08 | pair destructuringと共有lambda domain | done | done | `pairFirst`／`pairSecond`の多相scheme，静的型付け，runtime型保存・no-stuckを証明し，旧`matchFirst` tuple helperを全域的なpair分解へ置換 |
| P1-L09 | 明示的`let` | done | done | M2公開推論と`Source.Typing`を固定済み |
| P1-L10 | value pattern内の`x ++ [1]` | done | done | Integer/List不一致による宣言的拒否 |
| P1-L11 | `$x :: #x` | done | done | occurs checkによる宣言的拒否 |
| P1-L12 | `#x :: $x :: _` | done | done | 左で未束縛の参照を宣言的に拒否 |
| P1-L13 | `something`のvariable／cons | done | done | 掲載AST `[1,2,3] / $x -> x`を`List (List Int)`として公開`infer` exact結果と`M4.Typing`へ接続し，掲載cons AST `$x :: $xs -> (x,xs)`はcapability不足として宣言的に拒否 |
| P1-L14 | `matchAll 5 ... #1 -> 1` | done | done | 掲載ASTそのものを`List Int`としてexact推論し，`M4.Typing`へ接続済み |
| P1-L15 | Bool対象とinteger matcher | done | done | target型不一致による宣言的拒否 |

実行を主張するlistingだけを次に分ける．「実行」はexact `evalFuel`，「関係」は`Eval`または
対応する独立関係，「安全」はsource-to-runtime橋を含む任意fuel no-stuckを表す．

| ID | 実行 | 関係 | 安全 | 主な根拠／残り |
|---|---|---|---|---|
| P1-L01 | done | done | in progress | listの全join分割をsource順で確認し，実4-clause dispatchと型付き探索を固定した．実cons-arm環境ではrecursive self適用，内側`matchAll`，`letE`，pair分解，`map`，`append`を一つの全fuel型保存・no-stuck証明へ合成した．新しい環境添字付き経路は，探索全体のexact結果や，再帰closure環境に対する従来の構造的環境型付けの証拠を使わない．関係ベースの生成定理へも移行し，明示的な有限遷移木なしで同じfull cons-armまで証明した．ただし三種類のatom関係とcallback 13の局所dispatchを含む保存則はこの具体例に固有で，一般のM4導出から自動生成する橋が残る |
| P1-L02 | done | done | in progress | `[1,2,5,6] → [1,5]`と，実7-clause dispatchが完全な`$x :: #(x+1) :: _` patternを保持することを固定した．M4由来の再帰matcher本体証明と値に固定した`matchAll`規則により，掲載式全体の全fuel型保存・no-stuckも証明済み．target／matcher値の同定と探索はexact実行から作るため，一般のsource-to-runtime橋は未完 |
| P1-L04 | done | done | in progress | `listMatcherDefinition`，closed multiset constructor，`multiset something`の実matcher値生成を一つの実行pipelineとして固定した．公開M4主要導出から，exactに具体化されたlist／multiset matcher本体の証明書と実closed matcher値の全fuel型付けも構成済み．pipeline全体はなお具体的なexact実行に依存する．nil constructorは実dispatchが返す唯一の枝`[[]]`を固定し，全callback／search fuelで無条件にno-stuck．実第2節`$ :: _`は，`Value.buildList values`で作られた任意の有限runtime listについて，空入力なら探索が正常終了して回答0件，非空入力なら入力順・重複を保ち，各回答が1要素だけを含む回答列になることを，全callback／search fuelで直接証明した．固定fuelの成功やfuel単調性には依存しないが，実第2節に固定した証明であり，任意constructor節と再帰tailの一般橋は残る |
| P1-L05 | done | done | in progress | 三要素consの3結果をsource順で確認し，実7-clause dispatchが各候補で元の二つの`.var` patternを保持することを固定した．M4由来の再帰matcher本体証明と値に固定した`matchAll`規則により，掲載式全体の全fuel型保存・no-stuckも証明済み．さらに同じ固定targetと三branchでは，callback fuel 0--25のtimeoutと26の最初のhitを直接計算し，26以上はdispatchだけのcallback-fuel単調性で同じbranchを保つ．各branchの再帰atom型付けと組み合わせ，全callback／search fuelの型保存・no-stuckを得た．whole-searchのexact成功やsearch fuel単調性は使わないが，任意targetやM4 clauseに対する一般定理ではない |
| P1-L13 | done | done | done | `paperSomethingVariable`が掲載AST `[1,2,3] / $x -> x`そのものであることを固定し，公開`infer` exact結果`List (List Int)`，`M4.Typing`，同じM4 variable-pattern導出からの`TotalCoreTyping`を構成した．exact評価`[[1,2,3]]`を独立`Eval`へ接続し，任意fuel no-stuckも証明済み |
| P1-L14 | done | done | done | `paperIntegerValueMismatch`を掲載AST `5 / #1 -> 1`そのものに揃え，M4のvalue-pattern導出から`TotalCoreTyping`を構成した．正常な不一致として空Listを返すexact評価を独立`Eval`へ接続し，任意fuel no-stuckも証明済み |

論文listingを追加・削除・変更するときは，このinventoryと対応するsource／runtime回帰を同じ変更で
更新する．正確な結果の順序と重複も等式の一部として扱う．

### 7節multisetの実装境界

`multiset`は次の順序でsource定義として検証する．

1. M3でList，pattern宣言，使用するprimitiveの型を定義する．完了済み．
2. M4で7節をmatcher literalとして型付けし，clause順とhole要求を検査する．完了済み．
3. M5で同じ定義を評価し，nil，head-only，value-cons，general-cons，join，whole-value，
   catch-allを個別に固定する．exact評価，関係的導出，任意fuel no-stuckは完了済み．このうちhead-onlyは，
   単一fuelの成功とfuel単調性ではなく，実dispatchと探索の全fuelを直接分類した証明も持つ．general-consは
   固定target `[1,2,3]`について全callback／search fuelの型保存を持つが，26以上のdispatchはfuel 26の
   実行結果を単調性で運ぶ具体例固有の証明である．
4. 静的型付けとruntime typingを一般定理で接続し，各closed利用例のno-stuckを得る．未完了．

joinは末尾の分割を再帰的に列挙し，各段階で現在の要素を右側へ置く結果を，左側へ置く結果より
先に返す．性能上の理由で順序を変える場合は，この説明，回帰，論文を同じ変更で更新する．

## 次に進める作業

依存順に並べると，現在の作業列は次のとおりである．

1. `M5CompletionArchitecture`の条件付きschemaに対して，評価結果や探索結果そのものを内部へ埋め込まない
   具体的な帰納的runtime certificateを下位moduleに定義する．通常式laneでは，実
   `M4.PrincipalTypingDerivation`，context対応，型の具体化，MNode-freeなmatching taskの由来をこの
   certificateから作り，5.6／5.7／5.8の各fieldと連言全体を満たす最初のinstanceを置く．
2. `TotalCoreTyping.commonFuelSafety`を壊して前提を一つだけ交換するのではなく，環境・成功値・探索回答の
   関係とindex遷移を同時にparameter化した companion theoremを作る．探索についてはcaller指定の環境・answer
   関係と二つのindexを持つDFS定理，caller指定のatom関係からbranch-workを構造的に組み立てる定理，実M4 dispatchを
   その局所certificateへ変換するbridgeまで追加済みである．実multiset variable節は，再帰closureを環境・target・
   成功answerに置く三状態探索までこの経路で型付けした．さらにM4のpattern elaborationからbinding型・pattern順・
   bounded branch-workを生成するproducerを追加し，同回帰の手組みdispatch certificateを置換した．二index探索を
   `.matchAll`式全体のfuel付き結果安全性へ上げる一般合成定理も追加済みである．次は，fixture固有に与えている
   atom関係・一段のevaluator／dispatcher保存・実dispatch等式と初期state証明を，完全なM4 matcher-clause導出から
   生成する．
3. closed contextでは，任意に選んだM4主要導出を，`FullM4Coherence`／`FullM4ExecutableReplay`で
   公開`infer`から選んだ代表導出へ対応付ける定理と，coherenceを尊重するcertificate familyをその導出へ
   輸送する条件付き定理を`M4CanonicalCertificateTransport`に追加済みである．次は具体的な帰納的
   certificateについて`ClosedRuntimeCertificateRespectsCoherence`を証明する．open contextではruntime型列，
   多相contextではcontext関係も同時に輸送し，多相`letE`，matcherを返す`fixE`，matcher literal，
   `matchAll`，user matcher／constructorを含む`matchFirst`へ広げる．
4. `FrozenSignatureRuntimeCompatible`の追加，Paper 1証拠のfixture分離，一般runtime橋のparameter化まで
   完了した．次は，P1-L02／L05のhead-only／general-cons探索で得たbranch型付けを，field，capture，
   再帰tailを持つ任意のM4 constructor branchへ運ぶ．
5. callback fuelについては，隣接fuel間の近似，閾値でのexact成功，閾値以上という三つの前提から，同じ成功を
   任意の後続fuelへ運ぶ共通補題を追加し，P1-L01の閾値13，委譲variableの閾値2，P1-L05の閾値26へ適用した．
   残るtimeout側の直接計算や探索fuelの帰納は別の証明義務なので，全ての`rfl`を同じ理由で置換しない．
6. MNode laneでは，frozen definitionsと`PatternFunctionDefinitions.Agree`を保持したchecked evaluator版の
   completion schemaを具体化する．既存の二frame compilerと固定constructor回帰を，任意constructor／target，
   user matcher branch，resolver証明のM4由来生成へ広げる．
7. 以上を合成し，Paper 1 inventoryのL01／L02／L04／L05について，sourceの型付けから得られる
   任意fuel no-stuckを完成させる．

M0--M4，M4の5.1--5.5，公開freeze checkerは，必須`fallback`付き`matchFirst`を含めて確定している．
静的レーンと動的レーンで独立に進められる補題は並行して実装し，型安全性5.6--5.8を確定するのは
上記1--6の完了後とする．
DM3とPF6はこの作業列を止めず，「ユーザー判断が必要になる項目」に書いた論文上の判断時点まで
将来課題として保持する．

## 完了と主張する条件

M1断片の`Typing`を定義しただけでは，Type-PM全体からterminal auditを除けたとは主張しない．
次をすべて追加公理なしで証明した時点で，プロジェクト全体を完了とする．

- M0--M4の全対象構文に対する独立した`Typing`と，公開`infer`の健全性，完全性，受理同値，
  主要性，主要な代表型の一意性．
- M5の静的型付けからruntime typingへの橋，型保存，局所progress，全域的断片に対する
  任意fuelのno-stuck．静的に受理する`matchFirst`は通常armを1本以上持ち，その全armの探索結果が
  空でも必須`fallback`へ進む．target／matcherの先行評価，元の環境でのfallback評価，型保存を
  含めて証明する．
- 公開freeze checkerが受理したsource-defined pattern functionについて，独立した実行関係と
  型安全性．全具体化でのinterface主要性PF6は含めない．
- このREADMEのPaper 1 inventoryで必要とした各段階．
- `TypePM/AxiomAudit.lean`の強制監査とCIを含む全build．

一般の停止性，相互`letrec`，旧実装との後方互換性は現行の完了条件に含めない．bounded DFSの
5.6--5.8と，公平な`matchAll`の有限prefixに対する型安全性・有限到達可能な成功の公平性は別の
完了条件として管理する．後者を式評価の遅延collectionへ統合することはPaper 3の対象とし，現行の
有限DFS定理をその完成証拠とは数えない．DM一般対応と全具体化のpattern-function主要性は，論文の
最終主張へ含めると決めた場合に完了条件へ昇格する．

## 主なファイル

| 目的 | 入口 |
|---|---|
| M1公開推論と型付け | [Inference.lean](TypePM/Inference.lean)，[InferenceCompleteness.lean](TypePM/InferenceCompleteness.lean)，[Principality.lean](TypePM/Principality.lean) |
| M2--M3完全性・主要性 | [FullM2Completion.lean](TypePM/Source/FullM2Completion.lean) |
| M4実行可能／関係的elaboration | [M4RecursiveElaboration.lean](TypePM/Source/M4RecursiveElaboration.lean) |
| M4 matcher形状とpatternの関係的回帰 | [MatcherPattern.lean](TypePM/Source/MatcherPattern.lean)，[MatcherClauseShape.lean](TypePM/Source/MatcherClauseShape.lean)，[M4MatcherPatternRegression.lean](TypePM/Source/M4MatcherPatternRegression.lean)，[M4PatternTypingRegression.lean](TypePM/Source/M4PatternTypingRegression.lean)，[M4OrPatternRelationalRegression.lean](TypePM/Source/M4OrPatternRelationalRegression.lean) |
| M4 fuelとsupport | [M4ElaborationFuelMonotonicity.lean](TypePM/Source/M4ElaborationFuelMonotonicity.lean)，[M4SupplySupport.lean](TypePM/Source/M4SupplySupport.lean) |
| M4完全性の境界と公開系 | [M4CompletenessArchitecture.lean](TypePM/Source/M4CompletenessArchitecture.lean)，[M4StructuralReplay.lean](TypePM/Source/M4StructuralReplay.lean)，[M4PatternReplay.lean](TypePM/Source/M4PatternReplay.lean)，[M4MatchAllReplay.lean](TypePM/Source/M4MatchAllReplay.lean)，[M4MatchFirstReplay.lean](TypePM/Source/M4MatchFirstReplay.lean)，[M4CompletionConsequences.lean](TypePM/Source/M4CompletionConsequences.lean)，[FullM4Completion.lean](TypePM/Source/FullM4Completion.lean) |
| M4からruntimeへの橋 | [M4RuntimeBridge.lean](TypePM/Source/M4RuntimeBridge.lean)，[M4UserMatcherRuntimeBridge.lean](TypePM/Source/M4UserMatcherRuntimeBridge.lean) |
| M4 user matcherの`matchFirst`具体回帰 | [M4RecursiveMatcherRuntimeInputBridge.lean](TypePM/Source/M4RecursiveMatcherRuntimeInputBridge.lean)，[M4UserMatcherMatchFirstRegression.lean](TypePM/Source/M4UserMatcherMatchFirstRegression.lean)，[M4UserMatcherMatchFirstConsRegression.lean](TypePM/Source/M4UserMatcherMatchFirstConsRegression.lean) |
| M4 renaming／coherence | [M4FreshRenamingTransport.lean](TypePM/Source/M4FreshRenamingTransport.lean)，[M4OrdinaryCoherence.lean](TypePM/Source/M4OrdinaryCoherence.lean)，[M4PatternCoherence.lean](TypePM/Source/M4PatternCoherence.lean)，[M4MatcherCoherence.lean](TypePM/Source/M4MatcherCoherence.lean)，[M4MatchAllCoherence.lean](TypePM/Source/M4MatchAllCoherence.lean)，[M4MatchFirstCoherence.lean](TypePM/Source/M4MatchFirstCoherence.lean)，[M4FixCoherence.lean](TypePM/Source/M4FixCoherence.lean)，[M4LetCoherence.lean](TypePM/Source/M4LetCoherence.lean) |
| Paper 1 source | [Paper1Programs.lean](TypePM/Source/Paper1Programs.lean) |
| Paper 1 exact静的回帰 | [M4Paper1ListExactRegression.lean](TypePM/Source/M4Paper1ListExactRegression.lean)，[M4Paper1ClosedMultisetExactRegression.lean](TypePM/Source/M4Paper1ClosedMultisetExactRegression.lean) |
| 評価とmatching | [Evaluation.lean](TypePM/Runtime/Evaluation.lean)，[EvalFuel.lean](TypePM/Runtime/EvalFuel.lean)，[EvaluationStuckMonotonicity.lean](TypePM/Runtime/EvaluationStuckMonotonicity.lean)，[MatchingState.lean](TypePM/Runtime/MatchingState.lean)，[MatchingSearch.lean](TypePM/Runtime/MatchingSearch.lean) |
| Paper 1の全fuel実行回帰 | [Paper1NeverStuckRegression.lean](TypePM/Runtime/Paper1NeverStuckRegression.lean)，[M4Paper1MatcherLiteralEvaluationSafetyRegression.lean](TypePM/Source/M4Paper1MatcherLiteralEvaluationSafetyRegression.lean) |
| Paper 1 list joinの実dispatchと型付き探索 | [M4Paper1ListJoinSearchSafety.lean](TypePM/Source/M4Paper1ListJoinSearchSafety.lean) |
| Paper 1 multisetの実dispatchと型付き探索 | [M4Paper1MultisetSearchSafety.lean](TypePM/Source/M4Paper1MultisetSearchSafety.lean) |
| runtime typingと安全性 | [RuntimeTyping.lean](TypePM/RuntimeTyping.lean)，[CoreSafety.lean](TypePM/CoreSafety.lean)，[MatcherSafety.lean](TypePM/MatcherSafety.lean)，[CommonFuelSafety.lean](TypePM/CommonFuelSafety.lean)，[NoStuck.lean](TypePM/NoStuck.lean) |
| frozen signatureとruntime constructorの整合性 | [FrozenSignatureRuntimeCompatibility.lean](TypePM/Source/FrozenSignatureRuntimeCompatibility.lean)，[Paper1FrozenSignatureRuntimeCompatibility.lean](TypePM/Source/Paper1FrozenSignatureRuntimeCompatibility.lean) |
| M5の条件付き完成interface | [M5CompletionArchitecture.lean](TypePM/Source/M5CompletionArchitecture.lean) |
| M4主要導出から公開推論の代表導出へのclosed certificate輸送 | [M4CanonicalCertificateTransport.lean](TypePM/Source/M4CanonicalCertificateTransport.lean) |
| 再帰matcherを捕捉する通常lambdaの安全性 | [TotalPlainClosureSafety.lean](TypePM/TotalPlainClosureSafety.lean)，[TotalPlainClosureSafetyRegression.lean](TypePM/TotalPlainClosureSafetyRegression.lean) |
| total再帰closureの値・環境型付け | [RecursiveTotalClosureSafety.lean](TypePM/RecursiveTotalClosureSafety.lean)，[M4Paper1RecursiveClosureTotalTyping.lean](TypePM/Source/M4Paper1RecursiveClosureTotalTyping.lean)，[M4Paper1RecursiveClosureTypingBoundary.lean](TypePM/Source/M4Paper1RecursiveClosureTypingBoundary.lean) |
| fuelごとの再帰closure適用安全性 | [StepIndexedClosureSafety.lean](TypePM/StepIndexedClosureSafety.lean)，[StepIndexedPaper1ListSafetyRegression.lean](TypePM/StepIndexedPaper1ListSafetyRegression.lean) |
| fuel付き探索answerと二index DFS／`matchAll`合成 | [ValueIndexedMatchingSearchSafety.lean](TypePM/ValueIndexedMatchingSearchSafety.lean)，[TwoIndexMatchingSearchSafety.lean](TypePM/TwoIndexMatchingSearchSafety.lean)，[TwoIndexMatchAllSafety.lean](TypePM/TwoIndexMatchAllSafety.lean)，[M4TwoIndexRecursiveClosureSearchRegression.lean](TypePM/Source/M4TwoIndexRecursiveClosureSearchRegression.lean)，[M4TwoIndexMatchAllSafetyRegression.lean](TypePM/Source/M4TwoIndexMatchAllSafetyRegression.lean) |
| M4 user dispatchからcaller指定関係の二index DFSへのbridge | [M4TwoIndexUserMatcherReducerBridge.lean](TypePM/Source/M4TwoIndexUserMatcherReducerBridge.lean)，[M4TwoIndexPatternDispatchProducer.lean](TypePM/Source/M4TwoIndexPatternDispatchProducer.lean)，[M4TwoIndexUserMatcherReducerBridgeRegression.lean](TypePM/Source/M4TwoIndexUserMatcherReducerBridgeRegression.lean) |
| `matchAll`とmultiset節の探索安全性 | [ValueIndexedMatchAllSafety.lean](TypePM/ValueIndexedMatchAllSafety.lean)，[ValueIndexedPaper1ListJoinMatchAllSafetyRegression.lean](TypePM/ValueIndexedPaper1ListJoinMatchAllSafetyRegression.lean)，[ValueIndexedStableFirstOrderSafety.lean](TypePM/ValueIndexedStableFirstOrderSafety.lean)，[ValueIndexedPaper1ListClauseBodySafety.lean](TypePM/ValueIndexedPaper1ListClauseBodySafety.lean)，[ValueIndexedPaper1MultisetTopLevelSafety.lean](TypePM/ValueIndexedPaper1MultisetTopLevelSafety.lean)，[ValueIndexedPaper1MultisetHeadConsSafety.lean](TypePM/ValueIndexedPaper1MultisetHeadConsSafety.lean)，[ValueIndexedPaper1MultisetHeadConsGeneralSafety.lean](TypePM/ValueIndexedPaper1MultisetHeadConsGeneralSafety.lean)，[ValueIndexedPaper1MultisetGeneralConsSafety.lean](TypePM/ValueIndexedPaper1MultisetGeneralConsSafety.lean)，[ValueIndexedPaper1MultisetGeneralConsAllCallbackSafety.lean](TypePM/ValueIndexedPaper1MultisetGeneralConsAllCallbackSafety.lean)，[ValueIndexedPaper1MultisetGeneralConsFuelIndexedRegression.lean](TypePM/ValueIndexedPaper1MultisetGeneralConsFuelIndexedRegression.lean) |
| source多相`let`のruntime由来証明 | [PolymorphicLetRuntimeBridge.lean](TypePM/Source/PolymorphicLetRuntimeBridge.lean)，[PolymorphicLetProtectedClosureRegression.lean](TypePM/Source/PolymorphicLetProtectedClosureRegression.lean)，[PolymorphicLetProtectedSyntaxRegression.lean](TypePM/Source/PolymorphicLetProtectedSyntaxRegression.lean)，[PolymorphicLetInferenceOrdinary.lean](TypePM/Source/PolymorphicLetInferenceOrdinary.lean)，[PolymorphicLetInferenceOrdinaryStructural.lean](TypePM/Source/PolymorphicLetInferenceOrdinaryStructural.lean)，[PolymorphicLetInferenceOrdinaryStructuralChecker.lean](TypePM/Source/PolymorphicLetInferenceOrdinaryStructuralChecker.lean)，[PolymorphicLetInferenceOrdinaryStructuralCheckerRegression.lean](TypePM/Source/PolymorphicLetInferenceOrdinaryStructuralCheckerRegression.lean)，[PolymorphicLetInferenceOrdinaryStructuralAutomation.lean](TypePM/Source/PolymorphicLetInferenceOrdinaryStructuralAutomation.lean)，[PolymorphicLetInferenceOrdinaryStructuralAutomationRegression.lean](TypePM/Source/PolymorphicLetInferenceOrdinaryStructuralAutomationRegression.lean)，[PolymorphicLetInferenceOrdinaryStructuralFragment.lean](TypePM/Source/PolymorphicLetInferenceOrdinaryStructuralFragment.lean)，[PolymorphicLetInferenceOrdinaryStructuralFragmentRegression.lean](TypePM/Source/PolymorphicLetInferenceOrdinaryStructuralFragmentRegression.lean) |
| source断片の構文判定 | [PolymorphicLetInferenceOrdinaryStructuralFragmentChecker.lean](TypePM/Source/PolymorphicLetInferenceOrdinaryStructuralFragmentChecker.lean)，[PolymorphicLetInferenceOrdinaryStructuralFragmentCheckerRegression.lean](TypePM/Source/PolymorphicLetInferenceOrdinaryStructuralFragmentCheckerRegression.lean) |
| user matcherの型付けと条件付き安全性 | [UserMatcherSafety.lean](TypePM/UserMatcherSafety.lean)，[UserMatcherGeneralSafety.lean](TypePM/UserMatcherGeneralSafety.lean) |
| pattern function freeze／MNode | [PatternFunctionFreeze.lean](TypePM/Source/PatternFunctionFreeze.lean)，[PatternFunctionNodeEvaluation.lean](TypePM/Runtime/PatternFunctionNodeEvaluation.lean)，[PatternFunctionSafety.lean](TypePM/PatternFunctionSafety.lean)，[PatternFunctionSafetyRegression.lean](TypePM/PatternFunctionSafetyRegression.lean)，[PatternFunctionBodyPlanAutomation.lean](TypePM/PatternFunctionBodyPlanAutomation.lean)，[PatternFunctionBodyPlanAutomationRegression.lean](TypePM/PatternFunctionBodyPlanAutomationRegression.lean)，[PatternFunctionNestedBodyPlanAutomation.lean](TypePM/PatternFunctionNestedBodyPlanAutomation.lean)，[PatternFunctionNestedBodyPlanAutomationRegression.lean](TypePM/PatternFunctionNestedBodyPlanAutomationRegression.lean)，[PatternFunctionPrivateBodyPlanAutomation.lean](TypePM/PatternFunctionPrivateBodyPlanAutomation.lean)，[PatternFunctionPrivateBodyPlanAutomationRegression.lean](TypePM/PatternFunctionPrivateBodyPlanAutomationRegression.lean)，[PatternFunctionPrivateSuccessfulConstructorActualEvaluationRegression.lean](TypePM/PatternFunctionPrivateSuccessfulConstructorActualEvaluationRegression.lean)，[PatternFunctionPrivateSuccessfulConstructorAllCallbackEvaluationRegression.lean](TypePM/PatternFunctionPrivateSuccessfulConstructorAllCallbackEvaluationRegression.lean) |
| 再帰user matcherの探索安全性 | [TotalUserMatcherSafety.lean](TypePM/TotalUserMatcherSafety.lean)，[RecursiveTotalMatchingSafety.lean](TypePM/RecursiveTotalMatchingSafety.lean)，[PatternIndexedRecursiveScopedSafety.lean](TypePM/Source/PatternIndexedRecursiveScopedSafety.lean)，[M4PatternIndexedRecursiveDispatchBridge.lean](TypePM/Source/M4PatternIndexedRecursiveDispatchBridge.lean)，[M4PatternIndexedRecursiveDispatchBridgeRegression.lean](TypePM/Source/M4PatternIndexedRecursiveDispatchBridgeRegression.lean)，[M4Paper1RecursiveSafetyBoundaryRegression.lean](TypePM/Source/M4Paper1RecursiveSafetyBoundaryRegression.lean) |
| 再帰closure環境の探索安全性 | [M4EnvironmentIndexedRecursiveSearchBridge.lean](TypePM/Source/M4EnvironmentIndexedRecursiveSearchBridge.lean)，[M4EnvironmentIndexedFuelRecursiveProducer.lean](TypePM/Source/M4EnvironmentIndexedFuelRecursiveProducer.lean)，[M4EnvironmentIndexedRelationalProducer.lean](TypePM/Source/M4EnvironmentIndexedRelationalProducer.lean)，[M4Paper1ListJoinEnvironmentIndexedSearchRegression.lean](TypePM/Source/M4Paper1ListJoinEnvironmentIndexedSearchRegression.lean)，[M4Paper1ListJoinRelationalProducerRegression.lean](TypePM/Source/M4Paper1ListJoinRelationalProducerRegression.lean) |
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
