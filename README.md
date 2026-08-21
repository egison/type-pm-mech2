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
- **pattern function**はpatternを引数として受け取るsource定義であり，**MNode**はその適用を
  runtimeで処理するためのmatching nodeである．
- **surface loop pattern**は，繰返しpatternをsource上で直接書く表面構文である．
- 公平探索の**round（巡回）**は，現在のfrontierにある各探索節点の先頭を一度ずつ進める単位である．
  **prefix**は有限roundまでに観測した結果列，**frontier**はまだ展開していない探索状態である．
- **matching atom**は，一つのpatternを一つの対象値とmatcherで照合する，探索状態内の最小作業単位である．

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

### 進捗を数える範囲

動的な定理の進捗は，次の三つの範囲を区別して記す．この区別を省いた具体例の成功を，
言語全体の完成とは数えない．

- **言語クラス全体（class-wide）**は，後述するPaper 1／2／3の各クラスに属する任意のsource式を
  対象にし，公開推論から必要な実行時証拠までを一般定理で構成できる範囲である．
- **実行時層（runtime layer）**は，式・値・探索状態が既に実行時型付けを持つと仮定した後の
  型保存やno-stuckである．sourceの型付けからその前提を作る定理は別に数える．
- **具体断片（concrete fragment）**は，特定の構文断片またはPaper 1の特定listingについて，
  必要な証拠を個別に構成した範囲である．exact regressionもこの範囲に入る．

### 大括りの要約

| 区分 | 状態 | 現在地 |
|---|---|---|
| 共通静的基盤 M0--M4 | **done** | 現在実装済みのM4構文について，5.1--5.5の公開健全性・完全性・受理決定・主要性・主要型の一意性を証明済み |
| Paper 1静的定理 | **done**（言語クラス全体） | fuelで探索量を制限した深さ優先探索（bounded DFS）を使い，pattern functionを含まないクラスは，共通静的基盤の部分クラスである |
| Paper 1動的定理 | **in progress** | bounded DFSの実行時層と複数の具体listingは安全だが，任意のPaper 1 source導出から5.6--5.8を得る一般接続が残る |
| Paper 2 | **in progress** | pattern functionのfreezeとchecked MNode実行の具体断片はある．表面loop patternの構文・型付け・評価が未形式化なので，クラス全体は未完成 |
| Paper 3 | **in progress** | 公平な有限prefix探索の実行時層と，有限successor列・対象深さまでの局所step完了を仮定したruntime有限到達観測定理はある．Paper 2 source評価と遅延結果列への統合が残る |

M4の既存構文に対する静的成果と，M5の動的成果を同じ`done`へまとめない．特に，
`TotalCoreTyping`，二添字探索，checked MNode，公平探索の定理は重要な実行時基盤だが，
それだけでsource言語クラス全体の5.6--5.8が完成したことにはならない．

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

source多相`let`をruntime typingへ接続する課題は，ユーザーの対象範囲判断ではない．
Paper 1の5.6として目標に含め，状態は`in progress`である．難点は，source contextでは一つの
多相schemeを利用ごとに別の型へ具体化できる一方，runtime contextを単相型の`List Ty`として
保持していることにある．変数規則へ単純に「任意の具体化」を足すだけでは，後から型代入を行うと
その証明が保存されない．runtime contextをscheme入りへ変更せず，量化されたbindingの由来と
freshnessを外部の証明関係で記録して接続する方針で進める．別方式へ変える判断は，この方針で
矛盾が見つかった場合にだけ改めて求める．

相互`letrec`，完全なEgison処理系との後方互換性などは「判断待ち」ではなく，現行仕様では
明示的に対象外である．対象へ戻す場合は新しい機能追加として，完了条件とロードマップを先に更新する．

## 累積言語クラス

ここで**言語クラス**とは，一組のsource構文と，その評価方法をまとめた対象範囲である．
三つのクラスは累積的であり，Paper 2はPaper 1を，Paper 3はPaper 2をすべて含む．

### Paper 1：fuelで制限した深さ優先探索

Paper 1クラスは，現在のM4 source構文からpattern functionを除いた範囲を，`matchAllDFS`で評価する．
`matchAllDFS`は，fuelで探索量を制限した深さ優先探索（bounded depth-first search）であり，
`depthFirstFuel`／`searchPatternFuel`／`evalFuel`の`.matchAll` caseがこの意味を実装する．
source順と重複を保存し，探索が完了したとき有限なanswer列を一括して返す．pattern functionと
その実行時nodeであるMNodeはこのクラスに含めない．

現時点ではsource constructor名は`.matchAll`のままである．これを`matchAllDFS`へ改名し，公平な
`matchAll`を別のsource／evaluator入口として追加する作業は，Paper 3のsource統合に含める．

`timeout`は探索がまだ完了していないことを表し，正常な不一致`[]`や`stuck`ではない．
先頭branchが無限に展開する場合，後続branchの有限深さに成功があってもDFSでは観測できない．
`left_recursive_branch_starves_later_success`はこの境界を実行可能な回帰として固定する．
したがってPaper 1の5.6--5.8はbounded DFSについての主張であり，公平な列挙完全性を含まない．

### Paper 2：pattern functionとsurface loop pattern

Paper 2クラスはPaper 1に，source-defined pattern functionと**surface loop pattern**を加える．
surface loop patternとは，繰返しpatternをsource上で直接書くための表面構文である．
現在はpattern functionのfreeze，`PatternFunctionDefinitions.Agree`，checked MNode evaluatorの
基盤と具体回帰がある．一方，surface loop pattern自体のAST，静的規則，runtime規則はまだ
形式化されていない．このためpattern functionの既存断片が安全でも，Paper 2クラス全体を
`done`とはしない．

### Paper 3：公平な`matchAll`

Paper 3クラスはPaper 2に，幅優先に探索機会を配る公平な`matchAll`を加える．完了条件は，
有限回の簡約で到達できる各成功が，有限round後の結果prefixで観測されることである．
無限個の結果を扱うため，完成した有限Listではなく，有限prefixと未探索frontierを返すか，
それと同等の遅延した結果表現が必要になる．

`FairReductionTreeSearch`は有限roundのprefixとfrontierを返し，`FairTwoIndexMatchingSearchSafety`は
実際のmatching stateについてprefixとfrontierの型安全性・任意roundのno-stuckを証明する．
`FairReductionTreeCompleteness`は，有限successor列と，対象深さまでの各局所stepが完了するという
前提の下で，有限深さのyieldが有限roundで観測されることを証明する．これは局所stepの`timeout`を
自動的に追い越す定理ではない．また，現状はruntime探索木の定理であり，Paper 2 source評価，
真に遅延した結果列，無限successor列にはまだ接続していない．

APLAS 2018で既定とされる`match-all`はこのPaper 3側である．現在のbounded `matchAllDFS`は
同論文付録の`match-all-dfs`に対応する別の実行方式として残す．

`matchFirst`の通常armに結果があるかを型推論で判定しない設計は三クラスで共通である．
user matcherは型の正しい空の候補分解を返せるため，すべての通常armが空なら，
arm内のbindingに依存しない必須`else`を元の環境で評価する．

## 定理軸ロードマップ

5.1--5.5は静的型推論，5.6--5.8はsource型付けと実行時安全性の接続を追跡する．
Paper 3では，これらに公平性の定理を追加する．

| 軸 | このREADMEでの完了条件 |
|---|---|
| 5.1--5.5 | 公開`infer`の健全性・完全性・受理決定・主要性と，主要な代表型の有限な変数名変更を除く一意性 |
| 5.6 | sourceの主要型付け導出から，推論状態を含まない値・環境・探索状態の実行時証拠を構成する |
| 5.7 | 実際の評価・matching・有限探索が型を保存し，fuel不足は`timeout`，それ以外の型付き局所状態は`stuck`せず進むか正常終了する |
| 5.8 | 全域的な対象断片の型付きclosed programが，任意のfuelで`stuck`にならない |
| Paper 3公平性 | 有限回の簡約で到達する各成功を，公平な`matchAll`の有限round後のprefixで観測する |

5.6は「古い環境型付けを消す」操作ではない．このリポジトリの独立したsource `Typing`を，
実行時の値・環境・matching stateの型付けへ移す構造的な定理である．

### クラス×定理の状態表

| 言語クラス | 5.1--5.5 | 5.6 | 5.7 | 5.8 | Paper 3公平性 |
|---|---|---|---|---|---|
| Paper 1 | **done** — 言語クラス全体 | **in progress** — 目標interfaceと具体断片 | **in progress** — bounded DFSの実行時層はdone，一般source接続は未完 | **in progress** — `TotalCoreTyping`と具体listingはあるがクラス全体は未完 | 対象外 |
| Paper 2 | **in progress** — pattern-function構文はdone，surface loop patternが未形式化 | **in progress** — freeze／`Agree`はあるが一般certificateは未完 | **in progress** — checked MNodeの具体断片，loopは未着手 | **in progress** — 具体断片のみ | 対象外 |
| Paper 3 | **in progress** — Paper 2の未完を継承 | **in progress** — sourceから公平探索frontierへの接続が未完 | **in progress** — 公平prefixの実行時層はdone，式評価への統合は未完 | **in progress** — Paper 2の未完と公平評価の未統合を継承 | **in progress** — 一般runtime探索木ではdone，source言語クラス全体では未完 |

### 完了済みの共通静的基盤：5.1--5.5

| 範囲 | 完了済みの内容 | 主な公開入口 |
|---|---|---|
| M0--M1 | 二種類の型変数，raw synthesis，局所checking，制約生成，停止する単一化，飽和，coverage，公開推論の健全性・完全性・主要性 | `Inference.infer_success_typing`，`Typing.infer_isSome` |
| M2 | bound-index scheme，多相`letE`，full-cut一般化，入れ子`letE`のcoherenceとreplay | `FullM2Completion` |
| M3 | data／pattern constructor，primitive，signature，`ifE`とM2--M3全域の公開定理 | `FullM2Completion`とM3 signature検査 |
| M4の既存構文 | pattern，matcher literal，`matchAll`，必須`else`付き`matchFirst`，`fixE`，pattern functionについて，fuel正規化，support，coherence，replay，5.1--5.5 | `M4.infer_success_typing`，`M4.Typing.infer_isSome`，`M4.PrincipalTyping.finiteRenamingEq`，`M4.infer_success_principalResult` |
| matcher形状 | constructorとarity，capture／hole順序，binding順序，最終catch-allを帰納的命題とBool検査の同値で固定 | `MatcherPattern`，`MatcherClauseShape` |
| pattern function宣言 | source interfaceとbodyからfrozen signature，runtime定義表，`PatternFunctionDefinitions.Agree`を構成 | `PatternFunctionFreeze` |

この表のM4は「現在ASTに存在する構文」についての完了である．surface loop patternはAST自体が
未形式化なので，それを含むPaper 2／3の5.1--5.5を完了にしない．一般Damas--Milner対応DM3と，
pattern functionの全具体化でのinterface主要性PF6も，ここで完了した5.1--5.5には含めない．

### Paper 1：bounded DFSの5.6--5.8

#### 5.6：source導出から実行時証拠へ

`M5CompletionArchitecture.ConditionalCompletionSchema`は，実際の
`M4.PrincipalTypingDerivation`に添字を付けたcertificate，source contextとruntime contextの対応，
結果型の具体化，評価・探索の安全性，closed programのno-stuckを束ねる目標interfaceである．
`PrincipalStateErasure`と`MatchingStateErasure`は，source導出から実行時証拠を作る位置を明示する．
これらは抽象的なcertificate familyやsearch originを引数に取るため，interfaceだけを5.6完成の
証拠とは数えない．

`M4RuntimeBridge`，`PolymorphicLetRuntimeBridge`，解決済みmatcher clause，通常の`fixE`，
限定した`matchFirst`については具体的な接続がある．`M4CanonicalCertificateTransport`はclosedな
主要導出を公開`infer`の代表導出へ結ぶが，certificateがcoherenceを尊重することを条件にする．
残る中心課題は，任意のPaper 1主要導出から，context対応，評価certificate，matching taskの由来を
同時に構成する帰納的な一般定理である．

`M4LetRuntimeWorldStep`は，その帰納法で最初にcontextを変える一般構成子を固定する．任意の正の
静的fuelを持つM4 `letE`導出を，実際に選ばれた右辺の主要closure，同じ一段小さい静的fuelを持つ
value／body導出，親の制約解が満たすinterface制約とbody制約へ分解する．さらに，外側のsource
contextとruntime型列・provenanceの長さ対応を保ち，generalizeしたschemeのcanonicalな単相型と
`true` provenanceを先頭へ加えたbody contextを構成する．公開`infer`から選んだ主要導出を使う回帰では，
多相identityを`Int`とmatcher型で別々に具体化するbodyについて，このworldと静的fuelの厳密な一段減少を
検査した．これは**一般M4 `letE`の静的な分解とbody world構築**である．`ProtectedContextCompatible`は
runtime値の安全性ではないため，それだけでは右辺値の全具体化に対する`FuelValueSafe`，body評価，
whole-letの`TypedEvaluation`／no-stuckを主張しない．

`ProtectedPolymorphicLetFuelSafety`は，この静的worldと将来接続するための独立した動的環境関係を追加する．通常の
環境要素は一つの型での`FuelValueSafe`を保持し，多相化した環境要素は，指定した論理indexにおいて
`IsInstance`で得られるすべての具体型で安全であることを保持する．さらに，右辺値がすべての論理indexと
すべての具体型で安全なら，bodyが必要とするindexを後から選んで`letE`の結果安全性へ合成できる．
多相identityを同じruntime環境要素から`Int → Int`とmatcher関数型の二通りで使う回帰では，任意の
評価fuelで`stuck`しないことまで確認した．ただし，静的worldから実runtime環境の安全性，右辺の
全index・全具体型の実行後安全性，bodyの後続証明を同時に作るsource certificateはまだない．現在の
「評価fuelと結果indexを足す」入力添字だけで任意のopenな右辺を通常の帰納仮定へ再帰させるには
添字が不足するため，より強い内部定理または入力添字の再設計が残る．したがって，
これは**条件付きの動的`letE`構成子と具体回帰**であり，Paper 1クラス全体の5.6--5.8完成ではない．

`M4ProtectedFuelContextBridge`は，M4の正の静的fuelを持つ変数導出からsource schemeの実lookupを
取り出し，`ProtectedContextCompatible`と上の動的環境関係を合成して，その変数出現で選ばれた具体型の
`FuelValueSafe`を構成する．通常束縛ではruntime contextの正確な型を使い，多相束縛では静的な
`IsInstance`証拠を同じ位置の動的な多相要素へ適用する．評価fuelと論理indexを別々に量化した
変数評価の結果安全性まで一般に証明し，回帰では通常の整数要素と，同じidentity closureを一つの共有
代入の下で`Int → Int`／matcher関数型へ具体化する二経路を検査した．これは将来のraw M4導出に対する
帰納証明の**条件付きの変数の場合**を完成するが，多相右辺から動的環境要素を作る逆向きの定理ではない．
現在の全`IsInstance`条件は，general型にopen context由来の自由型変数が残る場合，その変数まで置換できる
強い十分条件である．

`SchemeIndexedFuelSafety`は，この過剰な条件を避け，source schemeと一つの固定solutionに直接添字を付ける．
一つのruntime値を，同じsolutionの下での全`Scheme.instantiate supply`出現型，すなわち各変数出現で
schemeを具体化して得る型に結び付け，環境全体を
source contextと同じ順序・長さで保持する．有限な論理indexでの単相lambda引数・matching bindingの追加，
変数lookup，indexの縮小に加え，`LetRuntimeWorld.interfaceSolved`と同じ静的interface条件だけを使って，
外側contextから`context.applyFree`後のbody-tail contextへ環境証拠を輸送できる．raw M4変数導出については，
runtime monotype，provenance，`IsInstance`を経由せず，任意の評価fuelと独立な論理indexで結果安全性まで証明した．

同じ決定的な右辺評価について，全supply・全論理indexの子証明を一つのscheme値証拠へまとめる補題と，
それを消費するclosed-firstの条件付き`letE`合成も持つ．回帰では，一つの多相identityを同じbody内で
`Int → Int`とmatcher関数型へ具体化し，任意fuelで`stuck`しないことを確認した．ここで量化するのは
「実際に現れた有限個」や「freshness証拠を持つsupplyだけ」ではなく，同じ固定solutionの下の
**全supply-indexed occurrence type**である．このall-index環境をPaper 1全体の内部不変条件には使えない．
lambda引数やpattern bindingは一般に有限indexしか持たないためである．任意のM4右辺からgeneralized schemeの
全出現証拠を作るproducer，式ごとの入力需要を持つ有限indexの帰納法，open M5の環境interfaceへの統合は未完である．

`M5ClosedPairProjectionCertificate`は，整数，二要素の整数pair，入れ子のpair projectionからなる
closedかつsearch-freeな具体断片について，`ConditionalCompletionSchema`の連言全体を満たす．
certificateが保持するのは，実際のM4主要導出に対応するfragment証拠と`RuntimeTyping`だけであり，
具体的な評価結果，探索結果，それらを予測する等式は含まない．公開M4 `infer`，独立`Typing`，
主要型の具体化，任意fuel no-stuckを入れ子のpair回帰で検査した．certificateのcoherence輸送は
`closedRuntimeCertificateRespectsCoherence`として一般に証明した．
この断片はmatchingを発行しないためsearch originは空であり，探索に関する連言は空虚に成立する．
したがってこれは**完了した具体断片**だが，`matchAllDFS`を含むPaper 1クラス全体の5.6--5.8を
完了した証拠ではない．

`M5ClosedLiteralMatchAllCertificate`は，closedな整数literal族
`matchAll literal as something with $x -> x`について，同じ連言全体を**空でない探索証拠**とともに
満たす．certificateは実際のM4主要導出とgroundな結果型だけを保持し，targetとmatcherの評価が
成功した時点で，その値から発行されるbuilt-in variableのbounded-DFS taskを`SearchOrigin`へ記録する．
`MatchingStateErasure`はその起点をgroundな探索taskのcertificateへ変換し，`TypedMatchingSearch`が
二添字初期state証拠を任意の三添字について再構成する．式全体の`TypedEvaluation`も同じ探索経路を
消費する．探索定理ではcallback fuel，探索fuel，結果の論理indexを任意かつ別々に量化する．式評価との
合成では，実行意味論どおりcallbackと探索へ同じoperational fuelを渡し，結果の論理indexだけを独立に
保つ．公開`infer`から選んだ主要導出を用いる回帰では，実search origin，探索の
型安全性，公開`Typing`，任意fuel no-stuckを接続した．完成した探索結果や最終評価結果の等式は
安全性証明とは独立した回帰としてだけ置く．これはsearch-bearingな最初の**完了した具体断片**だが，
recursive closure，非空runtime環境，user matcher，callback評価を使うpattern，任意pattern，外側の
多相`letE`を含むPaper 1クラス全体の一般certificateではない．

#### 5.7：評価・matching・bounded DFS

`Source.Typing.coreSafety`，built-in matching，user matcherの条件付き安全性，
`TwoIndexMatchingSearchSafety`，`Runtime.matchAllFuel_twoIndexSafe`により，
実行時層では評価fuel，callback fuel，探索fuel，answerの論理indexを分離して型保存とno-stuckを
扱える．環境・成功値・探索answerの関係はcallerが同時に選べるため，従来の構造的な
`EnvironmentTyping`／`ValueTyping`だけに固定されない．

`M4TwoIndexMatchAllInitialProducer`は，Paper 1のvariable patternと最終catch-all一節に限り，
実際のenclosing M4 `matchAll`導出と同じ`Generated.fromMatchAll`の制約解から初期state証拠を作る
bounded DFS用の局所合成bridgeである．target→pattern→matcher→bodyのsupply順と，runtime matcherが
同じclauseを持つことを保持する．完成した探索結果の等式は要求しない．局所dispatchのno-stuck，
hit時のactual branch証拠，局所reducer保存則は明示的な前提である．任意のpattern，capture，constructor節を
扱う一般的なsource-to-runtime producerではない．

`M4TwoIndexPatternDispatchProducer`と`M4TwoIndexUserMatcherReducerBridge`は，M4 pattern elaboration，
実dispatch，caller指定のatom関係を二添字DFSへ接続する部品である．残る課題は，任意のPaper 1
matcher-clause導出から，actual branchの証拠，atom関係，局所evaluator／reducer保存則，初期stateを
構造的に生成することである．

#### 5.8：closed programの任意fuel no-stuck

`TotalCoreTyping.commonFuelSafety`は，`matchAll`と必須`else`付き`matchFirst`を含む全域的な
`TotalCoreTyping`断片について任意fuel no-stuckを与える．Paper 1の複数listingにも，
exact評価とは別の型保存・no-stuck証拠がある．どのlistingが一般source接続まで持つかは，
後述のinventoryだけで管理する．

Paper 1クラス全体の5.8には，任意の公開M4型付けから5.6のcertificateを作り，5.7のbounded DFS
安全性と合成して`ClosedNoStuck`を得る定理が必要である．具体target，特定fuelでの成功，
具体例固有のdispatch certificateを前提にする回帰だけではこの条件を満たさない．

### Paper 2：pattern functionとsurface loop pattern

`PatternFunctionFreeze.freezePatternFunctions`は，source宣言から検査済み`FrozenSignature`，
runtime定義表，`PatternFunctionDefinitions.Agree`を構成する．checked MNode evaluatorと安全性は，
outer／privateのscopeを分け，tuple，conjunction，variable，or，nested application，証明付きの
一部constructorを扱う．これらはPaper 2の重要な実行時部品である．

ただし，freeze／`Agree`はsource式全体の実行時certificateではなく，5.6の代わりにならない．
現在のconstructorを実行規則へ対応させる処理とbodyの評価手順は具体断片に限られ，任意のM4 pattern-function導出からの
自動生成も未完である．さらにsurface loop patternは構文・静的規則・評価規則が存在しない．
したがってPaper 2については，次のすべてが残る．

- 5.1--5.5：surface loop patternを追加し，既存M4の健全性・完全性・主要性へ統合する．
- 5.6：frozen definitionsと`Agree`を保持するchecked-evaluator certificateを，任意のPaper 2導出から作る．
- 5.7：任意constructor／user matcherを実行規則へ対応させる処理の保存則と，loopの実行時型保存・局所progressを証明する．
- 5.8：pattern functionとloopを含む全域的なclosed断片を，一般source導出から任意fuel no-stuckへ接続する．

### Paper 3：公平探索と有限到達観測

`FairReductionTreeSearch`は，有限round後のanswer prefixと未探索frontierを返す．
`FairTwoIndexMatchingSearchSafety`は，matching stateについてprefixとfrontierの型安全性を保ち，
型の付いた有限prefix探索が`stuck`しないことを証明する．
`Runtime.reductionTreeYield_eventually_observed`は，有限successor列と，
対象深さまでの局所stepが完了するという仮定の下で，有限深さの到達可能なyieldが有限roundで
prefixに現れることを証明する．

これらは一般runtime探索木の定理であり，Paper 3 source言語クラス全体の完成証拠ではない．
Paper 3には，Paper 2の5.1--5.8に加えて，source `matchAll`から型付き初期frontierを作る定理，
公平prefix探索を式評価と遅延した結果collectionへ統合する定理，source由来の各有限到達解へ
一般runtime公平性定理を適用する定理が必要である．局所stepの`timeout`や無限successor列を
どの意味論で扱うかも，この統合時に明示する．

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

## 未完の定理境界

次の表は具体回帰の追加ではなく，言語クラス全体の状態を変えるために必要な一般定理を依存順に示す．

| クラス／軸 | 状態 | 次に必要な一般結果 |
|---|---|---|
| Paper 1／5.6 | **in progress** | 一般M4 `letE`の静的body world，全`IsInstance`版とsource scheme＋固定solution版の動的環境関係，interface輸送，raw M4変数caseは完了．次は式ごとの入力需要を持つ有限indexの内部certificateから右辺のscheme出現証拠，body評価，MNodeを含まないmatching taskの由来を構成し，rootの公開主要導出へ一度だけ包む |
| Paper 1／5.6 | **in progress** | 上の具体certificateがcoherenceを尊重することを証明し，公開`infer`が選ぶ代表導出へclosed certificateを輸送する．多相`letE`ではscheme bindingの由来とfreshnessを保存する |
| Paper 1／5.7 | **in progress** | 任意のM4 matcher-clause導出から，actual dispatchの各branch，atom関係，局所evaluator／reducer保存則，二添字初期stateを生成する．具体例固有の有限branch証拠を一般定理の外部前提に残さず，complete-search等式にも依存しない |
| Paper 1／5.8 | **in progress** | 5.6のsource certificateと5.7のbounded DFS安全性を合成し，任意の全域的Paper 1 closed式について`ClosedNoStuck`を得る |
| Paper 2／言語 | **not started** | surface loop patternのAST，binding interface，静的elaboration，実行規則を定義する |
| Paper 2／loopの5.1--5.5 | **not started** | loop patternをM4のfuel・support・coherence・replay・主要性へ統合する |
| Paper 2／5.6 | **in progress** | frozen definitionsと`PatternFunctionDefinitions.Agree`を保持するchecked-evaluator certificateを，任意のpattern-function／loop導出から構成する |
| Paper 2／5.7 | **in progress** | 任意constructor／user matcherを実行規則へ対応させる処理とbody評価の保存則，およびloopの局所progressを証明する |
| Paper 2／5.8 | **in progress** | pattern functionとloopを含む全域的closed断片を，一般source導出から任意fuel no-stuckへ接続する |
| Paper 3／5.6--5.7 | **in progress** | 現在のDFS用`.matchAll`を`matchAllDFS`として分離し，公平な`matchAll`を別のsource／evaluator入口として追加する．そのsource導出から型付きfrontierを作り，有限prefix探索を式評価と遅延結果collectionへ統合する |
| Paper 3／5.8 | **in progress** | 公平評価を含む全域的closed断片について，任意の有限roundでno-stuckとprefix型安全性を得る |
| Paper 3／公平性 | **in progress** | source由来の各有限到達解へ一般runtime公平性定理を適用し，有限roundでの観測を示す．局所`timeout`と無限successor列の扱いを意味論に明記する |

独立に進められる補題は並行して実装できるが，表の状態を`done`へ変えるのは，その行の量化範囲を
満たす公開定理と公理監査が揃ったときだけである．DM3とPF6はこの依存列を止めず，
「ユーザー判断が必要になる項目」に記した論文上の判断時点まで将来課題として保持する．

## 完了と主張する条件

完了は累積言語クラスごとに主張する．一つの具体回帰，目標interface，実行時層の定理だけで，
そのクラス全体を完了とはしない．

### Paper 1の完了条件

- Paper 1クラス全体について5.1--5.5が成立する．これは完了済みである．
- 任意の主要source導出から5.6の実行時certificateとmatching taskの由来を構成できる．
- 実際のbounded DFSについて5.7の型保存と局所progressをsource導出から得られる．
- 全域的なclosed断片について5.8の任意fuel no-stuckを得られる．
- Paper 1 inventoryで実行を主張する各listingが，その行に記した実行・関係・安全の条件を満たす．

### Paper 2の完了条件

- Paper 1が完了している．
- pattern functionとsurface loop patternの構文・5.1--5.5・実行規則が揃っている．
- 公開freeze checkerが受理した定義について，`Agree`を保持するsource-to-runtime certificateと，
  checked MNode／loop評価の5.7，対象closed断片の5.8が一般定理として成立する．
- 全具体化でのinterface主要性PF6は，別途対象へ含める判断がない限り完了条件に含めない．

### Paper 3の完了条件

- Paper 2が完了している．
- sourceの公平な`matchAll`が有限prefixまたは同等の遅延結果として定義され，5.6--5.8へ統合されている．
- 各有限到達解が有限roundで観測されることを，source由来の探索について証明している．

一般の停止性，相互`letrec`，旧実装との後方互換性は，どのクラスの完了条件にも含めない．
一般Damas--Milner対応DM3と全具体化でのpattern-function主要性PF6は，論文の最終主張へ含めると
決めた場合にだけ該当クラスの完了条件へ昇格する．

## 証拠ファイル索引

この表は代表的な入口だけを示す．具体的なPaper 1の結果・順序・重複・残る境界は，
前節のlisting inventoryを正本とする．

| 定理軸／範囲 | 主な入口 | 証拠の範囲 |
|---|---|---|
| M1静的基盤 | [Inference.lean](TypePM/Inference.lean)，[InferenceCompleteness.lean](TypePM/InferenceCompleteness.lean)，[Principality.lean](TypePM/Principality.lean) | 5.1--5.5の基礎 |
| M2--M3静的基盤 | [FullM2Completion.lean](TypePM/Source/FullM2Completion.lean) | 多相`letE`，constructor／primitive／`ifE`を含む完了済み基盤 |
| M4静的elaboration | [M4RecursiveElaboration.lean](TypePM/Source/M4RecursiveElaboration.lean)，[FullM4Completion.lean](TypePM/Source/FullM4Completion.lean) | 現在のM4 ASTに対する5.1--5.5 |
| M4 coherence／replay | [M4CompletenessArchitecture.lean](TypePM/Source/M4CompletenessArchitecture.lean)，[M4StructuralReplay.lean](TypePM/Source/M4StructuralReplay.lean)，[M4FreshRenamingTransport.lean](TypePM/Source/M4FreshRenamingTransport.lean) | 関係的導出と公開推論の接続 |
| matcher形状 | [MatcherPattern.lean](TypePM/Source/MatcherPattern.lean)，[MatcherClauseShape.lean](TypePM/Source/MatcherClauseShape.lean) | 宣言的形状条件とBool検査の対応 |
| Paper 1 source／静的回帰 | [Paper1Programs.lean](TypePM/Source/Paper1Programs.lean)，[M4Paper1ListExactRegression.lean](TypePM/Source/M4Paper1ListExactRegression.lean)，[M4Paper1ClosedMultisetExactRegression.lean](TypePM/Source/M4Paper1ClosedMultisetExactRegression.lean) | listing inventoryのsourceと5.1--5.5 |
| 評価・matching基盤 | [Evaluation.lean](TypePM/Runtime/Evaluation.lean)，[EvalFuel.lean](TypePM/Runtime/EvalFuel.lean)，[MatchingState.lean](TypePM/Runtime/MatchingState.lean)，[MatchingSearch.lean](TypePM/Runtime/MatchingSearch.lean) | 関係的評価，実行可能評価，matching state |
| Paper 1 bounded DFS実行時層 | [DepthFirstSearch.lean](TypePM/Runtime/DepthFirstSearch.lean)，[CoreSafety.lean](TypePM/CoreSafety.lean)，[MatcherSafety.lean](TypePM/MatcherSafety.lean)，[CommonFuelSafety.lean](TypePM/CommonFuelSafety.lean)，[NoStuck.lean](TypePM/NoStuck.lean) | 既に実行時型付けされた項の型保存・no-stuck |
| 5.6目標interface／部分橋 | [M5CompletionArchitecture.lean](TypePM/Source/M5CompletionArchitecture.lean)，[M4RuntimeBridge.lean](TypePM/Source/M4RuntimeBridge.lean)，[PolymorphicLetRuntimeBridge.lean](TypePM/Source/PolymorphicLetRuntimeBridge.lean)，[M4CanonicalCertificateTransport.lean](TypePM/Source/M4CanonicalCertificateTransport.lean)，[M4LetRuntimeWorldStep.lean](TypePM/Source/M4LetRuntimeWorldStep.lean)，[M4LetRuntimeWorldStepRegression.lean](TypePM/Source/M4LetRuntimeWorldStepRegression.lean)，[ProtectedPolymorphicLetFuelSafety.lean](TypePM/ProtectedPolymorphicLetFuelSafety.lean)，[ProtectedPolymorphicLetFuelSafetyRegression.lean](TypePM/ProtectedPolymorphicLetFuelSafetyRegression.lean)，[M4ProtectedFuelContextBridge.lean](TypePM/Source/M4ProtectedFuelContextBridge.lean)，[M4ProtectedFuelContextBridgeRegression.lean](TypePM/Source/M4ProtectedFuelContextBridgeRegression.lean)，[SchemeIndexedFuelSafety.lean](TypePM/SchemeIndexedFuelSafety.lean)，[SchemeIndexedFuelSafetyRegression.lean](TypePM/SchemeIndexedFuelSafetyRegression.lean) | interface，限定したsource-to-runtime接続，一般`letE`の静的body world，全`IsInstance`版とsource scheme＋固定solution版の動的環境，interface輸送，条件付きclosed-first `letE`，raw M4変数case．多相右辺を一般source導出からscheme環境へ入れるproducerとクラス全体は未完 |
| closed pair certificate | [M5ClosedPairProjectionCertificate.lean](TypePM/Source/M5ClosedPairProjectionCertificate.lean)，[M5ClosedPairProjectionCertificateRegression.lean](TypePM/Source/M5ClosedPairProjectionCertificateRegression.lean) | 5.6--5.8とcoherence輸送を満たす完了したsearch-free具体断片．Paper 1クラス全体ではない |
| closed literal `matchAllDFS` certificate | [M5ClosedLiteralMatchAllCertificate.lean](TypePM/Source/M5ClosedLiteralMatchAllCertificate.lean)，[M5ClosedLiteralMatchAllCertificateRegression.lean](TypePM/Source/M5ClosedLiteralMatchAllCertificateRegression.lean) | 5.6--5.8を実際に発行された空でないbounded-DFS taskとともに満たす完了した具体断片．user matcherを含むクラス全体ではない |
| 二添字bounded DFS | [TwoIndexMatchingSearchSafety.lean](TypePM/TwoIndexMatchingSearchSafety.lean)，[TwoIndexMatchAllSafety.lean](TypePM/TwoIndexMatchAllSafety.lean) | caller指定の環境・answer関係と局所保存則を合成する実行時層 |
| M4から二添字DFSへの局所bridge | [M4TwoIndexMatchAllInitialProducer.lean](TypePM/Source/M4TwoIndexMatchAllInitialProducer.lean)，[M4TwoIndexPatternDispatchProducer.lean](TypePM/Source/M4TwoIndexPatternDispatchProducer.lean)，[M4TwoIndexUserMatcherReducerBridge.lean](TypePM/Source/M4TwoIndexUserMatcherReducerBridge.lean) | bounded DFSの限定的な局所合成．dispatch no-stuck，hit時のbranch証拠，局所reducer保存則が残る |
| Paper 1実行回帰 | [Paper1NeverStuckRegression.lean](TypePM/Runtime/Paper1NeverStuckRegression.lean)，[M4Paper1ListJoinSearchSafety.lean](TypePM/Source/M4Paper1ListJoinSearchSafety.lean)，[M4Paper1MultisetSearchSafety.lean](TypePM/Source/M4Paper1MultisetSearchSafety.lean) | inventoryに列挙した具体listing |
| Paper 2 freeze／checked MNode | [PatternFunctionFreeze.lean](TypePM/Source/PatternFunctionFreeze.lean)，[PatternFunctionNodeEvaluation.lean](TypePM/Runtime/PatternFunctionNodeEvaluation.lean)，[PatternFunctionSafety.lean](TypePM/PatternFunctionSafety.lean) | pattern-function断片．surface loop patternは含まない |
| Paper 3公平探索 | [FairReductionTreeSearch.lean](TypePM/Runtime/FairReductionTreeSearch.lean)，[FairReductionTreeCompleteness.lean](TypePM/Runtime/FairReductionTreeCompleteness.lean)，[FairTwoIndexMatchingSearchSafety.lean](TypePM/FairTwoIndexMatchingSearchSafety.lean) | 一般runtime探索木の有限prefix安全性と有限到達観測 |
| 公理監査 | [AxiomAuditCommand.lean](TypePM/AxiomAuditCommand.lean)，[AxiomAudit.lean](TypePM/AxiomAudit.lean) | 許可集合外の公理があればbuildを失敗させる |

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
- 状態を変えるときは，累積クラス×定理の表，未完の定理境界，該当するPaper inventoryを同時に更新する．
- 実装途中の一時的なbranch名，worktree名，担当者名は記録しない．再開時は
  `git status --short --branch`と`git worktree list`で実際の状態を確認する．
- 過去の予定module名を先に固定しない．実在するmodule／theoremだけを証拠欄に記す．
- 設計判断を変更するときは「形式体系として固定している範囲」と，影響する完了条件を同時に
  更新する．
