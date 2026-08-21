# `productMatcher` 単独変換の削除指示書

## 目的

`Prod [Matcher ...]`を`Matcher ...`として検査する単独変換
`CheckConversion.productMatcher`を削除し，matcherの積は利用箇所が明示的に
`Slot ...`を要求した場合にだけ`CheckConversion.productMatcherToSlot`で受理する．

この変更により，producer（実際にmatcher値を作る式の型）とslot（利用箇所がmatcherへ
要求する型）の境界を単純化する．積をmatcherとして使う暗黙変換は設けず，積matcherの
利用は常にslotへの直接変換として表す．

## 固定する仕様

- 削除するものは，単独の`ConversionClass.productMatcher`，
  `CheckConversion.productMatcher`，`Resolution.productMatcher`，
  `Resolution.Branch.productMatcher`である．
- `CheckConversion.matcherToSlot`は残す．単独のmatcher producerは従来どおりslotへ変換できる．
- `CheckConversion.productMatcherToSlot`は残す．非空のmatcher積は従来どおりslotへ直接変換できる．
- `Ty.matcher`，matcher literal，`.something`は削除しない．変更対象は積からmatcherへの
  暗黙変換だけである．
- `Prod [Matcher ...]`を明示的な`Matcher ...`期待型に対して検査した場合は受理しない．
  `resolve`では通常の型等式として扱い，外側の`Prod`と`Matcher`が一致しないため失敗させる．
- `matchAll`のmatcher位置とmatcher clauseの次matcherは，従来どおり`Slot ...`を要求する．
- 後方互換性のための別名，shim，deprecated経路は追加しない．

変更後に残る変換は次の三つだけとする．

```text
ordinary
Matcher producer target -> Slot consumer target
Prod [Matcher ...] -> Slot consumer (Prod [...])
```

## 作業前の注意

開始時に`git status --short`と関連ファイルの`git diff`を確認すること．このリポジトリでは
並行作業による未commit変更が存在することがある．特に`OriginDemandSafety.lean`，
`M5ClosedPairProjectionCertificate.lean`，`AxiomAudit.lean`，`TypePM.lean`などが変更済みなら，
既存変更を上書きせず，この仕様変更だけを局所的に組み込む．

最初に次の検索を実行し，この指示書に列挙していない新しい参照もすべて対象に含める．

```sh
rg -n '\bproductMatcher\b|mayBecomeExpectedMatcher|source_eq_target_of_target_not_matcher_or_slot' TypePM TypePM.lean README.md
```

## 実装手順

### 1. checking変換を三種類へ縮小する

`TypePM/Checking.lean`を変更する．

- `ConversionClass.productMatcher`を削除する．
- `CheckConversion.productMatcher`を削除する．
- `CheckConversion.productMatcherToSlot`は独立した直接変換として残す．
- `CheckConversion.source_eq_target_of_target_not_matcher_or_slot`は，matcher期待型を
  除外条件に含める必要がなくなる．`source_eq_target_of_target_not_slot`へ改名し，
  「期待型がslotでなければ通常変換なのでsourceとexpectedが等しい」という定理へ単純化する．
- 古い定理名の別名は残さない．すべての利用箇所を新しい名前へ更新する．

### 2. residual resolutionから積-to-matcher分岐を削除する

`TypePM/Resolution.lean`を変更する．

- `Resolution.productMatcher`を削除する．
- `Resolution.Branch.productMatcher`を削除する．
- `branch`，`conversionClass`，`equations`，`Resolution.sound`の対応caseを削除する．
- `resolve (.prod items) (.matcher capability target)`の専用分岐を削除する．この組合せは
  最後の通常分岐へ入り，`.ordinary`と型等式`Prod ... = Matcher ...`を返すようにする．
- `matcherProduct?`など，`productMatcherToSlot`でも使う積解析処理は削除しない．
- `special_expected_head`は，特殊変換の期待型が常にslotになったことを直接述べる
  `special_expected_slot`へ変更する．返り値は次だけでよい．

```lean
∃ capability target, expected = .slot capability target
```

- `resolve_sound`と関連するcase解析を更新する．

`TypePM/ResolutionTransport.lean`では`branch_productMatcher`だけを削除する．
`productMatcherToSlotEqual`と`productMatcherToSlotAny`の二つのbranchは残す．

### 3. 特殊変換候補の判定をslot期待型だけに限定する

`TypePM/ConversionPotential.lean`を変更する．

- `Ty.mayBecomeExpectedMatcher`と`mayBecomeExpectedMatcher_of_apply`を削除する．
- `couldSpecial`は，sourceが将来単独matcherまたは非空matcher積になり得て，かつexpectedが
  将来slotになり得る場合だけ`true`にする．例えば次の形に整理できる．

```text
(source.mayBecomeMatcher || source.mayBecomeMatcherProduct)
  && expected.mayBecomeExpectedSlot
```

- `couldSpecial_of_apply`を新しい定義に合わせて証明し直す．
- `Resolution.special_implies_couldSpecial`から`productMatcher` caseを削除する．
- expectedが`Matcher ...`であることだけを理由にobligationをpendingへ残してはならない．

次も同時に整理する．

- `TypePM/SaturationRenaming.lean`の`mayBecomeExpectedMatcher_rename`
- `TypePM/Source/ElaborationRenaming.lean`の
  `mayBecomeExpectedMatcher_renameVariables`
- 回帰や証明の`simp`引数に列挙された`Ty.mayBecomeExpectedMatcher`

定義を削除した後，`rg -n 'mayBecomeExpectedMatcher' TypePM`が空になるまで更新する．

### 4. 変換caseを列挙する一般定理を更新する

少なくとも次のファイルには単独`productMatcher`のcaseがある．各caseを単に機械的に消すだけでなく，
定理の主張が三種類の変換に対して自然になっているか確認する．

- `TypePM/CoreSafety.lean`
- `TypePM/OriginDemandSafety.lean`
- `TypePM/RuntimeTyping.lean`
- `TypePM/ResolutionSupport.lean`
- `TypePM/StepIndexedClosureSafety.lean`
- `TypePM/Source/M5ClosedPairProjectionCertificate.lean`

特に次を行う．

- `CheckConversion.apply`から単独`productMatcher` caseを削除する．
- `CheckConversion.trans`は`ordinary`，`matcherToSlot`，`productMatcherToSlot`だけで証明し直す．
  `productMatcher`と`matcherToSlot`の合成caseは不要になる．
- safety判定で`Prod`値を`Matcher`安全性へ移すcaseを削除する．
  `productMatcherToSlot`によって`Slot`安全性へ移すcaseは残す．
- `Resolution.equations_support`から積-to-matcher専用caseだけを削除する．

### 5. 実行時bridgeをslot型の証拠に揃える

`TypePM/Source/M4MatchingAtomRuntimeBridge.lean`の
`PatternElaborates.toBuiltinTotalMatchingAtomTyping`は，現在matcher値について
`ValueTyping matcherValue (.matcher ...)`を受け取る．通常のsource typingではmatcher位置が
slotを要求するため，これを次のslot型の証拠へ変更する．

```text
ValueTyping matcherValue
  (.slot generated.dual.capability generated.dual.target)
```

この引数は現状の証明本体では使用されていなくても削除せず，sourceのmatcher検査が成功したことを
runtime bridgeの前提として保持する．呼出し側では，単独matcherなら`matcherToSlot`，matcher積なら
`productMatcherToSlot`でこの証拠を構成する．

次の呼出し側を検索して更新する．

```sh
rg -n 'toBuiltinTotalMatchingAtomTyping' TypePM
```

少なくとも`M4Paper1SafetyRegression.lean`と
`M4MatchingAtomRuntimeBridgeRegression.lean`が対象になる．

`M4MatchingAtomRuntimeBridgeRegression.lean`のtuple例は削除しない．従来の
`tupleMatcher_typed : ValueTyping ... (.matcher ...)`をslot型の証拠へ変更し，
`CheckConversion.productMatcherToSlot`を使って同じ実行時tuple matcherが扱えることを固定する．

### 6. 単独変換専用の回帰と反例を整理する

`TypePM/Regression.lean`では次を行う．

- `pair_checks_as_matcher`を削除する．
- 代わりに，同じpairが明示的な`Matcher ...`期待型では検査に失敗する負の回帰を追加する．
- `pair_checks_as_slot`は残し，`productMatcherToSlot`による成功を固定する．
- `pair_does_not_synthesize_matcher`は残す．

`TypePM/GeneratedSemanticAcceptanceRegression.lean`は，単独`productMatcher`が存在することを前提にした
反例だけを収録している．この変換を削除すると反例の前提が消えるため，ファイルを削除し，
`TypePM.lean`のimportと`TypePM/AxiomAudit.lean`の対応するaudit行も削除する．同じ内容を別名で残さない．

`TypePM/Source/M4RawOriginRequestCertificateRegression.lean`では，次の単独変換専用定理と，それだけに
依存する証明を削除する．

- `actualMatcherProduct_conversion`
- `actualMatcherProduct_targetFuelSafe`

`actualMatcherProductToSlot_conversion`と`actualMatcherProduct_slotFuelSafe`は残す．
`AxiomAudit.lean`のaudit行も同じ基準で更新する．

### 7. 公開説明とauditを新仕様へ合わせる

`README.md`のmatcherと制約の説明へ，次の内容を標準的な用語で追記する．

> matcherの非空積はmatcher producer型へ暗黙変換しない．利用箇所が明示するmatcher slotへだけ，
> 積から直接変換する．

`TypePM/AxiomAudit.lean`では次を行う．

- 削除した定理のaudit行を削除する．
- 改名した`special_expected_slot`と`source_eq_target_of_target_not_slot`をauditする．
- 新しく追加した負の回帰が公開定理ならauditへ追加する．
- 現在作業中の新規ファイルにも古い定理名の参照があり得るため，追跡済みファイルだけに限定せず
  `rg`の結果をすべて更新する．

## 必須回帰

変更後は少なくとも次をLeanの定理として固定する．

1. `Prod [Matcher ...]`は対応する`Slot ...`へ検査できる．
2. 同じ`Prod [Matcher ...]`は`Matcher ...`期待型へ検査できない．
3. `resolve (Prod [Matcher ...]) (Matcher ...)`は`.ordinary`分岐を選び，残差型等式は解けない．
4. `resolve (Prod [Matcher ...]) (Slot ...)`は従来どおり`productMatcherToSlot`分岐を選ぶ．
5. 単独の`Matcher ...`から`Slot ...`への`matcherToSlot`は従来どおり成功する．
6. tuple matcherを使う既存のruntime bridge回帰は，slot型の証拠を使って成功する．
7. Paper 1の既存`matchAll`とmatcher clauseの回帰がすべて通る．

## 完了確認

まず残存参照を確認する．`productMatcherToSlot`は残すため，単純な部分文字列検索ではなく単語境界を使う．

```sh
rg -n '\bproductMatcher\b' TypePM --glob '*.lean'
rg -n 'mayBecomeExpectedMatcher' TypePM --glob '*.lean'
rg -n 'source_eq_target_of_target_not_matcher_or_slot' TypePM --glob '*.lean'
```

三つとも出力が空であること．続いてリポジトリ直下で全体を検証する．

```sh
lake build
```

最後に次を確認する．

- `productMatcherToSlot`の定義・resolution・soundness・runtime safetyが残っている．
- expectedが`Matcher`のobligationを特殊変換候補としてpendingに保持していない．
- `matchAll`と次matcherの期待型が`Slot`のままである．
- 削除した変換を別名や補助公理で復活させていない．
- `sorry`，`admit`，新しい公理がない．
- ユーザーの無関係な変更をcommitへ混ぜていない．

`lake build`と必要な回帰が通ったら，このリポジトリの`AGENTS.md`に従い，この変更だけをcommitして
pushする．関連する既存変更と安全に分離できない場合はcommit／pushせず，その状況を報告する．
