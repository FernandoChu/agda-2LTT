# Identity types

```agda
module foundation-core.identity-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Theᵉ {{#conceptᵉ "equality"ᵉ Agda=Idᵉ}} relationᵉ isᵉ definedᵉ in typeᵉ theoryᵉ byᵉ theᵉ
{{#conceptᵉ "identityᵉ type"ᵉ Agda=Id}}.ᵉ Theᵉ identityᵉ typeᵉ onᵉ aᵉ typeᵉ `A`ᵉ isᵉ aᵉ
binaryᵉ familyᵉ ofᵉ typesᵉ

```text
  Idᵉ : Aᵉ → Aᵉ → 𝒰ᵉ
```

equippedᵉ with aᵉ
{{#conceptᵉ "reflexivityᵉ element"ᵉ Disambiguation="identityᵉ type"ᵉ Agda=reflᵉ}}

```text
  reflᵉ : (xᵉ : Aᵉ) → Idᵉ xᵉ x.ᵉ
```

Inᵉ otherᵉ words,ᵉ theᵉ identityᵉ typeᵉ isᵉ aᵉ reflexiveᵉ
[typeᵉ valuedᵉ relation](foundation.binary-relations.mdᵉ) onᵉ `A`.ᵉ Furthermore,ᵉ theᵉ
identityᵉ typeᵉ onᵉ `A`ᵉ satisfiesᵉ theᵉ
[universalᵉ property](foundation.universal-property-identity-types.mdᵉ) thatᵉ itᵉ
mapsᵉ uniquelyᵉ intoᵉ anyᵉ otherᵉ reflexiveᵉ relation.ᵉ

Inᵉ typeᵉ theory,ᵉ weᵉ introduceᵉ theᵉ identityᵉ typeᵉ asᵉ anᵉ inductive familyᵉ ofᵉ types,ᵉ
where theᵉ inductionᵉ principleᵉ canᵉ beᵉ understoodᵉ asᵉ expressingᵉ thatᵉ theᵉ identityᵉ
typeᵉ isᵉ theᵉ leastᵉ reflexiveᵉ relation.ᵉ

### Notation of the identity type

Weᵉ includeᵉ twoᵉ notationsᵉ forᵉ theᵉ identityᵉ type.ᵉ First,ᵉ weᵉ introduceᵉ theᵉ identityᵉ
typeᵉ using Martin-Löf'sᵉ originalᵉ notationᵉ `Id`.ᵉ Thenᵉ weᵉ introduceᵉ asᵉ aᵉ secondaryᵉ
optionᵉ theᵉ infix notationᵉ `_＝_`.ᵉ

**Note**ᵉ: Theᵉ equalsᵉ signᵉ in theᵉ infix notationᵉ isᵉ notᵉ theᵉ standardᵉ equalsᵉ signᵉ
onᵉ yourᵉ keyboard,ᵉ butᵉ itᵉ isᵉ theᵉ
[fullᵉ widthᵉ equalsᵉ sign](https://codepoints.net/U+ff1d).ᵉ Noteᵉ thatᵉ theᵉ fullᵉ
widthᵉ equalsᵉ signᵉ isᵉ slightlyᵉ wider,ᵉ andᵉ itᵉ isᵉ highlightedᵉ likeᵉ allᵉ theᵉ otherᵉ
definedᵉ constructionsᵉ in Agda.ᵉ Inᵉ orderᵉ to typeᵉ theᵉ fullᵉ widthᵉ equalsᵉ signᵉ in
Agda'sᵉ Emacsᵉ Mode,ᵉ youᵉ needᵉ to addᵉ itᵉ to yourᵉ agdaᵉ inputᵉ methodᵉ asᵉ followsᵉ:

-ᵉ Typeᵉ `M-xᵉ customize-variable`ᵉ andᵉ pressᵉ enter.ᵉ
-ᵉ Typeᵉ `agda-input-user-translations`ᵉ andᵉ pressᵉ enter.ᵉ
-ᵉ Clickᵉ theᵉ `INS`ᵉ buttonᵉ
-ᵉ Typeᵉ theᵉ regularᵉ equalsᵉ signᵉ `=`ᵉ in theᵉ Keyᵉ sequenceᵉ field.ᵉ
-ᵉ Clickᵉ theᵉ `INS`ᵉ buttonᵉ
-ᵉ Typeᵉ theᵉ fullᵉ widthᵉ equalsᵉ signᵉ `＝`ᵉ in theᵉ translationsᵉ field.ᵉ
-ᵉ Clickᵉ theᵉ `Applyᵉ andᵉ save`ᵉ button.ᵉ

Afterᵉ completingᵉ theseᵉ steps,ᵉ youᵉ canᵉ typeᵉ `\=`ᵉ in orderᵉ to obtainᵉ theᵉ fullᵉ
widthᵉ equalsᵉ signᵉ `＝`.ᵉ

## Table of files directly related to identity types

Theᵉ followingᵉ tableᵉ listsᵉ filesᵉ thatᵉ areᵉ aboutᵉ identityᵉ typesᵉ andᵉ operationsᵉ onᵉ
identificationsᵉ in arbitraryᵉ types.ᵉ

{{#includeᵉ tables/identity-types.mdᵉ}}

## Definition

### Identity types

Weᵉ introduceᵉ identityᵉ typesᵉ asᵉ aᵉ `data`ᵉ type.ᵉ Thisᵉ isᵉ Agda'sᵉ mechanismᵉ ofᵉ
introducingᵉ typesᵉ equippedᵉ with inductionᵉ principles.ᵉ Theᵉ onlyᵉ constructor ofᵉ
theᵉ identityᵉ typeᵉ `Idᵉ xᵉ : Aᵉ → 𝒰`ᵉ isᵉ theᵉ reflexivityᵉ identificationᵉ

```text
  reflᵉ : Idᵉ xᵉ x.ᵉ
```

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  data Idᵉ (xᵉ : Aᵉ) : Aᵉ → UUᵉ lᵉ where
    instance reflᵉ : Idᵉ xᵉ xᵉ

  infix 6 _＝ᵉ_
  _＝ᵉ_ : Aᵉ → Aᵉ → UUᵉ lᵉ
  (aᵉ ＝ᵉ bᵉ) = Idᵉ aᵉ bᵉ


```

Weᵉ markedᵉ `refl`ᵉ asᵉ anᵉ `instance`ᵉ to enableᵉ Agdaᵉ to automaticallyᵉ insertᵉ `refl`ᵉ
in definitionsᵉ thatᵉ makeᵉ useᵉ ofᵉ Agda'sᵉ
[instanceᵉ searchᵉ mechanism](https://agda.readthedocs.io/en/latest/language/instance-arguments.html).ᵉ

Furthermore,ᵉ weᵉ markedᵉ theᵉ identityᵉ typeᵉ asᵉ
[`BUILTIN`](https://agda.readthedocs.io/en/latest/language/built-ins.htmlᵉ) in
orderᵉ to supportᵉ fasterᵉ typeᵉ checking.ᵉ

### The induction principle of identity types

Theᵉ inductionᵉ principleᵉ ofᵉ identityᵉ typesᵉ statesᵉ thatᵉ givenᵉ aᵉ baseᵉ pointᵉ `xᵉ : A`ᵉ
andᵉ aᵉ familyᵉ ofᵉ typesᵉ overᵉ theᵉ identityᵉ typesᵉ basedᵉ atᵉ `x`,ᵉ
`Bᵉ : (yᵉ : Aᵉ) (pᵉ : xᵉ ＝ᵉ yᵉ) → UUᵉ l2`,ᵉ thenᵉ to constructᵉ aᵉ dependentᵉ functionᵉ
`fᵉ : (yᵉ : Aᵉ) (pᵉ : xᵉ ＝ᵉ yᵉ) → Bᵉ yᵉ p`ᵉ itᵉ sufficesᵉ to defineᵉ itᵉ atᵉ `fᵉ xᵉ refl`.ᵉ

Noteᵉ thatᵉ Agda'sᵉ pattern matchingᵉ machineryᵉ allowsᵉ usᵉ to defineᵉ manyᵉ operationsᵉ
onᵉ theᵉ identityᵉ typeᵉ directly.ᵉ However,ᵉ sometimesᵉ itᵉ isᵉ usefulᵉ to explicitlyᵉ
haveᵉ theᵉ inductionᵉ principleᵉ ofᵉ theᵉ identityᵉ type.ᵉ

```agda
ind-Idᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  (xᵉ : Aᵉ) (Bᵉ : (yᵉ : Aᵉ) (pᵉ : xᵉ ＝ᵉ yᵉ) → UUᵉ l2ᵉ) →
  (Bᵉ xᵉ reflᵉ) → (yᵉ : Aᵉ) (pᵉ : xᵉ ＝ᵉ yᵉ) → Bᵉ yᵉ pᵉ
ind-Idᵉ xᵉ Bᵉ bᵉ yᵉ reflᵉ = bᵉ
```

## Operations on the identity type

Theᵉ identityᵉ typesᵉ formᵉ aᵉ weakᵉ groupoidalᵉ structureᵉ onᵉ types.ᵉ Thusᵉ theyᵉ comeᵉ
equippedᵉ with
{{#conceptᵉ "concatenation"ᵉ Disambiguation="identifications"ᵉ Agda=concatᵉ}}
`(xᵉ ＝ᵉ yᵉ) → (yᵉ ＝ᵉ zᵉ) → (xᵉ ＝ᵉ z)`ᵉ andᵉ anᵉ
{{#conceptᵉ "inverse"ᵉ Disambiguation="identification"ᵉ Agda=invᵉ}} operationᵉ
`(xᵉ ＝ᵉ yᵉ) → (yᵉ ＝ᵉ x)`.ᵉ

Thereᵉ areᵉ manyᵉ moreᵉ operationsᵉ onᵉ identityᵉ types.ᵉ Someᵉ ofᵉ themᵉ areᵉ definedᵉ in
[pathᵉ algebra](foundation.path-algebra.mdᵉ) andᵉ
[whiskeringᵉ ofᵉ identifications](foundation.whiskering-identifications-concatenation.md).ᵉ
Forᵉ aᵉ completeᵉ referenceᵉ to allᵉ theᵉ filesᵉ aboutᵉ generalᵉ identityᵉ types,ᵉ seeᵉ theᵉ
tableᵉ givenᵉ above.ᵉ

### Concatenation of identifications

Theᵉ
{{#conceptᵉ "concatenationᵉ operationᵉ onᵉ identifications"ᵉ Agda=_∙ᵉ_ Agda=_∙'ᵉ_ Agda=concatᵉ}}
isᵉ aᵉ familyᵉ ofᵉ binaryᵉ operationsᵉ

```text
  _∙ᵉ_ : xᵉ ＝ᵉ yᵉ → yᵉ ＝ᵉ zᵉ → xᵉ ＝ᵉ zᵉ
```

indexedᵉ byᵉ `xᵉ yᵉ zᵉ : A`.ᵉ However,ᵉ thereᵉ areᵉ essentiallyᵉ threeᵉ differentᵉ waysᵉ weᵉ
canᵉ defineᵉ concatenationᵉ ofᵉ identifications,ᵉ allᵉ with differentᵉ computationalᵉ
behaviours.ᵉ

1.ᵉ Weᵉ canᵉ defineᵉ concatenationᵉ byᵉ inductionᵉ onᵉ theᵉ equalityᵉ `xᵉ ＝ᵉ y`.ᵉ Thisᵉ givesᵉ
   usᵉ theᵉ computationᵉ ruleᵉ `reflᵉ ∙ᵉ qᵉ ≐ᵉ q`.ᵉ
2.ᵉ Weᵉ canᵉ defineᵉ concatenationᵉ byᵉ inductionᵉ onᵉ theᵉ equalityᵉ `yᵉ ＝ᵉ z`.ᵉ Thisᵉ givesᵉ
   usᵉ theᵉ computationᵉ ruleᵉ `pᵉ ∙ᵉ reflᵉ ≐ᵉ p`.ᵉ
3.ᵉ Weᵉ canᵉ defineᵉ concatenationᵉ byᵉ inductionᵉ onᵉ bothᵉ `xᵉ ＝ᵉ y`ᵉ andᵉ `yᵉ ＝ᵉ z`.ᵉ Thisᵉ
   onlyᵉ givesᵉ usᵉ theᵉ computationᵉ ruleᵉ `reflᵉ ∙ᵉ reflᵉ ≐ᵉ refl`.ᵉ

Whileᵉ theᵉ thirdᵉ optionᵉ mayᵉ beᵉ preferredᵉ byᵉ someᵉ forᵉ itsᵉ symmetry,ᵉ forᵉ practicalᵉ
reasons,ᵉ weᵉ preferᵉ oneᵉ ofᵉ theᵉ firstᵉ two,ᵉ andᵉ byᵉ conventionᵉ weᵉ useᵉ theᵉ firstᵉ
alternative.ᵉ

Theᵉ secondᵉ optionᵉ isᵉ consideredᵉ in
[`foundation.strictly-right-unital-concatenation-identifications`](foundation.strictly-right-unital-concatenation-identifications.md),ᵉ
andᵉ in [`foundation.yoneda-identity-types`](foundation.yoneda-identity-types.mdᵉ)
weᵉ constructᵉ anᵉ identityᵉ typeᵉ whichᵉ satisfiesᵉ bothᵉ computationᵉ rulesᵉ amongᵉ
others.ᵉ

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  infixl 15 _∙ᵉ_
  _∙ᵉ_ : {xᵉ yᵉ zᵉ : Aᵉ} → xᵉ ＝ᵉ yᵉ → yᵉ ＝ᵉ zᵉ → xᵉ ＝ᵉ zᵉ
  reflᵉ ∙ᵉ qᵉ = qᵉ

  concatᵉ : {xᵉ yᵉ : Aᵉ} → xᵉ ＝ᵉ yᵉ → (zᵉ : Aᵉ) → yᵉ ＝ᵉ zᵉ → xᵉ ＝ᵉ zᵉ
  concatᵉ pᵉ zᵉ qᵉ = pᵉ ∙ᵉ qᵉ

  concat'ᵉ : (xᵉ : Aᵉ) {yᵉ zᵉ : Aᵉ} → yᵉ ＝ᵉ zᵉ → xᵉ ＝ᵉ yᵉ → xᵉ ＝ᵉ zᵉ
  concat'ᵉ xᵉ qᵉ pᵉ = pᵉ ∙ᵉ qᵉ
```

### Inverting identifications

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  invᵉ : {xᵉ yᵉ : Aᵉ} → xᵉ ＝ᵉ yᵉ → yᵉ ＝ᵉ xᵉ
  invᵉ reflᵉ = reflᵉ
```

### Concatenating with inverse identifications

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  inv-concatᵉ : {xᵉ yᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) (zᵉ : Aᵉ) → xᵉ ＝ᵉ zᵉ → yᵉ ＝ᵉ zᵉ
  inv-concatᵉ pᵉ = concatᵉ (invᵉ pᵉ)

  inv-concat'ᵉ : (xᵉ : Aᵉ) {yᵉ zᵉ : Aᵉ} → yᵉ ＝ᵉ zᵉ → xᵉ ＝ᵉ zᵉ → xᵉ ＝ᵉ yᵉ
  inv-concat'ᵉ xᵉ qᵉ = concat'ᵉ xᵉ (invᵉ qᵉ)
```

## Properties

### Associativity of concatenation

Forᵉ anyᵉ threeᵉ identificationsᵉ `pᵉ : xᵉ ＝ᵉ y`,ᵉ `qᵉ : yᵉ ＝ᵉ z`,ᵉ andᵉ `rᵉ : zᵉ ＝ᵉ w`,ᵉ weᵉ
haveᵉ anᵉ identificationᵉ

```text
  assocᵉ pᵉ qᵉ rᵉ : ((pᵉ ∙ᵉ qᵉ) ∙ᵉ rᵉ) ＝ᵉ (pᵉ ∙ᵉ (qᵉ ∙ᵉ r)).ᵉ
```

Theᵉ identificationᵉ `assocᵉ pᵉ qᵉ r`ᵉ isᵉ alsoᵉ calledᵉ theᵉ
{{#conceptᵉ "associator"ᵉ Disambiguation="identification"ᵉ Agda=assoc}}.ᵉ

Noteᵉ thatᵉ theᵉ associatorᵉ `assocᵉ pᵉ qᵉ r`ᵉ isᵉ anᵉ identificationᵉ in theᵉ typeᵉ
`xᵉ ＝ᵉ w`,ᵉ i.e.,ᵉ itᵉ isᵉ anᵉ identificationᵉ ofᵉ identifications.ᵉ Hereᵉ weᵉ makeᵉ crucialᵉ
useᵉ ofᵉ theᵉ factᵉ thatᵉ theᵉ identityᵉ typesᵉ areᵉ definedᵉ _forᵉ allᵉ types_.ᵉ Inᵉ otherᵉ
words,ᵉ sinceᵉ identityᵉ typesᵉ areᵉ themselvesᵉ types,ᵉ weᵉ canᵉ considerᵉ identityᵉ typesᵉ
ofᵉ identityᵉ types,ᵉ andᵉ soᵉ on.ᵉ

#### Associators

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  assocᵉ :
    {xᵉ yᵉ zᵉ wᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) (qᵉ : yᵉ ＝ᵉ zᵉ) (rᵉ : zᵉ ＝ᵉ wᵉ) →
    ((pᵉ ∙ᵉ qᵉ) ∙ᵉ rᵉ) ＝ᵉ (pᵉ ∙ᵉ (qᵉ ∙ᵉ rᵉ))
  assocᵉ reflᵉ qᵉ rᵉ = reflᵉ
```

### The unit laws for concatenation

Forᵉ anyᵉ identificationᵉ `pᵉ : xᵉ ＝ᵉ y`ᵉ thereᵉ isᵉ anᵉ identificationᵉ

```text
  left-unitᵉ : (reflᵉ ∙ᵉ pᵉ) ＝ᵉ p.ᵉ
```

Similarly,ᵉ thereᵉ isᵉ anᵉ identificationᵉ

```text
  right-unitᵉ : (pᵉ ∙ᵉ reflᵉ) ＝ᵉ p.ᵉ
```

Inᵉ otherᵉ words,ᵉ theᵉ reflexivityᵉ identificationᵉ isᵉ aᵉ unitᵉ elementᵉ forᵉ
concatenationᵉ ofᵉ identifications.ᵉ

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  double-assocᵉ :
    {xᵉ yᵉ zᵉ wᵉ vᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) (qᵉ : yᵉ ＝ᵉ zᵉ) (rᵉ : zᵉ ＝ᵉ wᵉ) (sᵉ : wᵉ ＝ᵉ vᵉ) →
    (((pᵉ ∙ᵉ qᵉ) ∙ᵉ rᵉ) ∙ᵉ sᵉ) ＝ᵉ pᵉ ∙ᵉ (qᵉ ∙ᵉ (rᵉ ∙ᵉ sᵉ))
  double-assocᵉ reflᵉ qᵉ rᵉ sᵉ = assocᵉ qᵉ rᵉ sᵉ

  triple-assocᵉ :
    {xᵉ yᵉ zᵉ wᵉ vᵉ uᵉ : Aᵉ}
    (pᵉ : xᵉ ＝ᵉ yᵉ) (qᵉ : yᵉ ＝ᵉ zᵉ) (rᵉ : zᵉ ＝ᵉ wᵉ) (sᵉ : wᵉ ＝ᵉ vᵉ) (tᵉ : vᵉ ＝ᵉ uᵉ) →
    ((((pᵉ ∙ᵉ qᵉ) ∙ᵉ rᵉ) ∙ᵉ sᵉ) ∙ᵉ tᵉ) ＝ᵉ pᵉ ∙ᵉ (qᵉ ∙ᵉ (rᵉ ∙ᵉ (sᵉ ∙ᵉ tᵉ)))
  triple-assocᵉ reflᵉ qᵉ rᵉ sᵉ tᵉ = double-assocᵉ qᵉ rᵉ sᵉ tᵉ
```

#### Unit laws

```agda
  left-unitᵉ : {xᵉ yᵉ : Aᵉ} {pᵉ : xᵉ ＝ᵉ yᵉ} → reflᵉ ∙ᵉ pᵉ ＝ᵉ pᵉ
  left-unitᵉ = reflᵉ

  right-unitᵉ : {xᵉ yᵉ : Aᵉ} {pᵉ : xᵉ ＝ᵉ yᵉ} → pᵉ ∙ᵉ reflᵉ ＝ᵉ pᵉ
  right-unitᵉ {pᵉ = reflᵉ} = reflᵉ
```

### The inverse laws for concatenation

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  left-invᵉ : {xᵉ yᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) → invᵉ pᵉ ∙ᵉ pᵉ ＝ᵉ reflᵉ
  left-invᵉ reflᵉ = reflᵉ

  right-invᵉ : {xᵉ yᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) → pᵉ ∙ᵉ (invᵉ pᵉ) ＝ᵉ reflᵉ
  right-invᵉ reflᵉ = reflᵉ
```

### Inverting identifications is an involution

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  inv-invᵉ : {xᵉ yᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) → invᵉ (invᵉ pᵉ) ＝ᵉ pᵉ
  inv-invᵉ reflᵉ = reflᵉ
```

### Inverting identifications distributes over concatenation

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  distributive-inv-concatᵉ :
    {xᵉ yᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) {zᵉ : Aᵉ} (qᵉ : yᵉ ＝ᵉ zᵉ) →
    invᵉ (pᵉ ∙ᵉ qᵉ) ＝ᵉ invᵉ qᵉ ∙ᵉ invᵉ pᵉ
  distributive-inv-concatᵉ reflᵉ reflᵉ = reflᵉ
```

### Concatenating with an inverse is inverse to concatenating

Weᵉ showᵉ thatᵉ theᵉ operationᵉ `qᵉ ↦ᵉ invᵉ pᵉ ∙ᵉ q`ᵉ isᵉ inverseᵉ to theᵉ operationᵉ
`qᵉ ↦ᵉ pᵉ ∙ᵉ q`ᵉ byᵉ constructingᵉ identificationsᵉ

```text
  invᵉ pᵉ ∙ᵉ (pᵉ ∙ᵉ qᵉ) ＝ᵉ qᵉ
  pᵉ ∙ᵉ (invᵉ pᵉ ∙ᵉ qᵉ) ＝ᵉ q.ᵉ
```

Similarly,ᵉ weᵉ showᵉ thatᵉ theᵉ operationᵉ `pᵉ ↦ᵉ pᵉ ∙ᵉ invᵉ q`ᵉ isᵉ inverseᵉ to theᵉ
operationᵉ `pᵉ ↦ᵉ pᵉ ∙ᵉ q`ᵉ byᵉ constructingᵉ identificationsᵉ

```text
  (pᵉ ∙ᵉ qᵉ) ∙ᵉ invᵉ qᵉ ＝ᵉ pᵉ
  (pᵉ ∙ᵉ invᵉ qᵉ) ∙ᵉ qᵉ ＝ᵉ p.ᵉ
```

Inᵉ [`foundation.identity-types`](foundation.identity-types.mdᵉ) weᵉ willᵉ useᵉ theseᵉ
familiesᵉ ofᵉ identificationsᵉ to concludeᵉ thatᵉ `concatᵉ pᵉ z`ᵉ andᵉ `concat'ᵉ xᵉ q`ᵉ areᵉ
[equivalences](foundation-core.equivalences.mdᵉ) with inversesᵉ `concatᵉ (invᵉ pᵉ) z`ᵉ
andᵉ `concat'ᵉ xᵉ (invᵉ q)`,ᵉ respectively.ᵉ

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  is-retraction-inv-concatᵉ :
    {xᵉ yᵉ zᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) (qᵉ : yᵉ ＝ᵉ zᵉ) → (invᵉ pᵉ ∙ᵉ (pᵉ ∙ᵉ qᵉ)) ＝ᵉ qᵉ
  is-retraction-inv-concatᵉ reflᵉ qᵉ = reflᵉ

  is-section-inv-concatᵉ :
    {xᵉ yᵉ zᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) (rᵉ : xᵉ ＝ᵉ zᵉ) → (pᵉ ∙ᵉ (invᵉ pᵉ ∙ᵉ rᵉ)) ＝ᵉ rᵉ
  is-section-inv-concatᵉ reflᵉ rᵉ = reflᵉ

  is-retraction-inv-concat'ᵉ :
    {xᵉ yᵉ zᵉ : Aᵉ} (qᵉ : yᵉ ＝ᵉ zᵉ) (pᵉ : xᵉ ＝ᵉ yᵉ) → (pᵉ ∙ᵉ qᵉ) ∙ᵉ invᵉ qᵉ ＝ᵉ pᵉ
  is-retraction-inv-concat'ᵉ reflᵉ reflᵉ = reflᵉ

  is-section-inv-concat'ᵉ :
    {xᵉ yᵉ zᵉ : Aᵉ} (qᵉ : yᵉ ＝ᵉ zᵉ) (rᵉ : xᵉ ＝ᵉ zᵉ) → (rᵉ ∙ᵉ invᵉ qᵉ) ∙ᵉ qᵉ ＝ᵉ rᵉ
  is-section-inv-concat'ᵉ reflᵉ reflᵉ = reflᵉ
```

### Transposing inverses

Considerᵉ aᵉ triangleᵉ ofᵉ identificationsᵉ

```text
      pᵉ
  xᵉ ---->ᵉ yᵉ
   \ᵉ     /ᵉ
  rᵉ \ᵉ   /ᵉ qᵉ
     ∨ᵉ ∨ᵉ
      zᵉ
```

in aᵉ typeᵉ `A`.ᵉ Thenᵉ weᵉ haveᵉ mapsᵉ

```text
  pᵉ ∙ᵉ qᵉ ＝ᵉ rᵉ → qᵉ ＝ᵉ invᵉ pᵉ ∙ᵉ rᵉ
  pᵉ ∙ᵉ qᵉ ＝ᵉ rᵉ → pᵉ ＝ᵉ rᵉ ∙ᵉ invᵉ q.ᵉ
```

Inᵉ [`foundation.identity-types`](foundation.identity-types.mdᵉ) weᵉ willᵉ showᵉ thatᵉ
theseᵉ mapsᵉ areᵉ equivalences.ᵉ

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  left-transpose-eq-concatᵉ :
    {xᵉ yᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) {zᵉ : Aᵉ} (qᵉ : yᵉ ＝ᵉ zᵉ) (rᵉ : xᵉ ＝ᵉ zᵉ) →
    pᵉ ∙ᵉ qᵉ ＝ᵉ rᵉ → qᵉ ＝ᵉ invᵉ pᵉ ∙ᵉ rᵉ
  left-transpose-eq-concatᵉ reflᵉ qᵉ rᵉ sᵉ = sᵉ

  inv-left-transpose-eq-concatᵉ :
    {xᵉ yᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) {zᵉ : Aᵉ} (qᵉ : yᵉ ＝ᵉ zᵉ) (rᵉ : xᵉ ＝ᵉ zᵉ) →
    qᵉ ＝ᵉ invᵉ pᵉ ∙ᵉ rᵉ → pᵉ ∙ᵉ qᵉ ＝ᵉ rᵉ
  inv-left-transpose-eq-concatᵉ reflᵉ qᵉ rᵉ sᵉ = sᵉ

  right-transpose-eq-concatᵉ :
    {xᵉ yᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) {zᵉ : Aᵉ} (qᵉ : yᵉ ＝ᵉ zᵉ) (rᵉ : xᵉ ＝ᵉ zᵉ) →
    pᵉ ∙ᵉ qᵉ ＝ᵉ rᵉ → pᵉ ＝ᵉ rᵉ ∙ᵉ invᵉ qᵉ
  right-transpose-eq-concatᵉ pᵉ reflᵉ rᵉ sᵉ = (invᵉ right-unitᵉ ∙ᵉ sᵉ) ∙ᵉ invᵉ right-unitᵉ

  inv-right-transpose-eq-concatᵉ :
    {xᵉ yᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) {zᵉ : Aᵉ} (qᵉ : yᵉ ＝ᵉ zᵉ) (rᵉ : xᵉ ＝ᵉ zᵉ) →
    pᵉ ＝ᵉ rᵉ ∙ᵉ invᵉ qᵉ → pᵉ ∙ᵉ qᵉ ＝ᵉ rᵉ
  inv-right-transpose-eq-concatᵉ pᵉ reflᵉ rᵉ sᵉ = right-unitᵉ ∙ᵉ (sᵉ ∙ᵉ right-unitᵉ)

  double-transpose-eq-concatᵉ :
    {xᵉ yᵉ uᵉ vᵉ : Aᵉ} (rᵉ : xᵉ ＝ᵉ uᵉ) (pᵉ : xᵉ ＝ᵉ yᵉ) (sᵉ : uᵉ ＝ᵉ vᵉ) (qᵉ : yᵉ ＝ᵉ vᵉ) →
    pᵉ ∙ᵉ qᵉ ＝ᵉ rᵉ ∙ᵉ sᵉ → invᵉ rᵉ ∙ᵉ pᵉ ＝ᵉ sᵉ ∙ᵉ invᵉ qᵉ
  double-transpose-eq-concatᵉ reflᵉ pᵉ sᵉ reflᵉ αᵉ =
    (invᵉ right-unitᵉ ∙ᵉ αᵉ) ∙ᵉ invᵉ right-unitᵉ

  double-transpose-eq-concat'ᵉ :
    {xᵉ yᵉ uᵉ vᵉ : Aᵉ} (rᵉ : xᵉ ＝ᵉ uᵉ) (pᵉ : xᵉ ＝ᵉ yᵉ) (sᵉ : uᵉ ＝ᵉ vᵉ) (qᵉ : yᵉ ＝ᵉ vᵉ) →
    pᵉ ∙ᵉ qᵉ ＝ᵉ rᵉ ∙ᵉ sᵉ → qᵉ ∙ᵉ invᵉ sᵉ ＝ᵉ invᵉ pᵉ ∙ᵉ rᵉ
  double-transpose-eq-concat'ᵉ rᵉ reflᵉ reflᵉ qᵉ αᵉ = right-unitᵉ ∙ᵉ (αᵉ ∙ᵉ right-unitᵉ)
```

### Splicing and unsplicing concatenations of identifications

Considerᵉ twoᵉ identificationsᵉ `pᵉ : aᵉ ＝ᵉ b`ᵉ andᵉ `qᵉ : bᵉ ＝ᵉ c`,ᵉ andᵉ considerᵉ twoᵉ
furtherᵉ identificationsᵉ `rᵉ : bᵉ ＝ᵉ x`ᵉ andᵉ `sᵉ : xᵉ ＝ᵉ b`ᵉ equippedᵉ with anᵉ
identificationᵉ `invᵉ rᵉ ＝ᵉ s`,ᵉ asᵉ indicatedᵉ in theᵉ diagramᵉ

```text
           xᵉ
          ∧ᵉ |
        rᵉ | | sᵉ
          | ∨ᵉ
  aᵉ ----->ᵉ bᵉ ----->ᵉ c.ᵉ
```

Thenᵉ weᵉ haveᵉ identificationsᵉ

```text
    splice-concatᵉ : pᵉ ∙ᵉ qᵉ ＝ᵉ (pᵉ ∙ᵉ rᵉ) ∙ᵉ (sᵉ ∙ᵉ qᵉ)
  unsplice-concatᵉ : (pᵉ ∙ᵉ rᵉ) ∙ᵉ (sᵉ ∙ᵉ qᵉ) ＝ᵉ pᵉ ∙ᵉ q.ᵉ
```

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  splice-concatᵉ :
    {aᵉ bᵉ cᵉ xᵉ : Aᵉ}
    (pᵉ : aᵉ ＝ᵉ bᵉ) {rᵉ : bᵉ ＝ᵉ xᵉ} {sᵉ : xᵉ ＝ᵉ bᵉ} (αᵉ : invᵉ rᵉ ＝ᵉ sᵉ) (qᵉ : bᵉ ＝ᵉ cᵉ) →
    pᵉ ∙ᵉ qᵉ ＝ᵉ (pᵉ ∙ᵉ rᵉ) ∙ᵉ (sᵉ ∙ᵉ qᵉ)
  splice-concatᵉ reflᵉ {rᵉ} reflᵉ qᵉ = invᵉ (is-section-inv-concatᵉ rᵉ qᵉ)

  splice-concat'ᵉ :
    {aᵉ bᵉ cᵉ xᵉ : Aᵉ}
    (pᵉ : aᵉ ＝ᵉ bᵉ) {rᵉ : bᵉ ＝ᵉ xᵉ} {sᵉ : xᵉ ＝ᵉ bᵉ} (αᵉ : rᵉ ＝ᵉ invᵉ sᵉ) (qᵉ : bᵉ ＝ᵉ cᵉ) →
    pᵉ ∙ᵉ qᵉ ＝ᵉ (pᵉ ∙ᵉ rᵉ) ∙ᵉ (sᵉ ∙ᵉ qᵉ)
  splice-concat'ᵉ reflᵉ {.(invᵉ sᵉ)} {sᵉ} reflᵉ qᵉ = invᵉ (is-retraction-inv-concatᵉ sᵉ qᵉ)

  unsplice-concatᵉ :
    {aᵉ bᵉ cᵉ xᵉ : Aᵉ}
    (pᵉ : aᵉ ＝ᵉ bᵉ) {rᵉ : bᵉ ＝ᵉ xᵉ} {sᵉ : xᵉ ＝ᵉ bᵉ} (αᵉ : invᵉ rᵉ ＝ᵉ sᵉ) (qᵉ : bᵉ ＝ᵉ cᵉ) →
    (pᵉ ∙ᵉ rᵉ) ∙ᵉ (sᵉ ∙ᵉ qᵉ) ＝ᵉ pᵉ ∙ᵉ qᵉ
  unsplice-concatᵉ pᵉ αᵉ qᵉ = invᵉ (splice-concatᵉ pᵉ αᵉ qᵉ)

  unsplice-concat'ᵉ :
    {aᵉ bᵉ cᵉ xᵉ : Aᵉ}
    (pᵉ : aᵉ ＝ᵉ bᵉ) {rᵉ : bᵉ ＝ᵉ xᵉ} {sᵉ : xᵉ ＝ᵉ bᵉ} (αᵉ : rᵉ ＝ᵉ invᵉ sᵉ) (qᵉ : bᵉ ＝ᵉ cᵉ) →
    (pᵉ ∙ᵉ rᵉ) ∙ᵉ (sᵉ ∙ᵉ qᵉ) ＝ᵉ pᵉ ∙ᵉ qᵉ
  unsplice-concat'ᵉ pᵉ αᵉ qᵉ = invᵉ (splice-concat'ᵉ pᵉ αᵉ qᵉ)
```

### Concatenation is injective

```agda
module _
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  where

  is-injective-concatᵉ :
    {xᵉ yᵉ zᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) {qᵉ rᵉ : yᵉ ＝ᵉ zᵉ} → pᵉ ∙ᵉ qᵉ ＝ᵉ pᵉ ∙ᵉ rᵉ → qᵉ ＝ᵉ rᵉ
  is-injective-concatᵉ reflᵉ sᵉ = sᵉ

  is-injective-concat'ᵉ :
    {xᵉ yᵉ zᵉ : Aᵉ} (rᵉ : yᵉ ＝ᵉ zᵉ) {pᵉ qᵉ : xᵉ ＝ᵉ yᵉ} → pᵉ ∙ᵉ rᵉ ＝ᵉ qᵉ ∙ᵉ rᵉ → pᵉ ＝ᵉ qᵉ
  is-injective-concat'ᵉ reflᵉ sᵉ = (invᵉ right-unitᵉ) ∙ᵉ (sᵉ ∙ᵉ right-unitᵉ)
```

## Equational reasoning

Identificationsᵉ canᵉ beᵉ constructedᵉ byᵉ equationalᵉ reasoningᵉ in theᵉ followingᵉ wayᵉ:

```text
equational-reasoningᵉ
  xᵉ ＝ᵉ yᵉ byᵉ eq-1ᵉ
    ＝ᵉ zᵉ byᵉ eq-2ᵉ
    ＝ᵉ vᵉ byᵉ eq-3ᵉ
```

Theᵉ resultingᵉ identificationᵉ ofᵉ thisᵉ computaionᵉ isᵉ `eq-1ᵉ ∙ᵉ (eq-2ᵉ ∙ᵉ eq-3)`,ᵉ i.e.,ᵉ
theᵉ identificationᵉ isᵉ associatedᵉ fullyᵉ to theᵉ right.ᵉ Forᵉ examplesᵉ ofᵉ theᵉ useᵉ ofᵉ
equationalᵉ reasoning,ᵉ seeᵉ
[addition-integers](elementary-number-theory.addition-integers.md).ᵉ

```agda
infixl 1 equational-reasoningᵉ_
infixl 0 step-equational-reasoningᵉ

equational-reasoningᵉ_ :
  {lᵉ : Level} {Xᵉ : UUᵉ lᵉ} (xᵉ : Xᵉ) → xᵉ ＝ᵉ xᵉ
equational-reasoningᵉ xᵉ = reflᵉ

step-equational-reasoningᵉ :
  {lᵉ : Level} {Xᵉ : UUᵉ lᵉ} {xᵉ yᵉ : Xᵉ} →
  (xᵉ ＝ᵉ yᵉ) → (uᵉ : Xᵉ) → (yᵉ ＝ᵉ uᵉ) → (xᵉ ＝ᵉ uᵉ)
step-equational-reasoningᵉ pᵉ zᵉ qᵉ = pᵉ ∙ᵉ qᵉ

syntax step-equational-reasoningᵉ pᵉ zᵉ qᵉ = pᵉ ＝ᵉ zᵉ byᵉ qᵉ
```

**Note.**ᵉ Equationalᵉ reasoningᵉ isᵉ aᵉ convenientᵉ wayᵉ to constructᵉ identifications.ᵉ
However,ᵉ in someᵉ situationsᵉ itᵉ mayᵉ notᵉ beᵉ theᵉ fastestᵉ orᵉ cleanestᵉ mechanismᵉ to
constructᵉ anᵉ identification.ᵉ Someᵉ constructionsᵉ ofᵉ identificationsᵉ naturallyᵉ
involveᵉ computationsᵉ thatᵉ areᵉ moreᵉ deeplyᵉ nestedᵉ in theᵉ terms.ᵉ Furthermore,ᵉ
proofsᵉ byᵉ equationalᵉ reasoningᵉ tendᵉ to requireᵉ aᵉ lotᵉ ofᵉ reassociation.ᵉ

Someᵉ toolsᵉ thatᵉ allowᵉ usᵉ to performᵉ fasterᵉ computationsᵉ areᵉ theᵉ transpositionsᵉ
definedᵉ above,ᵉ theᵉ transpositionsᵉ andᵉ splicingᵉ operationsᵉ definedᵉ in
[commutingᵉ squaresᵉ ofᵉ identifications](foundation.commuting-squares-of-identifications.mdᵉ)
andᵉ
[commutingᵉ trianglesᵉ ofᵉ identifications](foundation.commuting-triangles-of-identifications.md),ᵉ
andᵉ theᵉ higherᵉ concatenationᵉ operationsᵉ definedᵉ in
[pathᵉ algebra](foundation.path-algebra.md).ᵉ Eachᵉ ofᵉ theseᵉ operationsᵉ hasᵉ goodᵉ
computationalᵉ behavior,ᵉ soᵉ thereᵉ isᵉ infrastructureᵉ forᵉ reasoningᵉ aboutᵉ
identificationsᵉ thatᵉ areᵉ constructedᵉ using them.ᵉ

Weᵉ alsoᵉ noteᵉ thatᵉ thereᵉ isᵉ similarᵉ infrastructureᵉ forᵉ
[homotopyᵉ reasoning](foundation-core.homotopies.md).ᵉ

## References

Ourᵉ setupᵉ ofᵉ equationalᵉ reasoningᵉ isᵉ derivedᵉ fromᵉ theᵉ followingᵉ sourcesᵉ:

1.ᵉ Martínᵉ Escardó.ᵉ
   <https://github.com/martinescardo/TypeTopology/blob/master/source/Id.lagda>ᵉ

2.ᵉ Martínᵉ Escardó.ᵉ
   <https://github.com/martinescardo/TypeTopology/blob/master/source/UF-Equiv.lagda>ᵉ

3.ᵉ Theᵉ Agdaᵉ standardᵉ library.ᵉ
   <https://github.com/agda/agda-stdlib/blob/master/src/Relation/Binary/PropositionalEquality/Core.agda>ᵉ