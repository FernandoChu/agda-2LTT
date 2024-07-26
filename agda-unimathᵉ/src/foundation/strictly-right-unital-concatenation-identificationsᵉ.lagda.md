# The strictly right unital concatenation operation on identifications

```agda
module foundation.strictly-right-unital-concatenation-identificationsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.identity-typesᵉ
```

</details>

## Idea

Theᵉ concatenationᵉ operationᵉ onᵉ
[identifications](foundation-core.identity-types.mdᵉ) isᵉ aᵉ familyᵉ ofᵉ binaryᵉ
operationsᵉ

```text
  _∙ᵉ_ : xᵉ ＝ᵉ yᵉ → yᵉ ＝ᵉ zᵉ → xᵉ ＝ᵉ zᵉ
```

indexedᵉ byᵉ `xᵉ yᵉ zᵉ : A`.ᵉ However,ᵉ thereᵉ areᵉ essentiallyᵉ threeᵉ differentᵉ waysᵉ weᵉ
canᵉ defineᵉ concatenationᵉ ofᵉ identifications,ᵉ allᵉ with differentᵉ computationalᵉ
behavioursᵉ:

1.ᵉ Weᵉ canᵉ defineᵉ concatenationᵉ byᵉ inductionᵉ onᵉ theᵉ equalityᵉ `xᵉ ＝ᵉ y`.ᵉ Thisᵉ givesᵉ
   usᵉ theᵉ computationᵉ ruleᵉ `reflᵉ ∙ᵉ qᵉ ≐ᵉ q`.ᵉ
2.ᵉ Weᵉ canᵉ defineᵉ concatenationᵉ byᵉ inductionᵉ onᵉ theᵉ equalityᵉ `yᵉ ＝ᵉ z`.ᵉ Thisᵉ givesᵉ
   usᵉ theᵉ computationᵉ ruleᵉ `pᵉ ∙ᵉ reflᵉ ≐ᵉ p`.ᵉ
3.ᵉ Weᵉ canᵉ defineᵉ concatenationᵉ byᵉ inductionᵉ onᵉ bothᵉ `xᵉ ＝ᵉ y`ᵉ andᵉ `yᵉ ＝ᵉ z`.ᵉ Thisᵉ
   onlyᵉ givesᵉ usᵉ theᵉ computationᵉ ruleᵉ `reflᵉ ∙ᵉ reflᵉ ≐ᵉ refl`.ᵉ

Whileᵉ theᵉ thirdᵉ optionᵉ mayᵉ beᵉ preferredᵉ byᵉ someᵉ forᵉ itsᵉ symmetry,ᵉ forᵉ practicalᵉ
reasons,ᵉ weᵉ preferᵉ oneᵉ ofᵉ theᵉ firstᵉ two,ᵉ andᵉ byᵉ conventionᵉ weᵉ useᵉ theᵉ firstᵉ
alternative.ᵉ However,ᵉ thereᵉ areᵉ casesᵉ where theᵉ secondᵉ caseᵉ mayᵉ beᵉ preferred.ᵉ
Henceᵉ whyᵉ weᵉ onᵉ thisᵉ pageᵉ considerᵉ theᵉ
{{#conceptᵉ "strictlyᵉ rightᵉ unitalᵉ concatenationᵉ operationᵉ onᵉ identifications"ᵉ Agda=_∙ᵣᵉ_ Agda=right-strict-concatᵉ Agda=right-strict-concat'}}.ᵉ

Thisᵉ definitionᵉ isᵉ forᵉ instance usedᵉ with theᵉ
[strictlyᵉ involutiveᵉ identityᵉ types](foundation.strictly-involutive-identity-types.mdᵉ)
to constructᵉ aᵉ strictlyᵉ leftᵉ unitalᵉ concatenationᵉ operation.ᵉ

## Definition

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  infixl 15 _∙ᵣᵉ_
  _∙ᵣᵉ_ : {xᵉ yᵉ zᵉ : Aᵉ} → xᵉ ＝ᵉ yᵉ → yᵉ ＝ᵉ zᵉ → xᵉ ＝ᵉ zᵉ
  pᵉ ∙ᵣᵉ reflᵉ = pᵉ

  right-strict-concatᵉ : {xᵉ yᵉ : Aᵉ} → xᵉ ＝ᵉ yᵉ → (zᵉ : Aᵉ) → yᵉ ＝ᵉ zᵉ → xᵉ ＝ᵉ zᵉ
  right-strict-concatᵉ pᵉ zᵉ qᵉ = pᵉ ∙ᵣᵉ qᵉ

  right-strict-concat'ᵉ : (xᵉ : Aᵉ) {yᵉ zᵉ : Aᵉ} → yᵉ ＝ᵉ zᵉ → xᵉ ＝ᵉ yᵉ → xᵉ ＝ᵉ zᵉ
  right-strict-concat'ᵉ xᵉ qᵉ pᵉ = pᵉ ∙ᵣᵉ qᵉ
```

### Translating between the stictly left and stricly right unital versions of concatenation

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  eq-right-strict-concat-concatᵉ :
    {xᵉ yᵉ zᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) (qᵉ : yᵉ ＝ᵉ zᵉ) → pᵉ ∙ᵉ qᵉ ＝ᵉ pᵉ ∙ᵣᵉ qᵉ
  eq-right-strict-concat-concatᵉ pᵉ reflᵉ = right-unitᵉ

  eq-concat-right-strict-concatᵉ :
    {xᵉ yᵉ zᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) (qᵉ : yᵉ ＝ᵉ zᵉ) → pᵉ ∙ᵣᵉ qᵉ ＝ᵉ pᵉ ∙ᵉ qᵉ
  eq-concat-right-strict-concatᵉ pᵉ qᵉ = invᵉ (eq-right-strict-concat-concatᵉ pᵉ qᵉ)

  eq-double-right-strict-concat-concat-left-associatedᵉ :
    {xᵉ yᵉ zᵉ wᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) (qᵉ : yᵉ ＝ᵉ zᵉ) (rᵉ : zᵉ ＝ᵉ wᵉ) →
    (pᵉ ∙ᵉ qᵉ) ∙ᵉ rᵉ ＝ᵉ (pᵉ ∙ᵣᵉ qᵉ) ∙ᵣᵉ rᵉ
  eq-double-right-strict-concat-concat-left-associatedᵉ pᵉ qᵉ rᵉ =
    ( apᵉ (_∙ᵉ rᵉ) (eq-right-strict-concat-concatᵉ pᵉ qᵉ)) ∙ᵉ
    ( eq-right-strict-concat-concatᵉ (pᵉ ∙ᵣᵉ qᵉ) rᵉ)

  eq-double-right-strict-concat-concat-right-associatedᵉ :
    {xᵉ yᵉ zᵉ wᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) (qᵉ : yᵉ ＝ᵉ zᵉ) (rᵉ : zᵉ ＝ᵉ wᵉ) →
    pᵉ ∙ᵉ (qᵉ ∙ᵉ rᵉ) ＝ᵉ pᵉ ∙ᵣᵉ (qᵉ ∙ᵣᵉ rᵉ)
  eq-double-right-strict-concat-concat-right-associatedᵉ pᵉ qᵉ rᵉ =
    ( apᵉ (pᵉ ∙ᵉ_) (eq-right-strict-concat-concatᵉ qᵉ rᵉ)) ∙ᵉ
    ( eq-right-strict-concat-concatᵉ pᵉ (qᵉ ∙ᵣᵉ rᵉ))

  eq-double-concat-right-strict-concat-left-associatedᵉ :
    {xᵉ yᵉ zᵉ wᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) (qᵉ : yᵉ ＝ᵉ zᵉ) (rᵉ : zᵉ ＝ᵉ wᵉ) →
    (pᵉ ∙ᵣᵉ qᵉ) ∙ᵣᵉ rᵉ ＝ᵉ (pᵉ ∙ᵉ qᵉ) ∙ᵉ rᵉ
  eq-double-concat-right-strict-concat-left-associatedᵉ pᵉ qᵉ rᵉ =
    ( apᵉ (_∙ᵣᵉ rᵉ) (eq-concat-right-strict-concatᵉ pᵉ qᵉ)) ∙ᵉ
    ( eq-concat-right-strict-concatᵉ (pᵉ ∙ᵉ qᵉ) rᵉ)

  eq-double-concat-right-strict-concat-right-associatedᵉ :
    {xᵉ yᵉ zᵉ wᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) (qᵉ : yᵉ ＝ᵉ zᵉ) (rᵉ : zᵉ ＝ᵉ wᵉ) →
    pᵉ ∙ᵣᵉ (qᵉ ∙ᵣᵉ rᵉ) ＝ᵉ pᵉ ∙ᵉ (qᵉ ∙ᵉ rᵉ)
  eq-double-concat-right-strict-concat-right-associatedᵉ pᵉ qᵉ rᵉ =
    ( apᵉ (pᵉ ∙ᵣᵉ_) (eq-concat-right-strict-concatᵉ qᵉ rᵉ)) ∙ᵉ
    ( eq-concat-right-strict-concatᵉ pᵉ (qᵉ ∙ᵉ rᵉ))
```

## Properties

### The groupoidal laws

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  assoc-right-strict-concatᵉ :
    {xᵉ yᵉ zᵉ wᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) (qᵉ : yᵉ ＝ᵉ zᵉ) (rᵉ : zᵉ ＝ᵉ wᵉ) →
    ((pᵉ ∙ᵣᵉ qᵉ) ∙ᵣᵉ rᵉ) ＝ᵉ (pᵉ ∙ᵣᵉ (qᵉ ∙ᵣᵉ rᵉ))
  assoc-right-strict-concatᵉ pᵉ qᵉ reflᵉ = reflᵉ

  left-unit-right-strict-concatᵉ : {xᵉ yᵉ : Aᵉ} {pᵉ : xᵉ ＝ᵉ yᵉ} → reflᵉ ∙ᵣᵉ pᵉ ＝ᵉ pᵉ
  left-unit-right-strict-concatᵉ {pᵉ = reflᵉ} = reflᵉ

  right-unit-right-strict-concatᵉ : {xᵉ yᵉ : Aᵉ} {pᵉ : xᵉ ＝ᵉ yᵉ} → pᵉ ∙ᵣᵉ reflᵉ ＝ᵉ pᵉ
  right-unit-right-strict-concatᵉ = reflᵉ

  left-inv-right-strict-concatᵉ : {xᵉ yᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) → invᵉ pᵉ ∙ᵣᵉ pᵉ ＝ᵉ reflᵉ
  left-inv-right-strict-concatᵉ reflᵉ = reflᵉ

  right-inv-right-strict-concatᵉ : {xᵉ yᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) → pᵉ ∙ᵣᵉ invᵉ pᵉ ＝ᵉ reflᵉ
  right-inv-right-strict-concatᵉ reflᵉ = reflᵉ

  inv-inv-right-strict-concatᵉ : {xᵉ yᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) → invᵉ (invᵉ pᵉ) ＝ᵉ pᵉ
  inv-inv-right-strict-concatᵉ reflᵉ = reflᵉ

  distributive-inv-right-strict-concatᵉ :
    {xᵉ yᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) {zᵉ : Aᵉ} (qᵉ : yᵉ ＝ᵉ zᵉ) →
    invᵉ (pᵉ ∙ᵣᵉ qᵉ) ＝ᵉ invᵉ qᵉ ∙ᵣᵉ invᵉ pᵉ
  distributive-inv-right-strict-concatᵉ reflᵉ reflᵉ = reflᵉ
```

### Transposing inverses

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  left-transpose-eq-right-strict-concatᵉ :
    {xᵉ yᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) {zᵉ : Aᵉ} (qᵉ : yᵉ ＝ᵉ zᵉ) (rᵉ : xᵉ ＝ᵉ zᵉ) →
    pᵉ ∙ᵣᵉ qᵉ ＝ᵉ rᵉ → qᵉ ＝ᵉ invᵉ pᵉ ∙ᵣᵉ rᵉ
  left-transpose-eq-right-strict-concatᵉ reflᵉ qᵉ rᵉ sᵉ =
    (invᵉ left-unit-right-strict-concatᵉ ∙ᵉ sᵉ) ∙ᵉ invᵉ left-unit-right-strict-concatᵉ

  right-transpose-eq-right-strict-concatᵉ :
    {xᵉ yᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) {zᵉ : Aᵉ} (qᵉ : yᵉ ＝ᵉ zᵉ) (rᵉ : xᵉ ＝ᵉ zᵉ) →
    pᵉ ∙ᵣᵉ qᵉ ＝ᵉ rᵉ → pᵉ ＝ᵉ rᵉ ∙ᵣᵉ invᵉ qᵉ
  right-transpose-eq-right-strict-concatᵉ pᵉ reflᵉ rᵉ sᵉ = sᵉ
```

### Concatenation is injective

```agda
module _
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  where

  is-injective-right-strict-concatᵉ :
    {xᵉ yᵉ zᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) {qᵉ rᵉ : yᵉ ＝ᵉ zᵉ} → pᵉ ∙ᵣᵉ qᵉ ＝ᵉ pᵉ ∙ᵣᵉ rᵉ → qᵉ ＝ᵉ rᵉ
  is-injective-right-strict-concatᵉ reflᵉ sᵉ =
    (invᵉ left-unit-right-strict-concatᵉ ∙ᵉ sᵉ) ∙ᵉ left-unit-right-strict-concatᵉ

  is-injective-right-strict-concat'ᵉ :
    {xᵉ yᵉ zᵉ : Aᵉ} (rᵉ : yᵉ ＝ᵉ zᵉ) {pᵉ qᵉ : xᵉ ＝ᵉ yᵉ} → pᵉ ∙ᵣᵉ rᵉ ＝ᵉ qᵉ ∙ᵣᵉ rᵉ → pᵉ ＝ᵉ qᵉ
  is-injective-right-strict-concat'ᵉ reflᵉ sᵉ = sᵉ
```

## See also

-ᵉ [Yonedaᵉ identityᵉ types](foundation.yoneda-identity-types.mdᵉ)
-ᵉ [Computationalᵉ identityᵉ types](foundation.computational-identity-types.mdᵉ)