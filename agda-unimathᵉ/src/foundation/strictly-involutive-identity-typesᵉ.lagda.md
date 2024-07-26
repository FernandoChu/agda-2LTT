# Strictly involutive identity types

```agda
module foundation.strictly-involutive-identity-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functionsᵉ
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equality-cartesian-product-typesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.multivariable-homotopiesᵉ
open import foundation.strictly-right-unital-concatenation-identificationsᵉ
open import foundation.univalenceᵉ
open import foundation.universal-property-identity-systemsᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.cartesian-product-typesᵉ
open import foundation-core.contractible-typesᵉ
open import foundation-core.equality-dependent-pair-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.functoriality-dependent-pair-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.retractionsᵉ
open import foundation-core.sectionsᵉ
open import foundation-core.torsorial-type-familiesᵉ
open import foundation-core.transport-along-identificationsᵉ
```

</details>

## Idea

Theᵉ standardᵉ definitionᵉ ofᵉ [identityᵉ types](foundation-core.identity-types.mdᵉ)
hasᵉ theᵉ limitationᵉ thatᵉ manyᵉ ofᵉ theᵉ basicᵉ operationsᵉ onlyᵉ satisfyᵉ algebraicᵉ lawsᵉ
_weakly_.ᵉ Onᵉ thisᵉ page,ᵉ weᵉ considerᵉ theᵉ
{{#conceptᵉ "strictlyᵉ involutiveᵉ identityᵉ types"ᵉ Agda=involutive-Idᵉ}}

```text
  (xᵉ ＝ⁱᵉ yᵉ) :=ᵉ Σᵉ (zᵉ : Aᵉ) ((zᵉ ＝ᵉ yᵉ) ×ᵉ (zᵉ ＝ᵉ xᵉ))
```

whoseᵉ elementsᵉ weᵉ callᵉ
{{#conceptᵉ "strictlyᵉ involutiveᵉ identifications"ᵉ Agda=involutive-Id}}.ᵉ Thisᵉ typeᵉ
familyᵉ isᵉ [equivalent](foundation-core.equivalences.mdᵉ) to theᵉ standardᵉ identityᵉ
types,ᵉ butᵉ satisfiesᵉ theᵉ strictᵉ lawsᵉ

-ᵉ `invⁱᵉ (invⁱᵉ pᵉ) ≐ᵉ p`ᵉ
-ᵉ `invⁱᵉ reflⁱᵉ ≐ᵉ reflⁱ`ᵉ

where weᵉ useᵉ aᵉ superscriptᵉ `i`ᵉ to distinguishᵉ theᵉ strictlyᵉ involutiveᵉ identityᵉ
typeᵉ fromᵉ theᵉ standardᵉ identityᵉ type.ᵉ

Inᵉ addition,ᵉ weᵉ maintainᵉ theᵉ followingᵉ strictᵉ lawsᵉ

-ᵉ `invⁱᵉ reflⁱᵉ ≐ᵉ reflⁱ`ᵉ
-ᵉ `reflⁱᵉ ∙ᵉ pᵉ ≐ᵉ p`ᵉ orᵉ `pᵉ ∙ᵉ reflⁱᵉ ≐ᵉ p`ᵉ
-ᵉ `ind-Idⁱᵉ Bᵉ fᵉ reflⁱᵉ ≐ᵉ fᵉ reflⁱ`ᵉ

amongᵉ otherᵉ moreᵉ specificᵉ lawsᵉ consideredᵉ onᵉ thisᵉ page.ᵉ

## Definition

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  involutive-Idᵉ : (xᵉ yᵉ : Aᵉ) → UUᵉ lᵉ
  involutive-Idᵉ xᵉ yᵉ = Σᵉ Aᵉ (λ zᵉ → (zᵉ ＝ᵉ yᵉ) ×ᵉ (zᵉ ＝ᵉ xᵉ))

  infix 6 _＝ⁱᵉ_
  _＝ⁱᵉ_ : Aᵉ → Aᵉ → UUᵉ lᵉ
  (aᵉ ＝ⁱᵉ bᵉ) = involutive-Idᵉ aᵉ bᵉ

  reflⁱᵉ : {xᵉ : Aᵉ} → xᵉ ＝ⁱᵉ xᵉ
  reflⁱᵉ {xᵉ} = (xᵉ ,ᵉ reflᵉ ,ᵉ reflᵉ)
```

## Properties

### The strictly involutive identity types are equivalent to the standard identity types

Theᵉ equivalenceᵉ `(xᵉ ＝ᵉ yᵉ) ≃ᵉ (xᵉ ＝ⁱᵉ y)`ᵉ isᵉ definedᵉ fromᵉ leftᵉ to rightᵉ byᵉ
inclusionᵉ atᵉ theᵉ secondᵉ componentᵉ

```text
  involutive-eq-eqᵉ :=ᵉ pᵉ ↦ᵉ (xᵉ ,ᵉ pᵉ ,ᵉ reflᵉ)   : xᵉ ＝ᵉ yᵉ → xᵉ ＝ⁱᵉ y,ᵉ
```

andᵉ fromᵉ rightᵉ to leftᵉ byᵉ theᵉ concatenationᵉ

```text
  eq-involutive-eqᵉ :=ᵉ (zᵉ ,ᵉ pᵉ ,ᵉ qᵉ) ↦ᵉ invᵉ qᵉ ∙ᵉ pᵉ   : xᵉ ＝ⁱᵉ yᵉ → xᵉ ＝ᵉ y.ᵉ
```

Thisᵉ equivalenceᵉ weaklyᵉ preservesᵉ theᵉ groupoidᵉ structureᵉ onᵉ theᵉ strictlyᵉ
involutiveᵉ identityᵉ typesᵉ asᵉ weᵉ willᵉ seeᵉ later.ᵉ Moreover,ᵉ theᵉ compositionᵉ
`eq-involutive-eqᵉ ∘ᵉ involutive-eq-eq`ᵉ computesᵉ strictlyᵉ to theᵉ identityᵉ:

```text
  eq-involutive-eqᵉ ∘ᵉ involutive-eq-eqᵉ
  ≐ᵉ pᵉ ↦ᵉ (((zᵉ ,ᵉ pᵉ ,ᵉ qᵉ) ↦ᵉ invᵉ qᵉ ∙ᵉ pᵉ) (rᵉ ↦ᵉ (wᵉ ,ᵉ rᵉ ,ᵉ reflᵉ)))
  ≐ᵉ pᵉ ↦ᵉ invᵉ reflᵉ ∙ᵉ pᵉ
  ≐ᵉ pᵉ ↦ᵉ reflᵉ ∙ᵉ pᵉ
  ≐ᵉ pᵉ ↦ᵉ pᵉ
```

andᵉ theᵉ reflexivitiesᵉ areᵉ preservedᵉ strictlyᵉ:

```text
  eq-involutive-eqᵉ reflⁱᵉ ≐ᵉ invᵉ reflᵉ ∙ᵉ reflᵉ ≐ᵉ reflᵉ ∙ᵉ reflᵉ ≐ᵉ refl,ᵉ
```

andᵉ

```text
  involutive-eq-eqᵉ reflᵉ ≐ᵉ (xᵉ ,ᵉ reflᵉ ,ᵉ reflᵉ) ≐ᵉ reflⁱ.ᵉ
```

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {xᵉ yᵉ : Aᵉ}
  where

  involutive-eq-eqᵉ : xᵉ ＝ᵉ yᵉ → xᵉ ＝ⁱᵉ yᵉ
  involutive-eq-eqᵉ pᵉ = (xᵉ ,ᵉ pᵉ ,ᵉ reflᵉ)

  eq-involutive-eqᵉ : xᵉ ＝ⁱᵉ yᵉ → xᵉ ＝ᵉ yᵉ
  eq-involutive-eqᵉ (zᵉ ,ᵉ pᵉ ,ᵉ qᵉ) = invᵉ qᵉ ∙ᵉ pᵉ

  is-section-eq-involutive-eqᵉ : is-sectionᵉ involutive-eq-eqᵉ eq-involutive-eqᵉ
  is-section-eq-involutive-eqᵉ (zᵉ ,ᵉ pᵉ ,ᵉ reflᵉ) = reflᵉ

  is-retraction-eq-involutive-eqᵉ :
    is-retractionᵉ involutive-eq-eqᵉ eq-involutive-eqᵉ
  is-retraction-eq-involutive-eqᵉ pᵉ = reflᵉ

  is-equiv-involutive-eq-eqᵉ : is-equivᵉ involutive-eq-eqᵉ
  pr1ᵉ (pr1ᵉ is-equiv-involutive-eq-eqᵉ) = eq-involutive-eqᵉ
  pr2ᵉ (pr1ᵉ is-equiv-involutive-eq-eqᵉ) = is-section-eq-involutive-eqᵉ
  pr1ᵉ (pr2ᵉ is-equiv-involutive-eq-eqᵉ) = eq-involutive-eqᵉ
  pr2ᵉ (pr2ᵉ is-equiv-involutive-eq-eqᵉ) = is-retraction-eq-involutive-eqᵉ

  is-equiv-eq-involutive-eqᵉ : is-equivᵉ eq-involutive-eqᵉ
  pr1ᵉ (pr1ᵉ is-equiv-eq-involutive-eqᵉ) = involutive-eq-eqᵉ
  pr2ᵉ (pr1ᵉ is-equiv-eq-involutive-eqᵉ) = is-retraction-eq-involutive-eqᵉ
  pr1ᵉ (pr2ᵉ is-equiv-eq-involutive-eqᵉ) = involutive-eq-eqᵉ
  pr2ᵉ (pr2ᵉ is-equiv-eq-involutive-eqᵉ) = is-section-eq-involutive-eqᵉ

  equiv-involutive-eq-eqᵉ : (xᵉ ＝ᵉ yᵉ) ≃ᵉ (xᵉ ＝ⁱᵉ yᵉ)
  pr1ᵉ equiv-involutive-eq-eqᵉ = involutive-eq-eqᵉ
  pr2ᵉ equiv-involutive-eq-eqᵉ = is-equiv-involutive-eq-eqᵉ

  equiv-eq-involutive-eqᵉ : (xᵉ ＝ⁱᵉ yᵉ) ≃ᵉ (xᵉ ＝ᵉ yᵉ)
  pr1ᵉ equiv-eq-involutive-eqᵉ = eq-involutive-eqᵉ
  pr2ᵉ equiv-eq-involutive-eqᵉ = is-equiv-eq-involutive-eqᵉ
```

Thisᵉ equivalenceᵉ preservesᵉ theᵉ reflexivityᵉ elementsᵉ strictlyᵉ in bothᵉ directions.ᵉ

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  preserves-refl-involutive-eq-eqᵉ :
    {xᵉ : Aᵉ} → involutive-eq-eqᵉ (reflᵉ {xᵉ = xᵉ}) ＝ᵉ reflⁱᵉ
  preserves-refl-involutive-eq-eqᵉ = reflᵉ

  preserves-refl-eq-involutive-eqᵉ :
    {xᵉ : Aᵉ} → eq-involutive-eqᵉ (reflⁱᵉ {xᵉ = xᵉ}) ＝ᵉ reflᵉ
  preserves-refl-eq-involutive-eqᵉ = reflᵉ
```

### Torsoriality of the strictly involutive identity types

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {xᵉ : Aᵉ}
  where

  is-torsorial-involutive-Idᵉ : is-torsorialᵉ (involutive-Idᵉ xᵉ)
  is-torsorial-involutive-Idᵉ =
    is-contr-equivᵉ
      ( Σᵉ Aᵉ (xᵉ ＝ᵉ_))
      ( equiv-totᵉ (λ yᵉ → equiv-eq-involutive-eqᵉ {xᵉ = xᵉ} {yᵉ}))
      ( is-torsorial-Idᵉ xᵉ)
```

### The dependent universal property of the strictly involutive identity types

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {xᵉ : Aᵉ}
  where

  dependent-universal-property-identity-system-involutive-Idᵉ :
    dependent-universal-property-identity-systemᵉ
      ( involutive-Idᵉ xᵉ)
      ( reflⁱᵉ)
  dependent-universal-property-identity-system-involutive-Idᵉ =
    dependent-universal-property-identity-system-is-torsorialᵉ
      ( reflⁱᵉ)
      ( is-torsorial-involutive-Idᵉ)
```

### The induction principle for strictly involutive identity types

Theᵉ strictlyᵉ involutiveᵉ identityᵉ typesᵉ satisfyᵉ theᵉ inductionᵉ principleᵉ ofᵉ theᵉ
identityᵉ types.ᵉ Thisᵉ statesᵉ thatᵉ givenᵉ aᵉ baseᵉ pointᵉ `xᵉ : A`ᵉ andᵉ aᵉ familyᵉ ofᵉ
typesᵉ overᵉ theᵉ identityᵉ typesᵉ basedᵉ atᵉ `x`,ᵉ `Bᵉ : (yᵉ : Aᵉ) (pᵉ : xᵉ ＝ⁱᵉ yᵉ) → UUᵉ l2`,ᵉ
thenᵉ to constructᵉ aᵉ dependentᵉ functionᵉ `fᵉ : (yᵉ : Aᵉ) (pᵉ : xᵉ ＝ⁱᵉ yᵉ) → Bᵉ yᵉ p`ᵉ itᵉ
sufficesᵉ to defineᵉ itᵉ atᵉ `fᵉ xᵉ reflⁱ`.ᵉ Theᵉ strictlyᵉ involutiveᵉ identityᵉ typesᵉ
alsoᵉ satisfyᵉ theᵉ correspondingᵉ computationᵉ ruleᵉ strictly.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  (xᵉ : Aᵉ) (Bᵉ : (yᵉ : Aᵉ) (pᵉ : xᵉ ＝ⁱᵉ yᵉ) → UUᵉ l2ᵉ)
  where

  ind-involutive-Idᵉ :
    Bᵉ xᵉ reflⁱᵉ → (yᵉ : Aᵉ) (pᵉ : xᵉ ＝ⁱᵉ yᵉ) → Bᵉ yᵉ pᵉ
  ind-involutive-Idᵉ bᵉ .xᵉ (.xᵉ ,ᵉ reflᵉ ,ᵉ reflᵉ) = bᵉ

  compute-ind-involutive-Idᵉ :
    (bᵉ : Bᵉ xᵉ reflⁱᵉ) → ind-involutive-Idᵉ bᵉ xᵉ reflⁱᵉ ＝ᵉ bᵉ
  compute-ind-involutive-Idᵉ bᵉ = reflᵉ

  uniqueness-ind-involutive-Idᵉ :
    (fᵉ : (yᵉ : Aᵉ) (pᵉ : xᵉ ＝ⁱᵉ yᵉ) → Bᵉ yᵉ pᵉ) →
    ind-involutive-Idᵉ (fᵉ xᵉ reflⁱᵉ) ＝ᵉ fᵉ
  uniqueness-ind-involutive-Idᵉ fᵉ =
    eq-multivariable-htpyᵉ 2 (λ where .xᵉ (.xᵉ ,ᵉ reflᵉ ,ᵉ reflᵉ) → reflᵉ)
```

**Note.**ᵉ Theᵉ onlyᵉ reasonᵉ weᵉ mustᵉ applyᵉ
[functionᵉ extensionality](foundation.function-extensionality.mdᵉ) isᵉ to showᵉ
uniquenessᵉ ofᵉ theᵉ inductionᵉ principleᵉ upᵉ to _equality_.ᵉ

## Structure

Theᵉ strictlyᵉ involutiveᵉ identityᵉ typesᵉ formᵉ aᵉ strictlyᵉ involutiveᵉ weakᵉ
groupoidalᵉ structureᵉ onᵉ types.ᵉ

### Inverting strictly involutive identifications

Weᵉ haveᵉ anᵉ inversionᵉ operationᵉ onᵉ `involutive-Id`ᵉ definedᵉ byᵉ swappingᵉ theᵉ
positionᵉ ofᵉ theᵉ identifications.ᵉ Thisᵉ operationᵉ satisfiesᵉ theᵉ strictᵉ lawsᵉ

-ᵉ `invⁱᵉ (invⁱᵉ pᵉ) ≐ᵉ p`,ᵉ andᵉ
-ᵉ `invⁱᵉ reflⁱᵉ ≐ᵉ reflⁱ`.ᵉ

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  invⁱᵉ : {xᵉ yᵉ : Aᵉ} → xᵉ ＝ⁱᵉ yᵉ → yᵉ ＝ⁱᵉ xᵉ
  invⁱᵉ (zᵉ ,ᵉ pᵉ ,ᵉ qᵉ) = (zᵉ ,ᵉ qᵉ ,ᵉ pᵉ)

  compute-refl-inv-involutive-Idᵉ : {xᵉ : Aᵉ} → invⁱᵉ (reflⁱᵉ {xᵉ = xᵉ}) ＝ᵉ reflⁱᵉ
  compute-refl-inv-involutive-Idᵉ = reflᵉ

  inv-inv-involutive-Idᵉ : {xᵉ yᵉ : Aᵉ} (pᵉ : xᵉ ＝ⁱᵉ yᵉ) → invⁱᵉ (invⁱᵉ pᵉ) ＝ᵉ pᵉ
  inv-inv-involutive-Idᵉ pᵉ = reflᵉ
```

Theᵉ inversionᵉ operationᵉ correspondsᵉ to theᵉ standardᵉ inversionᵉ operationᵉ onᵉ
identifications.ᵉ

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  preserves-inv-involutive-eq-eqᵉ :
    {xᵉ yᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) →
    involutive-eq-eqᵉ (invᵉ pᵉ) ＝ᵉ invⁱᵉ (involutive-eq-eqᵉ pᵉ)
  preserves-inv-involutive-eq-eqᵉ reflᵉ = reflᵉ

  preserves-inv-eq-involutive-eqᵉ :
    {xᵉ yᵉ : Aᵉ} (pᵉ : xᵉ ＝ⁱᵉ yᵉ) →
    eq-involutive-eqᵉ (invⁱᵉ pᵉ) ＝ᵉ invᵉ (eq-involutive-eqᵉ pᵉ)
  preserves-inv-eq-involutive-eqᵉ (zᵉ ,ᵉ pᵉ ,ᵉ qᵉ) =
    apᵉ (invᵉ pᵉ ∙ᵉ_) (invᵉ (inv-invᵉ qᵉ)) ∙ᵉ invᵉ (distributive-inv-concatᵉ (invᵉ qᵉ) pᵉ)
```

### Concatenation of strictly involutive identifications

Weᵉ have,ᵉ practicallyᵉ speaking,ᵉ twoᵉ definitionsᵉ ofᵉ theᵉ concatenationᵉ operationᵉ onᵉ
strictlyᵉ involutiveᵉ identityᵉ types.ᵉ Oneᵉ satisfiesᵉ aᵉ strictᵉ leftᵉ unitᵉ lawᵉ andᵉ theᵉ
otherᵉ satisfiesᵉ aᵉ strictᵉ rightᵉ unitᵉ law.ᵉ Inᵉ bothᵉ cases,ᵉ weᵉ mustᵉ useᵉ theᵉ
[strictlyᵉ rightᵉ unitalᵉ concatenationᵉ operationᵉ onᵉ standardᵉ identifications](foundation.strictly-right-unital-concatenation-identifications.mdᵉ)
`_∙ᵣ_`,ᵉ to obtainᵉ thisᵉ strictᵉ one-sidedᵉ unitᵉ law,ᵉ asᵉ willᵉ momentarilyᵉ beᵉ
demonstrated.ᵉ

Theᵉ strictlyᵉ leftᵉ unitalᵉ concatenationᵉ operationᵉ isᵉ definedᵉ byᵉ

```text
  (wᵉ ,ᵉ pᵉ ,ᵉ qᵉ) ∙ⁱᵉ (w'ᵉ ,ᵉ p'ᵉ ,ᵉ q'ᵉ) :=ᵉ (w'ᵉ ,ᵉ p'ᵉ ,ᵉ (q'ᵉ ∙ᵣᵉ invᵉ pᵉ) ∙ᵣᵉ q),ᵉ
```

andᵉ theᵉ strictlyᵉ rightᵉ unitalᵉ concatenationᵉ operationᵉ isᵉ definedᵉ byᵉ

```text
  (wᵉ ,ᵉ pᵉ ,ᵉ qᵉ) ∙ᵣⁱᵉ (w'ᵉ ,ᵉ p'ᵉ ,ᵉ q'ᵉ) = (wᵉ ,ᵉ (pᵉ ∙ᵣᵉ invᵉ q'ᵉ) ∙ᵣᵉ p'ᵉ ,ᵉ q).ᵉ
```

Theᵉ followingᵉ computationᵉ verifiesᵉ thatᵉ theᵉ strictlyᵉ leftᵉ unitalᵉ concatenationᵉ
operationᵉ isᵉ indeedᵉ strictlyᵉ leftᵉ unitalᵉ:

```text
  reflⁱᵉ ∙ⁱᵉ rᵉ
  ≐ᵉ (xᵉ ,ᵉ reflᵉ ,ᵉ reflᵉ) ∙ⁱᵉ (wᵉ ,ᵉ pᵉ ,ᵉ qᵉ)
  ≐ᵉ (wᵉ ,ᵉ pᵉ ,ᵉ (qᵉ ∙ᵣᵉ invᵉ reflᵉ) ∙ᵣᵉ reflᵉ)
  ≐ᵉ (wᵉ ,ᵉ pᵉ ,ᵉ (qᵉ ∙ᵣᵉ invᵉ reflᵉ))
  ≐ᵉ (wᵉ ,ᵉ pᵉ ,ᵉ (qᵉ ∙ᵣᵉ reflᵉ))
  ≐ᵉ (wᵉ ,ᵉ pᵉ ,ᵉ qᵉ)
  ≐ᵉ r.ᵉ
```

Whileᵉ forᵉ theᵉ strictlyᵉ rightᵉ unitalᵉ concatenationᵉ operation,ᵉ weᵉ haveᵉ theᵉ
computationᵉ

```text
  rᵉ ∙ᵣⁱᵉ reflⁱᵉ
  ≐ᵉ  (wᵉ ,ᵉ pᵉ ,ᵉ qᵉ) ∙ᵣⁱᵉ (xᵉ ,ᵉ reflᵉ ,ᵉ reflᵉ)
  ≐ᵉ (wᵉ ,ᵉ (pᵉ ∙ᵣᵉ invᵉ reflᵉ) ∙ᵣᵉ reflᵉ ,ᵉ qᵉ)
  ≐ᵉ (wᵉ ,ᵉ pᵉ ∙ᵣᵉ invᵉ reflᵉ ,ᵉ qᵉ)
  ≐ᵉ (wᵉ ,ᵉ pᵉ ∙ᵣᵉ reflᵉ ,ᵉ qᵉ)
  ≐ᵉ (wᵉ ,ᵉ pᵉ ,ᵉ qᵉ)
  ≐ᵉ r.ᵉ
```

Toᵉ beᵉ consistentᵉ with theᵉ conventionᵉ forᵉ theᵉ standardᵉ identityᵉ types,ᵉ weᵉ takeᵉ
theᵉ strictlyᵉ leftᵉ unitalᵉ concatenationᵉ operationᵉ to beᵉ theᵉ defaultᵉ concatenationᵉ
operationᵉ onᵉ strictlyᵉ involutiveᵉ identityᵉ types.ᵉ

#### The strictly left unital concatenation operation

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  infixl 15 _∙ⁱᵉ_
  _∙ⁱᵉ_ : {xᵉ yᵉ zᵉ : Aᵉ} → xᵉ ＝ⁱᵉ yᵉ → yᵉ ＝ⁱᵉ zᵉ → xᵉ ＝ⁱᵉ zᵉ
  (wᵉ ,ᵉ pᵉ ,ᵉ qᵉ) ∙ⁱᵉ (w'ᵉ ,ᵉ p'ᵉ ,ᵉ q'ᵉ) = (w'ᵉ ,ᵉ p'ᵉ ,ᵉ (q'ᵉ ∙ᵣᵉ invᵉ pᵉ) ∙ᵣᵉ qᵉ)

  concat-involutive-Idᵉ : {xᵉ yᵉ : Aᵉ} → xᵉ ＝ⁱᵉ yᵉ → (zᵉ : Aᵉ) → yᵉ ＝ⁱᵉ zᵉ → xᵉ ＝ⁱᵉ zᵉ
  concat-involutive-Idᵉ pᵉ zᵉ qᵉ = pᵉ ∙ⁱᵉ qᵉ

  concat-involutive-Id'ᵉ : (xᵉ : Aᵉ) {yᵉ zᵉ : Aᵉ} → yᵉ ＝ⁱᵉ zᵉ → xᵉ ＝ⁱᵉ yᵉ → xᵉ ＝ⁱᵉ zᵉ
  concat-involutive-Id'ᵉ xᵉ qᵉ pᵉ = pᵉ ∙ⁱᵉ qᵉ

  preserves-concat-involutive-eq-eqᵉ :
    {xᵉ yᵉ zᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) (qᵉ : yᵉ ＝ᵉ zᵉ) →
    involutive-eq-eqᵉ (pᵉ ∙ᵉ qᵉ) ＝ᵉ involutive-eq-eqᵉ pᵉ ∙ⁱᵉ involutive-eq-eqᵉ qᵉ
  preserves-concat-involutive-eq-eqᵉ reflᵉ qᵉ = reflᵉ

  preserves-concat-eq-involutive-eqᵉ :
    {xᵉ yᵉ zᵉ : Aᵉ} (pᵉ : xᵉ ＝ⁱᵉ yᵉ) (qᵉ : yᵉ ＝ⁱᵉ zᵉ) →
    eq-involutive-eqᵉ (pᵉ ∙ⁱᵉ qᵉ) ＝ᵉ eq-involutive-eqᵉ pᵉ ∙ᵉ eq-involutive-eqᵉ qᵉ
  preserves-concat-eq-involutive-eqᵉ (wᵉ ,ᵉ pᵉ ,ᵉ qᵉ) (w'ᵉ ,ᵉ p'ᵉ ,ᵉ q'ᵉ) =
    ( apᵉ
      ( _∙ᵉ p'ᵉ)
      ( ( distributive-inv-right-strict-concatᵉ (q'ᵉ ∙ᵣᵉ invᵉ pᵉ) qᵉ) ∙ᵉ
        ( ( apᵉ
            ( invᵉ qᵉ ∙ᵣᵉ_)
            ( ( distributive-inv-right-strict-concatᵉ q'ᵉ (invᵉ pᵉ)) ∙ᵉ
              ( apᵉ (_∙ᵣᵉ invᵉ q'ᵉ) (inv-invᵉ pᵉ)))) ∙ᵉ
          ( invᵉ (assoc-right-strict-concatᵉ (invᵉ qᵉ) pᵉ (invᵉ q'ᵉ))) ∙ᵉ
          ( eq-double-concat-right-strict-concat-left-associatedᵉ
            ( invᵉ qᵉ)
            ( pᵉ)
            ( invᵉ q'ᵉ))))) ∙ᵉ
    ( assocᵉ (invᵉ qᵉ ∙ᵉ pᵉ) (invᵉ q'ᵉ) p'ᵉ)
```

#### The strictly right unital concatenation operation

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  infixl 15 _∙ᵣⁱᵉ_
  _∙ᵣⁱᵉ_ : {xᵉ yᵉ zᵉ : Aᵉ} → xᵉ ＝ⁱᵉ yᵉ → yᵉ ＝ⁱᵉ zᵉ → xᵉ ＝ⁱᵉ zᵉ
  (wᵉ ,ᵉ pᵉ ,ᵉ qᵉ) ∙ᵣⁱᵉ (w'ᵉ ,ᵉ p'ᵉ ,ᵉ q'ᵉ) = (wᵉ ,ᵉ (pᵉ ∙ᵣᵉ invᵉ q'ᵉ) ∙ᵣᵉ p'ᵉ ,ᵉ qᵉ)

  right-strict-concat-involutive-Idᵉ :
    {xᵉ yᵉ : Aᵉ} → xᵉ ＝ⁱᵉ yᵉ → (zᵉ : Aᵉ) → yᵉ ＝ⁱᵉ zᵉ → xᵉ ＝ⁱᵉ zᵉ
  right-strict-concat-involutive-Idᵉ pᵉ zᵉ qᵉ = pᵉ ∙ᵣⁱᵉ qᵉ

  right-strict-concat-involutive-Id'ᵉ :
    (xᵉ : Aᵉ) {yᵉ zᵉ : Aᵉ} → yᵉ ＝ⁱᵉ zᵉ → xᵉ ＝ⁱᵉ yᵉ → xᵉ ＝ⁱᵉ zᵉ
  right-strict-concat-involutive-Id'ᵉ xᵉ qᵉ pᵉ = pᵉ ∙ᵣⁱᵉ qᵉ

  eq-concat-right-strict-concat-involutive-Idᵉ :
    {xᵉ yᵉ zᵉ : Aᵉ} (pᵉ : xᵉ ＝ⁱᵉ yᵉ) (qᵉ : yᵉ ＝ⁱᵉ zᵉ) → pᵉ ∙ᵣⁱᵉ qᵉ ＝ᵉ pᵉ ∙ⁱᵉ qᵉ
  eq-concat-right-strict-concat-involutive-Idᵉ (wᵉ ,ᵉ reflᵉ ,ᵉ qᵉ) (w'ᵉ ,ᵉ p'ᵉ ,ᵉ reflᵉ) =
    eq-pair-eq-fiberᵉ
      ( eq-pairᵉ
        ( left-unit-right-strict-concatᵉ)
        ( invᵉ left-unit-right-strict-concatᵉ))

  preserves-right-strict-concat-involutive-eq-eqᵉ :
    {xᵉ yᵉ zᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) (qᵉ : yᵉ ＝ᵉ zᵉ) →
    involutive-eq-eqᵉ (pᵉ ∙ᵉ qᵉ) ＝ᵉ involutive-eq-eqᵉ pᵉ ∙ᵣⁱᵉ involutive-eq-eqᵉ qᵉ
  preserves-right-strict-concat-involutive-eq-eqᵉ pᵉ reflᵉ =
    apᵉ involutive-eq-eqᵉ right-unitᵉ

  preserves-right-strict-concat-eq-involutive-eqᵉ :
    {xᵉ yᵉ zᵉ : Aᵉ} (pᵉ : xᵉ ＝ⁱᵉ yᵉ) (qᵉ : yᵉ ＝ⁱᵉ zᵉ) →
    eq-involutive-eqᵉ (pᵉ ∙ᵣⁱᵉ qᵉ) ＝ᵉ eq-involutive-eqᵉ pᵉ ∙ᵉ eq-involutive-eqᵉ qᵉ
  preserves-right-strict-concat-eq-involutive-eqᵉ (wᵉ ,ᵉ pᵉ ,ᵉ qᵉ) (w'ᵉ ,ᵉ p'ᵉ ,ᵉ q'ᵉ) =
    ( apᵉ
      ( invᵉ qᵉ ∙ᵉ_)
      ( ( eq-double-concat-right-strict-concat-left-associatedᵉ pᵉ (invᵉ q'ᵉ) p'ᵉ) ∙ᵉ
        ( assocᵉ pᵉ (invᵉ q'ᵉ) p'ᵉ))) ∙ᵉ
    ( invᵉ (assocᵉ (invᵉ qᵉ) pᵉ (invᵉ q'ᵉ ∙ᵉ p'ᵉ)))
```

### The groupoidal laws for the strictly involutive identity types

Theᵉ generalᵉ proofᵉ strategyᵉ isᵉ to inductᵉ onᵉ theᵉ minimalᵉ numberᵉ ofᵉ identificationsᵉ
to makeᵉ theᵉ leftᵉ endpointsᵉ strictlyᵉ equal,ᵉ andᵉ thenᵉ proceedᵉ byᵉ reasoningᵉ with
theᵉ groupoidᵉ lawsᵉ ofᵉ theᵉ underlyingᵉ identityᵉ types.ᵉ

#### The groupoidal laws for the strictly left unital concatenation operation

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {xᵉ yᵉ zᵉ wᵉ : Aᵉ}
  where

  assoc-involutive-Idᵉ :
    (pᵉ : xᵉ ＝ⁱᵉ yᵉ) (qᵉ : yᵉ ＝ⁱᵉ zᵉ) (rᵉ : zᵉ ＝ⁱᵉ wᵉ) → (pᵉ ∙ⁱᵉ qᵉ) ∙ⁱᵉ rᵉ ＝ᵉ pᵉ ∙ⁱᵉ (qᵉ ∙ⁱᵉ rᵉ)
  assoc-involutive-Idᵉ (ᵉ_ ,ᵉ pᵉ ,ᵉ qᵉ) (ᵉ_ ,ᵉ p'ᵉ ,ᵉ q'ᵉ) (ᵉ_ ,ᵉ p''ᵉ ,ᵉ q''ᵉ) =
    eq-pair-eq-fiberᵉ
      ( eq-pair-eq-fiberᵉ
        ( ( invᵉ (assoc-right-strict-concatᵉ (q''ᵉ ∙ᵣᵉ invᵉ p'ᵉ) (q'ᵉ ∙ᵣᵉ invᵉ pᵉ) qᵉ)) ∙ᵉ
          ( apᵉ
            ( _∙ᵣᵉ qᵉ)
            ( invᵉ (assoc-right-strict-concatᵉ (q''ᵉ ∙ᵣᵉ invᵉ p'ᵉ) q'ᵉ (invᵉ pᵉ))))))
```

**Note.**ᵉ Observeᵉ thatᵉ theᵉ previousᵉ proofᵉ reliesᵉ solelyᵉ onᵉ theᵉ associatorᵉ ofᵉ theᵉ
underlyingᵉ identityᵉ type.ᵉ Thisᵉ isᵉ oneᵉ ofᵉ theᵉ fundamentalᵉ observationsᵉ leadingᵉ to
theᵉ constructionᵉ ofᵉ theᵉ
[computationalᵉ identityᵉ type](foundation.computational-identity-types.md).ᵉ

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {xᵉ yᵉ : Aᵉ}
  where

  left-unit-involutive-Idᵉ :
    {pᵉ : xᵉ ＝ⁱᵉ yᵉ} → reflⁱᵉ ∙ⁱᵉ pᵉ ＝ᵉ pᵉ
  left-unit-involutive-Idᵉ = reflᵉ

  right-unit-involutive-Idᵉ :
    {pᵉ : xᵉ ＝ⁱᵉ yᵉ} → pᵉ ∙ⁱᵉ reflⁱᵉ ＝ᵉ pᵉ
  right-unit-involutive-Idᵉ {pᵉ = .yᵉ ,ᵉ reflᵉ ,ᵉ qᵉ} =
    eq-pair-eq-fiberᵉ (eq-pair-eq-fiberᵉ left-unit-right-strict-concatᵉ)

  left-inv-involutive-Idᵉ :
    (pᵉ : xᵉ ＝ⁱᵉ yᵉ) → invⁱᵉ pᵉ ∙ⁱᵉ pᵉ ＝ᵉ reflⁱᵉ
  left-inv-involutive-Idᵉ (.yᵉ ,ᵉ reflᵉ ,ᵉ qᵉ) =
    eq-pair-eq-fiberᵉ (eq-pair-eq-fiberᵉ (right-inv-right-strict-concatᵉ qᵉ))

  right-inv-involutive-Idᵉ :
    (pᵉ : xᵉ ＝ⁱᵉ yᵉ) → pᵉ ∙ⁱᵉ invⁱᵉ pᵉ ＝ᵉ reflⁱᵉ
  right-inv-involutive-Idᵉ (.xᵉ ,ᵉ pᵉ ,ᵉ reflᵉ) =
    eq-pair-eq-fiberᵉ (eq-pair-eq-fiberᵉ (right-inv-right-strict-concatᵉ pᵉ))

  distributive-inv-concat-involutive-Idᵉ :
    (pᵉ : xᵉ ＝ⁱᵉ yᵉ) {zᵉ : Aᵉ} (qᵉ : yᵉ ＝ⁱᵉ zᵉ) → invⁱᵉ (pᵉ ∙ⁱᵉ qᵉ) ＝ᵉ invⁱᵉ qᵉ ∙ⁱᵉ invⁱᵉ pᵉ
  distributive-inv-concat-involutive-Idᵉ (.yᵉ ,ᵉ reflᵉ ,ᵉ q'ᵉ) (.yᵉ ,ᵉ p'ᵉ ,ᵉ reflᵉ) =
    eq-pair-eq-fiberᵉ
      ( eq-pairᵉ
        ( left-unit-right-strict-concatᵉ)
        ( invᵉ left-unit-right-strict-concatᵉ))
```

#### The groupoidal laws for the strictly right unital concatenation operation

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {xᵉ yᵉ zᵉ wᵉ : Aᵉ}
  where

  assoc-right-strict-concat-involutive-Idᵉ :
    (pᵉ : xᵉ ＝ⁱᵉ yᵉ) (qᵉ : yᵉ ＝ⁱᵉ zᵉ) (rᵉ : zᵉ ＝ⁱᵉ wᵉ) → (pᵉ ∙ᵣⁱᵉ qᵉ) ∙ᵣⁱᵉ rᵉ ＝ᵉ pᵉ ∙ᵣⁱᵉ (qᵉ ∙ᵣⁱᵉ rᵉ)
  assoc-right-strict-concat-involutive-Idᵉ
    ( _ ,ᵉ pᵉ ,ᵉ qᵉ) (ᵉ_ ,ᵉ p'ᵉ ,ᵉ q'ᵉ) (ᵉ_ ,ᵉ p''ᵉ ,ᵉ q''ᵉ) =
    eq-pair-eq-fiberᵉ
      ( eq-pairᵉ
        ( ( assoc-right-strict-concatᵉ (pᵉ ∙ᵣᵉ invᵉ q'ᵉ ∙ᵣᵉ p'ᵉ) (invᵉ q''ᵉ) p''ᵉ) ∙ᵉ
          ( assoc-right-strict-concatᵉ (pᵉ ∙ᵣᵉ invᵉ q'ᵉ) p'ᵉ (invᵉ q''ᵉ ∙ᵣᵉ p''ᵉ)) ∙ᵉ
          ( apᵉ
            ( pᵉ ∙ᵣᵉ invᵉ q'ᵉ ∙ᵣᵉ_)
            ( invᵉ (assoc-right-strict-concatᵉ p'ᵉ (invᵉ q''ᵉ) p''ᵉ))))
        ( reflᵉ))

module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {xᵉ yᵉ : Aᵉ}
  where

  left-unit-right-strict-concat-involutive-Idᵉ :
    {pᵉ : xᵉ ＝ⁱᵉ yᵉ} → reflⁱᵉ ∙ᵣⁱᵉ pᵉ ＝ᵉ pᵉ
  left-unit-right-strict-concat-involutive-Idᵉ {pᵉ = .xᵉ ,ᵉ pᵉ ,ᵉ reflᵉ} =
    eq-pair-eq-fiberᵉ (eq-pairᵉ left-unit-right-strict-concatᵉ reflᵉ)

  right-unit-right-strict-concat-involutive-Idᵉ :
    {pᵉ : xᵉ ＝ⁱᵉ yᵉ} → pᵉ ∙ᵣⁱᵉ reflⁱᵉ ＝ᵉ pᵉ
  right-unit-right-strict-concat-involutive-Idᵉ = reflᵉ

  left-inv-right-strict-concat-involutive-Idᵉ :
    (pᵉ : xᵉ ＝ⁱᵉ yᵉ) → invⁱᵉ pᵉ ∙ᵣⁱᵉ pᵉ ＝ᵉ reflⁱᵉ
  left-inv-right-strict-concat-involutive-Idᵉ (.yᵉ ,ᵉ reflᵉ ,ᵉ qᵉ) =
    eq-pair-eq-fiberᵉ (eq-pairᵉ (right-inv-right-strict-concatᵉ qᵉ) reflᵉ)

  right-inv-right-strict-concat-involutive-Idᵉ :
    (pᵉ : xᵉ ＝ⁱᵉ yᵉ) → pᵉ ∙ᵣⁱᵉ invⁱᵉ pᵉ ＝ᵉ reflⁱᵉ
  right-inv-right-strict-concat-involutive-Idᵉ (.xᵉ ,ᵉ pᵉ ,ᵉ reflᵉ) =
    eq-pair-eq-fiberᵉ (eq-pairᵉ (right-inv-right-strict-concatᵉ pᵉ) reflᵉ)

  distributive-inv-right-strict-concat-involutive-Idᵉ :
    (pᵉ : xᵉ ＝ⁱᵉ yᵉ) {zᵉ : Aᵉ} (qᵉ : yᵉ ＝ⁱᵉ zᵉ) →
    invⁱᵉ (pᵉ ∙ᵣⁱᵉ qᵉ) ＝ᵉ invⁱᵉ qᵉ ∙ᵣⁱᵉ invⁱᵉ pᵉ
  distributive-inv-right-strict-concat-involutive-Idᵉ
    ( .yᵉ ,ᵉ reflᵉ ,ᵉ qᵉ) (.yᵉ ,ᵉ p'ᵉ ,ᵉ reflᵉ) =
    eq-pair-eq-fiberᵉ
      ( eq-pairᵉ
        ( invᵉ left-unit-right-strict-concatᵉ)
        ( left-unit-right-strict-concatᵉ))
```

## Operations

Weᵉ defineᵉ aᵉ rangeᵉ ofᵉ basicᵉ operationsᵉ onᵉ theᵉ strictlyᵉ involutiveᵉ identificationsᵉ
thatᵉ allᵉ enjoyᵉ strictᵉ computationalᵉ properties.ᵉ

### Action of functions on strictly involutive identifications

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ)
  where

  eq-ap-involutive-Idᵉ : {xᵉ yᵉ : Aᵉ} → xᵉ ＝ⁱᵉ yᵉ → fᵉ xᵉ ＝ᵉ fᵉ yᵉ
  eq-ap-involutive-Idᵉ = apᵉ fᵉ ∘ᵉ eq-involutive-eqᵉ

  ap-involutive-Idᵉ : {xᵉ yᵉ : Aᵉ} → xᵉ ＝ⁱᵉ yᵉ → fᵉ xᵉ ＝ⁱᵉ fᵉ yᵉ
  ap-involutive-Idᵉ = involutive-eq-eqᵉ ∘ᵉ eq-ap-involutive-Idᵉ

  compute-ap-refl-involutive-Idᵉ :
    {xᵉ : Aᵉ} → ap-involutive-Idᵉ (reflⁱᵉ {xᵉ = xᵉ}) ＝ᵉ reflⁱᵉ
  compute-ap-refl-involutive-Idᵉ = reflᵉ

module _
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  where

  compute-ap-id-involutive-Idᵉ :
    {xᵉ yᵉ : Aᵉ} (pᵉ : xᵉ ＝ⁱᵉ yᵉ) → ap-involutive-Idᵉ idᵉ pᵉ ＝ᵉ pᵉ
  compute-ap-id-involutive-Idᵉ (zᵉ ,ᵉ qᵉ ,ᵉ reflᵉ) =
    eq-pair-eq-fiberᵉ (eq-pairᵉ (ap-idᵉ qᵉ) reflᵉ)
```

### Action of binary functions on strictly involutive identifications

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} (fᵉ : Aᵉ → Bᵉ → Cᵉ)
  where

  ap-binary-involutive-Idᵉ :
    {xᵉ x'ᵉ : Aᵉ} (pᵉ : xᵉ ＝ⁱᵉ x'ᵉ) {yᵉ y'ᵉ : Bᵉ} (qᵉ : yᵉ ＝ⁱᵉ y'ᵉ) → fᵉ xᵉ yᵉ ＝ⁱᵉ fᵉ x'ᵉ y'ᵉ
  ap-binary-involutive-Idᵉ (zᵉ ,ᵉ p1ᵉ ,ᵉ p2ᵉ) (wᵉ ,ᵉ q1ᵉ ,ᵉ q2ᵉ) =
    ( fᵉ zᵉ wᵉ ,ᵉ ap-binaryᵉ fᵉ p1ᵉ q1ᵉ ,ᵉ ap-binaryᵉ fᵉ p2ᵉ q2ᵉ)

  left-unit-ap-binary-involutive-Idᵉ :
    {xᵉ : Aᵉ} {yᵉ y'ᵉ : Bᵉ} (qᵉ : yᵉ ＝ⁱᵉ y'ᵉ) →
    ap-binary-involutive-Idᵉ reflⁱᵉ qᵉ ＝ᵉ ap-involutive-Idᵉ (fᵉ xᵉ) qᵉ
  left-unit-ap-binary-involutive-Idᵉ (zᵉ ,ᵉ pᵉ ,ᵉ reflᵉ) = reflᵉ

  right-unit-ap-binary-involutive-Idᵉ :
    {xᵉ x'ᵉ : Aᵉ} (pᵉ : xᵉ ＝ⁱᵉ x'ᵉ) {yᵉ : Bᵉ} →
    ap-binary-involutive-Idᵉ pᵉ reflⁱᵉ ＝ᵉ ap-involutive-Idᵉ (λ zᵉ → fᵉ zᵉ yᵉ) pᵉ
  right-unit-ap-binary-involutive-Idᵉ {.zᵉ} {x'ᵉ} (zᵉ ,ᵉ pᵉ ,ᵉ reflᵉ) {yᵉ} =
    eq-pair-eq-fiberᵉ (eq-pairᵉ right-unitᵉ reflᵉ)
```

### Transport along strictly involutive identifications

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : Aᵉ → UUᵉ l2ᵉ)
  where

  tr-involutive-Idᵉ : {xᵉ yᵉ : Aᵉ} → xᵉ ＝ⁱᵉ yᵉ → Bᵉ xᵉ → Bᵉ yᵉ
  tr-involutive-Idᵉ = trᵉ Bᵉ ∘ᵉ eq-involutive-eqᵉ

  compute-tr-refl-involutive-Idᵉ :
    {xᵉ : Aᵉ} → tr-involutive-Idᵉ (reflⁱᵉ {xᵉ = xᵉ}) ＝ᵉ idᵉ
  compute-tr-refl-involutive-Idᵉ = reflᵉ
```

### Function extensionality with respect to strictly involutive identifications

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {fᵉ gᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ}
  where

  htpy-involutive-eqᵉ : fᵉ ＝ⁱᵉ gᵉ → fᵉ ~ᵉ gᵉ
  htpy-involutive-eqᵉ = htpy-eqᵉ ∘ᵉ eq-involutive-eqᵉ

  involutive-eq-htpyᵉ : fᵉ ~ᵉ gᵉ → fᵉ ＝ⁱᵉ gᵉ
  involutive-eq-htpyᵉ = involutive-eq-eqᵉ ∘ᵉ eq-htpyᵉ

  equiv-htpy-involutive-eqᵉ : (fᵉ ＝ⁱᵉ gᵉ) ≃ᵉ (fᵉ ~ᵉ gᵉ)
  equiv-htpy-involutive-eqᵉ = equiv-funextᵉ ∘eᵉ equiv-eq-involutive-eqᵉ

  equiv-involutive-eq-htpyᵉ : (fᵉ ~ᵉ gᵉ) ≃ᵉ (fᵉ ＝ⁱᵉ gᵉ)
  equiv-involutive-eq-htpyᵉ = equiv-involutive-eq-eqᵉ ∘eᵉ equiv-eq-htpyᵉ

  funext-involutive-Idᵉ : is-equivᵉ htpy-involutive-eqᵉ
  funext-involutive-Idᵉ = is-equiv-map-equivᵉ equiv-htpy-involutive-eqᵉ
```

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {fᵉ gᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ}
  where

  involutive-htpy-involutive-eqᵉ : fᵉ ＝ⁱᵉ gᵉ → (xᵉ : Aᵉ) → fᵉ xᵉ ＝ⁱᵉ gᵉ xᵉ
  involutive-htpy-involutive-eqᵉ (hᵉ ,ᵉ pᵉ ,ᵉ qᵉ) xᵉ =
    ( hᵉ xᵉ ,ᵉ htpy-eqᵉ pᵉ xᵉ ,ᵉ htpy-eqᵉ qᵉ xᵉ)

  involutive-eq-involutive-htpyᵉ : ((xᵉ : Aᵉ) → fᵉ xᵉ ＝ⁱᵉ gᵉ xᵉ) → fᵉ ＝ⁱᵉ gᵉ
  involutive-eq-involutive-htpyᵉ Hᵉ =
    ( pr1ᵉ ∘ᵉ Hᵉ ,ᵉ eq-htpyᵉ (pr1ᵉ ∘ᵉ (pr2ᵉ ∘ᵉ Hᵉ)) ,ᵉ eq-htpyᵉ (pr2ᵉ ∘ᵉ (pr2ᵉ ∘ᵉ Hᵉ)))
```

Itᵉ remainsᵉ to showᵉ thatᵉ theseᵉ mapsᵉ areᵉ partᵉ ofᵉ anᵉ equivalence.ᵉ

### Standard univalence with respect to strictly involutive identifications

```agda
module _
  {l1ᵉ : Level} {Aᵉ Bᵉ : UUᵉ l1ᵉ}
  where

  map-involutive-eqᵉ : Aᵉ ＝ⁱᵉ Bᵉ → Aᵉ → Bᵉ
  map-involutive-eqᵉ = map-eqᵉ ∘ᵉ eq-involutive-eqᵉ

  equiv-involutive-eqᵉ : Aᵉ ＝ⁱᵉ Bᵉ → Aᵉ ≃ᵉ Bᵉ
  equiv-involutive-eqᵉ = equiv-eqᵉ ∘ᵉ eq-involutive-eqᵉ

  involutive-eq-equivᵉ : Aᵉ ≃ᵉ Bᵉ → Aᵉ ＝ⁱᵉ Bᵉ
  involutive-eq-equivᵉ = involutive-eq-eqᵉ ∘ᵉ eq-equivᵉ

  equiv-equiv-involutive-eqᵉ : (Aᵉ ＝ⁱᵉ Bᵉ) ≃ᵉ (Aᵉ ≃ᵉ Bᵉ)
  equiv-equiv-involutive-eqᵉ = equiv-univalenceᵉ ∘eᵉ equiv-eq-involutive-eqᵉ

  is-equiv-equiv-involutive-eqᵉ : is-equivᵉ equiv-involutive-eqᵉ
  is-equiv-equiv-involutive-eqᵉ = is-equiv-map-equivᵉ equiv-equiv-involutive-eqᵉ

  equiv-involutive-eq-equivᵉ : (Aᵉ ≃ᵉ Bᵉ) ≃ᵉ (Aᵉ ＝ⁱᵉ Bᵉ)
  equiv-involutive-eq-equivᵉ = equiv-involutive-eq-eqᵉ ∘eᵉ equiv-eq-equivᵉ Aᵉ Bᵉ

  is-equiv-involutive-eq-equivᵉ : is-equivᵉ involutive-eq-equivᵉ
  is-equiv-involutive-eq-equivᵉ = is-equiv-map-equivᵉ equiv-involutive-eq-equivᵉ
```

### Whiskering of strictly involutive identifications

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {xᵉ yᵉ zᵉ : Aᵉ}
  where

  left-whisker-concat-involutive-Idᵉ :
    (pᵉ : xᵉ ＝ⁱᵉ yᵉ) {qᵉ rᵉ : yᵉ ＝ⁱᵉ zᵉ} → qᵉ ＝ⁱᵉ rᵉ → pᵉ ∙ⁱᵉ qᵉ ＝ⁱᵉ pᵉ ∙ⁱᵉ rᵉ
  left-whisker-concat-involutive-Idᵉ pᵉ βᵉ = ap-involutive-Idᵉ (pᵉ ∙ⁱᵉ_) βᵉ

  right-whisker-concat-involutive-Idᵉ :
    {pᵉ qᵉ : xᵉ ＝ⁱᵉ yᵉ} → pᵉ ＝ⁱᵉ qᵉ → (rᵉ : yᵉ ＝ⁱᵉ zᵉ) → pᵉ ∙ⁱᵉ rᵉ ＝ⁱᵉ qᵉ ∙ⁱᵉ rᵉ
  right-whisker-concat-involutive-Idᵉ αᵉ rᵉ = ap-involutive-Idᵉ (_∙ⁱᵉ rᵉ) αᵉ
```

### Horizontal concatenation of strictly involutive identifications

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {xᵉ yᵉ zᵉ : Aᵉ}
  where

  horizontal-concat-involutive-Id²ᵉ :
    {pᵉ qᵉ : xᵉ ＝ⁱᵉ yᵉ} → pᵉ ＝ⁱᵉ qᵉ → {uᵉ vᵉ : yᵉ ＝ⁱᵉ zᵉ} → uᵉ ＝ⁱᵉ vᵉ → pᵉ ∙ⁱᵉ uᵉ ＝ⁱᵉ qᵉ ∙ⁱᵉ vᵉ
  horizontal-concat-involutive-Id²ᵉ = ap-binary-involutive-Idᵉ (_∙ⁱᵉ_)
```

### Vertical concatenation of strictly involutive identifications

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {xᵉ yᵉ : Aᵉ}
  where

  vertical-concat-involutive-Id²ᵉ :
    {pᵉ qᵉ rᵉ : xᵉ ＝ⁱᵉ yᵉ} → pᵉ ＝ⁱᵉ qᵉ → qᵉ ＝ⁱᵉ rᵉ → pᵉ ＝ⁱᵉ rᵉ
  vertical-concat-involutive-Id²ᵉ αᵉ βᵉ = αᵉ ∙ⁱᵉ βᵉ
```

## See also

-ᵉ [Theᵉ Yonedaᵉ identityᵉ types](foundation.yoneda-identity-types.mdᵉ) forᵉ anᵉ
  identityᵉ relationᵉ thatᵉ isᵉ strictlyᵉ associativeᵉ andᵉ two-sidedᵉ unital.ᵉ
-ᵉ [Theᵉ computationalᵉ identityᵉ types](foundation.computational-identity-types.mdᵉ)
  forᵉ anᵉ identityᵉ relationᵉ thatᵉ isᵉ strictlyᵉ involutive,ᵉ associative,ᵉ andᵉ
  one-sidedᵉ unital.ᵉ

## References

{{#bibliographyᵉ}} {{#referenceᵉ Esc19DefinitionsEquivalenceᵉ}}