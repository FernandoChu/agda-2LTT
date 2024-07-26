# Central elements of groups

```agda
module group-theory.central-elements-groupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.subtypesᵉ
open import foundation.universe-levelsᵉ

open import group-theory.central-elements-monoidsᵉ
open import group-theory.conjugationᵉ
open import group-theory.groupsᵉ
```

</details>

## Idea

Anᵉ elementᵉ `x`ᵉ ofᵉ aᵉ groupᵉ `G`ᵉ isᵉ saidᵉ to beᵉ centralᵉ ifᵉ `xyᵉ ＝ᵉ yx`ᵉ forᵉ everyᵉ
`yᵉ : G`.ᵉ

## Definition

```agda
module _
  {lᵉ : Level} (Gᵉ : Groupᵉ lᵉ)
  where

  is-central-element-prop-Groupᵉ : type-Groupᵉ Gᵉ → Propᵉ lᵉ
  is-central-element-prop-Groupᵉ =
    is-central-element-prop-Monoidᵉ (monoid-Groupᵉ Gᵉ)

  is-central-element-Groupᵉ : type-Groupᵉ Gᵉ → UUᵉ lᵉ
  is-central-element-Groupᵉ = is-central-element-Monoidᵉ (monoid-Groupᵉ Gᵉ)

  is-prop-is-central-element-Groupᵉ :
    (xᵉ : type-Groupᵉ Gᵉ) → is-propᵉ (is-central-element-Groupᵉ xᵉ)
  is-prop-is-central-element-Groupᵉ =
    is-prop-is-central-element-Monoidᵉ (monoid-Groupᵉ Gᵉ)
```

## Properties

### The unit element is central

```agda
module _
  {lᵉ : Level} (Gᵉ : Groupᵉ lᵉ)
  where

  is-central-element-unit-Groupᵉ : is-central-element-Groupᵉ Gᵉ (unit-Groupᵉ Gᵉ)
  is-central-element-unit-Groupᵉ =
    is-central-element-unit-Monoidᵉ (monoid-Groupᵉ Gᵉ)
```

### The product of two central elements is central

```agda
module _
  {lᵉ : Level} (Gᵉ : Groupᵉ lᵉ)
  where

  is-central-element-mul-Groupᵉ :
    {xᵉ yᵉ : type-Groupᵉ Gᵉ} →
    is-central-element-Groupᵉ Gᵉ xᵉ → is-central-element-Groupᵉ Gᵉ yᵉ →
    is-central-element-Groupᵉ Gᵉ (mul-Groupᵉ Gᵉ xᵉ yᵉ)
  is-central-element-mul-Groupᵉ {xᵉ} {yᵉ} =
    is-central-element-mul-Monoidᵉ (monoid-Groupᵉ Gᵉ) xᵉ yᵉ
```

### The inverse of a central element is central

```agda
module _
  {lᵉ : Level} (Gᵉ : Groupᵉ lᵉ)
  where

  is-central-element-inv-Groupᵉ :
    {xᵉ : type-Groupᵉ Gᵉ} → is-central-element-Groupᵉ Gᵉ xᵉ →
    is-central-element-Groupᵉ Gᵉ (inv-Groupᵉ Gᵉ xᵉ)
  is-central-element-inv-Groupᵉ {xᵉ} Hᵉ yᵉ =
    ( invᵉ (inv-left-div-Groupᵉ Gᵉ yᵉ xᵉ)) ∙ᵉ
    ( apᵉ (inv-Groupᵉ Gᵉ) (invᵉ (Hᵉ (inv-Groupᵉ Gᵉ yᵉ)))) ∙ᵉ
    ( inv-right-div-Groupᵉ Gᵉ xᵉ yᵉ)
```

### The central elements are closed under conjugation

```agda
module _
  {lᵉ : Level} (Gᵉ : Groupᵉ lᵉ)
  where

  is-fixed-point-conjugation-is-central-element-Groupᵉ :
    (xᵉ yᵉ : type-Groupᵉ Gᵉ) → is-central-element-Groupᵉ Gᵉ xᵉ →
    conjugation-Groupᵉ Gᵉ yᵉ xᵉ ＝ᵉ xᵉ
  is-fixed-point-conjugation-is-central-element-Groupᵉ xᵉ yᵉ Hᵉ =
    ( apᵉ (λ zᵉ → right-div-Groupᵉ Gᵉ zᵉ yᵉ) (invᵉ (Hᵉ yᵉ))) ∙ᵉ
    ( is-retraction-right-div-Groupᵉ Gᵉ yᵉ xᵉ)

  is-central-element-conjugation-Groupᵉ :
    (xᵉ yᵉ : type-Groupᵉ Gᵉ) → is-central-element-Groupᵉ Gᵉ xᵉ →
    is-central-element-Groupᵉ Gᵉ (conjugation-Groupᵉ Gᵉ yᵉ xᵉ)
  is-central-element-conjugation-Groupᵉ xᵉ yᵉ Hᵉ =
    is-closed-under-eq-subtype'ᵉ
      ( is-central-element-prop-Groupᵉ Gᵉ)
      ( Hᵉ)
      ( is-fixed-point-conjugation-is-central-element-Groupᵉ xᵉ yᵉ Hᵉ)
```