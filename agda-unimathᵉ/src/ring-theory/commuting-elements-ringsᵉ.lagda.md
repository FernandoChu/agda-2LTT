# Commuting elements of rings

```agda
module ring-theory.commuting-elements-ringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.commuting-elements-monoidsᵉ

open import ring-theory.ringsᵉ
```

</details>

## Idea

Twoᵉ elementsᵉ `x`ᵉ andᵉ `y`ᵉ ofᵉ aᵉ [ring](ring-theory.rings.mdᵉ) `R`ᵉ areᵉ saidᵉ to
**commute**ᵉ ifᵉ `xyᵉ ＝ᵉ yx`.ᵉ

## Definitions

### Commuting elements

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  commute-prop-Ringᵉ : (xᵉ yᵉ : type-Ringᵉ Rᵉ) → Propᵉ lᵉ
  commute-prop-Ringᵉ = commute-prop-Monoidᵉ (multiplicative-monoid-Ringᵉ Rᵉ)

  commute-Ringᵉ : (xᵉ yᵉ : type-Ringᵉ Rᵉ) → UUᵉ lᵉ
  commute-Ringᵉ = commute-Monoidᵉ (multiplicative-monoid-Ringᵉ Rᵉ)

  commute-Ring'ᵉ : (xᵉ yᵉ : type-Ringᵉ Rᵉ) → UUᵉ lᵉ
  commute-Ring'ᵉ = commute-Monoid'ᵉ (multiplicative-monoid-Ringᵉ Rᵉ)

  is-prop-commute-Ringᵉ : (xᵉ yᵉ : type-Ringᵉ Rᵉ) → is-propᵉ (commute-Ringᵉ xᵉ yᵉ)
  is-prop-commute-Ringᵉ = is-prop-commute-Monoidᵉ (multiplicative-monoid-Ringᵉ Rᵉ)
```

## Properties

### The relation `commute-Ring` is reflexive

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  refl-commute-Ringᵉ : (xᵉ : type-Ringᵉ Rᵉ) → commute-Ringᵉ Rᵉ xᵉ xᵉ
  refl-commute-Ringᵉ = refl-commute-Monoidᵉ (multiplicative-monoid-Ringᵉ Rᵉ)
```

### The relation `commute-Ring` is symmetric

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  symmetric-commute-Ringᵉ :
    (xᵉ yᵉ : type-Ringᵉ Rᵉ) → commute-Ringᵉ Rᵉ xᵉ yᵉ → commute-Ringᵉ Rᵉ yᵉ xᵉ
  symmetric-commute-Ringᵉ =
    symmetric-commute-Monoidᵉ (multiplicative-monoid-Ringᵉ Rᵉ)
```

### The zero element commutes with every element of the ring

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  commute-zero-Ringᵉ : (xᵉ : type-Ringᵉ Rᵉ) → commute-Ringᵉ Rᵉ (zero-Ringᵉ Rᵉ) xᵉ
  commute-zero-Ringᵉ xᵉ =
    left-zero-law-mul-Ringᵉ Rᵉ xᵉ ∙ᵉ invᵉ (right-zero-law-mul-Ringᵉ Rᵉ xᵉ)
```

### The multiplicative unit element commutes with every element of the ring

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  commute-one-Ringᵉ : (xᵉ : type-Ringᵉ Rᵉ) → commute-Ringᵉ Rᵉ xᵉ (one-Ringᵉ Rᵉ)
  commute-one-Ringᵉ = commute-unit-Monoidᵉ (multiplicative-monoid-Ringᵉ Rᵉ)
```

### If `y` and `z` commute with `x`, then `y + z` commutes with `x`

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  commute-add-Ringᵉ :
    {xᵉ yᵉ zᵉ : type-Ringᵉ Rᵉ} → commute-Ringᵉ Rᵉ xᵉ yᵉ → commute-Ringᵉ Rᵉ xᵉ zᵉ →
    commute-Ringᵉ Rᵉ xᵉ (add-Ringᵉ Rᵉ yᵉ zᵉ)
  commute-add-Ringᵉ Hᵉ Kᵉ =
    left-distributive-mul-add-Ringᵉ Rᵉ _ _ _ ∙ᵉ
    ap-add-Ringᵉ Rᵉ Hᵉ Kᵉ ∙ᵉ
    invᵉ (right-distributive-mul-add-Ringᵉ Rᵉ _ _ _)
```

### If `x` commutes with `y`, then `x` commutes with `-y`

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  commute-neg-Ringᵉ :
    {xᵉ yᵉ : type-Ringᵉ Rᵉ} → commute-Ringᵉ Rᵉ xᵉ yᵉ → commute-Ringᵉ Rᵉ xᵉ (neg-Ringᵉ Rᵉ yᵉ)
  commute-neg-Ringᵉ Hᵉ =
    right-negative-law-mul-Ringᵉ Rᵉ _ _ ∙ᵉ
    apᵉ (neg-Ringᵉ Rᵉ) Hᵉ ∙ᵉ
    invᵉ (left-negative-law-mul-Ringᵉ Rᵉ _ _)
```

### If `x` commutes with `y`, then `-x` commutes with `-y`

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  commute-neg-neg-Ringᵉ :
    {xᵉ yᵉ : type-Ringᵉ Rᵉ} → commute-Ringᵉ Rᵉ xᵉ yᵉ →
    commute-Ringᵉ Rᵉ (neg-Ringᵉ Rᵉ xᵉ) (neg-Ringᵉ Rᵉ yᵉ)
  commute-neg-neg-Ringᵉ Hᵉ =
    mul-neg-Ringᵉ Rᵉ _ _ ∙ᵉ
    Hᵉ ∙ᵉ
    invᵉ (mul-neg-Ringᵉ Rᵉ _ _)
```

### If `x` commutes with `y` and `z`, then `x` commutes with `-y + z` and with `y - z`

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  commute-left-subtraction-Ringᵉ :
    {xᵉ yᵉ zᵉ : type-Ringᵉ Rᵉ} → commute-Ringᵉ Rᵉ xᵉ yᵉ → commute-Ringᵉ Rᵉ xᵉ zᵉ →
    commute-Ringᵉ Rᵉ xᵉ (left-subtraction-Ringᵉ Rᵉ yᵉ zᵉ)
  commute-left-subtraction-Ringᵉ Hᵉ Kᵉ =
    left-distributive-mul-left-subtraction-Ringᵉ Rᵉ _ _ _ ∙ᵉ
    ap-left-subtraction-Ringᵉ Rᵉ Hᵉ Kᵉ ∙ᵉ
    invᵉ (right-distributive-mul-left-subtraction-Ringᵉ Rᵉ _ _ _)

  commute-right-subtraction-Ringᵉ :
    {xᵉ yᵉ zᵉ : type-Ringᵉ Rᵉ} → commute-Ringᵉ Rᵉ xᵉ yᵉ → commute-Ringᵉ Rᵉ xᵉ zᵉ →
    commute-Ringᵉ Rᵉ xᵉ (right-subtraction-Ringᵉ Rᵉ yᵉ zᵉ)
  commute-right-subtraction-Ringᵉ Hᵉ Kᵉ =
    left-distributive-mul-right-subtraction-Ringᵉ Rᵉ _ _ _ ∙ᵉ
    ap-right-subtraction-Ringᵉ Rᵉ Hᵉ Kᵉ ∙ᵉ
    invᵉ (right-distributive-mul-right-subtraction-Ringᵉ Rᵉ _ _ _)
```

### If `x` commutes with `y`, then `x * (y * z) ＝ y * (x * z)` for any element `z`

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  private
    infix 50 _*ᵉ_
    _*ᵉ_ = mul-Ringᵉ Rᵉ

  left-swap-commute-Ringᵉ :
    (xᵉ yᵉ zᵉ : type-Ringᵉ Rᵉ) → commute-Ringᵉ Rᵉ xᵉ yᵉ →
    xᵉ *ᵉ (yᵉ *ᵉ zᵉ) ＝ᵉ yᵉ *ᵉ (xᵉ *ᵉ zᵉ)
  left-swap-commute-Ringᵉ =
    left-swap-commute-Monoidᵉ (multiplicative-monoid-Ringᵉ Rᵉ)

  right-swap-commute-Ringᵉ :
    (xᵉ yᵉ zᵉ : type-Ringᵉ Rᵉ) → commute-Ringᵉ Rᵉ yᵉ zᵉ →
    (xᵉ *ᵉ yᵉ) *ᵉ zᵉ ＝ᵉ (xᵉ *ᵉ zᵉ) *ᵉ yᵉ
  right-swap-commute-Ringᵉ =
    right-swap-commute-Monoidᵉ (multiplicative-monoid-Ringᵉ Rᵉ)
```

### If `x` commutes with `y` and with `z`, then `x` commutes with `yz`

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  commute-mul-Ringᵉ :
    (xᵉ yᵉ zᵉ : type-Ringᵉ Rᵉ) →
    commute-Ringᵉ Rᵉ xᵉ yᵉ → commute-Ringᵉ Rᵉ xᵉ zᵉ →
    commute-Ringᵉ Rᵉ xᵉ (mul-Ringᵉ Rᵉ yᵉ zᵉ)
  commute-mul-Ringᵉ = commute-mul-Monoidᵉ (multiplicative-monoid-Ringᵉ Rᵉ)
```