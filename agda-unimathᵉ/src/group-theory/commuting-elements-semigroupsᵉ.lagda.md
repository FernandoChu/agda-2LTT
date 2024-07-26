# Commuting elements of semigroups

```agda
module group-theory.commuting-elements-semigroupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.semigroupsᵉ
```

</details>

## Idea

Twoᵉ elementsᵉ `x`ᵉ andᵉ `y`ᵉ ofᵉ aᵉ [semigroup](group-theory.semigroups.mdᵉ) areᵉ saidᵉ
to **commute**ᵉ ifᵉ `xyᵉ ＝ᵉ yx`.ᵉ

## Definitions

### Commuting elements

```agda
module _
  {lᵉ : Level} (Gᵉ : Semigroupᵉ lᵉ)
  where

  commute-prop-Semigroupᵉ : (xᵉ yᵉ : type-Semigroupᵉ Gᵉ) → Propᵉ lᵉ
  commute-prop-Semigroupᵉ xᵉ yᵉ =
    Id-Propᵉ (set-Semigroupᵉ Gᵉ) (mul-Semigroupᵉ Gᵉ xᵉ yᵉ) (mul-Semigroupᵉ Gᵉ yᵉ xᵉ)

  commute-Semigroupᵉ : (xᵉ yᵉ : type-Semigroupᵉ Gᵉ) → UUᵉ lᵉ
  commute-Semigroupᵉ xᵉ yᵉ = type-Propᵉ (commute-prop-Semigroupᵉ xᵉ yᵉ)

  commute-Semigroup'ᵉ : (xᵉ yᵉ : type-Semigroupᵉ Gᵉ) → UUᵉ lᵉ
  commute-Semigroup'ᵉ xᵉ yᵉ = commute-Semigroupᵉ yᵉ xᵉ

  is-prop-commute-Semigroupᵉ :
    (xᵉ yᵉ : type-Semigroupᵉ Gᵉ) → is-propᵉ (commute-Semigroupᵉ xᵉ yᵉ)
  is-prop-commute-Semigroupᵉ xᵉ yᵉ = is-prop-type-Propᵉ (commute-prop-Semigroupᵉ xᵉ yᵉ)
```

## Properties

### The relation `commute-Semigroup` is reflexive

```agda
module _
  {lᵉ : Level} (Gᵉ : Semigroupᵉ lᵉ)
  where

  refl-commute-Semigroupᵉ : (xᵉ : type-Semigroupᵉ Gᵉ) → commute-Semigroupᵉ Gᵉ xᵉ xᵉ
  refl-commute-Semigroupᵉ xᵉ = reflᵉ
```

### The relation `commute-Semigroup` is symmetric

```agda
module _
  {lᵉ : Level} (Gᵉ : Semigroupᵉ lᵉ)
  where

  symmetric-commute-Semigroupᵉ :
    (xᵉ yᵉ : type-Semigroupᵉ Gᵉ) → commute-Semigroupᵉ Gᵉ xᵉ yᵉ → commute-Semigroupᵉ Gᵉ yᵉ xᵉ
  symmetric-commute-Semigroupᵉ xᵉ yᵉ = invᵉ
```

### If `x` commutes with `y`, then `x * (y * z) ＝ y * (x * z)` for any element `z`

```agda
module _
  {lᵉ : Level} (Gᵉ : Semigroupᵉ lᵉ)
  where

  private
    infix 45 _*ᵉ_
    _*ᵉ_ = mul-Semigroupᵉ Gᵉ

  left-swap-commute-Semigroupᵉ :
    (xᵉ yᵉ zᵉ : type-Semigroupᵉ Gᵉ) → commute-Semigroupᵉ Gᵉ xᵉ yᵉ →
    xᵉ *ᵉ (yᵉ *ᵉ zᵉ) ＝ᵉ yᵉ *ᵉ (xᵉ *ᵉ zᵉ)
  left-swap-commute-Semigroupᵉ xᵉ yᵉ zᵉ Hᵉ =
    ( invᵉ (associative-mul-Semigroupᵉ Gᵉ _ _ _)) ∙ᵉ
    ( apᵉ (_*ᵉ zᵉ) Hᵉ) ∙ᵉ
    ( associative-mul-Semigroupᵉ Gᵉ _ _ _)

  right-swap-commute-Semigroupᵉ :
    (xᵉ yᵉ zᵉ : type-Semigroupᵉ Gᵉ) → commute-Semigroupᵉ Gᵉ yᵉ zᵉ →
    (xᵉ *ᵉ yᵉ) *ᵉ zᵉ ＝ᵉ (xᵉ *ᵉ zᵉ) *ᵉ yᵉ
  right-swap-commute-Semigroupᵉ xᵉ yᵉ zᵉ Hᵉ =
    ( associative-mul-Semigroupᵉ Gᵉ _ _ _) ∙ᵉ
    ( apᵉ (xᵉ *ᵉ_) Hᵉ) ∙ᵉ
    ( invᵉ (associative-mul-Semigroupᵉ Gᵉ _ _ _))
```

### If `x` commutes with `y` and with `z`, then `x` commutes with `yz`

```agda
module _
  {lᵉ : Level} (Gᵉ : Semigroupᵉ lᵉ)
  where

  private
    infix 45 _*ᵉ_
    _*ᵉ_ = mul-Semigroupᵉ Gᵉ

  commute-mul-Semigroupᵉ :
    (xᵉ yᵉ zᵉ : type-Semigroupᵉ Gᵉ) →
    commute-Semigroupᵉ Gᵉ xᵉ yᵉ → commute-Semigroupᵉ Gᵉ xᵉ zᵉ →
    commute-Semigroupᵉ Gᵉ xᵉ (mul-Semigroupᵉ Gᵉ yᵉ zᵉ)
  commute-mul-Semigroupᵉ xᵉ yᵉ zᵉ Hᵉ Kᵉ =
    equational-reasoningᵉ
      (xᵉ *ᵉ (yᵉ *ᵉ zᵉ))
      ＝ᵉ yᵉ *ᵉ (xᵉ *ᵉ zᵉ) byᵉ left-swap-commute-Semigroupᵉ Gᵉ _ _ _ Hᵉ
      ＝ᵉ yᵉ *ᵉ (zᵉ *ᵉ xᵉ) byᵉ apᵉ (yᵉ *ᵉ_) Kᵉ
      ＝ᵉ (yᵉ *ᵉ zᵉ) *ᵉ xᵉ byᵉ invᵉ (associative-mul-Semigroupᵉ Gᵉ _ _ _)
```