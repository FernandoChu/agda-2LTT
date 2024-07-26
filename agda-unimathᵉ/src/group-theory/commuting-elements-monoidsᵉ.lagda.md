# Commuting elements of monoids

```agda
module group-theory.commuting-elements-monoidsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.commuting-elements-semigroupsᵉ
open import group-theory.monoidsᵉ
```

</details>

## Idea

Twoᵉ elementsᵉ `x`ᵉ andᵉ `y`ᵉ ofᵉ aᵉ [monoid](group-theory.monoids.mdᵉ) `G`ᵉ areᵉ saidᵉ to
**commute**ᵉ ifᵉ theᵉ equalityᵉ `xyᵉ ＝ᵉ yx`ᵉ holds.ᵉ

## Definitions

### Commuting elements

```agda
module _
  {lᵉ : Level} (Mᵉ : Monoidᵉ lᵉ)
  where

  commute-prop-Monoidᵉ : (xᵉ yᵉ : type-Monoidᵉ Mᵉ) → Propᵉ lᵉ
  commute-prop-Monoidᵉ = commute-prop-Semigroupᵉ (semigroup-Monoidᵉ Mᵉ)

  commute-Monoidᵉ : (xᵉ yᵉ : type-Monoidᵉ Mᵉ) → UUᵉ lᵉ
  commute-Monoidᵉ = commute-Semigroupᵉ (semigroup-Monoidᵉ Mᵉ)

  commute-Monoid'ᵉ : (xᵉ yᵉ : type-Monoidᵉ Mᵉ) → UUᵉ lᵉ
  commute-Monoid'ᵉ = commute-Semigroup'ᵉ (semigroup-Monoidᵉ Mᵉ)

  is-prop-commute-Monoidᵉ : (xᵉ yᵉ : type-Monoidᵉ Mᵉ) → is-propᵉ (commute-Monoidᵉ xᵉ yᵉ)
  is-prop-commute-Monoidᵉ = is-prop-commute-Semigroupᵉ (semigroup-Monoidᵉ Mᵉ)
```

## Properties

### The relation `commute-Monoid` is reflexive

```agda
module _
  {lᵉ : Level} (Mᵉ : Monoidᵉ lᵉ)
  where

  refl-commute-Monoidᵉ : (xᵉ : type-Monoidᵉ Mᵉ) → commute-Monoidᵉ Mᵉ xᵉ xᵉ
  refl-commute-Monoidᵉ = refl-commute-Semigroupᵉ (semigroup-Monoidᵉ Mᵉ)
```

### The relation `commute-Monoid` is symmetric

```agda
module _
  {lᵉ : Level} (Mᵉ : Monoidᵉ lᵉ)
  where

  symmetric-commute-Monoidᵉ :
    (xᵉ yᵉ : type-Monoidᵉ Mᵉ) → commute-Monoidᵉ Mᵉ xᵉ yᵉ → commute-Monoidᵉ Mᵉ yᵉ xᵉ
  symmetric-commute-Monoidᵉ = symmetric-commute-Semigroupᵉ (semigroup-Monoidᵉ Mᵉ)
```

### The unit element commutes with every element of the monoid

```agda
module _
  {lᵉ : Level} (Mᵉ : Monoidᵉ lᵉ)
  where

  commute-unit-Monoidᵉ : (xᵉ : type-Monoidᵉ Mᵉ) → commute-Monoidᵉ Mᵉ xᵉ (unit-Monoidᵉ Mᵉ)
  commute-unit-Monoidᵉ xᵉ =
    right-unit-law-mul-Monoidᵉ Mᵉ xᵉ ∙ᵉ invᵉ (left-unit-law-mul-Monoidᵉ Mᵉ xᵉ)
```

### If `x` commutes with `y`, then `x * (y * z) ＝ y * (x * z)` for any element `z`

```agda
module _
  {lᵉ : Level} (Mᵉ : Monoidᵉ lᵉ)
  where

  private
    infix 45 _*ᵉ_
    _*ᵉ_ = mul-Monoidᵉ Mᵉ

  left-swap-commute-Monoidᵉ :
    (xᵉ yᵉ zᵉ : type-Monoidᵉ Mᵉ) → commute-Monoidᵉ Mᵉ xᵉ yᵉ →
    xᵉ *ᵉ (yᵉ *ᵉ zᵉ) ＝ᵉ yᵉ *ᵉ (xᵉ *ᵉ zᵉ)
  left-swap-commute-Monoidᵉ = left-swap-commute-Semigroupᵉ (semigroup-Monoidᵉ Mᵉ)

  right-swap-commute-Monoidᵉ :
    (xᵉ yᵉ zᵉ : type-Monoidᵉ Mᵉ) → commute-Monoidᵉ Mᵉ yᵉ zᵉ →
    (xᵉ *ᵉ yᵉ) *ᵉ zᵉ ＝ᵉ (xᵉ *ᵉ zᵉ) *ᵉ yᵉ
  right-swap-commute-Monoidᵉ = right-swap-commute-Semigroupᵉ (semigroup-Monoidᵉ Mᵉ)
```

### If `x` commutes with `y` and with `z`, then `x` commutes with `yz`

```agda
module _
  {lᵉ : Level} (Mᵉ : Monoidᵉ lᵉ)
  where

  commute-mul-Monoidᵉ :
    (xᵉ yᵉ zᵉ : type-Monoidᵉ Mᵉ) →
    commute-Monoidᵉ Mᵉ xᵉ yᵉ → commute-Monoidᵉ Mᵉ xᵉ zᵉ →
    commute-Monoidᵉ Mᵉ xᵉ (mul-Monoidᵉ Mᵉ yᵉ zᵉ)
  commute-mul-Monoidᵉ = commute-mul-Semigroupᵉ (semigroup-Monoidᵉ Mᵉ)
```