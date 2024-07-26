# Commuting elements of groups

```agda
module group-theory.commuting-elements-groupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.commuting-elements-monoidsᵉ
open import group-theory.groupsᵉ
```

</details>

## Idea

Twoᵉ elementsᵉ `x`ᵉ andᵉ `y`ᵉ ofᵉ aᵉ [group](group-theory.groups.mdᵉ) `G`ᵉ areᵉ saidᵉ to
**commute**ᵉ ifᵉ theᵉ equalityᵉ `xyᵉ ＝ᵉ yx`ᵉ holds.ᵉ Forᵉ anyᵉ elementᵉ `x`,ᵉ theᵉ subsetᵉ ofᵉ
elementsᵉ thatᵉ commuteᵉ with `x`ᵉ formᵉ aᵉ [subgroup](group-theory.subgroups.mdᵉ) ofᵉ
`G`ᵉ calledᵉ theᵉ [centralizer](group-theory.centralizer-subgroups.mdᵉ) ofᵉ theᵉ
elementᵉ `x`.ᵉ

## Definitions

### Commuting elements

```agda
module _
  {lᵉ : Level} (Gᵉ : Groupᵉ lᵉ)
  where

  commute-prop-Groupᵉ : (xᵉ yᵉ : type-Groupᵉ Gᵉ) → Propᵉ lᵉ
  commute-prop-Groupᵉ = commute-prop-Monoidᵉ (monoid-Groupᵉ Gᵉ)

  commute-Groupᵉ : (xᵉ yᵉ : type-Groupᵉ Gᵉ) → UUᵉ lᵉ
  commute-Groupᵉ = commute-Monoidᵉ (monoid-Groupᵉ Gᵉ)

  commute-Group'ᵉ : (xᵉ yᵉ : type-Groupᵉ Gᵉ) → UUᵉ lᵉ
  commute-Group'ᵉ = commute-Monoid'ᵉ (monoid-Groupᵉ Gᵉ)

  is-prop-commute-Groupᵉ : (xᵉ yᵉ : type-Groupᵉ Gᵉ) → is-propᵉ (commute-Groupᵉ xᵉ yᵉ)
  is-prop-commute-Groupᵉ = is-prop-commute-Monoidᵉ (monoid-Groupᵉ Gᵉ)
```

## Properties

### The relation `commute-Group` is reflexive

```agda
module _
  {lᵉ : Level} (Gᵉ : Groupᵉ lᵉ)
  where

  refl-commute-Groupᵉ : (xᵉ : type-Groupᵉ Gᵉ) → commute-Groupᵉ Gᵉ xᵉ xᵉ
  refl-commute-Groupᵉ = refl-commute-Monoidᵉ (monoid-Groupᵉ Gᵉ)
```

### The relation `commute-Group` is symmetric

```agda
module _
  {lᵉ : Level} (Gᵉ : Groupᵉ lᵉ)
  where

  symmetric-commute-Groupᵉ :
    (xᵉ yᵉ : type-Groupᵉ Gᵉ) → commute-Groupᵉ Gᵉ xᵉ yᵉ → commute-Groupᵉ Gᵉ yᵉ xᵉ
  symmetric-commute-Groupᵉ = symmetric-commute-Monoidᵉ (monoid-Groupᵉ Gᵉ)
```

### The unit element commutes with every element of the group

```agda
module _
  {lᵉ : Level} (Gᵉ : Groupᵉ lᵉ)
  where

  commute-unit-Groupᵉ : (xᵉ : type-Groupᵉ Gᵉ) → commute-Groupᵉ Gᵉ xᵉ (unit-Groupᵉ Gᵉ)
  commute-unit-Groupᵉ = commute-unit-Monoidᵉ (monoid-Groupᵉ Gᵉ)
```

### If `x` commutes with `y`, then `x` commutes with `y⁻¹`

```agda
module _
  {lᵉ : Level} (Gᵉ : Groupᵉ lᵉ)
  where

  commute-inv-Groupᵉ :
    (xᵉ yᵉ : type-Groupᵉ Gᵉ) →
    commute-Groupᵉ Gᵉ xᵉ yᵉ → commute-Groupᵉ Gᵉ xᵉ (inv-Groupᵉ Gᵉ yᵉ)
  commute-inv-Groupᵉ xᵉ yᵉ Hᵉ =
    double-transpose-eq-mul-Group'ᵉ Gᵉ (invᵉ Hᵉ)
```

### If `x` commutes with `y`, then `x * (y * z) ＝ y * (x * z)` for any element `z`

```agda
module _
  {lᵉ : Level} (Gᵉ : Groupᵉ lᵉ)
  where

  private
    infix 45 _*ᵉ_
    _*ᵉ_ = mul-Groupᵉ Gᵉ

  left-swap-commute-Groupᵉ :
    (xᵉ yᵉ zᵉ : type-Groupᵉ Gᵉ) → commute-Groupᵉ Gᵉ xᵉ yᵉ →
    xᵉ *ᵉ (yᵉ *ᵉ zᵉ) ＝ᵉ yᵉ *ᵉ (xᵉ *ᵉ zᵉ)
  left-swap-commute-Groupᵉ = left-swap-commute-Monoidᵉ (monoid-Groupᵉ Gᵉ)

  right-swap-commute-Groupᵉ :
    (xᵉ yᵉ zᵉ : type-Groupᵉ Gᵉ) → commute-Groupᵉ Gᵉ yᵉ zᵉ →
    (xᵉ *ᵉ yᵉ) *ᵉ zᵉ ＝ᵉ (xᵉ *ᵉ zᵉ) *ᵉ yᵉ
  right-swap-commute-Groupᵉ = right-swap-commute-Monoidᵉ (monoid-Groupᵉ Gᵉ)
```

### If `x` commutes with `y` and with `z`, then `x` commutes with `yz`

```agda
module _
  {lᵉ : Level} (Gᵉ : Groupᵉ lᵉ)
  where

  commute-mul-Groupᵉ :
    (xᵉ yᵉ zᵉ : type-Groupᵉ Gᵉ) →
    commute-Groupᵉ Gᵉ xᵉ yᵉ → commute-Groupᵉ Gᵉ xᵉ zᵉ →
    commute-Groupᵉ Gᵉ xᵉ (mul-Groupᵉ Gᵉ yᵉ zᵉ)
  commute-mul-Groupᵉ = commute-mul-Monoidᵉ (monoid-Groupᵉ Gᵉ)
```