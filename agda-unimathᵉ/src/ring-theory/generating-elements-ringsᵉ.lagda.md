# Generating elements of rings

```agda
module ring-theory.generating-elements-ringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.propositionsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.generating-elements-groupsᵉ

open import ring-theory.ringsᵉ
```

</details>

## Idea

Aᵉ **generatingᵉ element**ᵉ ofᵉ aᵉ [ring](ring-theory.rings.mdᵉ) `R`ᵉ isᵉ anᵉ elementᵉ `g`ᵉ
whichᵉ isᵉ aᵉ [generatingᵉ element](group-theory.generating-elements-groups.mdᵉ) ofᵉ
theᵉ underlyingᵉ additiveᵉ [group](group-theory.groups.mdᵉ) ofᵉ `R`.ᵉ Thatᵉ is,ᵉ `g`ᵉ isᵉ
aᵉ generatingᵉ elementᵉ ofᵉ aᵉ ringᵉ `R`ᵉ ifᵉ forᵉ everyᵉ elementᵉ `xᵉ : R`ᵉ thereᵉ existsᵉ anᵉ
integerᵉ `k`ᵉ suchᵉ thatᵉ `kgᵉ ＝ᵉ x`.ᵉ

## Definitions

### Generating elements of a ring

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ) (gᵉ : type-Ringᵉ Rᵉ)
  where

  is-generating-element-prop-Ringᵉ : Propᵉ lᵉ
  is-generating-element-prop-Ringᵉ =
    is-generating-element-prop-Groupᵉ (group-Ringᵉ Rᵉ) gᵉ
```