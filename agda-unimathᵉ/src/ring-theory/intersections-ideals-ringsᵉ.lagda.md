# Intersections of ideals of rings

```agda
module ring-theory.intersections-ideals-ringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.intersections-subtypesᵉ
open import foundation.universe-levelsᵉ

open import order-theory.greatest-lower-bounds-large-posetsᵉ

open import ring-theory.ideals-ringsᵉ
open import ring-theory.poset-of-ideals-ringsᵉ
open import ring-theory.ringsᵉ
open import ring-theory.subsets-ringsᵉ
```

</details>

## Idea

Theᵉ **intersection**ᵉ ofᵉ twoᵉ [ideals](ring-theory.ideals-rings.mdᵉ) ofᵉ aᵉ
[ring](ring-theory.rings.mdᵉ) `R`ᵉ consistsᵉ ofᵉ theᵉ elementsᵉ containedᵉ in bothᵉ ofᵉ
them.ᵉ

## Definitions

### The universal property of intersections of ideals in rings

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Aᵉ : Ringᵉ l1ᵉ)
  (Iᵉ : ideal-Ringᵉ l2ᵉ Aᵉ)
  (Jᵉ : ideal-Ringᵉ l3ᵉ Aᵉ)
  where

  is-intersection-ideal-Ringᵉ :
    {l4ᵉ : Level} (Kᵉ : ideal-Ringᵉ l4ᵉ Aᵉ) → UUωᵉ
  is-intersection-ideal-Ringᵉ Kᵉ =
    is-greatest-binary-lower-bound-Large-Posetᵉ
      ( ideal-Ring-Large-Posetᵉ Aᵉ)
      ( Iᵉ)
      ( Jᵉ)
      ( Kᵉ)
```

### Intersections of ideals in rings

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ) (Iᵉ : ideal-Ringᵉ l2ᵉ Rᵉ) (Jᵉ : ideal-Ringᵉ l3ᵉ Rᵉ)
  where

  subset-intersection-ideal-Ringᵉ : subset-Ringᵉ (l2ᵉ ⊔ l3ᵉ) Rᵉ
  subset-intersection-ideal-Ringᵉ =
    intersection-subtypeᵉ (subset-ideal-Ringᵉ Rᵉ Iᵉ) (subset-ideal-Ringᵉ Rᵉ Jᵉ)

  contains-zero-intersection-ideal-Ringᵉ :
    contains-zero-subset-Ringᵉ Rᵉ subset-intersection-ideal-Ringᵉ
  pr1ᵉ contains-zero-intersection-ideal-Ringᵉ =
    contains-zero-ideal-Ringᵉ Rᵉ Iᵉ
  pr2ᵉ contains-zero-intersection-ideal-Ringᵉ =
    contains-zero-ideal-Ringᵉ Rᵉ Jᵉ

  is-closed-under-addition-intersection-ideal-Ringᵉ :
    is-closed-under-addition-subset-Ringᵉ Rᵉ
      subset-intersection-ideal-Ringᵉ
  pr1ᵉ (is-closed-under-addition-intersection-ideal-Ringᵉ Hᵉ Kᵉ) =
    is-closed-under-addition-ideal-Ringᵉ Rᵉ Iᵉ (pr1ᵉ Hᵉ) (pr1ᵉ Kᵉ)
  pr2ᵉ (is-closed-under-addition-intersection-ideal-Ringᵉ Hᵉ Kᵉ) =
    is-closed-under-addition-ideal-Ringᵉ Rᵉ Jᵉ (pr2ᵉ Hᵉ) (pr2ᵉ Kᵉ)

  is-closed-under-negatives-intersection-ideal-Ringᵉ :
    is-closed-under-negatives-subset-Ringᵉ Rᵉ
      subset-intersection-ideal-Ringᵉ
  pr1ᵉ (is-closed-under-negatives-intersection-ideal-Ringᵉ Hᵉ) =
    is-closed-under-negatives-ideal-Ringᵉ Rᵉ Iᵉ (pr1ᵉ Hᵉ)
  pr2ᵉ (is-closed-under-negatives-intersection-ideal-Ringᵉ Hᵉ) =
    is-closed-under-negatives-ideal-Ringᵉ Rᵉ Jᵉ (pr2ᵉ Hᵉ)

  is-closed-under-left-multiplication-intersection-ideal-Ringᵉ :
    is-closed-under-left-multiplication-subset-Ringᵉ Rᵉ
      subset-intersection-ideal-Ringᵉ
  pr1ᵉ (is-closed-under-left-multiplication-intersection-ideal-Ringᵉ xᵉ yᵉ Hᵉ) =
    is-closed-under-left-multiplication-ideal-Ringᵉ Rᵉ Iᵉ xᵉ yᵉ (pr1ᵉ Hᵉ)
  pr2ᵉ (is-closed-under-left-multiplication-intersection-ideal-Ringᵉ xᵉ yᵉ Hᵉ) =
    is-closed-under-left-multiplication-ideal-Ringᵉ Rᵉ Jᵉ xᵉ yᵉ (pr2ᵉ Hᵉ)

  is-closed-under-right-multiplication-intersection-ideal-Ringᵉ :
    is-closed-under-right-multiplication-subset-Ringᵉ Rᵉ
      subset-intersection-ideal-Ringᵉ
  pr1ᵉ (is-closed-under-right-multiplication-intersection-ideal-Ringᵉ xᵉ yᵉ Hᵉ) =
    is-closed-under-right-multiplication-ideal-Ringᵉ Rᵉ Iᵉ xᵉ yᵉ (pr1ᵉ Hᵉ)
  pr2ᵉ (is-closed-under-right-multiplication-intersection-ideal-Ringᵉ xᵉ yᵉ Hᵉ) =
    is-closed-under-right-multiplication-ideal-Ringᵉ Rᵉ Jᵉ xᵉ yᵉ (pr2ᵉ Hᵉ)

  is-additive-subgroup-intersection-ideal-Ringᵉ :
    is-additive-subgroup-subset-Ringᵉ Rᵉ subset-intersection-ideal-Ringᵉ
  pr1ᵉ is-additive-subgroup-intersection-ideal-Ringᵉ =
    contains-zero-intersection-ideal-Ringᵉ
  pr1ᵉ (pr2ᵉ is-additive-subgroup-intersection-ideal-Ringᵉ) =
    is-closed-under-addition-intersection-ideal-Ringᵉ
  pr2ᵉ (pr2ᵉ is-additive-subgroup-intersection-ideal-Ringᵉ) =
    is-closed-under-negatives-intersection-ideal-Ringᵉ

  is-ideal-intersection-ideal-Ringᵉ :
    is-ideal-subset-Ringᵉ Rᵉ subset-intersection-ideal-Ringᵉ
  pr1ᵉ is-ideal-intersection-ideal-Ringᵉ =
    is-additive-subgroup-intersection-ideal-Ringᵉ
  pr1ᵉ (pr2ᵉ is-ideal-intersection-ideal-Ringᵉ) =
    is-closed-under-left-multiplication-intersection-ideal-Ringᵉ
  pr2ᵉ (pr2ᵉ is-ideal-intersection-ideal-Ringᵉ) =
    is-closed-under-right-multiplication-intersection-ideal-Ringᵉ

  intersection-ideal-Ringᵉ : ideal-Ringᵉ (l2ᵉ ⊔ l3ᵉ) Rᵉ
  pr1ᵉ intersection-ideal-Ringᵉ = subset-intersection-ideal-Ringᵉ
  pr2ᵉ intersection-ideal-Ringᵉ = is-ideal-intersection-ideal-Ringᵉ

  is-intersection-intersection-ideal-Ringᵉ :
    is-intersection-ideal-Ringᵉ Rᵉ Iᵉ Jᵉ intersection-ideal-Ringᵉ
  is-intersection-intersection-ideal-Ringᵉ Kᵉ =
    is-greatest-binary-lower-bound-intersection-subtypeᵉ
      ( subset-ideal-Ringᵉ Rᵉ Iᵉ)
      ( subset-ideal-Ringᵉ Rᵉ Jᵉ)
      ( subset-ideal-Ringᵉ Rᵉ Kᵉ)
```