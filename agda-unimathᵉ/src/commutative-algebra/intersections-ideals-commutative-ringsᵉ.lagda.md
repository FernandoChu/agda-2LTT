# Intersections of ideals of commutative rings

```agda
module commutative-algebra.intersections-ideals-commutative-ringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-ringsᵉ
open import commutative-algebra.ideals-commutative-ringsᵉ
open import commutative-algebra.poset-of-ideals-commutative-ringsᵉ
open import commutative-algebra.subsets-commutative-ringsᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.intersections-subtypesᵉ
open import foundation.subtypesᵉ
open import foundation.universe-levelsᵉ

open import order-theory.greatest-lower-bounds-large-posetsᵉ

open import ring-theory.intersections-ideals-ringsᵉ
```

</details>

## Idea

Theᵉ **intersection**ᵉ ofᵉ twoᵉ idealsᵉ `I`ᵉ andᵉ `J`ᵉ in aᵉ commutativeᵉ ringᵉ isᵉ theᵉ
idealᵉ consistingᵉ ofᵉ theᵉ elementsᵉ containedᵉ in bothᵉ ofᵉ theᵉ idealsᵉ `I`ᵉ andᵉ `J`.ᵉ

## Definitions

### The universal property of intersections of radical ideals

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Aᵉ : Commutative-Ringᵉ l1ᵉ)
  (Iᵉ : ideal-Commutative-Ringᵉ l2ᵉ Aᵉ)
  (Jᵉ : ideal-Commutative-Ringᵉ l3ᵉ Aᵉ)
  where

  is-intersection-ideal-Commutative-Ringᵉ :
    {l4ᵉ : Level} (Kᵉ : ideal-Commutative-Ringᵉ l4ᵉ Aᵉ) → UUωᵉ
  is-intersection-ideal-Commutative-Ringᵉ Kᵉ =
    is-greatest-binary-lower-bound-Large-Posetᵉ
      ( ideal-Commutative-Ring-Large-Posetᵉ Aᵉ)
      ( Iᵉ)
      ( Jᵉ)
      ( Kᵉ)
```

### Intersections of ideals in commutative rings

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Rᵉ : Commutative-Ringᵉ l1ᵉ)
  (Iᵉ : ideal-Commutative-Ringᵉ l2ᵉ Rᵉ) (Jᵉ : ideal-Commutative-Ringᵉ l3ᵉ Rᵉ)
  where

  subset-intersection-ideal-Commutative-Ringᵉ :
    subset-Commutative-Ringᵉ (l2ᵉ ⊔ l3ᵉ) Rᵉ
  subset-intersection-ideal-Commutative-Ringᵉ =
    intersection-subtypeᵉ
      ( subset-ideal-Commutative-Ringᵉ Rᵉ Iᵉ)
      ( subset-ideal-Commutative-Ringᵉ Rᵉ Jᵉ)

  is-in-intersection-ideal-Commutative-Ringᵉ :
    type-Commutative-Ringᵉ Rᵉ → UUᵉ (l2ᵉ ⊔ l3ᵉ)
  is-in-intersection-ideal-Commutative-Ringᵉ =
    is-in-subtypeᵉ subset-intersection-ideal-Commutative-Ringᵉ

  contains-zero-intersection-ideal-Commutative-Ringᵉ :
    is-in-intersection-ideal-Commutative-Ringᵉ (zero-Commutative-Ringᵉ Rᵉ)
  pr1ᵉ contains-zero-intersection-ideal-Commutative-Ringᵉ =
    contains-zero-ideal-Commutative-Ringᵉ Rᵉ Iᵉ
  pr2ᵉ contains-zero-intersection-ideal-Commutative-Ringᵉ =
    contains-zero-ideal-Commutative-Ringᵉ Rᵉ Jᵉ

  is-closed-under-addition-intersection-ideal-Commutative-Ringᵉ :
    is-closed-under-addition-subset-Commutative-Ringᵉ Rᵉ
      ( subset-intersection-ideal-Commutative-Ringᵉ)
  pr1ᵉ
    ( is-closed-under-addition-intersection-ideal-Commutative-Ringᵉ
      ( H1ᵉ ,ᵉ H2ᵉ)
      ( K1ᵉ ,ᵉ K2ᵉ)) =
    is-closed-under-addition-ideal-Commutative-Ringᵉ Rᵉ Iᵉ H1ᵉ K1ᵉ
  pr2ᵉ
    ( is-closed-under-addition-intersection-ideal-Commutative-Ringᵉ
      ( H1ᵉ ,ᵉ H2ᵉ)
      ( K1ᵉ ,ᵉ K2ᵉ)) =
    is-closed-under-addition-ideal-Commutative-Ringᵉ Rᵉ Jᵉ H2ᵉ K2ᵉ

  is-closed-under-negatives-intersection-ideal-Commutative-Ringᵉ :
    is-closed-under-negatives-subset-Commutative-Ringᵉ Rᵉ
      ( subset-intersection-ideal-Commutative-Ringᵉ)
  pr1ᵉ
    ( is-closed-under-negatives-intersection-ideal-Commutative-Ringᵉ
      ( H1ᵉ ,ᵉ H2ᵉ)) =
    is-closed-under-negatives-ideal-Commutative-Ringᵉ Rᵉ Iᵉ H1ᵉ
  pr2ᵉ
    ( is-closed-under-negatives-intersection-ideal-Commutative-Ringᵉ
      ( H1ᵉ ,ᵉ H2ᵉ)) =
    is-closed-under-negatives-ideal-Commutative-Ringᵉ Rᵉ Jᵉ H2ᵉ

  is-additive-subgroup-intersection-ideal-Commutative-Ringᵉ :
    is-additive-subgroup-subset-Commutative-Ringᵉ Rᵉ
      ( subset-intersection-ideal-Commutative-Ringᵉ)
  pr1ᵉ is-additive-subgroup-intersection-ideal-Commutative-Ringᵉ =
    contains-zero-intersection-ideal-Commutative-Ringᵉ
  pr1ᵉ (pr2ᵉ is-additive-subgroup-intersection-ideal-Commutative-Ringᵉ) =
    is-closed-under-addition-intersection-ideal-Commutative-Ringᵉ
  pr2ᵉ (pr2ᵉ is-additive-subgroup-intersection-ideal-Commutative-Ringᵉ) =
    is-closed-under-negatives-intersection-ideal-Commutative-Ringᵉ

  is-closed-under-left-multiplication-intersection-ideal-Commutative-Ringᵉ :
    is-closed-under-left-multiplication-subset-Commutative-Ringᵉ Rᵉ
      ( subset-intersection-ideal-Commutative-Ringᵉ)
  pr1ᵉ
    ( is-closed-under-left-multiplication-intersection-ideal-Commutative-Ringᵉ
      xᵉ yᵉ (H1ᵉ ,ᵉ H2ᵉ)) =
    is-closed-under-left-multiplication-ideal-Commutative-Ringᵉ Rᵉ Iᵉ xᵉ yᵉ H1ᵉ
  pr2ᵉ
    ( is-closed-under-left-multiplication-intersection-ideal-Commutative-Ringᵉ
      xᵉ yᵉ (H1ᵉ ,ᵉ H2ᵉ)) =
    is-closed-under-left-multiplication-ideal-Commutative-Ringᵉ Rᵉ Jᵉ xᵉ yᵉ H2ᵉ

  intersection-ideal-Commutative-Ringᵉ : ideal-Commutative-Ringᵉ (l2ᵉ ⊔ l3ᵉ) Rᵉ
  intersection-ideal-Commutative-Ringᵉ =
    ideal-left-ideal-Commutative-Ringᵉ Rᵉ
      subset-intersection-ideal-Commutative-Ringᵉ
      contains-zero-intersection-ideal-Commutative-Ringᵉ
      is-closed-under-addition-intersection-ideal-Commutative-Ringᵉ
      is-closed-under-negatives-intersection-ideal-Commutative-Ringᵉ
      is-closed-under-left-multiplication-intersection-ideal-Commutative-Ringᵉ

  is-intersection-intersection-ideal-Commutative-Ringᵉ :
    is-intersection-ideal-Commutative-Ringᵉ Rᵉ Iᵉ Jᵉ
      ( intersection-ideal-Commutative-Ringᵉ)
  is-intersection-intersection-ideal-Commutative-Ringᵉ =
    is-intersection-intersection-ideal-Ringᵉ (ring-Commutative-Ringᵉ Rᵉ) Iᵉ Jᵉ
```