# Full ideals of rings

```agda
module ring-theory.full-ideals-ringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.full-subtypesᵉ
open import foundation.propositionsᵉ
open import foundation.subtypesᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import order-theory.top-elements-large-posetsᵉ

open import ring-theory.ideals-ringsᵉ
open import ring-theory.left-ideals-ringsᵉ
open import ring-theory.poset-of-ideals-ringsᵉ
open import ring-theory.right-ideals-ringsᵉ
open import ring-theory.ringsᵉ
open import ring-theory.subsets-ringsᵉ
```

</details>

## Idea

Aᵉ **fullᵉ ideal**ᵉ in aᵉ [ring](ring-theory.rings.mdᵉ) `R`ᵉ isᵉ anᵉ
[ideal](ring-theory.ideals-rings.mdᵉ) thatᵉ containsᵉ everyᵉ elementᵉ ofᵉ `R`.ᵉ

## Definitions

### The predicate of being a full ideal

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ) (Iᵉ : ideal-Ringᵉ l2ᵉ Rᵉ)
  where

  is-full-ideal-Ring-Propᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  is-full-ideal-Ring-Propᵉ =
    Π-Propᵉ (type-Ringᵉ Rᵉ) (λ xᵉ → subset-ideal-Ringᵉ Rᵉ Iᵉ xᵉ)

  is-full-ideal-Ringᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-full-ideal-Ringᵉ = type-Propᵉ is-full-ideal-Ring-Propᵉ

  is-prop-is-full-ideal-Ringᵉ : is-propᵉ is-full-ideal-Ringᵉ
  is-prop-is-full-ideal-Ringᵉ =
    is-prop-type-Propᵉ is-full-ideal-Ring-Propᵉ
```

### The (standard) full ideal

```agda
module _
  {l1ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ)
  where

  subset-full-ideal-Ringᵉ : subset-Ringᵉ lzero Rᵉ
  subset-full-ideal-Ringᵉ = full-subtypeᵉ lzero (type-Ringᵉ Rᵉ)

  is-in-full-ideal-Ringᵉ : type-Ringᵉ Rᵉ → UUᵉ lzero
  is-in-full-ideal-Ringᵉ = is-in-subtypeᵉ subset-full-ideal-Ringᵉ

  contains-zero-full-ideal-Ringᵉ :
    contains-zero-subset-Ringᵉ Rᵉ subset-full-ideal-Ringᵉ
  contains-zero-full-ideal-Ringᵉ = raise-starᵉ

  is-closed-under-addition-full-ideal-Ringᵉ :
    is-closed-under-addition-subset-Ringᵉ Rᵉ subset-full-ideal-Ringᵉ
  is-closed-under-addition-full-ideal-Ringᵉ Hᵉ Kᵉ = raise-starᵉ

  is-closed-under-negatives-full-ideal-Ringᵉ :
    is-closed-under-negatives-subset-Ringᵉ Rᵉ subset-full-ideal-Ringᵉ
  is-closed-under-negatives-full-ideal-Ringᵉ Hᵉ = raise-starᵉ

  is-additive-subgroup-full-ideal-Ringᵉ :
    is-additive-subgroup-subset-Ringᵉ Rᵉ subset-full-ideal-Ringᵉ
  pr1ᵉ is-additive-subgroup-full-ideal-Ringᵉ =
    contains-zero-full-ideal-Ringᵉ
  pr1ᵉ (pr2ᵉ is-additive-subgroup-full-ideal-Ringᵉ) {xᵉ} {yᵉ} =
    is-closed-under-addition-full-ideal-Ringᵉ {xᵉ} {yᵉ}
  pr2ᵉ (pr2ᵉ is-additive-subgroup-full-ideal-Ringᵉ) {xᵉ} =
    is-closed-under-negatives-full-ideal-Ringᵉ {xᵉ}

  is-closed-under-left-multiplication-full-ideal-Ringᵉ :
    is-closed-under-left-multiplication-subset-Ringᵉ Rᵉ subset-full-ideal-Ringᵉ
  is-closed-under-left-multiplication-full-ideal-Ringᵉ xᵉ yᵉ Hᵉ = raise-starᵉ

  is-closed-under-right-multiplication-full-ideal-Ringᵉ :
    is-closed-under-right-multiplication-subset-Ringᵉ Rᵉ subset-full-ideal-Ringᵉ
  is-closed-under-right-multiplication-full-ideal-Ringᵉ xᵉ yᵉ Hᵉ = raise-starᵉ

  is-left-ideal-full-ideal-Ringᵉ :
    is-left-ideal-subset-Ringᵉ Rᵉ subset-full-ideal-Ringᵉ
  pr1ᵉ is-left-ideal-full-ideal-Ringᵉ =
    is-additive-subgroup-full-ideal-Ringᵉ
  pr2ᵉ is-left-ideal-full-ideal-Ringᵉ =
    is-closed-under-left-multiplication-full-ideal-Ringᵉ

  full-left-ideal-Ringᵉ : left-ideal-Ringᵉ lzero Rᵉ
  pr1ᵉ full-left-ideal-Ringᵉ = subset-full-ideal-Ringᵉ
  pr2ᵉ full-left-ideal-Ringᵉ = is-left-ideal-full-ideal-Ringᵉ

  is-right-ideal-full-ideal-Ringᵉ :
    is-right-ideal-subset-Ringᵉ Rᵉ subset-full-ideal-Ringᵉ
  pr1ᵉ is-right-ideal-full-ideal-Ringᵉ =
    is-additive-subgroup-full-ideal-Ringᵉ
  pr2ᵉ is-right-ideal-full-ideal-Ringᵉ =
    is-closed-under-right-multiplication-full-ideal-Ringᵉ

  full-right-ideal-Ringᵉ : right-ideal-Ringᵉ lzero Rᵉ
  pr1ᵉ full-right-ideal-Ringᵉ = subset-full-ideal-Ringᵉ
  pr2ᵉ full-right-ideal-Ringᵉ = is-right-ideal-full-ideal-Ringᵉ

  is-ideal-full-ideal-Ringᵉ : is-ideal-subset-Ringᵉ Rᵉ subset-full-ideal-Ringᵉ
  pr1ᵉ is-ideal-full-ideal-Ringᵉ =
    is-additive-subgroup-full-ideal-Ringᵉ
  pr1ᵉ (pr2ᵉ is-ideal-full-ideal-Ringᵉ) =
    is-closed-under-left-multiplication-full-ideal-Ringᵉ
  pr2ᵉ (pr2ᵉ is-ideal-full-ideal-Ringᵉ) =
    is-closed-under-right-multiplication-full-ideal-Ringᵉ

  full-ideal-Ringᵉ : ideal-Ringᵉ lzero Rᵉ
  pr1ᵉ full-ideal-Ringᵉ = subset-full-ideal-Ringᵉ
  pr2ᵉ full-ideal-Ringᵉ = is-ideal-full-ideal-Ringᵉ

  is-full-full-ideal-Ringᵉ : is-full-ideal-Ringᵉ Rᵉ full-ideal-Ringᵉ
  is-full-full-ideal-Ringᵉ xᵉ = raise-starᵉ
```

## Properties

### Any ideal is full if and only if it contains `1`

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ) (Iᵉ : ideal-Ringᵉ l2ᵉ Rᵉ)
  where

  is-full-contains-one-ideal-Ringᵉ :
    is-in-ideal-Ringᵉ Rᵉ Iᵉ (one-Ringᵉ Rᵉ) → is-full-ideal-Ringᵉ Rᵉ Iᵉ
  is-full-contains-one-ideal-Ringᵉ Hᵉ xᵉ =
    is-closed-under-eq-ideal-Ringᵉ Rᵉ Iᵉ
      ( is-closed-under-left-multiplication-ideal-Ringᵉ Rᵉ Iᵉ xᵉ (one-Ringᵉ Rᵉ) Hᵉ)
      ( right-unit-law-mul-Ringᵉ Rᵉ xᵉ)

  contains-one-is-full-ideal-Ringᵉ :
    is-full-ideal-Ringᵉ Rᵉ Iᵉ → is-in-ideal-Ringᵉ Rᵉ Iᵉ (one-Ringᵉ Rᵉ)
  contains-one-is-full-ideal-Ringᵉ Hᵉ = Hᵉ (one-Ringᵉ Rᵉ)
```

### Any ideal is full if and only if it is a top element in the large poset of ideals

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ) (Iᵉ : ideal-Ringᵉ l2ᵉ Rᵉ)
  where

  is-full-is-top-element-ideal-Ringᵉ :
    is-top-element-Large-Posetᵉ (ideal-Ring-Large-Posetᵉ Rᵉ) Iᵉ →
    is-full-ideal-Ringᵉ Rᵉ Iᵉ
  is-full-is-top-element-ideal-Ringᵉ Hᵉ xᵉ =
    Hᵉ (full-ideal-Ringᵉ Rᵉ) xᵉ (is-full-full-ideal-Ringᵉ Rᵉ xᵉ)

  is-top-element-is-full-ideal-Ringᵉ :
    is-full-ideal-Ringᵉ Rᵉ Iᵉ →
    is-top-element-Large-Posetᵉ (ideal-Ring-Large-Posetᵉ Rᵉ) Iᵉ
  is-top-element-is-full-ideal-Ringᵉ Hᵉ Iᵉ xᵉ Kᵉ = Hᵉ xᵉ

module _
  {l1ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ)
  where

  is-top-element-full-ideal-Ringᵉ :
    is-top-element-Large-Posetᵉ (ideal-Ring-Large-Posetᵉ Rᵉ) (full-ideal-Ringᵉ Rᵉ)
  is-top-element-full-ideal-Ringᵉ =
    is-top-element-is-full-ideal-Ringᵉ Rᵉ
      ( full-ideal-Ringᵉ Rᵉ)
      ( is-full-full-ideal-Ringᵉ Rᵉ)

  has-top-element-ideal-Ringᵉ :
    has-top-element-Large-Posetᵉ (ideal-Ring-Large-Posetᵉ Rᵉ)
  top-has-top-element-Large-Posetᵉ
    has-top-element-ideal-Ringᵉ =
    full-ideal-Ringᵉ Rᵉ
  is-top-element-top-has-top-element-Large-Posetᵉ
    has-top-element-ideal-Ringᵉ =
    is-top-element-full-ideal-Ringᵉ
```