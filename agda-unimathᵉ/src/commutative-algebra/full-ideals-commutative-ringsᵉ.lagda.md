# Full ideals of commutative rings

```agda
module commutative-algebra.full-ideals-commutative-ringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-ringsᵉ
open import commutative-algebra.ideals-commutative-ringsᵉ
open import commutative-algebra.poset-of-ideals-commutative-ringsᵉ
open import commutative-algebra.poset-of-radical-ideals-commutative-ringsᵉ
open import commutative-algebra.radical-ideals-commutative-ringsᵉ
open import commutative-algebra.subsets-commutative-ringsᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.propositionsᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import order-theory.top-elements-large-posetsᵉ

open import ring-theory.full-ideals-ringsᵉ
```

</details>

## Idea

Aᵉ **fullᵉ ideal**ᵉ in aᵉ
[commutativeᵉ ring](commutative-algebra.commutative-rings.mdᵉ) `A`ᵉ isᵉ anᵉ
[ideal](commutative-algebra.ideals-commutative-rings.mdᵉ) thatᵉ containsᵉ everyᵉ
elementᵉ ofᵉ `A`.ᵉ

## Definitions

### The predicate of being a full ideal

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Commutative-Ringᵉ l1ᵉ) (Iᵉ : ideal-Commutative-Ringᵉ l2ᵉ Aᵉ)
  where

  is-full-ideal-Commutative-Ring-Propᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  is-full-ideal-Commutative-Ring-Propᵉ =
    is-full-ideal-Ring-Propᵉ (ring-Commutative-Ringᵉ Aᵉ) Iᵉ

  is-full-ideal-Commutative-Ringᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-full-ideal-Commutative-Ringᵉ =
    is-full-ideal-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ) Iᵉ

  is-prop-is-full-ideal-Commutative-Ringᵉ :
    is-propᵉ is-full-ideal-Commutative-Ringᵉ
  is-prop-is-full-ideal-Commutative-Ringᵉ =
    is-prop-is-full-ideal-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ) Iᵉ
```

### The (standard) full ideal

```agda
module _
  {l1ᵉ : Level} (Aᵉ : Commutative-Ringᵉ l1ᵉ)
  where

  subset-full-ideal-Commutative-Ringᵉ : subset-Commutative-Ringᵉ lzero Aᵉ
  subset-full-ideal-Commutative-Ringᵉ =
    subset-full-ideal-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)

  is-in-full-ideal-Commutative-Ringᵉ : type-Commutative-Ringᵉ Aᵉ → UUᵉ lzero
  is-in-full-ideal-Commutative-Ringᵉ =
    is-in-full-ideal-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)

  contains-zero-full-ideal-Commutative-Ringᵉ :
    contains-zero-subset-Commutative-Ringᵉ Aᵉ subset-full-ideal-Commutative-Ringᵉ
  contains-zero-full-ideal-Commutative-Ringᵉ =
    contains-zero-full-ideal-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)

  is-closed-under-addition-full-ideal-Commutative-Ringᵉ :
    is-closed-under-addition-subset-Commutative-Ringᵉ Aᵉ
      subset-full-ideal-Commutative-Ringᵉ
  is-closed-under-addition-full-ideal-Commutative-Ringᵉ {xᵉ} {yᵉ} =
    is-closed-under-addition-full-ideal-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ) {xᵉ} {yᵉ}

  is-closed-under-negatives-full-ideal-Commutative-Ringᵉ :
    is-closed-under-negatives-subset-Commutative-Ringᵉ Aᵉ
      subset-full-ideal-Commutative-Ringᵉ
  is-closed-under-negatives-full-ideal-Commutative-Ringᵉ {xᵉ} =
    is-closed-under-negatives-full-ideal-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ) {xᵉ}

  is-additive-subgroup-full-ideal-Commutative-Ringᵉ :
    is-additive-subgroup-subset-Commutative-Ringᵉ Aᵉ
      subset-full-ideal-Commutative-Ringᵉ
  is-additive-subgroup-full-ideal-Commutative-Ringᵉ =
    is-additive-subgroup-full-ideal-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)

  is-closed-under-left-multiplication-full-ideal-Commutative-Ringᵉ :
    is-closed-under-left-multiplication-subset-Commutative-Ringᵉ Aᵉ
      subset-full-ideal-Commutative-Ringᵉ
  is-closed-under-left-multiplication-full-ideal-Commutative-Ringᵉ =
    is-closed-under-left-multiplication-full-ideal-Ringᵉ
      ( ring-Commutative-Ringᵉ Aᵉ)

  is-closed-under-right-multiplication-full-ideal-Commutative-Ringᵉ :
    is-closed-under-right-multiplication-subset-Commutative-Ringᵉ Aᵉ
      subset-full-ideal-Commutative-Ringᵉ
  is-closed-under-right-multiplication-full-ideal-Commutative-Ringᵉ =
    is-closed-under-right-multiplication-full-ideal-Ringᵉ
      ( ring-Commutative-Ringᵉ Aᵉ)

  is-left-ideal-full-ideal-Commutative-Ringᵉ :
    is-left-ideal-subset-Commutative-Ringᵉ Aᵉ subset-full-ideal-Commutative-Ringᵉ
  is-left-ideal-full-ideal-Commutative-Ringᵉ =
    is-left-ideal-full-ideal-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)

  full-left-ideal-Commutative-Ringᵉ : left-ideal-Commutative-Ringᵉ lzero Aᵉ
  full-left-ideal-Commutative-Ringᵉ =
    full-left-ideal-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)

  is-right-ideal-full-ideal-Commutative-Ringᵉ :
    is-right-ideal-subset-Commutative-Ringᵉ Aᵉ subset-full-ideal-Commutative-Ringᵉ
  is-right-ideal-full-ideal-Commutative-Ringᵉ =
    is-right-ideal-full-ideal-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)

  full-right-ideal-Commutative-Ringᵉ : right-ideal-Commutative-Ringᵉ lzero Aᵉ
  full-right-ideal-Commutative-Ringᵉ =
    full-right-ideal-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)

  is-ideal-full-ideal-Commutative-Ringᵉ :
    is-ideal-subset-Commutative-Ringᵉ Aᵉ subset-full-ideal-Commutative-Ringᵉ
  is-ideal-full-ideal-Commutative-Ringᵉ =
    is-ideal-full-ideal-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)

  full-ideal-Commutative-Ringᵉ : ideal-Commutative-Ringᵉ lzero Aᵉ
  full-ideal-Commutative-Ringᵉ = full-ideal-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)

  is-full-full-ideal-Commutative-Ringᵉ :
    is-full-ideal-Commutative-Ringᵉ Aᵉ full-ideal-Commutative-Ringᵉ
  is-full-full-ideal-Commutative-Ringᵉ =
    is-full-full-ideal-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)
```

## Properties

### Any ideal is full if and only if it contains `1`

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Commutative-Ringᵉ l1ᵉ) (Iᵉ : ideal-Commutative-Ringᵉ l2ᵉ Aᵉ)
  where

  is-full-contains-one-ideal-Commutative-Ringᵉ :
    is-in-ideal-Commutative-Ringᵉ Aᵉ Iᵉ (one-Commutative-Ringᵉ Aᵉ) →
    is-full-ideal-Commutative-Ringᵉ Aᵉ Iᵉ
  is-full-contains-one-ideal-Commutative-Ringᵉ =
    is-full-contains-one-ideal-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ) Iᵉ

  contains-one-is-full-ideal-Commutative-Ringᵉ :
    is-full-ideal-Commutative-Ringᵉ Aᵉ Iᵉ →
    is-in-ideal-Commutative-Ringᵉ Aᵉ Iᵉ (one-Commutative-Ringᵉ Aᵉ)
  contains-one-is-full-ideal-Commutative-Ringᵉ =
    contains-one-is-full-ideal-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ) Iᵉ
```

### Any ideal is full if and only if it is a top element in the large poset of ideals

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Commutative-Ringᵉ l1ᵉ) (Iᵉ : ideal-Commutative-Ringᵉ l2ᵉ Aᵉ)
  where

  is-full-is-top-element-ideal-Commutative-Ringᵉ :
    is-top-element-Large-Posetᵉ (ideal-Commutative-Ring-Large-Posetᵉ Aᵉ) Iᵉ →
    is-full-ideal-Commutative-Ringᵉ Aᵉ Iᵉ
  is-full-is-top-element-ideal-Commutative-Ringᵉ =
    is-full-is-top-element-ideal-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ) Iᵉ

  is-top-element-is-full-ideal-Commutative-Ringᵉ :
    is-full-ideal-Commutative-Ringᵉ Aᵉ Iᵉ →
    is-top-element-Large-Posetᵉ (ideal-Commutative-Ring-Large-Posetᵉ Aᵉ) Iᵉ
  is-top-element-is-full-ideal-Commutative-Ringᵉ =
    is-top-element-is-full-ideal-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ) Iᵉ

module _
  {l1ᵉ : Level} (Aᵉ : Commutative-Ringᵉ l1ᵉ)
  where

  is-top-element-full-ideal-Commutative-Ringᵉ :
    is-top-element-Large-Posetᵉ
      ( ideal-Commutative-Ring-Large-Posetᵉ Aᵉ)
      ( full-ideal-Commutative-Ringᵉ Aᵉ)
  is-top-element-full-ideal-Commutative-Ringᵉ =
    is-top-element-full-ideal-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)

  has-top-element-ideal-Commutative-Ringᵉ :
    has-top-element-Large-Posetᵉ (ideal-Commutative-Ring-Large-Posetᵉ Aᵉ)
  has-top-element-ideal-Commutative-Ringᵉ =
    has-top-element-ideal-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)
```

### The full ideal of a commutative ring is radical

```agda
module _
  {l1ᵉ : Level} (Aᵉ : Commutative-Ringᵉ l1ᵉ)
  where

  is-radical-full-ideal-Commutative-Ringᵉ :
    is-radical-ideal-Commutative-Ringᵉ Aᵉ (full-ideal-Commutative-Ringᵉ Aᵉ)
  is-radical-full-ideal-Commutative-Ringᵉ xᵉ nᵉ Hᵉ = raise-starᵉ

  full-radical-ideal-Commutative-Ringᵉ : radical-ideal-Commutative-Ringᵉ lzero Aᵉ
  pr1ᵉ full-radical-ideal-Commutative-Ringᵉ =
    full-ideal-Commutative-Ringᵉ Aᵉ
  pr2ᵉ full-radical-ideal-Commutative-Ringᵉ =
    is-radical-full-ideal-Commutative-Ringᵉ

  is-top-element-full-radical-ideal-Commutative-Ringᵉ :
    is-top-element-Large-Posetᵉ
      ( radical-ideal-Commutative-Ring-Large-Posetᵉ Aᵉ)
      ( full-radical-ideal-Commutative-Ringᵉ)
  is-top-element-full-radical-ideal-Commutative-Ringᵉ Iᵉ =
    is-top-element-full-ideal-Commutative-Ringᵉ Aᵉ
      ( ideal-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ)

  has-top-element-radical-ideal-Commutative-Ringᵉ :
    has-top-element-Large-Posetᵉ
      ( radical-ideal-Commutative-Ring-Large-Posetᵉ Aᵉ)
  top-has-top-element-Large-Posetᵉ
    has-top-element-radical-ideal-Commutative-Ringᵉ =
    full-radical-ideal-Commutative-Ringᵉ
  is-top-element-top-has-top-element-Large-Posetᵉ
    has-top-element-radical-ideal-Commutative-Ringᵉ =
    is-top-element-full-radical-ideal-Commutative-Ringᵉ
```