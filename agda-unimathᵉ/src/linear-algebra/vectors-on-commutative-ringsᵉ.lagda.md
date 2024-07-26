# Vectors on commutative rings

```agda
module linear-algebra.vectors-on-commutative-ringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-ringsᵉ

open import elementary-number-theory.natural-numbersᵉ

open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ

open import group-theory.commutative-monoidsᵉ
open import group-theory.monoidsᵉ
open import group-theory.semigroupsᵉ

open import linear-algebra.constant-vectorsᵉ
open import linear-algebra.vectors-on-ringsᵉ
```

</details>

## Idea

Vectorsᵉ onᵉ aᵉ commutativeᵉ ringᵉ `R`ᵉ areᵉ vectorsᵉ onᵉ theᵉ underlyingᵉ typeᵉ ofᵉ `R`.ᵉ Theᵉ
commutativeᵉ ringᵉ structureᵉ onᵉ `R`ᵉ inducesᵉ furtherᵉ structureᵉ onᵉ theᵉ typeᵉ ofᵉ
vectorsᵉ onᵉ `R`.ᵉ

## Definitions

### Listed vectors on commutative rings

```agda
module _
  {lᵉ : Level} (Rᵉ : Commutative-Ringᵉ lᵉ)
  where

  vec-Commutative-Ringᵉ : ℕᵉ → UUᵉ lᵉ
  vec-Commutative-Ringᵉ = vec-Ringᵉ (ring-Commutative-Ringᵉ Rᵉ)

  head-vec-Commutative-Ringᵉ :
    {nᵉ : ℕᵉ} → vec-Commutative-Ringᵉ (succ-ℕᵉ nᵉ) → type-Commutative-Ringᵉ Rᵉ
  head-vec-Commutative-Ringᵉ = head-vec-Ringᵉ (ring-Commutative-Ringᵉ Rᵉ)

  tail-vec-Commutative-Ringᵉ :
    {nᵉ : ℕᵉ} → vec-Commutative-Ringᵉ (succ-ℕᵉ nᵉ) → vec-Commutative-Ringᵉ nᵉ
  tail-vec-Commutative-Ringᵉ = tail-vec-Ringᵉ (ring-Commutative-Ringᵉ Rᵉ)

  snoc-vec-Commutative-Ringᵉ :
    {nᵉ : ℕᵉ} → vec-Commutative-Ringᵉ nᵉ → type-Commutative-Ringᵉ Rᵉ →
    vec-Commutative-Ringᵉ (succ-ℕᵉ nᵉ)
  snoc-vec-Commutative-Ringᵉ = snoc-vec-Ringᵉ (ring-Commutative-Ringᵉ Rᵉ)
```

### Functional vectors on commutative rings

```agda
module _
  {lᵉ : Level} (Rᵉ : Commutative-Ringᵉ lᵉ)
  where

  functional-vec-Commutative-Ringᵉ : ℕᵉ → UUᵉ lᵉ
  functional-vec-Commutative-Ringᵉ =
    functional-vec-Ringᵉ (ring-Commutative-Ringᵉ Rᵉ)

  head-functional-vec-Commutative-Ringᵉ :
    (nᵉ : ℕᵉ) → functional-vec-Commutative-Ringᵉ (succ-ℕᵉ nᵉ) →
    type-Commutative-Ringᵉ Rᵉ
  head-functional-vec-Commutative-Ringᵉ =
    head-functional-vec-Ringᵉ (ring-Commutative-Ringᵉ Rᵉ)

  tail-functional-vec-Commutative-Ringᵉ :
    (nᵉ : ℕᵉ) → functional-vec-Commutative-Ringᵉ (succ-ℕᵉ nᵉ) →
    functional-vec-Commutative-Ringᵉ nᵉ
  tail-functional-vec-Commutative-Ringᵉ =
    tail-functional-vec-Ringᵉ (ring-Commutative-Ringᵉ Rᵉ)

  cons-functional-vec-Commutative-Ringᵉ :
    (nᵉ : ℕᵉ) → type-Commutative-Ringᵉ Rᵉ →
    functional-vec-Commutative-Ringᵉ nᵉ →
    functional-vec-Commutative-Ringᵉ (succ-ℕᵉ nᵉ)
  cons-functional-vec-Commutative-Ringᵉ =
    cons-functional-vec-Ringᵉ (ring-Commutative-Ringᵉ Rᵉ)

  snoc-functional-vec-Commutative-Ringᵉ :
    (nᵉ : ℕᵉ) → functional-vec-Commutative-Ringᵉ nᵉ →
    type-Commutative-Ringᵉ Rᵉ → functional-vec-Commutative-Ringᵉ (succ-ℕᵉ nᵉ)
  snoc-functional-vec-Commutative-Ringᵉ =
    snoc-functional-vec-Ringᵉ (ring-Commutative-Ringᵉ Rᵉ)
```

### Zero vector on a commutative ring

#### The zero listed vector

```agda
module _
  {lᵉ : Level} (Rᵉ : Commutative-Ringᵉ lᵉ)
  where

  zero-vec-Commutative-Ringᵉ : {nᵉ : ℕᵉ} → vec-Commutative-Ringᵉ Rᵉ nᵉ
  zero-vec-Commutative-Ringᵉ = constant-vecᵉ (zero-Commutative-Ringᵉ Rᵉ)
```

#### The zero functional vector

```agda
module _
  {lᵉ : Level} (Rᵉ : Commutative-Ringᵉ lᵉ)
  where

  zero-functional-vec-Commutative-Ringᵉ :
    (nᵉ : ℕᵉ) → functional-vec-Commutative-Ringᵉ Rᵉ nᵉ
  zero-functional-vec-Commutative-Ringᵉ nᵉ iᵉ = zero-Commutative-Ringᵉ Rᵉ
```

### Pointwise addition of vectors on a commutative ring

#### Pointwise addition of listed vectors on a commutative ring

```agda
module _
  {lᵉ : Level} (Rᵉ : Commutative-Ringᵉ lᵉ)
  where

  add-vec-Commutative-Ringᵉ :
    {nᵉ : ℕᵉ} → vec-Commutative-Ringᵉ Rᵉ nᵉ → vec-Commutative-Ringᵉ Rᵉ nᵉ →
    vec-Commutative-Ringᵉ Rᵉ nᵉ
  add-vec-Commutative-Ringᵉ =
    add-vec-Ringᵉ (ring-Commutative-Ringᵉ Rᵉ)

  associative-add-vec-Commutative-Ringᵉ :
    {nᵉ : ℕᵉ} (v1ᵉ v2ᵉ v3ᵉ : vec-Commutative-Ringᵉ Rᵉ nᵉ) →
    add-vec-Commutative-Ringᵉ (add-vec-Commutative-Ringᵉ v1ᵉ v2ᵉ) v3ᵉ ＝ᵉ
    add-vec-Commutative-Ringᵉ v1ᵉ (add-vec-Commutative-Ringᵉ v2ᵉ v3ᵉ)
  associative-add-vec-Commutative-Ringᵉ =
    associative-add-vec-Ringᵉ (ring-Commutative-Ringᵉ Rᵉ)

  vec-Commutative-Ring-Semigroupᵉ : ℕᵉ → Semigroupᵉ lᵉ
  vec-Commutative-Ring-Semigroupᵉ =
    vec-Ring-Semigroupᵉ (ring-Commutative-Ringᵉ Rᵉ)

  left-unit-law-add-vec-Commutative-Ringᵉ :
    {nᵉ : ℕᵉ} (vᵉ : vec-Commutative-Ringᵉ Rᵉ nᵉ) →
    add-vec-Commutative-Ringᵉ (zero-vec-Commutative-Ringᵉ Rᵉ) vᵉ ＝ᵉ vᵉ
  left-unit-law-add-vec-Commutative-Ringᵉ =
    left-unit-law-add-vec-Ringᵉ (ring-Commutative-Ringᵉ Rᵉ)

  right-unit-law-add-vec-Commutative-Ringᵉ :
    {nᵉ : ℕᵉ} (vᵉ : vec-Commutative-Ringᵉ Rᵉ nᵉ) →
    add-vec-Commutative-Ringᵉ vᵉ (zero-vec-Commutative-Ringᵉ Rᵉ) ＝ᵉ vᵉ
  right-unit-law-add-vec-Commutative-Ringᵉ =
    right-unit-law-add-vec-Ringᵉ (ring-Commutative-Ringᵉ Rᵉ)

  vec-Commutative-Ring-Monoidᵉ : ℕᵉ → Monoidᵉ lᵉ
  vec-Commutative-Ring-Monoidᵉ =
    vec-Ring-Monoidᵉ (ring-Commutative-Ringᵉ Rᵉ)

  commutative-add-vec-Commutative-Ringᵉ :
    {nᵉ : ℕᵉ} (vᵉ wᵉ : vec-Commutative-Ringᵉ Rᵉ nᵉ) →
    add-vec-Commutative-Ringᵉ vᵉ wᵉ ＝ᵉ add-vec-Commutative-Ringᵉ wᵉ vᵉ
  commutative-add-vec-Commutative-Ringᵉ =
    commutative-add-vec-Ringᵉ (ring-Commutative-Ringᵉ Rᵉ)

  vec-Commutative-Ring-Commutative-Monoidᵉ : ℕᵉ → Commutative-Monoidᵉ lᵉ
  vec-Commutative-Ring-Commutative-Monoidᵉ =
    vec-Ring-Commutative-Monoidᵉ (ring-Commutative-Ringᵉ Rᵉ)
```

#### Pointwise addition of functional vectors on a commutative ring

```agda
module _
  {lᵉ : Level} (Rᵉ : Commutative-Ringᵉ lᵉ)
  where

  add-functional-vec-Commutative-Ringᵉ :
    (nᵉ : ℕᵉ) (vᵉ wᵉ : functional-vec-Commutative-Ringᵉ Rᵉ nᵉ) →
    functional-vec-Commutative-Ringᵉ Rᵉ nᵉ
  add-functional-vec-Commutative-Ringᵉ =
    add-functional-vec-Ringᵉ (ring-Commutative-Ringᵉ Rᵉ)

  associative-add-functional-vec-Commutative-Ringᵉ :
    (nᵉ : ℕᵉ) (v1ᵉ v2ᵉ v3ᵉ : functional-vec-Commutative-Ringᵉ Rᵉ nᵉ) →
    ( add-functional-vec-Commutative-Ringᵉ nᵉ
      ( add-functional-vec-Commutative-Ringᵉ nᵉ v1ᵉ v2ᵉ) v3ᵉ) ＝ᵉ
    ( add-functional-vec-Commutative-Ringᵉ nᵉ v1ᵉ
      ( add-functional-vec-Commutative-Ringᵉ nᵉ v2ᵉ v3ᵉ))
  associative-add-functional-vec-Commutative-Ringᵉ =
    associative-add-functional-vec-Ringᵉ (ring-Commutative-Ringᵉ Rᵉ)

  functional-vec-Commutative-Ring-Semigroupᵉ : ℕᵉ → Semigroupᵉ lᵉ
  functional-vec-Commutative-Ring-Semigroupᵉ =
    functional-vec-Ring-Semigroupᵉ (ring-Commutative-Ringᵉ Rᵉ)

  left-unit-law-add-functional-vec-Commutative-Ringᵉ :
    (nᵉ : ℕᵉ) (vᵉ : functional-vec-Commutative-Ringᵉ Rᵉ nᵉ) →
    add-functional-vec-Commutative-Ringᵉ nᵉ
      ( zero-functional-vec-Commutative-Ringᵉ Rᵉ nᵉ) vᵉ ＝ᵉ vᵉ
  left-unit-law-add-functional-vec-Commutative-Ringᵉ =
    left-unit-law-add-functional-vec-Ringᵉ (ring-Commutative-Ringᵉ Rᵉ)

  right-unit-law-add-functional-vec-Commutative-Ringᵉ :
    (nᵉ : ℕᵉ) (vᵉ : functional-vec-Commutative-Ringᵉ Rᵉ nᵉ) →
    add-functional-vec-Commutative-Ringᵉ nᵉ vᵉ
      ( zero-functional-vec-Commutative-Ringᵉ Rᵉ nᵉ) ＝ᵉ vᵉ
  right-unit-law-add-functional-vec-Commutative-Ringᵉ =
    right-unit-law-add-functional-vec-Ringᵉ (ring-Commutative-Ringᵉ Rᵉ)

  functional-vec-Commutative-Ring-Monoidᵉ : ℕᵉ → Monoidᵉ lᵉ
  functional-vec-Commutative-Ring-Monoidᵉ =
    functional-vec-Ring-Monoidᵉ (ring-Commutative-Ringᵉ Rᵉ)

  commutative-add-functional-vec-Commutative-Ringᵉ :
    (nᵉ : ℕᵉ) (vᵉ wᵉ : functional-vec-Commutative-Ringᵉ Rᵉ nᵉ) →
    add-functional-vec-Commutative-Ringᵉ nᵉ vᵉ wᵉ ＝ᵉ
    add-functional-vec-Commutative-Ringᵉ nᵉ wᵉ vᵉ
  commutative-add-functional-vec-Commutative-Ringᵉ =
    commutative-add-functional-vec-Ringᵉ (ring-Commutative-Ringᵉ Rᵉ)

  functional-vec-Commutative-Ring-Commutative-Monoidᵉ : ℕᵉ → Commutative-Monoidᵉ lᵉ
  functional-vec-Commutative-Ring-Commutative-Monoidᵉ =
    functional-vec-Ring-Commutative-Monoidᵉ (ring-Commutative-Ringᵉ Rᵉ)
```