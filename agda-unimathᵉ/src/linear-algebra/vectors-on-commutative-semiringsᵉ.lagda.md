# Vectors on commutative semirings

```agda
module linear-algebra.vectors-on-commutative-semiringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-semiringsᵉ

open import elementary-number-theory.natural-numbersᵉ

open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ

open import group-theory.commutative-monoidsᵉ
open import group-theory.monoidsᵉ
open import group-theory.semigroupsᵉ

open import linear-algebra.constant-vectorsᵉ
open import linear-algebra.vectors-on-semiringsᵉ
```

</details>

## Idea

Vectorsᵉ onᵉ aᵉ commutativeᵉ semiringᵉ `R`ᵉ areᵉ vectorsᵉ onᵉ theᵉ underlyingᵉ typeᵉ ofᵉ `R`.ᵉ
Theᵉ commutativeᵉ semiringᵉ structureᵉ onᵉ `R`ᵉ inducesᵉ furtherᵉ structureᵉ onᵉ theᵉ typeᵉ
ofᵉ vectorsᵉ onᵉ `R`.ᵉ

## Definitions

### Listed vectors on commutative semirings

```agda
module _
  {lᵉ : Level} (Rᵉ : Commutative-Semiringᵉ lᵉ)
  where

  vec-Commutative-Semiringᵉ : ℕᵉ → UUᵉ lᵉ
  vec-Commutative-Semiringᵉ =
    vec-Semiringᵉ (semiring-Commutative-Semiringᵉ Rᵉ)

  head-vec-Commutative-Semiringᵉ :
    {nᵉ : ℕᵉ} → vec-Commutative-Semiringᵉ (succ-ℕᵉ nᵉ) → type-Commutative-Semiringᵉ Rᵉ
  head-vec-Commutative-Semiringᵉ =
    head-vec-Semiringᵉ (semiring-Commutative-Semiringᵉ Rᵉ)

  tail-vec-Commutative-Semiringᵉ :
    {nᵉ : ℕᵉ} → vec-Commutative-Semiringᵉ (succ-ℕᵉ nᵉ) → vec-Commutative-Semiringᵉ nᵉ
  tail-vec-Commutative-Semiringᵉ =
    tail-vec-Semiringᵉ (semiring-Commutative-Semiringᵉ Rᵉ)

  snoc-vec-Commutative-Semiringᵉ :
    {nᵉ : ℕᵉ} → vec-Commutative-Semiringᵉ nᵉ → type-Commutative-Semiringᵉ Rᵉ →
    vec-Commutative-Semiringᵉ (succ-ℕᵉ nᵉ)
  snoc-vec-Commutative-Semiringᵉ =
    snoc-vec-Semiringᵉ (semiring-Commutative-Semiringᵉ Rᵉ)
```

### Functional vectors on commutative semirings

```agda
module _
  {lᵉ : Level} (Rᵉ : Commutative-Semiringᵉ lᵉ)
  where

  functional-vec-Commutative-Semiringᵉ : ℕᵉ → UUᵉ lᵉ
  functional-vec-Commutative-Semiringᵉ =
    functional-vec-Semiringᵉ (semiring-Commutative-Semiringᵉ Rᵉ)

  head-functional-vec-Commutative-Semiringᵉ :
    (nᵉ : ℕᵉ) → functional-vec-Commutative-Semiringᵉ (succ-ℕᵉ nᵉ) →
    type-Commutative-Semiringᵉ Rᵉ
  head-functional-vec-Commutative-Semiringᵉ =
    head-functional-vec-Semiringᵉ (semiring-Commutative-Semiringᵉ Rᵉ)

  tail-functional-vec-Commutative-Semiringᵉ :
    (nᵉ : ℕᵉ) → functional-vec-Commutative-Semiringᵉ (succ-ℕᵉ nᵉ) →
    functional-vec-Commutative-Semiringᵉ nᵉ
  tail-functional-vec-Commutative-Semiringᵉ =
    tail-functional-vec-Semiringᵉ (semiring-Commutative-Semiringᵉ Rᵉ)

  cons-functional-vec-Commutative-Semiringᵉ :
    (nᵉ : ℕᵉ) → type-Commutative-Semiringᵉ Rᵉ →
    functional-vec-Commutative-Semiringᵉ nᵉ →
    functional-vec-Commutative-Semiringᵉ (succ-ℕᵉ nᵉ)
  cons-functional-vec-Commutative-Semiringᵉ =
    cons-functional-vec-Semiringᵉ (semiring-Commutative-Semiringᵉ Rᵉ)

  snoc-functional-vec-Commutative-Semiringᵉ :
    (nᵉ : ℕᵉ) → functional-vec-Commutative-Semiringᵉ nᵉ →
    type-Commutative-Semiringᵉ Rᵉ → functional-vec-Commutative-Semiringᵉ (succ-ℕᵉ nᵉ)
  snoc-functional-vec-Commutative-Semiringᵉ =
    snoc-functional-vec-Semiringᵉ (semiring-Commutative-Semiringᵉ Rᵉ)
```

### Zero vector on a commutative semiring

#### The zero listed vector

```agda
module _
  {lᵉ : Level} (Rᵉ : Commutative-Semiringᵉ lᵉ)
  where

  zero-vec-Commutative-Semiringᵉ : {nᵉ : ℕᵉ} → vec-Commutative-Semiringᵉ Rᵉ nᵉ
  zero-vec-Commutative-Semiringᵉ = constant-vecᵉ (zero-Commutative-Semiringᵉ Rᵉ)
```

#### The zero functional vector

```agda
module _
  {lᵉ : Level} (Rᵉ : Commutative-Semiringᵉ lᵉ)
  where

  zero-functional-vec-Commutative-Semiringᵉ :
    (nᵉ : ℕᵉ) → functional-vec-Commutative-Semiringᵉ Rᵉ nᵉ
  zero-functional-vec-Commutative-Semiringᵉ nᵉ iᵉ = zero-Commutative-Semiringᵉ Rᵉ
```

### Pointwise addition of vectors on a commutative semiring

#### Pointwise addition of listed vectors on a commutative semiring

```agda
module _
  {lᵉ : Level} (Rᵉ : Commutative-Semiringᵉ lᵉ)
  where

  add-vec-Commutative-Semiringᵉ :
    {nᵉ : ℕᵉ} → vec-Commutative-Semiringᵉ Rᵉ nᵉ → vec-Commutative-Semiringᵉ Rᵉ nᵉ →
    vec-Commutative-Semiringᵉ Rᵉ nᵉ
  add-vec-Commutative-Semiringᵉ =
    add-vec-Semiringᵉ (semiring-Commutative-Semiringᵉ Rᵉ)

  associative-add-vec-Commutative-Semiringᵉ :
    {nᵉ : ℕᵉ} (v1ᵉ v2ᵉ v3ᵉ : vec-Commutative-Semiringᵉ Rᵉ nᵉ) →
    add-vec-Commutative-Semiringᵉ (add-vec-Commutative-Semiringᵉ v1ᵉ v2ᵉ) v3ᵉ ＝ᵉ
    add-vec-Commutative-Semiringᵉ v1ᵉ (add-vec-Commutative-Semiringᵉ v2ᵉ v3ᵉ)
  associative-add-vec-Commutative-Semiringᵉ =
    associative-add-vec-Semiringᵉ (semiring-Commutative-Semiringᵉ Rᵉ)

  vec-Commutative-Semiring-Semigroupᵉ : ℕᵉ → Semigroupᵉ lᵉ
  vec-Commutative-Semiring-Semigroupᵉ =
    vec-Semiring-Semigroupᵉ (semiring-Commutative-Semiringᵉ Rᵉ)

  left-unit-law-add-vec-Commutative-Semiringᵉ :
    {nᵉ : ℕᵉ} (vᵉ : vec-Commutative-Semiringᵉ Rᵉ nᵉ) →
    add-vec-Commutative-Semiringᵉ (zero-vec-Commutative-Semiringᵉ Rᵉ) vᵉ ＝ᵉ vᵉ
  left-unit-law-add-vec-Commutative-Semiringᵉ =
    left-unit-law-add-vec-Semiringᵉ (semiring-Commutative-Semiringᵉ Rᵉ)

  right-unit-law-add-vec-Commutative-Semiringᵉ :
    {nᵉ : ℕᵉ} (vᵉ : vec-Commutative-Semiringᵉ Rᵉ nᵉ) →
    add-vec-Commutative-Semiringᵉ vᵉ (zero-vec-Commutative-Semiringᵉ Rᵉ) ＝ᵉ vᵉ
  right-unit-law-add-vec-Commutative-Semiringᵉ =
    right-unit-law-add-vec-Semiringᵉ (semiring-Commutative-Semiringᵉ Rᵉ)

  vec-Commutative-Semiring-Monoidᵉ : ℕᵉ → Monoidᵉ lᵉ
  vec-Commutative-Semiring-Monoidᵉ =
    vec-Semiring-Monoidᵉ (semiring-Commutative-Semiringᵉ Rᵉ)

  commutative-add-vec-Commutative-Semiringᵉ :
    {nᵉ : ℕᵉ} (vᵉ wᵉ : vec-Commutative-Semiringᵉ Rᵉ nᵉ) →
    add-vec-Commutative-Semiringᵉ vᵉ wᵉ ＝ᵉ add-vec-Commutative-Semiringᵉ wᵉ vᵉ
  commutative-add-vec-Commutative-Semiringᵉ =
    commutative-add-vec-Semiringᵉ (semiring-Commutative-Semiringᵉ Rᵉ)

  vec-Commutative-Semiring-Commutative-Monoidᵉ : ℕᵉ → Commutative-Monoidᵉ lᵉ
  vec-Commutative-Semiring-Commutative-Monoidᵉ =
    vec-Semiring-Commutative-Monoidᵉ (semiring-Commutative-Semiringᵉ Rᵉ)
```

#### Pointwise addition of functional vectors on a commutative semiring

```agda
module _
  {lᵉ : Level} (Rᵉ : Commutative-Semiringᵉ lᵉ)
  where

  add-functional-vec-Commutative-Semiringᵉ :
    (nᵉ : ℕᵉ) (vᵉ wᵉ : functional-vec-Commutative-Semiringᵉ Rᵉ nᵉ) →
    functional-vec-Commutative-Semiringᵉ Rᵉ nᵉ
  add-functional-vec-Commutative-Semiringᵉ =
    add-functional-vec-Semiringᵉ (semiring-Commutative-Semiringᵉ Rᵉ)

  associative-add-functional-vec-Commutative-Semiringᵉ :
    (nᵉ : ℕᵉ) (v1ᵉ v2ᵉ v3ᵉ : functional-vec-Commutative-Semiringᵉ Rᵉ nᵉ) →
    ( add-functional-vec-Commutative-Semiringᵉ nᵉ
      ( add-functional-vec-Commutative-Semiringᵉ nᵉ v1ᵉ v2ᵉ) v3ᵉ) ＝ᵉ
    ( add-functional-vec-Commutative-Semiringᵉ nᵉ v1ᵉ
      ( add-functional-vec-Commutative-Semiringᵉ nᵉ v2ᵉ v3ᵉ))
  associative-add-functional-vec-Commutative-Semiringᵉ =
    associative-add-functional-vec-Semiringᵉ (semiring-Commutative-Semiringᵉ Rᵉ)

  functional-vec-Commutative-Semiring-Semigroupᵉ : ℕᵉ → Semigroupᵉ lᵉ
  functional-vec-Commutative-Semiring-Semigroupᵉ =
    functional-vec-Semiring-Semigroupᵉ (semiring-Commutative-Semiringᵉ Rᵉ)

  left-unit-law-add-functional-vec-Commutative-Semiringᵉ :
    (nᵉ : ℕᵉ) (vᵉ : functional-vec-Commutative-Semiringᵉ Rᵉ nᵉ) →
    add-functional-vec-Commutative-Semiringᵉ nᵉ
      ( zero-functional-vec-Commutative-Semiringᵉ Rᵉ nᵉ) vᵉ ＝ᵉ vᵉ
  left-unit-law-add-functional-vec-Commutative-Semiringᵉ =
    left-unit-law-add-functional-vec-Semiringᵉ (semiring-Commutative-Semiringᵉ Rᵉ)

  right-unit-law-add-functional-vec-Commutative-Semiringᵉ :
    (nᵉ : ℕᵉ) (vᵉ : functional-vec-Commutative-Semiringᵉ Rᵉ nᵉ) →
    add-functional-vec-Commutative-Semiringᵉ nᵉ vᵉ
      ( zero-functional-vec-Commutative-Semiringᵉ Rᵉ nᵉ) ＝ᵉ vᵉ
  right-unit-law-add-functional-vec-Commutative-Semiringᵉ =
    right-unit-law-add-functional-vec-Semiringᵉ (semiring-Commutative-Semiringᵉ Rᵉ)

  functional-vec-Commutative-Semiring-Monoidᵉ : ℕᵉ → Monoidᵉ lᵉ
  functional-vec-Commutative-Semiring-Monoidᵉ =
    functional-vec-Semiring-Monoidᵉ (semiring-Commutative-Semiringᵉ Rᵉ)

  commutative-add-functional-vec-Commutative-Semiringᵉ :
    (nᵉ : ℕᵉ) (vᵉ wᵉ : functional-vec-Commutative-Semiringᵉ Rᵉ nᵉ) →
    add-functional-vec-Commutative-Semiringᵉ nᵉ vᵉ wᵉ ＝ᵉ
    add-functional-vec-Commutative-Semiringᵉ nᵉ wᵉ vᵉ
  commutative-add-functional-vec-Commutative-Semiringᵉ =
    commutative-add-functional-vec-Semiringᵉ (semiring-Commutative-Semiringᵉ Rᵉ)

  functional-vec-Commutative-Semiring-Commutative-Monoidᵉ :
    ℕᵉ → Commutative-Monoidᵉ lᵉ
  functional-vec-Commutative-Semiring-Commutative-Monoidᵉ =
    functional-vec-Semiring-Commutative-Monoidᵉ (semiring-Commutative-Semiringᵉ Rᵉ)
```