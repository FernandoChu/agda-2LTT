# Sums of elements in rings

```agda
module ring-theory.sums-ringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ

open import foundation.function-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ

open import linear-algebra.vectorsᵉ
open import linear-algebra.vectors-on-ringsᵉ

open import ring-theory.ringsᵉ
open import ring-theory.sums-semiringsᵉ

open import univalent-combinatorics.coproduct-typesᵉ
open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Theᵉ sumᵉ operationᵉ extendsᵉ theᵉ binaryᵉ additionᵉ operationᵉ onᵉ aᵉ ringᵉ `R`ᵉ to anyᵉ
familyᵉ ofᵉ elementsᵉ ofᵉ `R`ᵉ indexedᵉ byᵉ aᵉ standardᵉ finiteᵉ type.ᵉ

## Definition

```agda
sum-Ringᵉ :
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ) (nᵉ : ℕᵉ) → functional-vec-Ringᵉ Rᵉ nᵉ → type-Ringᵉ Rᵉ
sum-Ringᵉ Rᵉ = sum-Semiringᵉ (semiring-Ringᵉ Rᵉ)
```

## Properties

### Sums of one and two elements

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  sum-one-element-Ringᵉ :
    (fᵉ : functional-vec-Ringᵉ Rᵉ 1ᵉ) → sum-Ringᵉ Rᵉ 1 fᵉ ＝ᵉ head-functional-vecᵉ 0 fᵉ
  sum-one-element-Ringᵉ = sum-one-element-Semiringᵉ (semiring-Ringᵉ Rᵉ)

  sum-two-elements-Ringᵉ :
    (fᵉ : functional-vec-Ringᵉ Rᵉ 2ᵉ) →
    sum-Ringᵉ Rᵉ 2 fᵉ ＝ᵉ add-Ringᵉ Rᵉ (fᵉ (zero-Finᵉ 1ᵉ)) (fᵉ (one-Finᵉ 1ᵉ))
  sum-two-elements-Ringᵉ = sum-two-elements-Semiringᵉ (semiring-Ringᵉ Rᵉ)
```

### Sums are homotopy invariant

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  htpy-sum-Ringᵉ :
    (nᵉ : ℕᵉ) {fᵉ gᵉ : functional-vec-Ringᵉ Rᵉ nᵉ} →
    (fᵉ ~ᵉ gᵉ) → sum-Ringᵉ Rᵉ nᵉ fᵉ ＝ᵉ sum-Ringᵉ Rᵉ nᵉ gᵉ
  htpy-sum-Ringᵉ = htpy-sum-Semiringᵉ (semiring-Ringᵉ Rᵉ)
```

### Sums are equal to the zero-th term plus the rest

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  cons-sum-Ringᵉ :
    (nᵉ : ℕᵉ) (fᵉ : functional-vec-Ringᵉ Rᵉ (succ-ℕᵉ nᵉ)) →
    {xᵉ : type-Ringᵉ Rᵉ} → head-functional-vecᵉ nᵉ fᵉ ＝ᵉ xᵉ →
    sum-Ringᵉ Rᵉ (succ-ℕᵉ nᵉ) fᵉ ＝ᵉ
    add-Ringᵉ Rᵉ (sum-Ringᵉ Rᵉ nᵉ (tail-functional-vecᵉ nᵉ fᵉ)) xᵉ
  cons-sum-Ringᵉ = cons-sum-Semiringᵉ (semiring-Ringᵉ Rᵉ)

  snoc-sum-Ringᵉ :
    (nᵉ : ℕᵉ) (fᵉ : functional-vec-Ringᵉ Rᵉ (succ-ℕᵉ nᵉ)) →
    {xᵉ : type-Ringᵉ Rᵉ} → fᵉ (zero-Finᵉ nᵉ) ＝ᵉ xᵉ →
    sum-Ringᵉ Rᵉ (succ-ℕᵉ nᵉ) fᵉ ＝ᵉ
    add-Ringᵉ Rᵉ
      ( xᵉ)
      ( sum-Ringᵉ Rᵉ nᵉ (fᵉ ∘ᵉ inr-Finᵉ nᵉ))
  snoc-sum-Ringᵉ = snoc-sum-Semiringᵉ (semiring-Ringᵉ Rᵉ)
```

### Multiplication distributes over sums

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  left-distributive-mul-sum-Ringᵉ :
    (nᵉ : ℕᵉ) (xᵉ : type-Ringᵉ Rᵉ)
    (fᵉ : functional-vec-Ringᵉ Rᵉ nᵉ) →
    mul-Ringᵉ Rᵉ xᵉ (sum-Ringᵉ Rᵉ nᵉ fᵉ) ＝ᵉ
    sum-Ringᵉ Rᵉ nᵉ (λ iᵉ → mul-Ringᵉ Rᵉ xᵉ (fᵉ iᵉ))
  left-distributive-mul-sum-Ringᵉ =
    left-distributive-mul-sum-Semiringᵉ (semiring-Ringᵉ Rᵉ)

  right-distributive-mul-sum-Ringᵉ :
    (nᵉ : ℕᵉ) (fᵉ : functional-vec-Ringᵉ Rᵉ nᵉ)
    (xᵉ : type-Ringᵉ Rᵉ) →
    mul-Ringᵉ Rᵉ (sum-Ringᵉ Rᵉ nᵉ fᵉ) xᵉ ＝ᵉ
    sum-Ringᵉ Rᵉ nᵉ (λ iᵉ → mul-Ringᵉ Rᵉ (fᵉ iᵉ) xᵉ)
  right-distributive-mul-sum-Ringᵉ =
    right-distributive-mul-sum-Semiringᵉ (semiring-Ringᵉ Rᵉ)
```

### Interchange law of sums and addition in a semiring

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  interchange-add-sum-Ringᵉ :
    (nᵉ : ℕᵉ) (fᵉ gᵉ : functional-vec-Ringᵉ Rᵉ nᵉ) →
    add-Ringᵉ Rᵉ
      ( sum-Ringᵉ Rᵉ nᵉ fᵉ)
      ( sum-Ringᵉ Rᵉ nᵉ gᵉ) ＝ᵉ
    sum-Ringᵉ Rᵉ nᵉ
      ( add-functional-vec-Ringᵉ Rᵉ nᵉ fᵉ gᵉ)
  interchange-add-sum-Ringᵉ = interchange-add-sum-Semiringᵉ (semiring-Ringᵉ Rᵉ)
```

### Extending a sum of elements in a semiring

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  extend-sum-Ringᵉ :
    (nᵉ : ℕᵉ) (fᵉ : functional-vec-Ringᵉ Rᵉ nᵉ) →
    sum-Ringᵉ Rᵉ
      ( succ-ℕᵉ nᵉ)
      ( cons-functional-vec-Ringᵉ Rᵉ nᵉ (zero-Ringᵉ Rᵉ) fᵉ) ＝ᵉ
    sum-Ringᵉ Rᵉ nᵉ fᵉ
  extend-sum-Ringᵉ = extend-sum-Semiringᵉ (semiring-Ringᵉ Rᵉ)
```

### Shifting a sum of elements in a semiring

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  shift-sum-Ringᵉ :
    (nᵉ : ℕᵉ) (fᵉ : functional-vec-Ringᵉ Rᵉ nᵉ) →
    sum-Ringᵉ Rᵉ
      ( succ-ℕᵉ nᵉ)
      ( snoc-functional-vec-Ringᵉ Rᵉ nᵉ fᵉ
        ( zero-Ringᵉ Rᵉ)) ＝ᵉ
    sum-Ringᵉ Rᵉ nᵉ fᵉ
  shift-sum-Ringᵉ = shift-sum-Semiringᵉ (semiring-Ringᵉ Rᵉ)
```

### A sum of zeroes is zero

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  sum-zero-Ringᵉ :
    (nᵉ : ℕᵉ) → sum-Ringᵉ Rᵉ nᵉ (zero-functional-vec-Ringᵉ Rᵉ nᵉ) ＝ᵉ zero-Ringᵉ Rᵉ
  sum-zero-Ringᵉ = sum-zero-Semiringᵉ (semiring-Ringᵉ Rᵉ)
```

### Splitting sums

```agda
split-sum-Ringᵉ :
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  (nᵉ mᵉ : ℕᵉ) (fᵉ : functional-vec-Ringᵉ Rᵉ (nᵉ +ℕᵉ mᵉ)) →
  sum-Ringᵉ Rᵉ (nᵉ +ℕᵉ mᵉ) fᵉ ＝ᵉ
  add-Ringᵉ Rᵉ
    ( sum-Ringᵉ Rᵉ nᵉ (fᵉ ∘ᵉ inl-coproduct-Finᵉ nᵉ mᵉ))
    ( sum-Ringᵉ Rᵉ mᵉ (fᵉ ∘ᵉ inr-coproduct-Finᵉ nᵉ mᵉ))
split-sum-Ringᵉ Rᵉ = split-sum-Semiringᵉ (semiring-Ringᵉ Rᵉ)
```