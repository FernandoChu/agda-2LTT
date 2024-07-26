# Sums in commutative semirings

```agda
module commutative-algebra.sums-commutative-semiringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-semiringsᵉ

open import elementary-number-theory.addition-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ

open import foundation.function-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ

open import linear-algebra.vectorsᵉ
open import linear-algebra.vectors-on-commutative-semiringsᵉ

open import ring-theory.sums-semiringsᵉ

open import univalent-combinatorics.coproduct-typesᵉ
open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Theᵉ **sumᵉ operation**ᵉ extendsᵉ theᵉ binaryᵉ additionᵉ operationᵉ onᵉ aᵉ commutativeᵉ
semiringᵉ `R`ᵉ to anyᵉ familyᵉ ofᵉ elementsᵉ ofᵉ `R`ᵉ indexedᵉ byᵉ aᵉ standardᵉ finiteᵉ type.ᵉ

## Definition

```agda
sum-Commutative-Semiringᵉ :
  {lᵉ : Level} (Aᵉ : Commutative-Semiringᵉ lᵉ) (nᵉ : ℕᵉ) →
  (functional-vec-Commutative-Semiringᵉ Aᵉ nᵉ) → type-Commutative-Semiringᵉ Aᵉ
sum-Commutative-Semiringᵉ Aᵉ = sum-Semiringᵉ (semiring-Commutative-Semiringᵉ Aᵉ)
```

## Properties

### Sums of one and two elements

```agda
module _
  {lᵉ : Level} (Aᵉ : Commutative-Semiringᵉ lᵉ)
  where

  sum-one-element-Commutative-Semiringᵉ :
    (fᵉ : functional-vec-Commutative-Semiringᵉ Aᵉ 1ᵉ) →
    sum-Commutative-Semiringᵉ Aᵉ 1 fᵉ ＝ᵉ head-functional-vecᵉ 0 fᵉ
  sum-one-element-Commutative-Semiringᵉ =
    sum-one-element-Semiringᵉ (semiring-Commutative-Semiringᵉ Aᵉ)

  sum-two-elements-Commutative-Semiringᵉ :
    (fᵉ : functional-vec-Commutative-Semiringᵉ Aᵉ 2ᵉ) →
    sum-Commutative-Semiringᵉ Aᵉ 2 fᵉ ＝ᵉ
    add-Commutative-Semiringᵉ Aᵉ (fᵉ (zero-Finᵉ 1ᵉ)) (fᵉ (one-Finᵉ 1ᵉ))
  sum-two-elements-Commutative-Semiringᵉ =
    sum-two-elements-Semiringᵉ (semiring-Commutative-Semiringᵉ Aᵉ)
```

### Sums are homotopy invariant

```agda
module _
  {lᵉ : Level} (Aᵉ : Commutative-Semiringᵉ lᵉ)
  where

  htpy-sum-Commutative-Semiringᵉ :
    (nᵉ : ℕᵉ) {fᵉ gᵉ : functional-vec-Commutative-Semiringᵉ Aᵉ nᵉ} →
    (fᵉ ~ᵉ gᵉ) → sum-Commutative-Semiringᵉ Aᵉ nᵉ fᵉ ＝ᵉ sum-Commutative-Semiringᵉ Aᵉ nᵉ gᵉ
  htpy-sum-Commutative-Semiringᵉ =
    htpy-sum-Semiringᵉ (semiring-Commutative-Semiringᵉ Aᵉ)
```

### Sums are equal to the zero-th term plus the rest

```agda
module _
  {lᵉ : Level} (Aᵉ : Commutative-Semiringᵉ lᵉ)
  where

  cons-sum-Commutative-Semiringᵉ :
    (nᵉ : ℕᵉ) (fᵉ : functional-vec-Commutative-Semiringᵉ Aᵉ (succ-ℕᵉ nᵉ)) →
    {xᵉ : type-Commutative-Semiringᵉ Aᵉ} → head-functional-vecᵉ nᵉ fᵉ ＝ᵉ xᵉ →
    sum-Commutative-Semiringᵉ Aᵉ (succ-ℕᵉ nᵉ) fᵉ ＝ᵉ
    add-Commutative-Semiringᵉ Aᵉ
      ( sum-Commutative-Semiringᵉ Aᵉ nᵉ (tail-functional-vecᵉ nᵉ fᵉ)) xᵉ
  cons-sum-Commutative-Semiringᵉ =
    cons-sum-Semiringᵉ (semiring-Commutative-Semiringᵉ Aᵉ)

  snoc-sum-Commutative-Semiringᵉ :
    (nᵉ : ℕᵉ) (fᵉ : functional-vec-Commutative-Semiringᵉ Aᵉ (succ-ℕᵉ nᵉ)) →
    {xᵉ : type-Commutative-Semiringᵉ Aᵉ} → fᵉ (zero-Finᵉ nᵉ) ＝ᵉ xᵉ →
    sum-Commutative-Semiringᵉ Aᵉ (succ-ℕᵉ nᵉ) fᵉ ＝ᵉ
    add-Commutative-Semiringᵉ Aᵉ
      ( xᵉ)
      ( sum-Commutative-Semiringᵉ Aᵉ nᵉ (fᵉ ∘ᵉ inr-Finᵉ nᵉ))
  snoc-sum-Commutative-Semiringᵉ =
    snoc-sum-Semiringᵉ (semiring-Commutative-Semiringᵉ Aᵉ)
```

### Multiplication distributes over sums

```agda
module _
  {lᵉ : Level} (Aᵉ : Commutative-Semiringᵉ lᵉ)
  where

  left-distributive-mul-sum-Commutative-Semiringᵉ :
    (nᵉ : ℕᵉ) (xᵉ : type-Commutative-Semiringᵉ Aᵉ)
    (fᵉ : functional-vec-Commutative-Semiringᵉ Aᵉ nᵉ) →
    mul-Commutative-Semiringᵉ Aᵉ xᵉ (sum-Commutative-Semiringᵉ Aᵉ nᵉ fᵉ) ＝ᵉ
    sum-Commutative-Semiringᵉ Aᵉ nᵉ (λ iᵉ → mul-Commutative-Semiringᵉ Aᵉ xᵉ (fᵉ iᵉ))
  left-distributive-mul-sum-Commutative-Semiringᵉ =
    left-distributive-mul-sum-Semiringᵉ (semiring-Commutative-Semiringᵉ Aᵉ)

  right-distributive-mul-sum-Commutative-Semiringᵉ :
    (nᵉ : ℕᵉ) (fᵉ : functional-vec-Commutative-Semiringᵉ Aᵉ nᵉ)
    (xᵉ : type-Commutative-Semiringᵉ Aᵉ) →
    mul-Commutative-Semiringᵉ Aᵉ (sum-Commutative-Semiringᵉ Aᵉ nᵉ fᵉ) xᵉ ＝ᵉ
    sum-Commutative-Semiringᵉ Aᵉ nᵉ (λ iᵉ → mul-Commutative-Semiringᵉ Aᵉ (fᵉ iᵉ) xᵉ)
  right-distributive-mul-sum-Commutative-Semiringᵉ =
    right-distributive-mul-sum-Semiringᵉ (semiring-Commutative-Semiringᵉ Aᵉ)
```

### Interchange law of sums and addition in a commutative semiring

```agda
module _
  {lᵉ : Level} (Aᵉ : Commutative-Semiringᵉ lᵉ)
  where

  interchange-add-sum-Commutative-Semiringᵉ :
    (nᵉ : ℕᵉ) (fᵉ gᵉ : functional-vec-Commutative-Semiringᵉ Aᵉ nᵉ) →
    add-Commutative-Semiringᵉ Aᵉ
      ( sum-Commutative-Semiringᵉ Aᵉ nᵉ fᵉ)
      ( sum-Commutative-Semiringᵉ Aᵉ nᵉ gᵉ) ＝ᵉ
    sum-Commutative-Semiringᵉ Aᵉ nᵉ
      ( add-functional-vec-Commutative-Semiringᵉ Aᵉ nᵉ fᵉ gᵉ)
  interchange-add-sum-Commutative-Semiringᵉ =
    interchange-add-sum-Semiringᵉ (semiring-Commutative-Semiringᵉ Aᵉ)
```

### Extending a sum of elements in a commutative semiring

```agda
module _
  {lᵉ : Level} (Aᵉ : Commutative-Semiringᵉ lᵉ)
  where

  extend-sum-Commutative-Semiringᵉ :
    (nᵉ : ℕᵉ) (fᵉ : functional-vec-Commutative-Semiringᵉ Aᵉ nᵉ) →
    sum-Commutative-Semiringᵉ Aᵉ
      ( succ-ℕᵉ nᵉ)
      ( cons-functional-vec-Commutative-Semiringᵉ Aᵉ nᵉ
        ( zero-Commutative-Semiringᵉ Aᵉ) fᵉ) ＝ᵉ
    sum-Commutative-Semiringᵉ Aᵉ nᵉ fᵉ
  extend-sum-Commutative-Semiringᵉ =
    extend-sum-Semiringᵉ (semiring-Commutative-Semiringᵉ Aᵉ)
```

### Shifting a sum of elements in a commutative semiring

```agda
module _
  {lᵉ : Level} (Aᵉ : Commutative-Semiringᵉ lᵉ)
  where

  shift-sum-Commutative-Semiringᵉ :
    (nᵉ : ℕᵉ) (fᵉ : functional-vec-Commutative-Semiringᵉ Aᵉ nᵉ) →
    sum-Commutative-Semiringᵉ Aᵉ
      ( succ-ℕᵉ nᵉ)
      ( snoc-functional-vec-Commutative-Semiringᵉ Aᵉ nᵉ fᵉ
        ( zero-Commutative-Semiringᵉ Aᵉ)) ＝ᵉ
    sum-Commutative-Semiringᵉ Aᵉ nᵉ fᵉ
  shift-sum-Commutative-Semiringᵉ =
    shift-sum-Semiringᵉ (semiring-Commutative-Semiringᵉ Aᵉ)
```

### A sum of zeroes is zero

```agda
module _
  {lᵉ : Level} (Aᵉ : Commutative-Semiringᵉ lᵉ)
  where

  sum-zero-Commutative-Semiringᵉ :
    (nᵉ : ℕᵉ) →
    sum-Commutative-Semiringᵉ Aᵉ nᵉ
      ( zero-functional-vec-Commutative-Semiringᵉ Aᵉ nᵉ) ＝ᵉ
    zero-Commutative-Semiringᵉ Aᵉ
  sum-zero-Commutative-Semiringᵉ =
    sum-zero-Semiringᵉ (semiring-Commutative-Semiringᵉ Aᵉ)
```

### Splitting sums

```agda
split-sum-Commutative-Semiringᵉ :
  {lᵉ : Level} (Aᵉ : Commutative-Semiringᵉ lᵉ)
  (nᵉ mᵉ : ℕᵉ) (fᵉ : functional-vec-Commutative-Semiringᵉ Aᵉ (nᵉ +ℕᵉ mᵉ)) →
  sum-Commutative-Semiringᵉ Aᵉ (nᵉ +ℕᵉ mᵉ) fᵉ ＝ᵉ
  add-Commutative-Semiringᵉ Aᵉ
    ( sum-Commutative-Semiringᵉ Aᵉ nᵉ (fᵉ ∘ᵉ inl-coproduct-Finᵉ nᵉ mᵉ))
    ( sum-Commutative-Semiringᵉ Aᵉ mᵉ (fᵉ ∘ᵉ inr-coproduct-Finᵉ nᵉ mᵉ))
split-sum-Commutative-Semiringᵉ Aᵉ =
  split-sum-Semiringᵉ (semiring-Commutative-Semiringᵉ Aᵉ)
```