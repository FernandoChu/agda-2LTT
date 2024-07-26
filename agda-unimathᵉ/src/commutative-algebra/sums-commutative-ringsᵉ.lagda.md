# Sums in commutative rings

```agda
module commutative-algebra.sums-commutative-ringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-ringsᵉ

open import elementary-number-theory.addition-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.coproduct-typesᵉ
open import foundation.function-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import linear-algebra.vectorsᵉ
open import linear-algebra.vectors-on-commutative-ringsᵉ

open import ring-theory.sums-ringsᵉ

open import univalent-combinatorics.coproduct-typesᵉ
open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Theᵉ **sumᵉ operation**ᵉ extendsᵉ theᵉ binaryᵉ additionᵉ operationᵉ onᵉ aᵉ commutativeᵉ
ringᵉ `A`ᵉ to anyᵉ familyᵉ ofᵉ elementsᵉ ofᵉ `A`ᵉ indexedᵉ byᵉ aᵉ standardᵉ finiteᵉ type.ᵉ

## Definition

```agda
sum-Commutative-Ringᵉ :
  {lᵉ : Level} (Aᵉ : Commutative-Ringᵉ lᵉ) (nᵉ : ℕᵉ) →
  (functional-vec-Commutative-Ringᵉ Aᵉ nᵉ) → type-Commutative-Ringᵉ Aᵉ
sum-Commutative-Ringᵉ Aᵉ = sum-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)
```

## Properties

### Sums of one and two elements

```agda
module _
  {lᵉ : Level} (Aᵉ : Commutative-Ringᵉ lᵉ)
  where

  sum-one-element-Commutative-Ringᵉ :
    (fᵉ : functional-vec-Commutative-Ringᵉ Aᵉ 1ᵉ) →
    sum-Commutative-Ringᵉ Aᵉ 1 fᵉ ＝ᵉ head-functional-vecᵉ 0 fᵉ
  sum-one-element-Commutative-Ringᵉ =
    sum-one-element-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)

  sum-two-elements-Commutative-Ringᵉ :
    (fᵉ : functional-vec-Commutative-Ringᵉ Aᵉ 2ᵉ) →
    sum-Commutative-Ringᵉ Aᵉ 2 fᵉ ＝ᵉ
    add-Commutative-Ringᵉ Aᵉ (fᵉ (zero-Finᵉ 1ᵉ)) (fᵉ (one-Finᵉ 1ᵉ))
  sum-two-elements-Commutative-Ringᵉ =
    sum-two-elements-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)
```

### Sums are homotopy invariant

```agda
module _
  {lᵉ : Level} (Aᵉ : Commutative-Ringᵉ lᵉ)
  where

  htpy-sum-Commutative-Ringᵉ :
    (nᵉ : ℕᵉ) {fᵉ gᵉ : functional-vec-Commutative-Ringᵉ Aᵉ nᵉ} →
    (fᵉ ~ᵉ gᵉ) → sum-Commutative-Ringᵉ Aᵉ nᵉ fᵉ ＝ᵉ sum-Commutative-Ringᵉ Aᵉ nᵉ gᵉ
  htpy-sum-Commutative-Ringᵉ = htpy-sum-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)
```

### Sums are equal to the zero-th term plus the rest

```agda
module _
  {lᵉ : Level} (Aᵉ : Commutative-Ringᵉ lᵉ)
  where

  cons-sum-Commutative-Ringᵉ :
    (nᵉ : ℕᵉ) (fᵉ : functional-vec-Commutative-Ringᵉ Aᵉ (succ-ℕᵉ nᵉ)) →
    {xᵉ : type-Commutative-Ringᵉ Aᵉ} → head-functional-vecᵉ nᵉ fᵉ ＝ᵉ xᵉ →
    sum-Commutative-Ringᵉ Aᵉ (succ-ℕᵉ nᵉ) fᵉ ＝ᵉ
    add-Commutative-Ringᵉ Aᵉ
      ( sum-Commutative-Ringᵉ Aᵉ nᵉ (tail-functional-vecᵉ nᵉ fᵉ)) xᵉ
  cons-sum-Commutative-Ringᵉ = cons-sum-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)

  snoc-sum-Commutative-Ringᵉ :
    (nᵉ : ℕᵉ) (fᵉ : functional-vec-Commutative-Ringᵉ Aᵉ (succ-ℕᵉ nᵉ)) →
    {xᵉ : type-Commutative-Ringᵉ Aᵉ} → fᵉ (zero-Finᵉ nᵉ) ＝ᵉ xᵉ →
    sum-Commutative-Ringᵉ Aᵉ (succ-ℕᵉ nᵉ) fᵉ ＝ᵉ
    add-Commutative-Ringᵉ Aᵉ
      ( xᵉ)
      ( sum-Commutative-Ringᵉ Aᵉ nᵉ (fᵉ ∘ᵉ inr-Finᵉ nᵉ))
  snoc-sum-Commutative-Ringᵉ = snoc-sum-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)
```

### Multiplication distributes over sums

```agda
module _
  {lᵉ : Level} (Aᵉ : Commutative-Ringᵉ lᵉ)
  where

  left-distributive-mul-sum-Commutative-Ringᵉ :
    (nᵉ : ℕᵉ) (xᵉ : type-Commutative-Ringᵉ Aᵉ)
    (fᵉ : functional-vec-Commutative-Ringᵉ Aᵉ nᵉ) →
    mul-Commutative-Ringᵉ Aᵉ xᵉ (sum-Commutative-Ringᵉ Aᵉ nᵉ fᵉ) ＝ᵉ
    sum-Commutative-Ringᵉ Aᵉ nᵉ (λ iᵉ → mul-Commutative-Ringᵉ Aᵉ xᵉ (fᵉ iᵉ))
  left-distributive-mul-sum-Commutative-Ringᵉ =
    left-distributive-mul-sum-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)

  right-distributive-mul-sum-Commutative-Ringᵉ :
    (nᵉ : ℕᵉ) (fᵉ : functional-vec-Commutative-Ringᵉ Aᵉ nᵉ)
    (xᵉ : type-Commutative-Ringᵉ Aᵉ) →
    mul-Commutative-Ringᵉ Aᵉ (sum-Commutative-Ringᵉ Aᵉ nᵉ fᵉ) xᵉ ＝ᵉ
    sum-Commutative-Ringᵉ Aᵉ nᵉ (λ iᵉ → mul-Commutative-Ringᵉ Aᵉ (fᵉ iᵉ) xᵉ)
  right-distributive-mul-sum-Commutative-Ringᵉ =
    right-distributive-mul-sum-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)
```

### Interchange law of sums and addition in a commutative ring

```agda
module _
  {lᵉ : Level} (Aᵉ : Commutative-Ringᵉ lᵉ)
  where

  interchange-add-sum-Commutative-Ringᵉ :
    (nᵉ : ℕᵉ) (fᵉ gᵉ : functional-vec-Commutative-Ringᵉ Aᵉ nᵉ) →
    add-Commutative-Ringᵉ Aᵉ
      ( sum-Commutative-Ringᵉ Aᵉ nᵉ fᵉ)
      ( sum-Commutative-Ringᵉ Aᵉ nᵉ gᵉ) ＝ᵉ
    sum-Commutative-Ringᵉ Aᵉ nᵉ
      ( add-functional-vec-Commutative-Ringᵉ Aᵉ nᵉ fᵉ gᵉ)
  interchange-add-sum-Commutative-Ringᵉ =
    interchange-add-sum-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)
```

### Extending a sum of elements in a commutative ring

```agda
module _
  {lᵉ : Level} (Aᵉ : Commutative-Ringᵉ lᵉ)
  where

  extend-sum-Commutative-Ringᵉ :
    (nᵉ : ℕᵉ) (fᵉ : functional-vec-Commutative-Ringᵉ Aᵉ nᵉ) →
    sum-Commutative-Ringᵉ Aᵉ
      ( succ-ℕᵉ nᵉ)
      ( cons-functional-vec-Commutative-Ringᵉ Aᵉ nᵉ (zero-Commutative-Ringᵉ Aᵉ) fᵉ) ＝ᵉ
    sum-Commutative-Ringᵉ Aᵉ nᵉ fᵉ
  extend-sum-Commutative-Ringᵉ = extend-sum-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)
```

### Shifting a sum of elements in a commutative ring

```agda
module _
  {lᵉ : Level} (Aᵉ : Commutative-Ringᵉ lᵉ)
  where

  shift-sum-Commutative-Ringᵉ :
    (nᵉ : ℕᵉ) (fᵉ : functional-vec-Commutative-Ringᵉ Aᵉ nᵉ) →
    sum-Commutative-Ringᵉ Aᵉ
      ( succ-ℕᵉ nᵉ)
      ( snoc-functional-vec-Commutative-Ringᵉ Aᵉ nᵉ fᵉ
        ( zero-Commutative-Ringᵉ Aᵉ)) ＝ᵉ
    sum-Commutative-Ringᵉ Aᵉ nᵉ fᵉ
  shift-sum-Commutative-Ringᵉ = shift-sum-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)
```

### Splitting sums

```agda
split-sum-Commutative-Ringᵉ :
  {lᵉ : Level} (Aᵉ : Commutative-Ringᵉ lᵉ)
  (nᵉ mᵉ : ℕᵉ) (fᵉ : functional-vec-Commutative-Ringᵉ Aᵉ (nᵉ +ℕᵉ mᵉ)) →
  sum-Commutative-Ringᵉ Aᵉ (nᵉ +ℕᵉ mᵉ) fᵉ ＝ᵉ
  add-Commutative-Ringᵉ Aᵉ
    ( sum-Commutative-Ringᵉ Aᵉ nᵉ (fᵉ ∘ᵉ inl-coproduct-Finᵉ nᵉ mᵉ))
    ( sum-Commutative-Ringᵉ Aᵉ mᵉ (fᵉ ∘ᵉ inr-coproduct-Finᵉ nᵉ mᵉ))
split-sum-Commutative-Ringᵉ Aᵉ nᵉ zero-ℕᵉ fᵉ =
  invᵉ (right-unit-law-add-Commutative-Ringᵉ Aᵉ (sum-Commutative-Ringᵉ Aᵉ nᵉ fᵉ))
split-sum-Commutative-Ringᵉ Aᵉ nᵉ (succ-ℕᵉ mᵉ) fᵉ =
  ( apᵉ
    ( add-Commutative-Ring'ᵉ Aᵉ (fᵉ (inrᵉ starᵉ)))
    ( split-sum-Commutative-Ringᵉ Aᵉ nᵉ mᵉ (fᵉ ∘ᵉ inlᵉ))) ∙ᵉ
  ( associative-add-Commutative-Ringᵉ Aᵉ _ _ _)
```

### A sum of zeroes is zero

```agda
module _
  {lᵉ : Level} (Aᵉ : Commutative-Ringᵉ lᵉ)
  where

  sum-zero-Commutative-Ringᵉ :
    (nᵉ : ℕᵉ) →
    sum-Commutative-Ringᵉ Aᵉ nᵉ
      ( zero-functional-vec-Commutative-Ringᵉ Aᵉ nᵉ) ＝ᵉ
    zero-Commutative-Ringᵉ Aᵉ
  sum-zero-Commutative-Ringᵉ = sum-zero-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)
```