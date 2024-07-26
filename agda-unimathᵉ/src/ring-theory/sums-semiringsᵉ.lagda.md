# Sums of elements in semirings

```agda
module ring-theory.sums-semiringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.coproduct-typesᵉ
open import foundation.function-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ

open import linear-algebra.vectorsᵉ
open import linear-algebra.vectors-on-semiringsᵉ

open import ring-theory.semiringsᵉ

open import univalent-combinatorics.coproduct-typesᵉ
open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Theᵉ sumᵉ operationᵉ extendsᵉ theᵉ binaryᵉ additionᵉ operationᵉ onᵉ aᵉ semiringᵉ `R`ᵉ to anyᵉ
familyᵉ ofᵉ elementsᵉ ofᵉ `R`ᵉ indexedᵉ byᵉ aᵉ standardᵉ finiteᵉ type.ᵉ

## Definition

```agda
sum-Semiringᵉ :
  {lᵉ : Level} (Rᵉ : Semiringᵉ lᵉ) (nᵉ : ℕᵉ) →
  (functional-vec-Semiringᵉ Rᵉ nᵉ) → type-Semiringᵉ Rᵉ
sum-Semiringᵉ Rᵉ zero-ℕᵉ fᵉ = zero-Semiringᵉ Rᵉ
sum-Semiringᵉ Rᵉ (succ-ℕᵉ nᵉ) fᵉ =
  add-Semiringᵉ Rᵉ
    ( sum-Semiringᵉ Rᵉ nᵉ (fᵉ ∘ᵉ inl-Finᵉ nᵉ))
    ( fᵉ (inrᵉ starᵉ))
```

## Properties

### Sums of one and two elements

```agda
module _
  {lᵉ : Level} (Rᵉ : Semiringᵉ lᵉ)
  where

  sum-one-element-Semiringᵉ :
    (fᵉ : functional-vec-Semiringᵉ Rᵉ 1ᵉ) →
    sum-Semiringᵉ Rᵉ 1 fᵉ ＝ᵉ head-functional-vecᵉ 0 fᵉ
  sum-one-element-Semiringᵉ fᵉ =
    left-unit-law-add-Semiringᵉ Rᵉ (fᵉ (inrᵉ starᵉ))

  sum-two-elements-Semiringᵉ :
    (fᵉ : functional-vec-Semiringᵉ Rᵉ 2ᵉ) →
    sum-Semiringᵉ Rᵉ 2 fᵉ ＝ᵉ add-Semiringᵉ Rᵉ (fᵉ (zero-Finᵉ 1ᵉ)) (fᵉ (one-Finᵉ 1ᵉ))
  sum-two-elements-Semiringᵉ fᵉ =
    ( associative-add-Semiringᵉ Rᵉ
      (zero-Semiringᵉ Rᵉ) (fᵉ (zero-Finᵉ 1ᵉ)) (fᵉ (one-Finᵉ 1ᵉ))) ∙ᵉ
    ( left-unit-law-add-Semiringᵉ Rᵉ
      ( add-Semiringᵉ Rᵉ (fᵉ (zero-Finᵉ 1ᵉ)) (fᵉ (one-Finᵉ 1ᵉ))))
```

### Sums are homotopy invariant

```agda
module _
  {lᵉ : Level} (Rᵉ : Semiringᵉ lᵉ)
  where

  htpy-sum-Semiringᵉ :
    (nᵉ : ℕᵉ) {fᵉ gᵉ : functional-vec-Semiringᵉ Rᵉ nᵉ} →
    (fᵉ ~ᵉ gᵉ) → sum-Semiringᵉ Rᵉ nᵉ fᵉ ＝ᵉ sum-Semiringᵉ Rᵉ nᵉ gᵉ
  htpy-sum-Semiringᵉ zero-ℕᵉ Hᵉ = reflᵉ
  htpy-sum-Semiringᵉ (succ-ℕᵉ nᵉ) Hᵉ =
    ap-add-Semiringᵉ Rᵉ
      ( htpy-sum-Semiringᵉ nᵉ (Hᵉ ·rᵉ inl-Finᵉ nᵉ))
      ( Hᵉ (inrᵉ starᵉ))
```

### Sums are equal to the zero-th term plus the rest

```agda
module _
  {lᵉ : Level} (Rᵉ : Semiringᵉ lᵉ)
  where

  cons-sum-Semiringᵉ :
    (nᵉ : ℕᵉ) (fᵉ : functional-vec-Semiringᵉ Rᵉ (succ-ℕᵉ nᵉ)) →
    {xᵉ : type-Semiringᵉ Rᵉ} → head-functional-vecᵉ nᵉ fᵉ ＝ᵉ xᵉ →
    sum-Semiringᵉ Rᵉ (succ-ℕᵉ nᵉ) fᵉ ＝ᵉ
    add-Semiringᵉ Rᵉ (sum-Semiringᵉ Rᵉ nᵉ (fᵉ ∘ᵉ inl-Finᵉ nᵉ)) xᵉ
  cons-sum-Semiringᵉ nᵉ fᵉ reflᵉ = reflᵉ

  snoc-sum-Semiringᵉ :
    (nᵉ : ℕᵉ) (fᵉ : functional-vec-Semiringᵉ Rᵉ (succ-ℕᵉ nᵉ)) →
    {xᵉ : type-Semiringᵉ Rᵉ} → fᵉ (zero-Finᵉ nᵉ) ＝ᵉ xᵉ →
    sum-Semiringᵉ Rᵉ (succ-ℕᵉ nᵉ) fᵉ ＝ᵉ
    add-Semiringᵉ Rᵉ
      ( xᵉ)
      ( sum-Semiringᵉ Rᵉ nᵉ (fᵉ ∘ᵉ inr-Finᵉ nᵉ))
  snoc-sum-Semiringᵉ zero-ℕᵉ fᵉ reflᵉ =
    ( sum-one-element-Semiringᵉ Rᵉ fᵉ) ∙ᵉ
    ( invᵉ (right-unit-law-add-Semiringᵉ Rᵉ (fᵉ (zero-Finᵉ 0ᵉ))))
  snoc-sum-Semiringᵉ (succ-ℕᵉ nᵉ) fᵉ reflᵉ =
    ( apᵉ
      ( add-Semiring'ᵉ Rᵉ (head-functional-vecᵉ (succ-ℕᵉ nᵉ) fᵉ))
      ( snoc-sum-Semiringᵉ nᵉ (fᵉ ∘ᵉ inl-Finᵉ (succ-ℕᵉ nᵉ)) reflᵉ)) ∙ᵉ
    ( associative-add-Semiringᵉ Rᵉ
      ( fᵉ (zero-Finᵉ (succ-ℕᵉ nᵉ)))
      ( sum-Semiringᵉ Rᵉ nᵉ (fᵉ ∘ᵉ (inr-Finᵉ (succ-ℕᵉ nᵉ) ∘ᵉ inl-Finᵉ nᵉ)))
      ( head-functional-vecᵉ (succ-ℕᵉ nᵉ) fᵉ))
```

### Multiplication distributes over sums

```agda
module _
  {lᵉ : Level} (Rᵉ : Semiringᵉ lᵉ)
  where

  left-distributive-mul-sum-Semiringᵉ :
    (nᵉ : ℕᵉ) (xᵉ : type-Semiringᵉ Rᵉ)
    (fᵉ : functional-vec-Semiringᵉ Rᵉ nᵉ) →
    mul-Semiringᵉ Rᵉ xᵉ (sum-Semiringᵉ Rᵉ nᵉ fᵉ) ＝ᵉ
    sum-Semiringᵉ Rᵉ nᵉ (λ iᵉ → mul-Semiringᵉ Rᵉ xᵉ (fᵉ iᵉ))
  left-distributive-mul-sum-Semiringᵉ zero-ℕᵉ xᵉ fᵉ =
    right-zero-law-mul-Semiringᵉ Rᵉ xᵉ
  left-distributive-mul-sum-Semiringᵉ (succ-ℕᵉ nᵉ) xᵉ fᵉ =
    ( left-distributive-mul-add-Semiringᵉ Rᵉ xᵉ
      ( sum-Semiringᵉ Rᵉ nᵉ (fᵉ ∘ᵉ inl-Finᵉ nᵉ))
      ( fᵉ (inrᵉ starᵉ))) ∙ᵉ
    ( apᵉ
      ( add-Semiring'ᵉ Rᵉ (mul-Semiringᵉ Rᵉ xᵉ (fᵉ (inrᵉ starᵉ))))
      ( left-distributive-mul-sum-Semiringᵉ nᵉ xᵉ (fᵉ ∘ᵉ inl-Finᵉ nᵉ)))

  right-distributive-mul-sum-Semiringᵉ :
    (nᵉ : ℕᵉ) (fᵉ : functional-vec-Semiringᵉ Rᵉ nᵉ)
    (xᵉ : type-Semiringᵉ Rᵉ) →
    mul-Semiringᵉ Rᵉ (sum-Semiringᵉ Rᵉ nᵉ fᵉ) xᵉ ＝ᵉ
    sum-Semiringᵉ Rᵉ nᵉ (λ iᵉ → mul-Semiringᵉ Rᵉ (fᵉ iᵉ) xᵉ)
  right-distributive-mul-sum-Semiringᵉ zero-ℕᵉ fᵉ xᵉ =
    left-zero-law-mul-Semiringᵉ Rᵉ xᵉ
  right-distributive-mul-sum-Semiringᵉ (succ-ℕᵉ nᵉ) fᵉ xᵉ =
    ( right-distributive-mul-add-Semiringᵉ Rᵉ
      ( sum-Semiringᵉ Rᵉ nᵉ (fᵉ ∘ᵉ inl-Finᵉ nᵉ))
      ( fᵉ (inrᵉ starᵉ))
      ( xᵉ)) ∙ᵉ
    ( apᵉ
      ( add-Semiring'ᵉ Rᵉ (mul-Semiringᵉ Rᵉ (fᵉ (inrᵉ starᵉ)) xᵉ))
      ( right-distributive-mul-sum-Semiringᵉ nᵉ (fᵉ ∘ᵉ inl-Finᵉ nᵉ) xᵉ))
```

### Interchange law of sums and addition in a semiring

```agda
module _
  {lᵉ : Level} (Rᵉ : Semiringᵉ lᵉ)
  where

  interchange-add-sum-Semiringᵉ :
    (nᵉ : ℕᵉ) (fᵉ gᵉ : functional-vec-Semiringᵉ Rᵉ nᵉ) →
    add-Semiringᵉ Rᵉ
      ( sum-Semiringᵉ Rᵉ nᵉ fᵉ)
      ( sum-Semiringᵉ Rᵉ nᵉ gᵉ) ＝ᵉ
    sum-Semiringᵉ Rᵉ nᵉ
      ( add-functional-vec-Semiringᵉ Rᵉ nᵉ fᵉ gᵉ)
  interchange-add-sum-Semiringᵉ zero-ℕᵉ fᵉ gᵉ =
    left-unit-law-add-Semiringᵉ Rᵉ (zero-Semiringᵉ Rᵉ)
  interchange-add-sum-Semiringᵉ (succ-ℕᵉ nᵉ) fᵉ gᵉ =
    ( interchange-add-add-Semiringᵉ Rᵉ
      ( sum-Semiringᵉ Rᵉ nᵉ (fᵉ ∘ᵉ inl-Finᵉ nᵉ))
      ( fᵉ (inrᵉ starᵉ))
      ( sum-Semiringᵉ Rᵉ nᵉ (gᵉ ∘ᵉ inl-Finᵉ nᵉ))
      ( gᵉ (inrᵉ starᵉ))) ∙ᵉ
    ( apᵉ
      ( add-Semiring'ᵉ Rᵉ
        ( add-Semiringᵉ Rᵉ (fᵉ (inrᵉ starᵉ)) (gᵉ (inrᵉ starᵉ))))
      ( interchange-add-sum-Semiringᵉ nᵉ
        ( fᵉ ∘ᵉ inl-Finᵉ nᵉ)
        ( gᵉ ∘ᵉ inl-Finᵉ nᵉ)))
```

### Extending a sum of elements in a semiring

```agda
module _
  {lᵉ : Level} (Rᵉ : Semiringᵉ lᵉ)
  where

  extend-sum-Semiringᵉ :
    (nᵉ : ℕᵉ) (fᵉ : functional-vec-Semiringᵉ Rᵉ nᵉ) →
    sum-Semiringᵉ Rᵉ
      ( succ-ℕᵉ nᵉ)
      ( cons-functional-vec-Semiringᵉ Rᵉ nᵉ (zero-Semiringᵉ Rᵉ) fᵉ) ＝ᵉ
    sum-Semiringᵉ Rᵉ nᵉ fᵉ
  extend-sum-Semiringᵉ nᵉ fᵉ =
    right-unit-law-add-Semiringᵉ Rᵉ (sum-Semiringᵉ Rᵉ nᵉ fᵉ)
```

### Shifting a sum of elements in a semiring

```agda
module _
  {lᵉ : Level} (Rᵉ : Semiringᵉ lᵉ)
  where

  shift-sum-Semiringᵉ :
    (nᵉ : ℕᵉ) (fᵉ : functional-vec-Semiringᵉ Rᵉ nᵉ) →
    sum-Semiringᵉ Rᵉ
      ( succ-ℕᵉ nᵉ)
      ( snoc-functional-vec-Semiringᵉ Rᵉ nᵉ fᵉ
        ( zero-Semiringᵉ Rᵉ)) ＝ᵉ
    sum-Semiringᵉ Rᵉ nᵉ fᵉ
  shift-sum-Semiringᵉ zero-ℕᵉ fᵉ =
    left-unit-law-add-Semiringᵉ Rᵉ (zero-Semiringᵉ Rᵉ)
  shift-sum-Semiringᵉ (succ-ℕᵉ nᵉ) fᵉ =
    apᵉ
      ( add-Semiring'ᵉ Rᵉ
        ( head-functional-vec-Semiringᵉ Rᵉ nᵉ fᵉ))
      ( shift-sum-Semiringᵉ nᵉ
        ( tail-functional-vec-Semiringᵉ Rᵉ nᵉ fᵉ))
```

### A sum of zeroes is zero

```agda
module _
  {lᵉ : Level} (Rᵉ : Semiringᵉ lᵉ)
  where

  sum-zero-Semiringᵉ :
    (nᵉ : ℕᵉ) →
    sum-Semiringᵉ Rᵉ nᵉ (zero-functional-vec-Semiringᵉ Rᵉ nᵉ) ＝ᵉ zero-Semiringᵉ Rᵉ
  sum-zero-Semiringᵉ zero-ℕᵉ = reflᵉ
  sum-zero-Semiringᵉ (succ-ℕᵉ nᵉ) =
    right-unit-law-add-Semiringᵉ Rᵉ _ ∙ᵉ sum-zero-Semiringᵉ nᵉ
```

### Splitting sums

```agda
split-sum-Semiringᵉ :
  {lᵉ : Level} (Rᵉ : Semiringᵉ lᵉ)
  (nᵉ mᵉ : ℕᵉ) (fᵉ : functional-vec-Semiringᵉ Rᵉ (nᵉ +ℕᵉ mᵉ)) →
  sum-Semiringᵉ Rᵉ (nᵉ +ℕᵉ mᵉ) fᵉ ＝ᵉ
  add-Semiringᵉ Rᵉ
    ( sum-Semiringᵉ Rᵉ nᵉ (fᵉ ∘ᵉ inl-coproduct-Finᵉ nᵉ mᵉ))
    ( sum-Semiringᵉ Rᵉ mᵉ (fᵉ ∘ᵉ inr-coproduct-Finᵉ nᵉ mᵉ))
split-sum-Semiringᵉ Rᵉ nᵉ zero-ℕᵉ fᵉ =
  invᵉ (right-unit-law-add-Semiringᵉ Rᵉ (sum-Semiringᵉ Rᵉ nᵉ fᵉ))
split-sum-Semiringᵉ Rᵉ nᵉ (succ-ℕᵉ mᵉ) fᵉ =
  ( apᵉ
    ( add-Semiring'ᵉ Rᵉ (fᵉ (inrᵉ starᵉ)))
    ( split-sum-Semiringᵉ Rᵉ nᵉ mᵉ (fᵉ ∘ᵉ inlᵉ))) ∙ᵉ
  ( associative-add-Semiringᵉ Rᵉ _ _ _)
```