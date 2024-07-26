# Strictly ordered pairs of natural numbers

```agda
module elementary-number-theory.strictly-ordered-pairs-of-natural-numbersᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ
open import elementary-number-theory.strict-inequality-natural-numbersᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.empty-typesᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.negated-equalityᵉ
open import foundation.pairs-of-distinct-elementsᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Aᵉ strictlyᵉ orderedᵉ pairᵉ ofᵉ naturalᵉ numbersᵉ consistsᵉ ofᵉ `xᵉ yᵉ : ℕ`ᵉ suchᵉ thatᵉ
`xᵉ <ᵉ y`.ᵉ

## Definition

```agda
strictly-ordered-pair-ℕᵉ : UUᵉ lzero
strictly-ordered-pair-ℕᵉ = Σᵉ ℕᵉ (λ xᵉ → Σᵉ ℕᵉ (λ yᵉ → le-ℕᵉ xᵉ yᵉ))

module _
  (pᵉ : strictly-ordered-pair-ℕᵉ)
  where

  first-strictly-ordered-pair-ℕᵉ : ℕᵉ
  first-strictly-ordered-pair-ℕᵉ = pr1ᵉ pᵉ

  second-strictly-ordered-pair-ℕᵉ : ℕᵉ
  second-strictly-ordered-pair-ℕᵉ = pr1ᵉ (pr2ᵉ pᵉ)

  strict-inequality-strictly-ordered-pair-ℕᵉ :
    le-ℕᵉ first-strictly-ordered-pair-ℕᵉ second-strictly-ordered-pair-ℕᵉ
  strict-inequality-strictly-ordered-pair-ℕᵉ = pr2ᵉ (pr2ᵉ pᵉ)
```

## Properties

### Strictly ordered pairs of natural numbers are pairs of distinct elements

```agda
pair-of-distinct-elements-strictly-ordered-pair-ℕᵉ :
  strictly-ordered-pair-ℕᵉ → pair-of-distinct-elementsᵉ ℕᵉ
pair-of-distinct-elements-strictly-ordered-pair-ℕᵉ (aᵉ ,ᵉ bᵉ ,ᵉ Hᵉ) =
  (aᵉ ,ᵉ bᵉ ,ᵉ neq-le-ℕᵉ Hᵉ)
```

### Any pair of distinct elements of natural numbers can be strictly ordered

```agda
strictly-ordered-pair-pair-of-distinct-elements-ℕ'ᵉ :
  (aᵉ bᵉ : ℕᵉ) → aᵉ ≠ᵉ bᵉ → strictly-ordered-pair-ℕᵉ
strictly-ordered-pair-pair-of-distinct-elements-ℕ'ᵉ zero-ℕᵉ zero-ℕᵉ Hᵉ =
  ex-falsoᵉ (Hᵉ reflᵉ)
strictly-ordered-pair-pair-of-distinct-elements-ℕ'ᵉ zero-ℕᵉ (succ-ℕᵉ bᵉ) Hᵉ =
  (0ᵉ ,ᵉ succ-ℕᵉ bᵉ ,ᵉ starᵉ)
strictly-ordered-pair-pair-of-distinct-elements-ℕ'ᵉ (succ-ℕᵉ aᵉ) zero-ℕᵉ Hᵉ =
  (0ᵉ ,ᵉ succ-ℕᵉ aᵉ ,ᵉ starᵉ)
strictly-ordered-pair-pair-of-distinct-elements-ℕ'ᵉ (succ-ℕᵉ aᵉ) (succ-ℕᵉ bᵉ) Hᵉ =
  map-Σᵉ
    ( λ xᵉ → Σᵉ ℕᵉ (λ yᵉ → le-ℕᵉ xᵉ yᵉ))
    ( succ-ℕᵉ)
    ( λ xᵉ →
      map-Σᵉ (le-ℕᵉ (succ-ℕᵉ xᵉ)) succ-ℕᵉ (λ yᵉ → idᵉ))
    ( strictly-ordered-pair-pair-of-distinct-elements-ℕ'ᵉ aᵉ bᵉ
      ( λ pᵉ → Hᵉ (apᵉ succ-ℕᵉ pᵉ)))

strictly-ordered-pair-pair-of-distinct-elements-ℕᵉ :
  pair-of-distinct-elementsᵉ ℕᵉ → strictly-ordered-pair-ℕᵉ
strictly-ordered-pair-pair-of-distinct-elements-ℕᵉ (aᵉ ,ᵉ bᵉ ,ᵉ Hᵉ) =
  strictly-ordered-pair-pair-of-distinct-elements-ℕ'ᵉ aᵉ bᵉ Hᵉ
```