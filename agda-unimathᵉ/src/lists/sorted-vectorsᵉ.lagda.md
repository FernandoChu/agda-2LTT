# Sorted vectors

```agda
module lists.sorted-vectorsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import finite-group-theory.permutations-standard-finite-typesᵉ

open import foundation.coproduct-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.propositionsᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import linear-algebra.vectorsᵉ

open import lists.permutation-vectorsᵉ

open import order-theory.decidable-total-ordersᵉ

open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Weᵉ defineᵉ aᵉ sortedᵉ vectorᵉ to beᵉ aᵉ vectorᵉ suchᵉ thatᵉ forᵉ everyᵉ pairᵉ ofᵉ consecutiveᵉ
elementsᵉ `x`ᵉ andᵉ `y`,ᵉ theᵉ inequalityᵉ `xᵉ ≤ᵉ y`ᵉ holds.ᵉ

## Definitions

### The proposition that a vector is sorted

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Xᵉ : Decidable-Total-Orderᵉ l1ᵉ l2ᵉ)
  where

  is-sorted-vec-Propᵉ :
    {nᵉ : ℕᵉ} → vecᵉ (type-Decidable-Total-Orderᵉ Xᵉ) nᵉ → Propᵉ l2ᵉ
  is-sorted-vec-Propᵉ {0ᵉ} vᵉ = raise-unit-Propᵉ l2ᵉ
  is-sorted-vec-Propᵉ {1ᵉ} vᵉ = raise-unit-Propᵉ l2ᵉ
  is-sorted-vec-Propᵉ {succ-ℕᵉ (succ-ℕᵉ nᵉ)} (xᵉ ∷ᵉ yᵉ ∷ᵉ vᵉ) =
    product-Propᵉ
      ( leq-Decidable-Total-Order-Propᵉ Xᵉ xᵉ yᵉ)
      ( is-sorted-vec-Propᵉ (yᵉ ∷ᵉ vᵉ))

  is-sorted-vecᵉ :
    {nᵉ : ℕᵉ} → vecᵉ (type-Decidable-Total-Orderᵉ Xᵉ) nᵉ → UUᵉ l2ᵉ
  is-sorted-vecᵉ lᵉ = type-Propᵉ (is-sorted-vec-Propᵉ lᵉ)
```

### The proposition that an element is less than or equal to every element in a vector

```agda
  is-least-element-vec-Propᵉ :
    {nᵉ : ℕᵉ} → type-Decidable-Total-Orderᵉ Xᵉ →
    vecᵉ (type-Decidable-Total-Orderᵉ Xᵉ) nᵉ → Propᵉ l2ᵉ
  is-least-element-vec-Propᵉ {0ᵉ} xᵉ vᵉ = raise-unit-Propᵉ l2ᵉ
  is-least-element-vec-Propᵉ {succ-ℕᵉ nᵉ} xᵉ (yᵉ ∷ᵉ vᵉ) =
    product-Propᵉ
      ( leq-Decidable-Total-Order-Propᵉ Xᵉ xᵉ yᵉ)
      ( is-least-element-vec-Propᵉ xᵉ vᵉ)

  is-least-element-vecᵉ :
    {nᵉ : ℕᵉ} → type-Decidable-Total-Orderᵉ Xᵉ →
    vecᵉ (type-Decidable-Total-Orderᵉ Xᵉ) nᵉ → UUᵉ l2ᵉ
  is-least-element-vecᵉ xᵉ vᵉ = type-Propᵉ (is-least-element-vec-Propᵉ xᵉ vᵉ)
```

## Properties

### If a vector is sorted, then its tail is also sorted

```agda
  is-sorted-tail-is-sorted-vecᵉ :
    {nᵉ : ℕᵉ} →
    (vᵉ : vecᵉ (type-Decidable-Total-Orderᵉ Xᵉ) (succ-ℕᵉ nᵉ)) →
    is-sorted-vecᵉ vᵉ → is-sorted-vecᵉ (tail-vecᵉ vᵉ)
  is-sorted-tail-is-sorted-vecᵉ {zero-ℕᵉ} (xᵉ ∷ᵉ empty-vecᵉ) sᵉ = raise-starᵉ
  is-sorted-tail-is-sorted-vecᵉ {succ-ℕᵉ nᵉ} (xᵉ ∷ᵉ yᵉ ∷ᵉ vᵉ) sᵉ = pr2ᵉ sᵉ

  is-leq-head-head-tail-is-sorted-vecᵉ :
    {nᵉ : ℕᵉ} → (vᵉ : vecᵉ (type-Decidable-Total-Orderᵉ Xᵉ) (succ-ℕᵉ (succ-ℕᵉ nᵉ))) →
    is-sorted-vecᵉ vᵉ →
    leq-Decidable-Total-Orderᵉ Xᵉ (head-vecᵉ vᵉ) (head-vecᵉ (tail-vecᵉ vᵉ))
  is-leq-head-head-tail-is-sorted-vecᵉ (xᵉ ∷ᵉ yᵉ ∷ᵉ vᵉ) sᵉ = pr1ᵉ sᵉ
```

### If a vector `v' ＝ y ∷ v` is sorted then for all elements `x` less than or equal to `y`, `x` is less than or equal to every element in the vector

```agda
  is-least-element-vec-is-leq-head-sorted-vecᵉ :
    {nᵉ : ℕᵉ}
    (xᵉ : type-Decidable-Total-Orderᵉ Xᵉ)
    (vᵉ : vecᵉ (type-Decidable-Total-Orderᵉ Xᵉ) (succ-ℕᵉ nᵉ)) →
    is-sorted-vecᵉ vᵉ → leq-Decidable-Total-Orderᵉ Xᵉ xᵉ (head-vecᵉ vᵉ) →
    is-least-element-vecᵉ xᵉ vᵉ
  is-least-element-vec-is-leq-head-sorted-vecᵉ {zero-ℕᵉ} xᵉ (yᵉ ∷ᵉ vᵉ) sᵉ pᵉ =
    pᵉ ,ᵉ raise-starᵉ
  is-least-element-vec-is-leq-head-sorted-vecᵉ {succ-ℕᵉ nᵉ} xᵉ (yᵉ ∷ᵉ vᵉ) sᵉ pᵉ =
    pᵉ ,ᵉ
    ( is-least-element-vec-is-leq-head-sorted-vecᵉ
      ( xᵉ)
      ( vᵉ)
      ( is-sorted-tail-is-sorted-vecᵉ (yᵉ ∷ᵉ vᵉ) sᵉ)
      ( transitive-leq-Decidable-Total-Orderᵉ
        ( Xᵉ)
        ( xᵉ)
        ( yᵉ)
        ( head-vecᵉ vᵉ)
        ( is-leq-head-head-tail-is-sorted-vecᵉ (yᵉ ∷ᵉ vᵉ) sᵉ)
        ( pᵉ)))
```

### An equivalent definition of being sorted

```agda
  is-sorted-least-element-vec-Propᵉ :
    {nᵉ : ℕᵉ} → vecᵉ (type-Decidable-Total-Orderᵉ Xᵉ) nᵉ → Propᵉ l2ᵉ
  is-sorted-least-element-vec-Propᵉ {0ᵉ} vᵉ = raise-unit-Propᵉ l2ᵉ
  is-sorted-least-element-vec-Propᵉ {1ᵉ} vᵉ = raise-unit-Propᵉ l2ᵉ
  is-sorted-least-element-vec-Propᵉ {succ-ℕᵉ (succ-ℕᵉ nᵉ)} (xᵉ ∷ᵉ vᵉ) =
    product-Propᵉ
      ( is-least-element-vec-Propᵉ xᵉ vᵉ)
      ( is-sorted-least-element-vec-Propᵉ vᵉ)

  is-sorted-least-element-vecᵉ :
    {nᵉ : ℕᵉ} → vecᵉ (type-Decidable-Total-Orderᵉ Xᵉ) nᵉ → UUᵉ l2ᵉ
  is-sorted-least-element-vecᵉ vᵉ =
    type-Propᵉ (is-sorted-least-element-vec-Propᵉ vᵉ)

  is-sorted-least-element-vec-is-sorted-vecᵉ :
    {nᵉ : ℕᵉ}
    (vᵉ : vecᵉ (type-Decidable-Total-Orderᵉ Xᵉ) nᵉ) →
    is-sorted-vecᵉ vᵉ → is-sorted-least-element-vecᵉ vᵉ
  is-sorted-least-element-vec-is-sorted-vecᵉ {0ᵉ} vᵉ xᵉ = raise-starᵉ
  is-sorted-least-element-vec-is-sorted-vecᵉ {1ᵉ} vᵉ xᵉ = raise-starᵉ
  is-sorted-least-element-vec-is-sorted-vecᵉ
    {succ-ℕᵉ (succ-ℕᵉ nᵉ)}
    ( xᵉ ∷ᵉ yᵉ ∷ᵉ vᵉ)
    ( pᵉ ,ᵉ qᵉ) =
    is-least-element-vec-is-leq-head-sorted-vecᵉ xᵉ (yᵉ ∷ᵉ vᵉ) qᵉ pᵉ ,ᵉ
    is-sorted-least-element-vec-is-sorted-vecᵉ (yᵉ ∷ᵉ vᵉ) qᵉ

  is-sorted-vec-is-sorted-least-element-vecᵉ :
    {nᵉ : ℕᵉ}
    (vᵉ : vecᵉ (type-Decidable-Total-Orderᵉ Xᵉ) nᵉ) →
    is-sorted-least-element-vecᵉ vᵉ →
    is-sorted-vecᵉ vᵉ
  is-sorted-vec-is-sorted-least-element-vecᵉ {0ᵉ} vᵉ xᵉ = raise-starᵉ
  is-sorted-vec-is-sorted-least-element-vecᵉ {1ᵉ} vᵉ xᵉ = raise-starᵉ
  is-sorted-vec-is-sorted-least-element-vecᵉ
    {succ-ℕᵉ (succ-ℕᵉ nᵉ)}
    (xᵉ ∷ᵉ yᵉ ∷ᵉ vᵉ)
    (pᵉ ,ᵉ qᵉ) =
    ( pr1ᵉ pᵉ) ,ᵉ
    ( is-sorted-vec-is-sorted-least-element-vecᵉ (yᵉ ∷ᵉ vᵉ) qᵉ)
```

### If the tail of a vector `v` is sorted and `x ≤ head-vec v`, then `v` is sorted

```agda
  is-sorted-vec-is-sorted-tail-is-leq-head-vecᵉ :
    {nᵉ : ℕᵉ}
    (vᵉ : vecᵉ (type-Decidable-Total-Orderᵉ Xᵉ) (succ-ℕᵉ (succ-ℕᵉ nᵉ))) →
    is-sorted-vecᵉ (tail-vecᵉ vᵉ) →
    (leq-Decidable-Total-Orderᵉ Xᵉ (head-vecᵉ vᵉ) (head-vecᵉ (tail-vecᵉ vᵉ))) →
    is-sorted-vecᵉ vᵉ
  is-sorted-vec-is-sorted-tail-is-leq-head-vecᵉ (xᵉ ∷ᵉ yᵉ ∷ᵉ vᵉ) sᵉ pᵉ = pᵉ ,ᵉ sᵉ
```

### If an element `x` is less than or equal to every element of a vector `v`, then it is less than or equal to every element of every permutation of `v`

```agda
  is-least-element-functional-vec-Propᵉ :
    (nᵉ : ℕᵉ)
    (xᵉ : type-Decidable-Total-Orderᵉ Xᵉ)
    (fvᵉ : functional-vecᵉ (type-Decidable-Total-Orderᵉ Xᵉ) nᵉ) →
    Propᵉ l2ᵉ
  is-least-element-functional-vec-Propᵉ nᵉ xᵉ fvᵉ =
    Π-Propᵉ (Finᵉ nᵉ) (λ kᵉ → leq-Decidable-Total-Order-Propᵉ Xᵉ xᵉ (fvᵉ kᵉ))

  is-least-element-functional-vecᵉ :
    (nᵉ : ℕᵉ)
    (xᵉ : type-Decidable-Total-Orderᵉ Xᵉ)
    (fvᵉ : functional-vecᵉ (type-Decidable-Total-Orderᵉ Xᵉ) nᵉ) →
    UUᵉ l2ᵉ
  is-least-element-functional-vecᵉ nᵉ xᵉ fvᵉ =
    type-Propᵉ (is-least-element-functional-vec-Propᵉ nᵉ xᵉ fvᵉ)

  is-least-element-permute-functional-vecᵉ :
    (nᵉ : ℕᵉ)
    (xᵉ : type-Decidable-Total-Orderᵉ Xᵉ)
    (fvᵉ : functional-vecᵉ (type-Decidable-Total-Orderᵉ Xᵉ) nᵉ)
    (aᵉ : Permutationᵉ nᵉ) →
    is-least-element-functional-vecᵉ nᵉ xᵉ fvᵉ →
    is-least-element-functional-vecᵉ nᵉ xᵉ (fvᵉ ∘ᵉ map-equivᵉ aᵉ)
  is-least-element-permute-functional-vecᵉ nᵉ xᵉ fvᵉ aᵉ pᵉ kᵉ =
    pᵉ (map-equivᵉ aᵉ kᵉ)

  is-least-element-vec-is-least-element-functional-vecᵉ :
    (nᵉ : ℕᵉ)
    (xᵉ : type-Decidable-Total-Orderᵉ Xᵉ)
    (fvᵉ : functional-vecᵉ (type-Decidable-Total-Orderᵉ Xᵉ) nᵉ) →
    is-least-element-functional-vecᵉ nᵉ xᵉ fvᵉ →
    is-least-element-vecᵉ xᵉ (listed-vec-functional-vecᵉ nᵉ fvᵉ)
  is-least-element-vec-is-least-element-functional-vecᵉ 0 xᵉ fvᵉ pᵉ = raise-starᵉ
  is-least-element-vec-is-least-element-functional-vecᵉ (succ-ℕᵉ nᵉ) xᵉ fvᵉ pᵉ =
    (pᵉ (inrᵉ starᵉ)) ,ᵉ
    ( is-least-element-vec-is-least-element-functional-vecᵉ
      ( nᵉ)
      ( xᵉ)
      ( tail-functional-vecᵉ nᵉ fvᵉ)
      ( pᵉ ∘ᵉ inlᵉ))

  is-least-element-functional-vec-is-least-element-vecᵉ :
    (nᵉ : ℕᵉ)
    (xᵉ : type-Decidable-Total-Orderᵉ Xᵉ)
    (vᵉ : vecᵉ (type-Decidable-Total-Orderᵉ Xᵉ) nᵉ) →
    is-least-element-vecᵉ xᵉ vᵉ →
    is-least-element-functional-vecᵉ nᵉ xᵉ (functional-vec-vecᵉ nᵉ vᵉ)
  is-least-element-functional-vec-is-least-element-vecᵉ
    ( succ-ℕᵉ nᵉ)
    ( xᵉ)
    ( yᵉ ∷ᵉ vᵉ)
    ( pᵉ ,ᵉ qᵉ)
    ( inlᵉ kᵉ) =
    is-least-element-functional-vec-is-least-element-vecᵉ nᵉ xᵉ vᵉ qᵉ kᵉ
  is-least-element-functional-vec-is-least-element-vecᵉ
    ( succ-ℕᵉ nᵉ)
    ( xᵉ)
    ( yᵉ ∷ᵉ vᵉ)
    ( pᵉ ,ᵉ qᵉ)
    ( inrᵉ starᵉ) =
    pᵉ

  is-least-element-permute-vecᵉ :
    {nᵉ : ℕᵉ}
    (xᵉ : type-Decidable-Total-Orderᵉ Xᵉ)
    (vᵉ : vecᵉ (type-Decidable-Total-Orderᵉ Xᵉ) nᵉ)
    (aᵉ : Permutationᵉ nᵉ) →
    is-least-element-vecᵉ xᵉ vᵉ →
    is-least-element-vecᵉ xᵉ (permute-vecᵉ nᵉ vᵉ aᵉ)
  is-least-element-permute-vecᵉ {nᵉ} xᵉ vᵉ aᵉ pᵉ =
    is-least-element-vec-is-least-element-functional-vecᵉ
      ( nᵉ)
      ( xᵉ)
      ( functional-vec-vecᵉ nᵉ vᵉ ∘ᵉ map-equivᵉ aᵉ)
      ( is-least-element-permute-functional-vecᵉ
        ( nᵉ)
        ( xᵉ)
        ( functional-vec-vecᵉ nᵉ vᵉ)
        ( aᵉ)
        ( is-least-element-functional-vec-is-least-element-vecᵉ nᵉ xᵉ vᵉ pᵉ))
```