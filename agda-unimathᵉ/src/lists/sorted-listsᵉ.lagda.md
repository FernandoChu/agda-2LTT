# Sorted lists

```agda
module lists.sorted-listsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.propositionsᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import linear-algebra.vectorsᵉ

open import lists.arraysᵉ
open import lists.listsᵉ
open import lists.sorted-vectorsᵉ

open import order-theory.decidable-total-ordersᵉ
```

</details>

## Idea

Weᵉ defineᵉ aᵉ sortedᵉ listᵉ to beᵉ aᵉ listᵉ suchᵉ thatᵉ forᵉ everyᵉ pairᵉ ofᵉ consecutiveᵉ
entriesᵉ `x`ᵉ andᵉ `y`,ᵉ theᵉ inequalityᵉ `xᵉ ≤ᵉ y`ᵉ holds.ᵉ

## Definitions

### The proposition that a list is sorted

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Xᵉ : Decidable-Total-Orderᵉ l1ᵉ l2ᵉ)
  where

  is-sorted-list-Propᵉ : listᵉ (type-Decidable-Total-Orderᵉ Xᵉ) → Propᵉ l2ᵉ
  is-sorted-list-Propᵉ nilᵉ = raise-unit-Propᵉ l2ᵉ
  is-sorted-list-Propᵉ (consᵉ xᵉ nilᵉ) = raise-unit-Propᵉ l2ᵉ
  is-sorted-list-Propᵉ (consᵉ xᵉ (consᵉ yᵉ lᵉ)) =
    product-Propᵉ
      ( leq-Decidable-Total-Order-Propᵉ Xᵉ xᵉ yᵉ)
      ( is-sorted-list-Propᵉ (consᵉ yᵉ lᵉ))

  is-sorted-listᵉ : listᵉ (type-Decidable-Total-Orderᵉ Xᵉ) → UUᵉ l2ᵉ
  is-sorted-listᵉ lᵉ = type-Propᵉ (is-sorted-list-Propᵉ lᵉ)

  is-prop-is-sorted-listᵉ :
    (lᵉ : listᵉ (type-Decidable-Total-Orderᵉ Xᵉ)) → is-propᵉ (is-sorted-listᵉ lᵉ)
  is-prop-is-sorted-listᵉ lᵉ = is-prop-type-Propᵉ (is-sorted-list-Propᵉ lᵉ)
```

### The proposition that an element is less or equal than every element in a list

```agda
  is-least-element-list-Propᵉ :
    type-Decidable-Total-Orderᵉ Xᵉ →
    listᵉ (type-Decidable-Total-Orderᵉ Xᵉ) → Propᵉ l2ᵉ
  is-least-element-list-Propᵉ xᵉ nilᵉ = raise-unit-Propᵉ l2ᵉ
  is-least-element-list-Propᵉ xᵉ (consᵉ yᵉ lᵉ) =
    product-Propᵉ
      ( leq-Decidable-Total-Order-Propᵉ Xᵉ xᵉ yᵉ)
      ( is-least-element-list-Propᵉ xᵉ lᵉ)

  is-least-element-listᵉ :
    type-Decidable-Total-Orderᵉ Xᵉ →
    listᵉ (type-Decidable-Total-Orderᵉ Xᵉ) → UUᵉ l2ᵉ
  is-least-element-listᵉ xᵉ lᵉ = type-Propᵉ (is-least-element-list-Propᵉ xᵉ lᵉ)
```

## Properties

### If a list is sorted, then its tail is also sorted

```agda
  is-sorted-tail-is-sorted-listᵉ :
    (lᵉ : listᵉ (type-Decidable-Total-Orderᵉ Xᵉ)) →
    is-sorted-listᵉ lᵉ → is-sorted-listᵉ (tail-listᵉ lᵉ)
  is-sorted-tail-is-sorted-listᵉ nilᵉ _ = raise-starᵉ
  is-sorted-tail-is-sorted-listᵉ (consᵉ xᵉ nilᵉ) sᵉ = raise-starᵉ
  is-sorted-tail-is-sorted-listᵉ (consᵉ xᵉ (consᵉ yᵉ lᵉ)) sᵉ = pr2ᵉ sᵉ
```

### If a list is sorted then its head is less or equal than every element in the list

```agda
  leq-element-in-list-leq-head-is-sorted-listᵉ :
    (xᵉ yᵉ zᵉ : type-Decidable-Total-Orderᵉ Xᵉ)
    (lᵉ : listᵉ (type-Decidable-Total-Orderᵉ Xᵉ)) →
    is-sorted-listᵉ (consᵉ yᵉ lᵉ) →
    zᵉ ∈-listᵉ (consᵉ yᵉ lᵉ) →
    leq-Decidable-Total-Orderᵉ Xᵉ xᵉ yᵉ →
    leq-Decidable-Total-Orderᵉ Xᵉ xᵉ zᵉ
  leq-element-in-list-leq-head-is-sorted-listᵉ xᵉ .zᵉ zᵉ lᵉ sᵉ (is-headᵉ .zᵉ lᵉ) qᵉ =
    qᵉ
  leq-element-in-list-leq-head-is-sorted-listᵉ
    ( xᵉ)
    ( yᵉ)
    ( zᵉ)
    ( consᵉ wᵉ lᵉ)
    ( sᵉ)
    ( is-in-tailᵉ .zᵉ .yᵉ .(consᵉ wᵉ lᵉ) iᵉ)
    ( qᵉ) =
    leq-element-in-list-leq-head-is-sorted-listᵉ
      ( xᵉ)
      ( wᵉ)
      ( zᵉ)
      ( lᵉ)
      ( pr2ᵉ sᵉ)
      ( iᵉ)
      ( transitive-leq-Decidable-Total-Orderᵉ Xᵉ xᵉ yᵉ wᵉ (pr1ᵉ sᵉ) qᵉ)
```

### An equivalent definition of being sorted

```agda
  is-sorted-least-element-list-Propᵉ :
    listᵉ (type-Decidable-Total-Orderᵉ Xᵉ) → Propᵉ l2ᵉ
  is-sorted-least-element-list-Propᵉ nilᵉ = raise-unit-Propᵉ l2ᵉ
  is-sorted-least-element-list-Propᵉ (consᵉ xᵉ lᵉ) =
    product-Propᵉ
      ( is-least-element-list-Propᵉ xᵉ lᵉ)
      ( is-sorted-least-element-list-Propᵉ lᵉ)

  is-sorted-least-element-listᵉ :
    listᵉ (type-Decidable-Total-Orderᵉ Xᵉ) → UUᵉ l2ᵉ
  is-sorted-least-element-listᵉ lᵉ =
    type-Propᵉ (is-sorted-least-element-list-Propᵉ lᵉ)

  is-sorted-list-is-sorted-least-element-listᵉ :
    (lᵉ : listᵉ (type-Decidable-Total-Orderᵉ Xᵉ)) →
    is-sorted-least-element-listᵉ lᵉ → is-sorted-listᵉ lᵉ
  is-sorted-list-is-sorted-least-element-listᵉ nilᵉ _ =
    raise-starᵉ
  is-sorted-list-is-sorted-least-element-listᵉ (consᵉ xᵉ nilᵉ) _ =
    raise-starᵉ
  is-sorted-list-is-sorted-least-element-listᵉ
    (consᵉ xᵉ (consᵉ yᵉ lᵉ))
    (pᵉ ,ᵉ qᵉ) =
    ( pr1ᵉ pᵉ ,ᵉ
      is-sorted-list-is-sorted-least-element-listᵉ (consᵉ yᵉ lᵉ) qᵉ)
```

### If a vector `v` of length `n` is sorted, then the list `list-vec n v` is also sorted

```agda
  is-sorted-list-is-sorted-vecᵉ :
    (nᵉ : ℕᵉ) (vᵉ : vecᵉ (type-Decidable-Total-Orderᵉ Xᵉ) nᵉ) →
    is-sorted-vecᵉ Xᵉ vᵉ →
    is-sorted-listᵉ (list-vecᵉ nᵉ vᵉ)
  is-sorted-list-is-sorted-vecᵉ 0 vᵉ Sᵉ = raise-starᵉ
  is-sorted-list-is-sorted-vecᵉ 1 (xᵉ ∷ᵉ vᵉ) Sᵉ = raise-starᵉ
  is-sorted-list-is-sorted-vecᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)) (xᵉ ∷ᵉ yᵉ ∷ᵉ vᵉ) Sᵉ =
    pr1ᵉ Sᵉ ,ᵉ is-sorted-list-is-sorted-vecᵉ (succ-ℕᵉ nᵉ) (yᵉ ∷ᵉ vᵉ) (pr2ᵉ Sᵉ)
```