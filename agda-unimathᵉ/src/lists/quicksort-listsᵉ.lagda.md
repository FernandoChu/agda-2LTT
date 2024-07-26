# Quicksort for lists

```agda
module lists.quicksort-listsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ
open import elementary-number-theory.strong-induction-natural-numbersᵉ

open import foundation.coproduct-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import lists.concatenation-listsᵉ
open import lists.listsᵉ

open import order-theory.decidable-total-ordersᵉ
```

</details>

## Idea

Quicksortᵉ isᵉ aᵉ sortingᵉ algorithmᵉ onᵉ listsᵉ thatᵉ worksᵉ byᵉ selectingᵉ aᵉ pivotingᵉ
element,ᵉ dividingᵉ theᵉ listᵉ intoᵉ elementsᵉ smallerᵉ thanᵉ theᵉ pivotingᵉ elementᵉ andᵉ
elementsᵉ greaterᵉ thanᵉ theᵉ pivotingᵉ element,ᵉ andᵉ sortingᵉ thoseᵉ twoᵉ listsᵉ byᵉ againᵉ
applyingᵉ theᵉ quicksortᵉ algorithm.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Xᵉ : Decidable-Total-Orderᵉ l1ᵉ l2ᵉ)
  where

  helper-quicksort-list-divide-leqᵉ :
    (xᵉ : type-Decidable-Total-Orderᵉ Xᵉ) →
    (yᵉ : type-Decidable-Total-Orderᵉ Xᵉ) →
    leq-or-strict-greater-Decidable-Posetᵉ Xᵉ xᵉ yᵉ →
    listᵉ (type-Decidable-Total-Orderᵉ Xᵉ) →
    listᵉ (type-Decidable-Total-Orderᵉ Xᵉ)
  helper-quicksort-list-divide-leqᵉ xᵉ yᵉ (inlᵉ pᵉ) lᵉ = lᵉ
  helper-quicksort-list-divide-leqᵉ xᵉ yᵉ (inrᵉ pᵉ) lᵉ = consᵉ yᵉ lᵉ

  quicksort-list-divide-leqᵉ :
    type-Decidable-Total-Orderᵉ Xᵉ → listᵉ (type-Decidable-Total-Orderᵉ Xᵉ) →
    listᵉ (type-Decidable-Total-Orderᵉ Xᵉ)
  quicksort-list-divide-leqᵉ xᵉ nilᵉ = nilᵉ
  quicksort-list-divide-leqᵉ xᵉ (consᵉ yᵉ lᵉ) =
    helper-quicksort-list-divide-leqᵉ
      ( xᵉ)
      ( yᵉ)
      ( is-leq-or-strict-greater-Decidable-Total-Orderᵉ Xᵉ xᵉ yᵉ)
      ( quicksort-list-divide-leqᵉ xᵉ lᵉ)

  helper-quicksort-list-divide-strict-greaterᵉ :
    (xᵉ : type-Decidable-Total-Orderᵉ Xᵉ) →
    (yᵉ : type-Decidable-Total-Orderᵉ Xᵉ) →
    leq-or-strict-greater-Decidable-Posetᵉ Xᵉ xᵉ yᵉ →
    listᵉ (type-Decidable-Total-Orderᵉ Xᵉ) →
    listᵉ (type-Decidable-Total-Orderᵉ Xᵉ)
  helper-quicksort-list-divide-strict-greaterᵉ xᵉ yᵉ (inlᵉ pᵉ) lᵉ = consᵉ yᵉ lᵉ
  helper-quicksort-list-divide-strict-greaterᵉ xᵉ yᵉ (inrᵉ pᵉ) lᵉ = lᵉ

  quicksort-list-divide-strict-greaterᵉ :
    type-Decidable-Total-Orderᵉ Xᵉ → listᵉ (type-Decidable-Total-Orderᵉ Xᵉ) →
    listᵉ (type-Decidable-Total-Orderᵉ Xᵉ)
  quicksort-list-divide-strict-greaterᵉ xᵉ nilᵉ = nilᵉ
  quicksort-list-divide-strict-greaterᵉ xᵉ (consᵉ yᵉ lᵉ) =
    helper-quicksort-list-divide-strict-greaterᵉ
      ( xᵉ)
      ( yᵉ)
      ( is-leq-or-strict-greater-Decidable-Total-Orderᵉ Xᵉ xᵉ yᵉ)
      ( quicksort-list-divide-strict-greaterᵉ xᵉ lᵉ)

  private
    helper-inequality-length-quicksort-list-divide-leqᵉ :
      (xᵉ : type-Decidable-Total-Orderᵉ Xᵉ) →
      (yᵉ : type-Decidable-Total-Orderᵉ Xᵉ) →
      (pᵉ : leq-or-strict-greater-Decidable-Posetᵉ Xᵉ xᵉ yᵉ) →
      (lᵉ : listᵉ (type-Decidable-Total-Orderᵉ Xᵉ)) →
      length-listᵉ (helper-quicksort-list-divide-leqᵉ xᵉ yᵉ pᵉ lᵉ) ≤-ℕᵉ
      length-listᵉ (consᵉ yᵉ lᵉ)
    helper-inequality-length-quicksort-list-divide-leqᵉ xᵉ yᵉ (inlᵉ _) lᵉ =
      succ-leq-ℕᵉ (length-listᵉ lᵉ)
    helper-inequality-length-quicksort-list-divide-leqᵉ xᵉ yᵉ (inrᵉ _) lᵉ =
      refl-leq-ℕᵉ (length-listᵉ (consᵉ yᵉ lᵉ))

    inequality-length-quicksort-list-divide-leqᵉ :
      (xᵉ : type-Decidable-Total-Orderᵉ Xᵉ) →
      (lᵉ : listᵉ (type-Decidable-Total-Orderᵉ Xᵉ)) →
      length-listᵉ (quicksort-list-divide-leqᵉ xᵉ lᵉ) ≤-ℕᵉ length-listᵉ lᵉ
    inequality-length-quicksort-list-divide-leqᵉ xᵉ nilᵉ = starᵉ
    inequality-length-quicksort-list-divide-leqᵉ xᵉ (consᵉ yᵉ lᵉ) =
      transitive-leq-ℕᵉ
        ( length-listᵉ (quicksort-list-divide-leqᵉ xᵉ (consᵉ yᵉ lᵉ)))
        ( length-listᵉ (consᵉ yᵉ (quicksort-list-divide-leqᵉ xᵉ lᵉ)))
        ( length-listᵉ (consᵉ yᵉ lᵉ))
        ( inequality-length-quicksort-list-divide-leqᵉ xᵉ lᵉ)
        ( helper-inequality-length-quicksort-list-divide-leqᵉ
            ( xᵉ)
            ( yᵉ)
            ( is-leq-or-strict-greater-Decidable-Total-Orderᵉ Xᵉ xᵉ yᵉ)
            ( quicksort-list-divide-leqᵉ xᵉ lᵉ))

    helper-inequality-length-quicksort-list-divide-strict-greaterᵉ :
      (xᵉ : type-Decidable-Total-Orderᵉ Xᵉ) →
      (yᵉ : type-Decidable-Total-Orderᵉ Xᵉ) →
      (pᵉ : leq-or-strict-greater-Decidable-Posetᵉ Xᵉ xᵉ yᵉ) →
      (lᵉ : listᵉ (type-Decidable-Total-Orderᵉ Xᵉ)) →
      length-listᵉ (helper-quicksort-list-divide-strict-greaterᵉ xᵉ yᵉ pᵉ lᵉ) ≤-ℕᵉ
      length-listᵉ (consᵉ yᵉ lᵉ)
    helper-inequality-length-quicksort-list-divide-strict-greaterᵉ
      ( xᵉ)
      ( yᵉ)
      ( inlᵉ _)
      ( lᵉ) =
      refl-leq-ℕᵉ (length-listᵉ (consᵉ yᵉ lᵉ))
    helper-inequality-length-quicksort-list-divide-strict-greaterᵉ
      ( xᵉ)
      ( yᵉ)
      ( inrᵉ _)
      ( lᵉ) =
      succ-leq-ℕᵉ (length-listᵉ lᵉ)

    inequality-length-quicksort-list-divide-strict-greaterᵉ :
      (xᵉ : type-Decidable-Total-Orderᵉ Xᵉ) →
      (lᵉ : listᵉ (type-Decidable-Total-Orderᵉ Xᵉ)) →
      length-listᵉ (quicksort-list-divide-strict-greaterᵉ xᵉ lᵉ) ≤-ℕᵉ length-listᵉ lᵉ
    inequality-length-quicksort-list-divide-strict-greaterᵉ xᵉ nilᵉ = starᵉ
    inequality-length-quicksort-list-divide-strict-greaterᵉ xᵉ (consᵉ yᵉ lᵉ) =
      transitive-leq-ℕᵉ
        ( length-listᵉ (quicksort-list-divide-strict-greaterᵉ xᵉ (consᵉ yᵉ lᵉ)))
        ( length-listᵉ (consᵉ yᵉ (quicksort-list-divide-strict-greaterᵉ xᵉ lᵉ)))
        ( length-listᵉ (consᵉ yᵉ lᵉ))
        ( inequality-length-quicksort-list-divide-strict-greaterᵉ xᵉ lᵉ)
        ( helper-inequality-length-quicksort-list-divide-strict-greaterᵉ
            ( xᵉ)
            ( yᵉ)
            ( is-leq-or-strict-greater-Decidable-Total-Orderᵉ Xᵉ xᵉ yᵉ)
            ( quicksort-list-divide-strict-greaterᵉ xᵉ lᵉ))

  base-quicksort-listᵉ :
    (lᵉ : listᵉ (type-Decidable-Total-Orderᵉ Xᵉ)) → zero-ℕᵉ ＝ᵉ length-listᵉ lᵉ →
    listᵉ (type-Decidable-Total-Orderᵉ Xᵉ)
  base-quicksort-listᵉ nilᵉ xᵉ = nilᵉ

  inductive-step-quicksort-listᵉ :
    (kᵉ : ℕᵉ) →
    □-≤-ℕᵉ
      ( λ nᵉ →
        (lᵉ : listᵉ (type-Decidable-Total-Orderᵉ Xᵉ)) →
        nᵉ ＝ᵉ length-listᵉ lᵉ → listᵉ (type-Decidable-Total-Orderᵉ Xᵉ))
      ( kᵉ) →
    (lᵉ : listᵉ (type-Decidable-Total-Orderᵉ Xᵉ)) →
    succ-ℕᵉ kᵉ ＝ᵉ length-listᵉ lᵉ → listᵉ (type-Decidable-Total-Orderᵉ Xᵉ)
  inductive-step-quicksort-listᵉ kᵉ sortᵉ (consᵉ xᵉ lᵉ) pᵉ =
    concat-listᵉ
      ( sortᵉ
          ( length-listᵉ (quicksort-list-divide-leqᵉ xᵉ lᵉ))
          ( transitive-leq-ℕᵉ
              ( length-listᵉ (quicksort-list-divide-leqᵉ xᵉ lᵉ))
              ( length-listᵉ lᵉ)
              ( kᵉ)
              ( leq-eq-ℕᵉ (length-listᵉ lᵉ) kᵉ (is-injective-succ-ℕᵉ (invᵉ pᵉ)))
              ( inequality-length-quicksort-list-divide-leqᵉ xᵉ lᵉ))
          ( quicksort-list-divide-leqᵉ xᵉ lᵉ)
          ( reflᵉ))
      ( consᵉ
          ( xᵉ)
          ( sortᵉ
              ( length-listᵉ (quicksort-list-divide-strict-greaterᵉ xᵉ lᵉ))
              ( transitive-leq-ℕᵉ
                  ( length-listᵉ (quicksort-list-divide-strict-greaterᵉ xᵉ lᵉ))
                  ( length-listᵉ lᵉ)
                  ( kᵉ)
                  ( leq-eq-ℕᵉ (length-listᵉ lᵉ) kᵉ (is-injective-succ-ℕᵉ (invᵉ pᵉ)))
                  ( inequality-length-quicksort-list-divide-strict-greaterᵉ xᵉ lᵉ))
              ( quicksort-list-divide-strict-greaterᵉ xᵉ lᵉ)
              ( reflᵉ)))

  quicksort-listᵉ :
    listᵉ (type-Decidable-Total-Orderᵉ Xᵉ) →
    listᵉ (type-Decidable-Total-Orderᵉ Xᵉ)
  quicksort-listᵉ lᵉ =
    strong-ind-ℕᵉ
      ( λ nᵉ →
        (lᵉ : listᵉ (type-Decidable-Total-Orderᵉ Xᵉ)) → nᵉ ＝ᵉ length-listᵉ lᵉ →
        listᵉ (type-Decidable-Total-Orderᵉ Xᵉ))
      ( base-quicksort-listᵉ)
      ( inductive-step-quicksort-listᵉ)
      ( length-listᵉ lᵉ)
      ( lᵉ)
      ( reflᵉ)
```