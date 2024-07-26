# Sorting algorithms for lists

```agda
module lists.sorting-algorithms-listsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import finite-group-theory.permutations-standard-finite-typesᵉ

open import foundation.cartesian-product-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ

open import linear-algebra.vectorsᵉ

open import lists.arraysᵉ
open import lists.listsᵉ
open import lists.permutation-listsᵉ
open import lists.sorted-listsᵉ
open import lists.sorting-algorithms-vectorsᵉ

open import order-theory.decidable-total-ordersᵉ
```

</details>

## Idea

Inᵉ thisᵉ fileᵉ weᵉ defineᵉ theᵉ notionᵉ ofᵉ sortingᵉ algorithmsᵉ forᵉ lists.ᵉ

## Definition

Aᵉ functionᵉ `f`ᵉ fromᵉ `list`ᵉ to `list`ᵉ isᵉ aᵉ sortᵉ ifᵉ `f`ᵉ isᵉ aᵉ permutationᵉ andᵉ ifᵉ
forᵉ everyᵉ listᵉ `l`,ᵉ `fᵉ l`ᵉ isᵉ sortedᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level}
  (Xᵉ : Decidable-Total-Orderᵉ l1ᵉ l2ᵉ)
  (fᵉ :
      listᵉ (type-Decidable-Total-Orderᵉ Xᵉ) →
      listᵉ (type-Decidable-Total-Orderᵉ Xᵉ))
  where

  is-sort-listᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-sort-listᵉ =
    is-permutation-listᵉ fᵉ ×ᵉ
    ((lᵉ : listᵉ (type-Decidable-Total-Orderᵉ Xᵉ)) → is-sorted-listᵉ Xᵉ (fᵉ lᵉ))

  is-permutation-list-is-sort-listᵉ :
    is-sort-listᵉ → is-permutation-listᵉ fᵉ
  is-permutation-list-is-sort-listᵉ Sᵉ = pr1ᵉ (Sᵉ)

  permutation-list-is-sort-listᵉ :
    is-sort-listᵉ → (lᵉ : listᵉ (type-Decidable-Total-Orderᵉ Xᵉ)) →
    Permutationᵉ (length-listᵉ lᵉ)
  permutation-list-is-sort-listᵉ Sᵉ lᵉ =
    permutation-is-permutation-listᵉ fᵉ (is-permutation-list-is-sort-listᵉ Sᵉ) lᵉ

  eq-permute-list-permutation-is-sort-listᵉ :
    (Sᵉ : is-sort-listᵉ) (lᵉ : listᵉ (type-Decidable-Total-Orderᵉ Xᵉ)) →
    fᵉ lᵉ ＝ᵉ permute-listᵉ lᵉ (permutation-list-is-sort-listᵉ Sᵉ lᵉ)
  eq-permute-list-permutation-is-sort-listᵉ Sᵉ lᵉ =
    eq-permute-list-permutation-is-permutation-listᵉ
      ( fᵉ)
      ( is-permutation-list-is-sort-listᵉ Sᵉ) lᵉ

  is-sorting-list-is-sort-listᵉ :
    is-sort-listᵉ →
    (lᵉ : listᵉ (type-Decidable-Total-Orderᵉ Xᵉ)) → is-sorted-listᵉ Xᵉ (fᵉ lᵉ)
  is-sorting-list-is-sort-listᵉ Sᵉ = pr2ᵉ (Sᵉ)
```

## Properties

### From sorting algorithms for vectors to sorting algorithms for lists

```agda
module _
  {l1ᵉ l2ᵉ : Level}
  (Xᵉ : Decidable-Total-Orderᵉ l1ᵉ l2ᵉ)
  where

  is-sort-list-is-sort-vecᵉ :
    (fᵉ :
      {nᵉ : ℕᵉ} →
      vecᵉ (type-Decidable-Total-Orderᵉ Xᵉ) nᵉ →
      vecᵉ (type-Decidable-Total-Orderᵉ Xᵉ) nᵉ) →
    is-sort-vecᵉ Xᵉ fᵉ →
    is-sort-listᵉ Xᵉ (λ lᵉ → list-vecᵉ (length-listᵉ lᵉ) (fᵉ (vec-listᵉ lᵉ)))
  pr1ᵉ (is-sort-list-is-sort-vecᵉ fᵉ Sᵉ) =
    is-permutation-list-is-permutation-vecᵉ
      ( λ nᵉ → fᵉ)
      ( λ nᵉ → pr1ᵉ (Sᵉ nᵉ))
  pr2ᵉ (is-sort-list-is-sort-vecᵉ fᵉ Sᵉ) lᵉ =
    is-sorted-list-is-sorted-vecᵉ
      ( Xᵉ)
      ( length-listᵉ lᵉ)
      ( fᵉ (vec-listᵉ lᵉ)) (pr2ᵉ (Sᵉ (length-listᵉ lᵉ)) (vec-listᵉ lᵉ))
```