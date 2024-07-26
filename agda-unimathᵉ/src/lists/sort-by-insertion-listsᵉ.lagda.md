# Sort by insertion for lists

```agda
module lists.sort-by-insertion-listsᵉ where
```

<details><summary>Imports</summary>

```agda
open import finite-group-theory.permutations-standard-finite-typesᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ

open import lists.arraysᵉ
open import lists.listsᵉ
open import lists.permutation-listsᵉ
open import lists.sort-by-insertion-vectorsᵉ
open import lists.sorted-listsᵉ
open import lists.sorting-algorithms-listsᵉ

open import order-theory.decidable-total-ordersᵉ
```

</details>

## Idea

Weᵉ useᵉ theᵉ definitionᵉ ofᵉ sortᵉ byᵉ insertionᵉ forᵉ vectorsᵉ
([`lists.sort-by-insertion-vectors`](lists.sort-by-insertion-vectors.mdᵉ)) andᵉ weᵉ
adaptᵉ itᵉ forᵉ lists.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Xᵉ : Decidable-Total-Orderᵉ l1ᵉ l2ᵉ)
  where

  insertion-sort-listᵉ :
    listᵉ (type-Decidable-Total-Orderᵉ Xᵉ) → listᵉ (type-Decidable-Total-Orderᵉ Xᵉ)
  insertion-sort-listᵉ lᵉ =
    list-vecᵉ (length-listᵉ lᵉ) (insertion-sort-vecᵉ Xᵉ (vec-listᵉ lᵉ))
```

## Properties

### Sort by insertion is a sort

```agda
  is-sort-insertion-sort-listᵉ :
    is-sort-listᵉ Xᵉ insertion-sort-listᵉ
  is-sort-insertion-sort-listᵉ =
    is-sort-list-is-sort-vecᵉ
      ( Xᵉ)
      ( insertion-sort-vecᵉ Xᵉ)
      ( is-sort-insertion-sort-vecᵉ Xᵉ)

  is-permutation-insertion-sort-listᵉ : is-permutation-listᵉ insertion-sort-listᵉ
  is-permutation-insertion-sort-listᵉ = pr1ᵉ (is-sort-insertion-sort-listᵉ)

  permutation-insertion-sort-listᵉ :
    (lᵉ : listᵉ (type-Decidable-Total-Orderᵉ Xᵉ)) →
    Permutationᵉ (length-listᵉ lᵉ)
  permutation-insertion-sort-listᵉ =
    permutation-list-is-sort-listᵉ
      Xᵉ
      insertion-sort-listᵉ
      is-sort-insertion-sort-listᵉ

  eq-permute-list-permutation-insertion-sort-listᵉ :
    (lᵉ : listᵉ (type-Decidable-Total-Orderᵉ Xᵉ)) →
    insertion-sort-listᵉ lᵉ ＝ᵉ permute-listᵉ lᵉ (permutation-insertion-sort-listᵉ lᵉ)
  eq-permute-list-permutation-insertion-sort-listᵉ =
    eq-permute-list-permutation-is-sort-listᵉ
      Xᵉ
      insertion-sort-listᵉ
      is-sort-insertion-sort-listᵉ

  is-sorting-insertion-sort-listᵉ :
    (lᵉ : listᵉ (type-Decidable-Total-Orderᵉ Xᵉ)) →
    is-sorted-listᵉ Xᵉ (insertion-sort-listᵉ lᵉ)
  is-sorting-insertion-sort-listᵉ = pr2ᵉ (is-sort-insertion-sort-listᵉ)
```