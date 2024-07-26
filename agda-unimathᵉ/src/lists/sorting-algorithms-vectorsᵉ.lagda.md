# Sorting algorithms for vectors

```agda
module lists.sorting-algorithms-vectorsᵉ where
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

open import lists.permutation-vectorsᵉ
open import lists.sorted-vectorsᵉ

open import order-theory.decidable-total-ordersᵉ
```

</details>

## Idea

Aᵉ functionᵉ `f`ᵉ onᵉ vectorsᵉ isᵉ aᵉ **sort**ᵉ ifᵉ `f`ᵉ isᵉ aᵉ permutationᵉ andᵉ ifᵉ forᵉ everyᵉ
vectorᵉ `v`,ᵉ `fᵉ v`ᵉ isᵉ sorted.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level}
  (Xᵉ : Decidable-Total-Orderᵉ l1ᵉ l2ᵉ)
  (fᵉ :
      {nᵉ : ℕᵉ} →
      vecᵉ (type-Decidable-Total-Orderᵉ Xᵉ) nᵉ →
      vecᵉ (type-Decidable-Total-Orderᵉ Xᵉ) nᵉ)
  where

  is-sort-vecᵉ :
    UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-sort-vecᵉ =
    (nᵉ : ℕᵉ) →
    is-permutation-vecᵉ nᵉ fᵉ ×ᵉ
    ((vᵉ : vecᵉ (type-Decidable-Total-Orderᵉ Xᵉ) nᵉ) → is-sorted-vecᵉ Xᵉ (fᵉ vᵉ))

  is-permutation-vec-is-sort-vecᵉ :
    is-sort-vecᵉ → (nᵉ : ℕᵉ) → is-permutation-vecᵉ nᵉ fᵉ
  is-permutation-vec-is-sort-vecᵉ Sᵉ nᵉ = pr1ᵉ (Sᵉ nᵉ)

  permutation-vec-is-sort-vecᵉ :
    is-sort-vecᵉ → (nᵉ : ℕᵉ) → vecᵉ (type-Decidable-Total-Orderᵉ Xᵉ) nᵉ → Permutationᵉ nᵉ
  permutation-vec-is-sort-vecᵉ Sᵉ nᵉ vᵉ =
    permutation-is-permutation-vecᵉ nᵉ fᵉ (is-permutation-vec-is-sort-vecᵉ Sᵉ nᵉ) vᵉ

  eq-permute-vec-permutation-is-sort-vecᵉ :
    (Sᵉ : is-sort-vecᵉ) (nᵉ : ℕᵉ) (vᵉ : vecᵉ (type-Decidable-Total-Orderᵉ Xᵉ) nᵉ) →
    fᵉ vᵉ ＝ᵉ permute-vecᵉ nᵉ vᵉ (permutation-vec-is-sort-vecᵉ Sᵉ nᵉ vᵉ)
  eq-permute-vec-permutation-is-sort-vecᵉ Sᵉ nᵉ vᵉ =
    eq-permute-vec-permutation-is-permutation-vecᵉ
      ( nᵉ)
      ( fᵉ)
      ( is-permutation-vec-is-sort-vecᵉ Sᵉ nᵉ) vᵉ

  is-sorting-vec-is-sort-vecᵉ :
    is-sort-vecᵉ → (nᵉ : ℕᵉ) →
    (vᵉ : vecᵉ (type-Decidable-Total-Orderᵉ Xᵉ) nᵉ) → is-sorted-vecᵉ Xᵉ (fᵉ vᵉ)
  is-sorting-vec-is-sort-vecᵉ Sᵉ nᵉ = pr2ᵉ (Sᵉ nᵉ)
```