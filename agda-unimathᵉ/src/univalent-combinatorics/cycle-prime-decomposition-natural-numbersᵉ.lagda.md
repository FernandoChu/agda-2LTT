# Cycle prime decompositions of natural numbers

```agda
module univalent-combinatorics.cycle-prime-decomposition-natural-numbersᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.decidable-total-order-natural-numbersᵉ
open import elementary-number-theory.fundamental-theorem-of-arithmeticᵉ
open import elementary-number-theory.inequality-natural-numbersᵉ
open import elementary-number-theory.multiplication-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ

open import finite-group-theory.permutations-standard-finite-typesᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.cartesian-product-typesᵉ
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.identity-typesᵉ
open import foundation.iterated-cartesian-product-typesᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.univalenceᵉ
open import foundation.universe-levelsᵉ

open import group-theory.concrete-groupsᵉ
open import group-theory.iterated-cartesian-products-concrete-groupsᵉ

open import lists.arraysᵉ
open import lists.concatenation-listsᵉ
open import lists.functoriality-listsᵉ
open import lists.permutation-listsᵉ
open import lists.sort-by-insertion-listsᵉ

open import univalent-combinatorics.cyclic-finite-typesᵉ
```

</details>

## Idea

Letᵉ `n`ᵉ beᵉ aᵉ naturalᵉ number.ᵉ Theᵉ `cycle-prime-decomposition-ℕ`ᵉ ofᵉ `n`ᵉ isᵉ theᵉ
iteratedᵉ cartesianᵉ productᵉ ofᵉ theᵉ cyclicᵉ typesᵉ assocatedᵉ to theᵉ primeᵉ
decompositionᵉ ofᵉ `n`.ᵉ

## Definition

```agda
concrete-group-cycle-prime-decomposition-ℕᵉ :
  (nᵉ : ℕᵉ) → leq-ℕᵉ 1 nᵉ → Concrete-Groupᵉ (lsuc lzero)
concrete-group-cycle-prime-decomposition-ℕᵉ nᵉ Hᵉ =
  iterated-product-Concrete-Groupᵉ
    ( length-arrayᵉ
      ( array-listᵉ
        ( map-listᵉ
          ( concrete-group-Cyclic-Typeᵉ)
          ( list-fundamental-theorem-arithmetic-ℕᵉ nᵉ Hᵉ))))
    ( functional-vec-arrayᵉ
      ( array-listᵉ
        ( map-listᵉ
          ( concrete-group-Cyclic-Typeᵉ)
          ( list-fundamental-theorem-arithmetic-ℕᵉ nᵉ Hᵉ))))

cycle-prime-decomposition-ℕᵉ :
  (nᵉ : ℕᵉ) → leq-ℕᵉ 1 nᵉ → UUᵉ (lsuc lzero)
cycle-prime-decomposition-ℕᵉ nᵉ Hᵉ =
  iterated-product-listsᵉ
    ( map-listᵉ (Cyclic-Typeᵉ lzero) (list-fundamental-theorem-arithmetic-ℕᵉ nᵉ Hᵉ))
```

## Properties

### Cycle prime decomposition are closed under cartesian products

Theᵉ cartesianᵉ productᵉ ofᵉ theᵉ cycleᵉ primeᵉ decompositionᵉ ofᵉ `n`ᵉ andᵉ `m`ᵉ isᵉ equalᵉ
to theᵉ cycleᵉ primeᵉ decompositionᵉ ofᵉ `nᵉ *ℕᵉ m`.ᵉ

```agda
equiv-product-cycle-prime-decomposition-ℕᵉ :
  (nᵉ mᵉ : ℕᵉ) → (Hᵉ : leq-ℕᵉ 1 nᵉ) → (Iᵉ : leq-ℕᵉ 1 mᵉ) →
  ( cycle-prime-decomposition-ℕᵉ nᵉ Hᵉ ×ᵉ cycle-prime-decomposition-ℕᵉ mᵉ Iᵉ) ≃ᵉ
  cycle-prime-decomposition-ℕᵉ (nᵉ *ℕᵉ mᵉ) (preserves-leq-mul-ℕᵉ 1 nᵉ 1 mᵉ Hᵉ Iᵉ)
equiv-product-cycle-prime-decomposition-ℕᵉ nᵉ mᵉ Hᵉ Iᵉ =
  ( ( equiv-eqᵉ
      ( apᵉ
        ( λ pᵉ → iterated-product-listsᵉ (map-listᵉ (Cyclic-Typeᵉ lzero) pᵉ))
        ( ( invᵉ
            ( eq-permute-list-permutation-insertion-sort-listᵉ
              ( ℕ-Decidable-Total-Orderᵉ)
              ( concat-listᵉ
                ( list-fundamental-theorem-arithmetic-ℕᵉ nᵉ Hᵉ)
                ( list-fundamental-theorem-arithmetic-ℕᵉ mᵉ Iᵉ)))) ∙ᵉ
          ( apᵉ
            ( pr1ᵉ)
            ( eq-is-contr'ᵉ
              ( fundamental-theorem-arithmetic-list-ℕᵉ
                ( nᵉ *ℕᵉ mᵉ)
                ( preserves-leq-mul-ℕᵉ 1 nᵉ 1 mᵉ Hᵉ Iᵉ))
              ( prime-decomposition-list-sort-concatenation-ℕᵉ
                ( nᵉ)
                ( mᵉ)
                ( Hᵉ)
                ( Iᵉ)
                ( list-fundamental-theorem-arithmetic-ℕᵉ nᵉ Hᵉ)
                ( list-fundamental-theorem-arithmetic-ℕᵉ mᵉ Iᵉ)
                ( is-prime-decomposition-list-fundamental-theorem-arithmetic-ℕᵉ
                  nᵉ
                  Hᵉ)
                ( is-prime-decomposition-list-fundamental-theorem-arithmetic-ℕᵉ
                  mᵉ
                  Iᵉ))
              ( prime-decomposition-fundamental-theorem-arithmetic-list-ℕᵉ
                (nᵉ *ℕᵉ mᵉ)
                ( preserves-leq-mul-ℕᵉ 1 nᵉ 1 mᵉ Hᵉ Iᵉ))))))) ∘eᵉ
    ( equiv-eqᵉ
      ( apᵉ
        ( iterated-product-listsᵉ)
        ( eq-map-list-permute-listᵉ
          ( Cyclic-Typeᵉ lzero)
          ( concat-listᵉ
            ( list-fundamental-theorem-arithmetic-ℕᵉ nᵉ Hᵉ)
            ( list-fundamental-theorem-arithmetic-ℕᵉ mᵉ Iᵉ))
          ( permutation-insertion-sort-listᵉ
            ( ℕ-Decidable-Total-Orderᵉ)
            ( concat-listᵉ
              ( list-fundamental-theorem-arithmetic-ℕᵉ nᵉ Hᵉ)
              ( list-fundamental-theorem-arithmetic-ℕᵉ mᵉ Iᵉ))))) ∘eᵉ
      ( ( inv-equivᵉ
          ( equiv-permutation-iterated-product-listsᵉ
            ( map-listᵉ
              ( Cyclic-Typeᵉ lzero)
              ( concat-listᵉ
                ( list-fundamental-theorem-arithmetic-ℕᵉ nᵉ Hᵉ)
                ( list-fundamental-theorem-arithmetic-ℕᵉ mᵉ Iᵉ)))
            ( trᵉ
              ( Permutationᵉ)
              ( invᵉ
                ( length-map-listᵉ
                  ( Cyclic-Typeᵉ lzero)
                  ( concat-listᵉ
                    ( list-fundamental-theorem-arithmetic-ℕᵉ nᵉ Hᵉ)
                    ( list-fundamental-theorem-arithmetic-ℕᵉ mᵉ Iᵉ))))
              ( permutation-insertion-sort-listᵉ
                ( ℕ-Decidable-Total-Orderᵉ)
                ( concat-listᵉ
                  ( list-fundamental-theorem-arithmetic-ℕᵉ nᵉ Hᵉ)
                  ( list-fundamental-theorem-arithmetic-ℕᵉ mᵉ Iᵉ)))))) ∘eᵉ
        ( ( equiv-eqᵉ
            ( apᵉ
              ( iterated-product-listsᵉ)
              ( invᵉ
                ( preserves-concat-map-listᵉ
                  ( Cyclic-Typeᵉ lzero)
                  ( list-fundamental-theorem-arithmetic-ℕᵉ nᵉ Hᵉ)
                  ( list-fundamental-theorem-arithmetic-ℕᵉ mᵉ Iᵉ))))) ∘eᵉ
          ( equiv-product-iterated-product-listsᵉ
            ( map-listᵉ
              ( Cyclic-Typeᵉ lzero)
              ( list-fundamental-theorem-arithmetic-ℕᵉ nᵉ Hᵉ))
            ( map-listᵉ
              ( Cyclic-Typeᵉ lzero)
              ( list-fundamental-theorem-arithmetic-ℕᵉ mᵉ Iᵉ)))))))
```