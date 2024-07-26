# Sort by insertion for vectors

```agda
module lists.sort-by-insertion-vectorsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import finite-group-theory.permutations-standard-finite-typesᵉ
open import finite-group-theory.transpositions-standard-finite-typesᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.coproduct-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.functoriality-coproduct-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import linear-algebra.vectorsᵉ

open import lists.permutation-vectorsᵉ
open import lists.sorted-vectorsᵉ
open import lists.sorting-algorithms-vectorsᵉ

open import order-theory.decidable-total-ordersᵉ
```

</details>

## Idea

Sortᵉ byᵉ insertionᵉ isᵉ aᵉ recursiveᵉ sortᵉ onᵉ vectors.ᵉ Ifᵉ aᵉ vectorᵉ isᵉ emptyᵉ orᵉ with
onlyᵉ oneᵉ elementᵉ thenᵉ itᵉ isᵉ sorted.ᵉ Otherwise,ᵉ weᵉ recursivelyᵉ sortᵉ theᵉ tailᵉ ofᵉ
theᵉ vector.ᵉ Thenᵉ weᵉ compareᵉ theᵉ headᵉ ofᵉ theᵉ vectorᵉ to theᵉ headᵉ ofᵉ theᵉ sortedᵉ
tail.ᵉ Ifᵉ theᵉ headᵉ isᵉ lessᵉ orᵉ equalᵉ thanᵉ theᵉ headᵉ ofᵉ theᵉ tailᵉ theᵉ vectorᵉ isᵉ
sorted.ᵉ Otherwiseᵉ weᵉ permuteᵉ theᵉ twoᵉ elementsᵉ andᵉ weᵉ recursivelyᵉ sortᵉ theᵉ tailᵉ
ofᵉ theᵉ vector.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Xᵉ : Decidable-Total-Orderᵉ l1ᵉ l2ᵉ)
  where

  helper-insertion-sort-vecᵉ :
    {nᵉ : ℕᵉ}
    (xᵉ yᵉ : type-Decidable-Total-Orderᵉ Xᵉ)
    (lᵉ : vecᵉ (type-Decidable-Total-Orderᵉ Xᵉ) nᵉ) →
    leq-or-strict-greater-Decidable-Posetᵉ Xᵉ xᵉ yᵉ →
    vecᵉ (type-Decidable-Total-Orderᵉ Xᵉ) (succ-ℕᵉ (succ-ℕᵉ (nᵉ)))
  helper-insertion-sort-vecᵉ xᵉ yᵉ lᵉ (inlᵉ pᵉ) = xᵉ ∷ᵉ yᵉ ∷ᵉ lᵉ
  helper-insertion-sort-vecᵉ {0ᵉ} xᵉ yᵉ empty-vecᵉ (inrᵉ pᵉ) = yᵉ ∷ᵉ xᵉ ∷ᵉ empty-vecᵉ
  helper-insertion-sort-vecᵉ {succ-ℕᵉ nᵉ} xᵉ yᵉ (zᵉ ∷ᵉ lᵉ) (inrᵉ pᵉ) =
    yᵉ ∷ᵉ
    ( helper-insertion-sort-vecᵉ
      ( xᵉ)
      ( zᵉ)
      ( lᵉ)
      ( is-leq-or-strict-greater-Decidable-Total-Orderᵉ Xᵉ xᵉ zᵉ))

  insertion-sort-vecᵉ :
    {nᵉ : ℕᵉ} →
    vecᵉ (type-Decidable-Total-Orderᵉ Xᵉ) nᵉ →
    vecᵉ (type-Decidable-Total-Orderᵉ Xᵉ) nᵉ
  insertion-sort-vecᵉ {zero-ℕᵉ} empty-vecᵉ = empty-vecᵉ
  insertion-sort-vecᵉ {1ᵉ} lᵉ = lᵉ
  insertion-sort-vecᵉ {succ-ℕᵉ (succ-ℕᵉ nᵉ)} (xᵉ ∷ᵉ yᵉ ∷ᵉ lᵉ) =
    helper-insertion-sort-vecᵉ
      ( xᵉ)
      ( head-vecᵉ (insertion-sort-vecᵉ (yᵉ ∷ᵉ lᵉ)))
      ( tail-vecᵉ (insertion-sort-vecᵉ (yᵉ ∷ᵉ lᵉ)))
      ( is-leq-or-strict-greater-Decidable-Total-Orderᵉ Xᵉ _ _)
```

## Properties

### Sort by insertion is a permutation

```agda
  helper-permutation-insertion-sort-vecᵉ :
    {nᵉ : ℕᵉ}
    (xᵉ yᵉ : type-Decidable-Total-Orderᵉ Xᵉ)
    (lᵉ : vecᵉ (type-Decidable-Total-Orderᵉ Xᵉ) nᵉ) →
    leq-or-strict-greater-Decidable-Posetᵉ Xᵉ xᵉ yᵉ →
    Permutationᵉ (succ-ℕᵉ (succ-ℕᵉ (nᵉ)))
  helper-permutation-insertion-sort-vecᵉ xᵉ yᵉ lᵉ (inlᵉ _) = id-equivᵉ
  helper-permutation-insertion-sort-vecᵉ {0ᵉ} xᵉ yᵉ empty-vecᵉ (inrᵉ _) =
    swap-two-last-elements-transposition-Finᵉ 0
  helper-permutation-insertion-sort-vecᵉ {succ-ℕᵉ nᵉ} xᵉ yᵉ (zᵉ ∷ᵉ lᵉ) (inrᵉ _) =
    ( ( swap-two-last-elements-transposition-Finᵉ (succ-ℕᵉ nᵉ)) ∘eᵉ
      ( ( equiv-coproductᵉ
          ( helper-permutation-insertion-sort-vecᵉ
            ( xᵉ)
            ( zᵉ)
            ( lᵉ)
            ( is-leq-or-strict-greater-Decidable-Total-Orderᵉ Xᵉ xᵉ zᵉ))
          ( id-equivᵉ))))

  permutation-insertion-sort-vecᵉ :
    {nᵉ : ℕᵉ}
    (vᵉ : vecᵉ (type-Decidable-Total-Orderᵉ Xᵉ) nᵉ) →
    Permutationᵉ nᵉ
  permutation-insertion-sort-vecᵉ {zero-ℕᵉ} empty-vecᵉ = id-equivᵉ
  permutation-insertion-sort-vecᵉ {1ᵉ} lᵉ = id-equivᵉ
  permutation-insertion-sort-vecᵉ {succ-ℕᵉ (succ-ℕᵉ nᵉ)} (xᵉ ∷ᵉ yᵉ ∷ᵉ lᵉ) =
    equiv-coproductᵉ
      ( permutation-insertion-sort-vecᵉ (yᵉ ∷ᵉ lᵉ))
      ( id-equivᵉ) ∘eᵉ
    helper-permutation-insertion-sort-vecᵉ
      ( xᵉ)
      ( head-vecᵉ (insertion-sort-vecᵉ (yᵉ ∷ᵉ lᵉ)))
      ( tail-vecᵉ (insertion-sort-vecᵉ (yᵉ ∷ᵉ lᵉ)))
      ( is-leq-or-strict-greater-Decidable-Total-Orderᵉ Xᵉ _ _)

  helper-eq-permute-vec-permutation-insertion-sort-vecᵉ :
    {nᵉ : ℕᵉ}
    (xᵉ yᵉ : type-Decidable-Total-Orderᵉ Xᵉ)
    (vᵉ : vecᵉ (type-Decidable-Total-Orderᵉ Xᵉ) nᵉ)
    (pᵉ : leq-or-strict-greater-Decidable-Posetᵉ Xᵉ xᵉ yᵉ) →
    helper-insertion-sort-vecᵉ xᵉ yᵉ vᵉ pᵉ ＝ᵉ
    permute-vecᵉ
      ( succ-ℕᵉ (succ-ℕᵉ nᵉ))
      ( xᵉ ∷ᵉ yᵉ ∷ᵉ vᵉ)
      ( helper-permutation-insertion-sort-vecᵉ xᵉ yᵉ vᵉ pᵉ)
  helper-eq-permute-vec-permutation-insertion-sort-vecᵉ xᵉ yᵉ vᵉ (inlᵉ _) =
    invᵉ (compute-permute-vec-id-equivᵉ (succ-ℕᵉ (succ-ℕᵉ _)) (xᵉ ∷ᵉ yᵉ ∷ᵉ vᵉ))
  helper-eq-permute-vec-permutation-insertion-sort-vecᵉ
    {0ᵉ}
    ( xᵉ)
    ( yᵉ)
    ( empty-vecᵉ)
    ( inrᵉ _) =
    reflᵉ
  helper-eq-permute-vec-permutation-insertion-sort-vecᵉ
    {succ-ℕᵉ nᵉ}
    ( xᵉ)
    ( yᵉ)
    ( zᵉ ∷ᵉ vᵉ)
    ( inrᵉ pᵉ) =
    eq-Eq-vecᵉ
      ( succ-ℕᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)))
      ( helper-insertion-sort-vecᵉ xᵉ yᵉ (zᵉ ∷ᵉ vᵉ) (inrᵉ pᵉ))
      ( permute-vecᵉ
        ( succ-ℕᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)))
        ( xᵉ ∷ᵉ yᵉ ∷ᵉ zᵉ ∷ᵉ vᵉ)
        ( helper-permutation-insertion-sort-vecᵉ xᵉ yᵉ (zᵉ ∷ᵉ vᵉ) (inrᵉ pᵉ)))
      ( reflᵉ ,ᵉ
        Eq-eq-vecᵉ
          ( succ-ℕᵉ (succ-ℕᵉ nᵉ))
          ( helper-insertion-sort-vecᵉ
            ( xᵉ)
            ( zᵉ)
            ( vᵉ)
            ( is-leq-or-strict-greater-Decidable-Total-Orderᵉ Xᵉ xᵉ zᵉ))
          ( tail-vecᵉ
            ( permute-vecᵉ
              ( succ-ℕᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)))
              ( xᵉ ∷ᵉ yᵉ ∷ᵉ zᵉ ∷ᵉ vᵉ)
              ( helper-permutation-insertion-sort-vecᵉ xᵉ yᵉ (zᵉ ∷ᵉ vᵉ) (inrᵉ pᵉ))))
          ( ( helper-eq-permute-vec-permutation-insertion-sort-vecᵉ
              ( xᵉ)
              ( zᵉ)
              ( vᵉ)
              ( is-leq-or-strict-greater-Decidable-Total-Orderᵉ Xᵉ xᵉ zᵉ)) ∙ᵉ
            ( apᵉ
              ( tail-vecᵉ)
              ( ap-permute-vecᵉ
                ( equiv-coproductᵉ
                  ( helper-permutation-insertion-sort-vecᵉ
                    ( xᵉ)
                    ( zᵉ)
                    ( vᵉ)
                    ( is-leq-or-strict-greater-Decidable-Total-Orderᵉ
                      ( Xᵉ)
                      ( xᵉ)
                      ( zᵉ)))
                  ( id-equivᵉ))
                ( invᵉ
                  ( compute-swap-two-last-elements-transposition-Fin-permute-vecᵉ
                    (succ-ℕᵉ nᵉ)
                    ( zᵉ ∷ᵉ vᵉ)
                    ( xᵉ)
                    ( yᵉ))) ∙ᵉ
                ( invᵉ
                  ( compute-composition-permute-vecᵉ
                    (succ-ℕᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)))
                    ( xᵉ ∷ᵉ yᵉ ∷ᵉ zᵉ ∷ᵉ vᵉ)
                    ( swap-two-last-elements-transposition-Finᵉ (succ-ℕᵉ nᵉ))
                    ( equiv-coproductᵉ
                      ( helper-permutation-insertion-sort-vecᵉ
                        ( xᵉ)
                        ( zᵉ)
                        ( vᵉ)
                        ( is-leq-or-strict-greater-Decidable-Total-Orderᵉ
                          ( Xᵉ)
                          ( xᵉ)
                          ( zᵉ)))
                        ( id-equivᵉ))))))))

  eq-permute-vec-permutation-insertion-sort-vecᵉ :
    {nᵉ : ℕᵉ}
    (vᵉ : vecᵉ (type-Decidable-Total-Orderᵉ Xᵉ) nᵉ) →
    insertion-sort-vecᵉ vᵉ ＝ᵉ permute-vecᵉ nᵉ vᵉ (permutation-insertion-sort-vecᵉ vᵉ)
  eq-permute-vec-permutation-insertion-sort-vecᵉ {0ᵉ} empty-vecᵉ = reflᵉ
  eq-permute-vec-permutation-insertion-sort-vecᵉ {1ᵉ} (xᵉ ∷ᵉ empty-vecᵉ) = reflᵉ
  eq-permute-vec-permutation-insertion-sort-vecᵉ
    {succ-ℕᵉ (succ-ℕᵉ nᵉ)}
    ( xᵉ ∷ᵉ yᵉ ∷ᵉ vᵉ) =
    ( ( helper-eq-permute-vec-permutation-insertion-sort-vecᵉ
        ( xᵉ)
        ( head-vecᵉ (insertion-sort-vecᵉ (yᵉ ∷ᵉ vᵉ)))
        ( tail-vecᵉ (insertion-sort-vecᵉ (yᵉ ∷ᵉ vᵉ)))
        ( is-leq-or-strict-greater-Decidable-Total-Orderᵉ Xᵉ _ _)) ∙ᵉ
      ( ( ap-permute-vecᵉ
          ( helper-permutation-insertion-sort-vecᵉ
            ( xᵉ)
            ( head-vecᵉ (insertion-sort-vecᵉ (yᵉ ∷ᵉ vᵉ)))
            ( tail-vecᵉ (insertion-sort-vecᵉ (yᵉ ∷ᵉ vᵉ)))
            ( is-leq-or-strict-greater-Decidable-Total-Orderᵉ Xᵉ _ _))
          ( apᵉ
            ( λ lᵉ → xᵉ ∷ᵉ lᵉ)
            ( cons-head-tail-vecᵉ nᵉ (insertion-sort-vecᵉ (yᵉ ∷ᵉ vᵉ)) ∙ᵉ
              eq-permute-vec-permutation-insertion-sort-vecᵉ (yᵉ ∷ᵉ vᵉ)))) ∙ᵉ
        ( ( invᵉ
            ( compute-composition-permute-vecᵉ
              (succ-ℕᵉ (succ-ℕᵉ nᵉ))
              ( xᵉ ∷ᵉ yᵉ ∷ᵉ vᵉ)
              ( equiv-coproductᵉ
                ( permutation-insertion-sort-vecᵉ (yᵉ ∷ᵉ vᵉ))
                ( id-equivᵉ))
              ( helper-permutation-insertion-sort-vecᵉ
                ( xᵉ)
                ( head-vecᵉ (insertion-sort-vecᵉ (yᵉ ∷ᵉ vᵉ)))
                ( tail-vecᵉ (insertion-sort-vecᵉ (yᵉ ∷ᵉ vᵉ)))
                ( is-leq-or-strict-greater-Decidable-Total-Orderᵉ Xᵉ _ _)))))))
```

### Sort by insertion is sorting vectors

```agda
  helper-is-sorting-insertion-sort-vecᵉ :
    {nᵉ : ℕᵉ}
    (xᵉ yᵉ : type-Decidable-Total-Orderᵉ Xᵉ)
    (vᵉ : vecᵉ (type-Decidable-Total-Orderᵉ Xᵉ) nᵉ) →
    (pᵉ : leq-or-strict-greater-Decidable-Posetᵉ Xᵉ xᵉ yᵉ) →
    is-sorted-vecᵉ Xᵉ (yᵉ ∷ᵉ vᵉ) →
    is-sorted-vecᵉ Xᵉ (helper-insertion-sort-vecᵉ xᵉ yᵉ vᵉ pᵉ)
  helper-is-sorting-insertion-sort-vecᵉ {0ᵉ} xᵉ yᵉ empty-vecᵉ (inlᵉ pᵉ) _ =
    pᵉ ,ᵉ raise-starᵉ
  helper-is-sorting-insertion-sort-vecᵉ {0ᵉ} xᵉ yᵉ empty-vecᵉ (inrᵉ pᵉ) _ =
    pr2ᵉ pᵉ ,ᵉ raise-starᵉ
  helper-is-sorting-insertion-sort-vecᵉ {succ-ℕᵉ nᵉ} xᵉ yᵉ lᵉ (inlᵉ pᵉ) sᵉ =
    pᵉ ,ᵉ sᵉ
  helper-is-sorting-insertion-sort-vecᵉ {succ-ℕᵉ nᵉ} xᵉ yᵉ (zᵉ ∷ᵉ vᵉ) (inrᵉ pᵉ) sᵉ =
    is-sorted-vec-is-sorted-least-element-vecᵉ
      ( Xᵉ)
      ( helper-insertion-sort-vecᵉ xᵉ yᵉ (zᵉ ∷ᵉ vᵉ) (inrᵉ pᵉ))
      ( trᵉ
        ( is-least-element-vecᵉ Xᵉ yᵉ)
        ( invᵉ
          ( helper-eq-permute-vec-permutation-insertion-sort-vecᵉ
            ( xᵉ)
            ( zᵉ)
            ( vᵉ)
            ( is-leq-or-strict-greater-Decidable-Total-Orderᵉ Xᵉ xᵉ zᵉ)))
        ( is-least-element-permute-vecᵉ
          ( Xᵉ)
          ( yᵉ)
          ( xᵉ ∷ᵉ zᵉ ∷ᵉ vᵉ)
          ( helper-permutation-insertion-sort-vecᵉ
            ( xᵉ)
            ( zᵉ)
            ( vᵉ)
            ( is-leq-or-strict-greater-Decidable-Total-Orderᵉ Xᵉ xᵉ zᵉ))
          ( pr2ᵉ pᵉ ,ᵉ
            pr1ᵉ
              ( is-sorted-least-element-vec-is-sorted-vecᵉ
                ( Xᵉ)
                ( yᵉ ∷ᵉ zᵉ ∷ᵉ vᵉ)
                ( sᵉ)))) ,ᵉ
        ( is-sorted-least-element-vec-is-sorted-vecᵉ
          ( Xᵉ)
          ( helper-insertion-sort-vecᵉ
            ( xᵉ)
            ( zᵉ)
            ( vᵉ)
            ( is-leq-or-strict-greater-Decidable-Total-Orderᵉ Xᵉ xᵉ zᵉ))
          ( helper-is-sorting-insertion-sort-vecᵉ
            ( xᵉ)
            ( zᵉ)
            ( vᵉ)
            ( is-leq-or-strict-greater-Decidable-Total-Orderᵉ Xᵉ xᵉ zᵉ)
            ( is-sorted-tail-is-sorted-vecᵉ Xᵉ (yᵉ ∷ᵉ zᵉ ∷ᵉ vᵉ) sᵉ))))

  is-sorting-insertion-sort-vecᵉ :
    {nᵉ : ℕᵉ}
    (vᵉ : vecᵉ (type-Decidable-Total-Orderᵉ Xᵉ) nᵉ) →
    is-sorted-vecᵉ Xᵉ (insertion-sort-vecᵉ vᵉ)
  is-sorting-insertion-sort-vecᵉ {0ᵉ} vᵉ = raise-starᵉ
  is-sorting-insertion-sort-vecᵉ {1ᵉ} vᵉ = raise-starᵉ
  is-sorting-insertion-sort-vecᵉ {succ-ℕᵉ (succ-ℕᵉ nᵉ)} (xᵉ ∷ᵉ yᵉ ∷ᵉ vᵉ) =
    helper-is-sorting-insertion-sort-vecᵉ
      ( xᵉ)
      ( head-vecᵉ (insertion-sort-vecᵉ (yᵉ ∷ᵉ vᵉ)))
      ( tail-vecᵉ (insertion-sort-vecᵉ (yᵉ ∷ᵉ vᵉ)))
      ( is-leq-or-strict-greater-Decidable-Total-Orderᵉ Xᵉ _ _)
      ( trᵉ
        ( λ lᵉ → is-sorted-vecᵉ Xᵉ lᵉ)
        ( invᵉ (cons-head-tail-vecᵉ nᵉ (insertion-sort-vecᵉ (yᵉ ∷ᵉ vᵉ))))
        ( is-sorting-insertion-sort-vecᵉ (yᵉ ∷ᵉ vᵉ)))
```

### Sort by insertion is a sort

```agda
  is-sort-insertion-sort-vecᵉ :
    is-sort-vecᵉ Xᵉ (insertion-sort-vecᵉ)
  pr1ᵉ (pr1ᵉ (is-sort-insertion-sort-vecᵉ nᵉ) vᵉ) = permutation-insertion-sort-vecᵉ vᵉ
  pr2ᵉ (pr1ᵉ (is-sort-insertion-sort-vecᵉ nᵉ) vᵉ) =
    eq-permute-vec-permutation-insertion-sort-vecᵉ vᵉ
  pr2ᵉ (is-sort-insertion-sort-vecᵉ nᵉ) = is-sorting-insertion-sort-vecᵉ
```