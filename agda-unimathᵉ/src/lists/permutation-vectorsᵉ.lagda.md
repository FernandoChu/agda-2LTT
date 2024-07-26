# Permutations of vectors

```agda
module lists.permutation-vectorsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import finite-group-theory.permutations-standard-finite-typesᵉ
open import finite-group-theory.transpositions-standard-finite-typesᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.cartesian-product-typesᵉ
open import foundation.coproduct-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalence-extensionalityᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-coproduct-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.negated-equalityᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.universe-levelsᵉ

open import linear-algebra.functoriality-vectorsᵉ
open import linear-algebra.vectorsᵉ

open import lists.arraysᵉ
open import lists.listsᵉ

open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Givenᵉ anᵉ functionalᵉ vectorᵉ `t`ᵉ ofᵉ lengthᵉ `n`ᵉ andᵉ aᵉ automorphismᵉ `σ`ᵉ ofᵉ `Finᵉ n`,ᵉ
theᵉ permutationᵉ ofᵉ `t`ᵉ accordingᵉ to `σ`ᵉ isᵉ theᵉ functionalᵉ vectorᵉ where theᵉ indexᵉ
areᵉ permutedᵉ byᵉ `σ`.ᵉ Then,ᵉ weᵉ canᵉ defineᵉ whatᵉ isᵉ aᵉ permutationᵉ ofᵉ aᵉ vectorᵉ ofᵉ
lengthᵉ `n`ᵉ viaᵉ theᵉ equivalenceᵉ betweenᵉ functionalᵉ vectorsᵉ andᵉ vectors.ᵉ

## Definitions

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  permute-vecᵉ : (nᵉ : ℕᵉ) → vecᵉ Aᵉ nᵉ → Permutationᵉ nᵉ → vecᵉ Aᵉ nᵉ
  permute-vecᵉ nᵉ vᵉ sᵉ =
    listed-vec-functional-vecᵉ nᵉ (functional-vec-vecᵉ nᵉ vᵉ ∘ᵉ (map-equivᵉ sᵉ))
```

### The predicate that a function from `vec` to `vec` is just permuting vectors

```agda
  is-permutation-vecᵉ : (nᵉ : ℕᵉ) → (vecᵉ Aᵉ nᵉ → vecᵉ Aᵉ nᵉ) → UUᵉ lᵉ
  is-permutation-vecᵉ nᵉ fᵉ =
    (vᵉ : vecᵉ Aᵉ nᵉ) →
    Σᵉ ( Permutationᵉ nᵉ)
      ( λ tᵉ → fᵉ vᵉ ＝ᵉ permute-vecᵉ nᵉ vᵉ tᵉ)

  permutation-is-permutation-vecᵉ :
    (nᵉ : ℕᵉ) (fᵉ : vecᵉ Aᵉ nᵉ → vecᵉ Aᵉ nᵉ) → is-permutation-vecᵉ nᵉ fᵉ →
    (vᵉ : vecᵉ Aᵉ nᵉ) → Permutationᵉ nᵉ
  permutation-is-permutation-vecᵉ nᵉ fᵉ Pᵉ vᵉ = pr1ᵉ (Pᵉ vᵉ)

  eq-permute-vec-permutation-is-permutation-vecᵉ :
    (nᵉ : ℕᵉ) (fᵉ : vecᵉ Aᵉ nᵉ → vecᵉ Aᵉ nᵉ) → (Pᵉ : is-permutation-vecᵉ nᵉ fᵉ) →
    (vᵉ : vecᵉ Aᵉ nᵉ) →
    (fᵉ vᵉ ＝ᵉ permute-vecᵉ nᵉ vᵉ (permutation-is-permutation-vecᵉ nᵉ fᵉ Pᵉ vᵉ))
  eq-permute-vec-permutation-is-permutation-vecᵉ nᵉ fᵉ Pᵉ vᵉ = pr2ᵉ (Pᵉ vᵉ)
```

## Properties

### Computational rules

```agda
  compute-permute-vec-id-equivᵉ :
    (nᵉ : ℕᵉ)
    (vᵉ : vecᵉ Aᵉ nᵉ) →
    permute-vecᵉ nᵉ vᵉ id-equivᵉ ＝ᵉ vᵉ
  compute-permute-vec-id-equivᵉ nᵉ vᵉ =
    apᵉ (λ fᵉ → map-equivᵉ fᵉ vᵉ) (right-inverse-law-equivᵉ (compute-vecᵉ nᵉ))

  compute-composition-permute-vecᵉ :
    (nᵉ : ℕᵉ)
    (vᵉ : vecᵉ Aᵉ nᵉ) →
    (aᵉ bᵉ : Permutationᵉ nᵉ) →
    permute-vecᵉ nᵉ vᵉ (aᵉ ∘eᵉ bᵉ) ＝ᵉ permute-vecᵉ nᵉ (permute-vecᵉ nᵉ vᵉ aᵉ) bᵉ
  compute-composition-permute-vecᵉ nᵉ vᵉ aᵉ bᵉ =
    apᵉ
      ( λ fᵉ → listed-vec-functional-vecᵉ nᵉ (fᵉ ∘ᵉ (map-equivᵉ bᵉ)))
      ( invᵉ
        ( is-retraction-functional-vec-vecᵉ nᵉ
          ( functional-vec-vecᵉ nᵉ vᵉ ∘ᵉ map-equivᵉ aᵉ)))

  compute-swap-two-last-elements-transposition-Fin-permute-vecᵉ :
    (nᵉ : ℕᵉ)
    (vᵉ : vecᵉ Aᵉ nᵉ) →
    (xᵉ yᵉ : Aᵉ) →
    permute-vecᵉ
      (succ-ℕᵉ (succ-ℕᵉ nᵉ))
      (xᵉ ∷ᵉ yᵉ ∷ᵉ vᵉ)
      (swap-two-last-elements-transposition-Finᵉ nᵉ) ＝ᵉ
    (yᵉ ∷ᵉ xᵉ ∷ᵉ vᵉ)
  compute-swap-two-last-elements-transposition-Fin-permute-vecᵉ nᵉ vᵉ xᵉ yᵉ =
    eq-Eq-vecᵉ
      ( succ-ℕᵉ (succ-ℕᵉ nᵉ))
      ( permute-vecᵉ
          ( succ-ℕᵉ (succ-ℕᵉ nᵉ))
          ( xᵉ ∷ᵉ yᵉ ∷ᵉ vᵉ)
          ( swap-two-last-elements-transposition-Finᵉ nᵉ))
      ( yᵉ ∷ᵉ xᵉ ∷ᵉ vᵉ)
      ( reflᵉ ,ᵉ
        reflᵉ ,ᵉ
        Eq-eq-vecᵉ
          ( nᵉ)
          ( permute-vecᵉ nᵉ vᵉ id-equivᵉ)
          ( vᵉ)
          ( compute-permute-vec-id-equivᵉ nᵉ vᵉ))

  compute-equiv-coproduct-permutation-id-equiv-permute-vecᵉ :
    (nᵉ : ℕᵉ)
    (vᵉ : vecᵉ Aᵉ nᵉ)
    (xᵉ : Aᵉ)
    (tᵉ : Permutationᵉ nᵉ) →
    permute-vecᵉ (succ-ℕᵉ nᵉ) (xᵉ ∷ᵉ vᵉ) (equiv-coproductᵉ tᵉ id-equivᵉ) ＝ᵉ
    (xᵉ ∷ᵉ permute-vecᵉ nᵉ vᵉ tᵉ)
  compute-equiv-coproduct-permutation-id-equiv-permute-vecᵉ nᵉ vᵉ xᵉ tᵉ =
    eq-Eq-vecᵉ
      ( succ-ℕᵉ nᵉ)
      ( permute-vecᵉ (succ-ℕᵉ nᵉ) (xᵉ ∷ᵉ vᵉ) (equiv-coproductᵉ tᵉ id-equivᵉ))
      ( xᵉ ∷ᵉ permute-vecᵉ nᵉ vᵉ tᵉ)
      ( reflᵉ ,ᵉ
        ( Eq-eq-vecᵉ
          ( nᵉ)
          ( _)
          ( permute-vecᵉ nᵉ vᵉ tᵉ)
          ( reflᵉ)))

  ap-permute-vecᵉ :
    {nᵉ : ℕᵉ}
    (aᵉ : Permutationᵉ nᵉ)
    {vᵉ wᵉ : vecᵉ Aᵉ nᵉ} →
    vᵉ ＝ᵉ wᵉ →
    permute-vecᵉ nᵉ vᵉ aᵉ ＝ᵉ permute-vecᵉ nᵉ wᵉ aᵉ
  ap-permute-vecᵉ aᵉ reflᵉ = reflᵉ
```

### `x` is in a vector `v` iff it is in `permute v t`

```agda
  is-in-functional-vec-is-in-permute-functional-vecᵉ :
    (nᵉ : ℕᵉ) (vᵉ : Finᵉ nᵉ → Aᵉ) (tᵉ : Permutationᵉ nᵉ) (xᵉ : Aᵉ) →
    in-functional-vecᵉ nᵉ xᵉ (vᵉ ∘ᵉ map-equivᵉ tᵉ) → in-functional-vecᵉ nᵉ xᵉ vᵉ
  is-in-functional-vec-is-in-permute-functional-vecᵉ nᵉ vᵉ tᵉ xᵉ (kᵉ ,ᵉ reflᵉ) =
    map-equivᵉ tᵉ kᵉ ,ᵉ reflᵉ

  is-in-vec-is-in-permute-vecᵉ :
    (nᵉ : ℕᵉ) (vᵉ : vecᵉ Aᵉ nᵉ) (tᵉ : Permutationᵉ nᵉ) (xᵉ : Aᵉ) →
    xᵉ ∈-vecᵉ (permute-vecᵉ nᵉ vᵉ tᵉ) → xᵉ ∈-vecᵉ vᵉ
  is-in-vec-is-in-permute-vecᵉ nᵉ vᵉ tᵉ xᵉ Iᵉ =
    is-in-vec-is-in-functional-vecᵉ
      ( nᵉ)
      ( vᵉ)
      ( xᵉ)
      ( is-in-functional-vec-is-in-permute-functional-vecᵉ
        ( nᵉ)
        ( functional-vec-vecᵉ nᵉ vᵉ)
        ( tᵉ)
        ( xᵉ)
        ( trᵉ
          ( λ pᵉ → in-functional-vecᵉ nᵉ xᵉ pᵉ)
          ( is-retraction-functional-vec-vecᵉ nᵉ
            ( functional-vec-vecᵉ nᵉ vᵉ ∘ᵉ map-equivᵉ tᵉ))
          ( is-in-functional-vec-is-in-vecᵉ nᵉ (permute-vecᵉ nᵉ vᵉ tᵉ) xᵉ Iᵉ)))

  is-in-permute-functional-vec-is-in-functional-vecᵉ :
    (nᵉ : ℕᵉ) (vᵉ : Finᵉ nᵉ → Aᵉ) (tᵉ : Permutationᵉ nᵉ) (xᵉ : Aᵉ) →
    in-functional-vecᵉ nᵉ xᵉ vᵉ → in-functional-vecᵉ nᵉ xᵉ (vᵉ ∘ᵉ map-equivᵉ tᵉ)
  is-in-permute-functional-vec-is-in-functional-vecᵉ nᵉ vᵉ tᵉ xᵉ (kᵉ ,ᵉ reflᵉ) =
    map-inv-equivᵉ tᵉ kᵉ ,ᵉ apᵉ vᵉ (invᵉ (is-section-map-inv-equivᵉ tᵉ kᵉ))

  is-in-permute-vec-is-in-vecᵉ :
    (nᵉ : ℕᵉ) (vᵉ : vecᵉ Aᵉ nᵉ) (tᵉ : Permutationᵉ nᵉ) (xᵉ : Aᵉ) →
    xᵉ ∈-vecᵉ vᵉ → xᵉ ∈-vecᵉ (permute-vecᵉ nᵉ vᵉ tᵉ)
  is-in-permute-vec-is-in-vecᵉ nᵉ vᵉ tᵉ xᵉ Iᵉ =
    is-in-vec-is-in-functional-vecᵉ
      ( nᵉ)
      ( permute-vecᵉ nᵉ vᵉ tᵉ)
      ( xᵉ)
      ( trᵉ
        ( λ pᵉ → in-functional-vecᵉ nᵉ xᵉ pᵉ)
        ( invᵉ
          ( is-retraction-functional-vec-vecᵉ nᵉ
            ( functional-vec-vecᵉ nᵉ vᵉ ∘ᵉ map-equivᵉ tᵉ)))
        ( is-in-permute-functional-vec-is-in-functional-vecᵉ
          ( nᵉ)
          ( functional-vec-vecᵉ nᵉ vᵉ)
          ( tᵉ)
          ( xᵉ)
          ( is-in-functional-vec-is-in-vecᵉ nᵉ vᵉ xᵉ Iᵉ)))
```

### If `μ : A → (B → B)` satisfies a commutativity property, then `fold-vec b μ` is invariant under permutation for every `b : B`

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (μᵉ : Aᵉ → (Bᵉ → Bᵉ))
  where

  commutative-fold-vecᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  commutative-fold-vecᵉ = (a1ᵉ a2ᵉ : Aᵉ) (bᵉ : Bᵉ) → μᵉ a1ᵉ (μᵉ a2ᵉ bᵉ) ＝ᵉ μᵉ a2ᵉ (μᵉ a1ᵉ bᵉ)

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  (bᵉ : Bᵉ)
  (μᵉ : Aᵉ → (Bᵉ → Bᵉ))
  (Cᵉ : commutative-fold-vecᵉ μᵉ)
  where

  invariant-swap-two-last-elements-transposition-fold-vecᵉ :
    {nᵉ : ℕᵉ} → (vᵉ : vecᵉ Aᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ))) →
    fold-vecᵉ bᵉ μᵉ vᵉ ＝ᵉ
    fold-vecᵉ
      ( bᵉ)
      ( μᵉ)
      ( permute-vecᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ))
      ( vᵉ)
      ( swap-two-last-elements-transposition-Finᵉ nᵉ))
  invariant-swap-two-last-elements-transposition-fold-vecᵉ {nᵉ} (yᵉ ∷ᵉ zᵉ ∷ᵉ vᵉ) =
    Cᵉ yᵉ zᵉ (fold-vecᵉ bᵉ μᵉ vᵉ) ∙ᵉ
    invᵉ
      ( apᵉ
        ( fold-vecᵉ bᵉ μᵉ)
        ( compute-swap-two-last-elements-transposition-Fin-permute-vecᵉ
          ( nᵉ)
          ( vᵉ)
          ( yᵉ)
          ( zᵉ)))

  invariant-adjacent-transposition-fold-vecᵉ :
    {nᵉ : ℕᵉ} → (vᵉ : vecᵉ Aᵉ (succ-ℕᵉ nᵉ)) → (kᵉ : Finᵉ nᵉ) →
    fold-vecᵉ bᵉ μᵉ vᵉ ＝ᵉ
    fold-vecᵉ bᵉ μᵉ (permute-vecᵉ (succ-ℕᵉ nᵉ) vᵉ (adjacent-transposition-Finᵉ nᵉ kᵉ))
  invariant-adjacent-transposition-fold-vecᵉ {succ-ℕᵉ nᵉ} (xᵉ ∷ᵉ vᵉ) (inlᵉ kᵉ) =
    apᵉ
      ( μᵉ xᵉ)
      ( invariant-adjacent-transposition-fold-vecᵉ vᵉ kᵉ) ∙ᵉ
    invᵉ
      ( apᵉ
        ( fold-vecᵉ bᵉ μᵉ)
        ( compute-equiv-coproduct-permutation-id-equiv-permute-vecᵉ
          ( succ-ℕᵉ nᵉ)
          ( vᵉ)
          ( xᵉ)
          ( adjacent-transposition-Finᵉ nᵉ kᵉ)))
  invariant-adjacent-transposition-fold-vecᵉ {succ-ℕᵉ nᵉ} (xᵉ ∷ᵉ vᵉ) (inrᵉ _) =
    invariant-swap-two-last-elements-transposition-fold-vecᵉ (xᵉ ∷ᵉ vᵉ)

  invariant-list-adjacent-transpositions-fold-vecᵉ :
    {nᵉ : ℕᵉ} (vᵉ : vecᵉ Aᵉ (succ-ℕᵉ nᵉ)) (lᵉ : listᵉ (Finᵉ nᵉ)) →
    fold-vecᵉ bᵉ μᵉ vᵉ ＝ᵉ
    fold-vecᵉ
      ( bᵉ)
      ( μᵉ)
      ( permute-vecᵉ
        ( succ-ℕᵉ nᵉ)
        ( vᵉ)
        ( permutation-list-adjacent-transpositionsᵉ nᵉ lᵉ))
  invariant-list-adjacent-transpositions-fold-vecᵉ {nᵉ} vᵉ nilᵉ =
    apᵉ (fold-vecᵉ bᵉ μᵉ) (invᵉ (compute-permute-vec-id-equivᵉ (succ-ℕᵉ nᵉ) vᵉ))
  invariant-list-adjacent-transpositions-fold-vecᵉ {nᵉ} vᵉ (consᵉ xᵉ lᵉ) =
    ( invariant-adjacent-transposition-fold-vecᵉ vᵉ xᵉ ∙ᵉ
      ( ( invariant-list-adjacent-transpositions-fold-vecᵉ
          ( permute-vecᵉ (succ-ℕᵉ nᵉ) vᵉ (adjacent-transposition-Finᵉ nᵉ xᵉ))
          ( lᵉ)) ∙ᵉ
        ( apᵉ
          ( fold-vecᵉ bᵉ μᵉ)
          ( invᵉ
            ( compute-composition-permute-vecᵉ
              ( succ-ℕᵉ nᵉ)
              ( vᵉ)
              ( adjacent-transposition-Finᵉ nᵉ xᵉ)
              ( permutation-list-adjacent-transpositionsᵉ nᵉ lᵉ))))))

  invariant-transposition-fold-vecᵉ :
    {nᵉ : ℕᵉ} (vᵉ : vecᵉ Aᵉ (succ-ℕᵉ nᵉ)) (iᵉ jᵉ : Finᵉ (succ-ℕᵉ nᵉ)) (neqᵉ : iᵉ ≠ᵉ jᵉ) →
    fold-vecᵉ bᵉ μᵉ vᵉ ＝ᵉ
    fold-vecᵉ
      ( bᵉ)
      ( μᵉ)
      ( permute-vecᵉ (succ-ℕᵉ nᵉ) vᵉ (transposition-Finᵉ (succ-ℕᵉ nᵉ) iᵉ jᵉ neqᵉ))
  invariant-transposition-fold-vecᵉ {nᵉ} vᵉ iᵉ jᵉ neqᵉ =
    ( ( invariant-list-adjacent-transpositions-fold-vecᵉ
        ( vᵉ)
        ( list-adjacent-transpositions-transposition-Finᵉ nᵉ iᵉ jᵉ)) ∙ᵉ
      ( apᵉ
        ( λ tᵉ → fold-vecᵉ bᵉ μᵉ (permute-vecᵉ (succ-ℕᵉ nᵉ) vᵉ tᵉ))
        ( eq-htpy-equivᵉ
          { eᵉ =
            permutation-list-adjacent-transpositionsᵉ
              ( nᵉ)
              ( list-adjacent-transpositions-transposition-Finᵉ nᵉ iᵉ jᵉ)}
          { e'ᵉ = transposition-Finᵉ (succ-ℕᵉ nᵉ) iᵉ jᵉ neqᵉ}
          ( htpy-permutation-list-adjacent-transpositions-transposition-Finᵉ
            ( nᵉ)
            ( iᵉ)
            ( jᵉ)
            ( neqᵉ)))))

  invariant-list-transpositions-fold-vecᵉ :
    {nᵉ : ℕᵉ}
    (vᵉ : vecᵉ Aᵉ nᵉ)
    (lᵉ : listᵉ (Σᵉ (Finᵉ nᵉ ×ᵉ Finᵉ nᵉ) (λ (iᵉ ,ᵉ jᵉ) → iᵉ ≠ᵉ jᵉ))) →
    fold-vecᵉ bᵉ μᵉ vᵉ ＝ᵉ
    fold-vecᵉ
      ( bᵉ)
      ( μᵉ)
      ( permute-vecᵉ
        ( nᵉ)
        ( vᵉ)
        ( permutation-list-standard-transpositions-Finᵉ nᵉ lᵉ))
  invariant-list-transpositions-fold-vecᵉ {nᵉ} vᵉ nilᵉ =
    apᵉ
      ( fold-vecᵉ bᵉ μᵉ)
      ( invᵉ ( compute-permute-vec-id-equivᵉ nᵉ vᵉ))
  invariant-list-transpositions-fold-vecᵉ {0ᵉ} vᵉ (consᵉ _ _) = reflᵉ
  invariant-list-transpositions-fold-vecᵉ {succ-ℕᵉ nᵉ} vᵉ (consᵉ ((iᵉ ,ᵉ jᵉ) ,ᵉ neqᵉ) lᵉ) =
    ( invariant-transposition-fold-vecᵉ vᵉ iᵉ jᵉ neqᵉ ∙ᵉ
      ( ( invariant-list-transpositions-fold-vecᵉ
          ( permute-vecᵉ (succ-ℕᵉ nᵉ) vᵉ (transposition-Finᵉ (succ-ℕᵉ nᵉ) iᵉ jᵉ neqᵉ))
          ( lᵉ)) ∙ᵉ
        ( apᵉ
          ( fold-vecᵉ bᵉ μᵉ)
          ( invᵉ
            ( compute-composition-permute-vecᵉ
              ( succ-ℕᵉ nᵉ)
              ( vᵉ)
              ( transposition-Finᵉ (succ-ℕᵉ nᵉ) iᵉ jᵉ neqᵉ)
              ( permutation-list-standard-transpositions-Finᵉ (succ-ℕᵉ nᵉ) lᵉ))))))

  invariant-permutation-fold-vecᵉ :
    {nᵉ : ℕᵉ} → (vᵉ : vecᵉ Aᵉ nᵉ) → (fᵉ : Permutationᵉ nᵉ) →
    fold-vecᵉ bᵉ μᵉ vᵉ ＝ᵉ fold-vecᵉ bᵉ μᵉ (permute-vecᵉ nᵉ vᵉ fᵉ)
  invariant-permutation-fold-vecᵉ {nᵉ} vᵉ fᵉ =
    ( ( invariant-list-transpositions-fold-vecᵉ
        ( vᵉ)
        ( list-standard-transpositions-permutation-Finᵉ nᵉ fᵉ)) ∙ᵉ
      ( apᵉ
        ( λ fᵉ → fold-vecᵉ bᵉ μᵉ (permute-vecᵉ nᵉ vᵉ fᵉ))
        ( eq-htpy-equivᵉ
          {eᵉ =
            permutation-list-standard-transpositions-Finᵉ
              ( nᵉ)
              ( list-standard-transpositions-permutation-Finᵉ nᵉ fᵉ)}
          {e'ᵉ = fᵉ}
          ( retraction-permutation-list-standard-transpositions-Finᵉ nᵉ fᵉ))))
```

### `map-vec` of the permutation of a vector

```agda
eq-map-vec-permute-vecᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  (fᵉ : Aᵉ → Bᵉ) {nᵉ : ℕᵉ} (vᵉ : vecᵉ Aᵉ nᵉ) (tᵉ : Permutationᵉ nᵉ) →
  permute-vecᵉ nᵉ (map-vecᵉ fᵉ vᵉ) tᵉ ＝ᵉ
  map-vecᵉ fᵉ (permute-vecᵉ nᵉ vᵉ tᵉ)
eq-map-vec-permute-vecᵉ fᵉ {nᵉ} vᵉ tᵉ =
  ( ( apᵉ
      ( λ wᵉ →
        ( listed-vec-functional-vecᵉ
          ( nᵉ)
          ( functional-vec-vecᵉ nᵉ wᵉ ∘ᵉ (map-equivᵉ tᵉ)))))
      ( invᵉ (map-vec-map-functional-vecᵉ fᵉ nᵉ vᵉ)) ∙ᵉ
    ( ( apᵉ
        ( λ pᵉ →
          listed-vec-functional-vecᵉ
            ( nᵉ)
            ( pᵉ ∘ᵉ map-equivᵉ tᵉ))
        ( is-retraction-functional-vec-vecᵉ
          ( nᵉ)
          ( map-functional-vecᵉ nᵉ fᵉ (functional-vec-vecᵉ nᵉ vᵉ)))) ∙ᵉ
      ( ( apᵉ
          ( listed-vec-functional-vecᵉ nᵉ ∘ᵉ map-functional-vecᵉ nᵉ fᵉ)
          ( invᵉ
            ( is-retraction-functional-vec-vecᵉ
              ( nᵉ)
              ( λ zᵉ → functional-vec-vecᵉ nᵉ vᵉ (map-equivᵉ tᵉ zᵉ))))) ∙ᵉ
        ( map-vec-map-functional-vecᵉ fᵉ nᵉ (permute-vecᵉ nᵉ vᵉ tᵉ)))))
```