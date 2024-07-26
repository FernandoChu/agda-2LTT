# Transpositions of standard finite types

```agda
{-# OPTIONSᵉ --lossy-unificationᵉ #-}

module finite-group-theory.transpositions-standard-finite-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import finite-group-theory.permutations-standard-finite-typesᵉ
open import finite-group-theory.transpositionsᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.coproduct-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.empty-typesᵉ
open import foundation.equivalence-extensionalityᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-coproduct-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.negated-equalityᵉ
open import foundation.negationᵉ
open import foundation.propositionsᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ

open import lists.functoriality-listsᵉ
open import lists.listsᵉ

open import univalent-combinatorics.equality-standard-finite-typesᵉ
open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Givenᵉ `i`ᵉ andᵉ `j`ᵉ in `Finᵉ n`,ᵉ theᵉ transpositionᵉ associatedᵉ to `i`ᵉ andᵉ `j`ᵉ swapᵉ
theseᵉ twoᵉ elements.ᵉ

## Definitions

### Transpositions on `Fin n`

Thisᵉ definitionᵉ usesᵉ theᵉ `standard-transposition`ᵉ in
[`finite-group-theory.transposition`](finite-group-theory.transpositions.md).ᵉ

```agda
module _
  (nᵉ : ℕᵉ) (iᵉ jᵉ : Finᵉ nᵉ) (neqᵉ : iᵉ ≠ᵉ jᵉ)
  where

  transposition-Finᵉ : Permutationᵉ nᵉ
  transposition-Finᵉ = standard-transpositionᵉ (has-decidable-equality-Finᵉ nᵉ) neqᵉ

  map-transposition-Finᵉ : Finᵉ nᵉ → Finᵉ nᵉ
  map-transposition-Finᵉ =
    map-standard-transpositionᵉ (has-decidable-equality-Finᵉ nᵉ) neqᵉ

  left-computation-transposition-Finᵉ :
    map-standard-transpositionᵉ (has-decidable-equality-Finᵉ nᵉ) neqᵉ iᵉ ＝ᵉ jᵉ
  left-computation-transposition-Finᵉ =
    left-computation-standard-transpositionᵉ (has-decidable-equality-Finᵉ nᵉ) neqᵉ

  right-computation-transposition-Finᵉ :
    map-standard-transpositionᵉ (has-decidable-equality-Finᵉ nᵉ) neqᵉ jᵉ ＝ᵉ iᵉ
  right-computation-transposition-Finᵉ =
    right-computation-standard-transpositionᵉ (has-decidable-equality-Finᵉ nᵉ) neqᵉ

  is-fixed-point-transposition-Finᵉ :
    (zᵉ : Finᵉ nᵉ) →
    iᵉ ≠ᵉ zᵉ →
    jᵉ ≠ᵉ zᵉ →
    map-standard-transpositionᵉ (has-decidable-equality-Finᵉ nᵉ) neqᵉ zᵉ ＝ᵉ zᵉ
  is-fixed-point-transposition-Finᵉ =
    is-fixed-point-standard-transpositionᵉ (has-decidable-equality-Finᵉ nᵉ) neqᵉ
```

### The transposition that swaps the two last elements of `Fin (succ-ℕ (succ-ℕ n))`

Weᵉ defineᵉ directlyᵉ theᵉ transpositionᵉ ofᵉ `Finᵉ (succ-ℕᵉ (succ-ℕᵉ n))`ᵉ thatᵉ exchangesᵉ
theᵉ twoᵉ elementsᵉ associatedᵉ to `n`ᵉ andᵉ `succ-ℕᵉ n`.ᵉ

```agda
module _
  (nᵉ : ℕᵉ)
  where

  map-swap-two-last-elements-transposition-Finᵉ :
    Finᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)) → Finᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ))
  map-swap-two-last-elements-transposition-Finᵉ (inlᵉ (inlᵉ xᵉ)) = inlᵉ (inlᵉ xᵉ)
  map-swap-two-last-elements-transposition-Finᵉ (inlᵉ (inrᵉ starᵉ)) = inrᵉ starᵉ
  map-swap-two-last-elements-transposition-Finᵉ (inrᵉ starᵉ) = inlᵉ (inrᵉ starᵉ)

  is-involution-map-swap-two-last-elements-transposition-Finᵉ :
    ( map-swap-two-last-elements-transposition-Finᵉ ∘ᵉ
      map-swap-two-last-elements-transposition-Finᵉ) ~ᵉ
    idᵉ
  is-involution-map-swap-two-last-elements-transposition-Finᵉ (inlᵉ (inlᵉ xᵉ)) =
    reflᵉ
  is-involution-map-swap-two-last-elements-transposition-Finᵉ (inlᵉ (inrᵉ starᵉ)) =
    reflᵉ
  is-involution-map-swap-two-last-elements-transposition-Finᵉ (inrᵉ starᵉ) = reflᵉ

  swap-two-last-elements-transposition-Finᵉ : Permutationᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ))
  pr1ᵉ swap-two-last-elements-transposition-Finᵉ =
    map-swap-two-last-elements-transposition-Finᵉ
  pr2ᵉ swap-two-last-elements-transposition-Finᵉ =
    is-equiv-is-invertibleᵉ
      map-swap-two-last-elements-transposition-Finᵉ
      is-involution-map-swap-two-last-elements-transposition-Finᵉ
      is-involution-map-swap-two-last-elements-transposition-Finᵉ
```

Weᵉ showᵉ thatᵉ thisᵉ definitonᵉ isᵉ anᵉ instance ofᵉ theᵉ previousᵉ one.ᵉ

```agda
  cases-htpy-swap-two-last-elements-transposition-Finᵉ :
    (xᵉ : Finᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ))) →
    (xᵉ ＝ᵉ neg-one-Finᵉ (succ-ℕᵉ nᵉ)) +ᵉ (xᵉ ≠ᵉ neg-one-Finᵉ (succ-ℕᵉ nᵉ)) →
    (xᵉ ＝ᵉ neg-two-Finᵉ (succ-ℕᵉ nᵉ)) +ᵉ (xᵉ ≠ᵉ neg-two-Finᵉ (succ-ℕᵉ nᵉ)) →
    map-swap-two-last-elements-transposition-Finᵉ xᵉ ＝ᵉ
    map-transposition-Finᵉ
      ( succ-ℕᵉ (succ-ℕᵉ nᵉ))
      ( neg-two-Finᵉ (succ-ℕᵉ nᵉ))
      ( neg-one-Finᵉ (succ-ℕᵉ nᵉ))
      ( neq-inl-inrᵉ)
      ( xᵉ)
  cases-htpy-swap-two-last-elements-transposition-Finᵉ _ (inlᵉ reflᵉ) _ =
    invᵉ
      ( right-computation-transposition-Finᵉ
        ( succ-ℕᵉ (succ-ℕᵉ nᵉ))
        ( neg-two-Finᵉ (succ-ℕᵉ nᵉ))
        ( neg-one-Finᵉ (succ-ℕᵉ nᵉ))
        ( neq-inl-inrᵉ))
  cases-htpy-swap-two-last-elements-transposition-Finᵉ _ (inrᵉ pᵉ) (inlᵉ reflᵉ) =
    invᵉ
      ( left-computation-transposition-Finᵉ
        ( succ-ℕᵉ (succ-ℕᵉ nᵉ))
        ( neg-two-Finᵉ (succ-ℕᵉ nᵉ))
        ( neg-one-Finᵉ (succ-ℕᵉ nᵉ))
        ( neq-inl-inrᵉ))
  cases-htpy-swap-two-last-elements-transposition-Finᵉ
    ( inlᵉ (inlᵉ xᵉ))
    ( inrᵉ pᵉ)
    ( inrᵉ qᵉ) =
    invᵉ
      ( is-fixed-point-transposition-Finᵉ
        ( succ-ℕᵉ (succ-ℕᵉ nᵉ))
        ( neg-two-Finᵉ (succ-ℕᵉ nᵉ))
        ( neg-one-Finᵉ (succ-ℕᵉ nᵉ))
        ( neq-inl-inrᵉ)
        ( inlᵉ (inlᵉ xᵉ))
        ( qᵉ ∘ᵉ invᵉ)
        ( pᵉ ∘ᵉ invᵉ))
  cases-htpy-swap-two-last-elements-transposition-Finᵉ
    ( inlᵉ (inrᵉ starᵉ))
    ( inrᵉ pᵉ)
    ( inrᵉ qᵉ) = ex-falsoᵉ (qᵉ reflᵉ)
  cases-htpy-swap-two-last-elements-transposition-Finᵉ
    ( inrᵉ starᵉ)
    ( inrᵉ pᵉ)
    ( inrᵉ qᵉ) = ex-falsoᵉ (pᵉ reflᵉ)

  htpy-swap-two-last-elements-transposition-Finᵉ :
    htpy-equivᵉ
      ( swap-two-last-elements-transposition-Finᵉ)
      ( transposition-Finᵉ
        ( succ-ℕᵉ (succ-ℕᵉ nᵉ))
        ( neg-two-Finᵉ (succ-ℕᵉ nᵉ))
        ( neg-one-Finᵉ (succ-ℕᵉ nᵉ))
        ( neq-inl-inrᵉ))
  htpy-swap-two-last-elements-transposition-Finᵉ xᵉ =
    cases-htpy-swap-two-last-elements-transposition-Finᵉ
      ( xᵉ)
      ( has-decidable-equality-Finᵉ
        ( succ-ℕᵉ (succ-ℕᵉ nᵉ))
        ( xᵉ)
        ( neg-one-Finᵉ (succ-ℕᵉ nᵉ)))
      ( has-decidable-equality-Finᵉ
        ( succ-ℕᵉ (succ-ℕᵉ nᵉ))
        ( xᵉ)
        ( neg-two-Finᵉ (succ-ℕᵉ nᵉ)))
```

### Transpositions of a pair of adjacent elements in `Fin (succ-ℕ n)`

#### Definition using `swap-two-last-elements-transposition-Fin`

```agda
adjacent-transposition-Finᵉ :
  (nᵉ : ℕᵉ) → (kᵉ : Finᵉ nᵉ) →
  Permutationᵉ (succ-ℕᵉ nᵉ)
adjacent-transposition-Finᵉ (succ-ℕᵉ nᵉ) (inlᵉ xᵉ) =
  equiv-coproductᵉ (adjacent-transposition-Finᵉ nᵉ xᵉ) id-equivᵉ
adjacent-transposition-Finᵉ (succ-ℕᵉ nᵉ) (inrᵉ xᵉ) =
  swap-two-last-elements-transposition-Finᵉ nᵉ

map-adjacent-transposition-Finᵉ :
  (nᵉ : ℕᵉ) → (kᵉ : Finᵉ nᵉ) →
  (Finᵉ (succ-ℕᵉ nᵉ) → Finᵉ (succ-ℕᵉ nᵉ))
map-adjacent-transposition-Finᵉ nᵉ kᵉ = map-equivᵉ (adjacent-transposition-Finᵉ nᵉ kᵉ)
```

#### `adjacent-transposition-Fin` is an instance of the definiton `transposition-Fin`

```agda
cases-htpy-map-coproduct-map-transposition-id-Finᵉ :
  (nᵉ : ℕᵉ) → (kᵉ lᵉ : Finᵉ nᵉ) → (neqᵉ : kᵉ ≠ᵉ lᵉ) →
  (xᵉ : Finᵉ (succ-ℕᵉ nᵉ)) →
  (xᵉ ＝ᵉ inl-Finᵉ nᵉ kᵉ) +ᵉ (xᵉ ≠ᵉ inl-Finᵉ nᵉ kᵉ) →
  (xᵉ ＝ᵉ inl-Finᵉ nᵉ lᵉ) +ᵉ (xᵉ ≠ᵉ inl-Finᵉ nᵉ lᵉ) →
  map-coproductᵉ (map-transposition-Finᵉ nᵉ kᵉ lᵉ neqᵉ) idᵉ xᵉ ＝ᵉ
  map-transposition-Finᵉ
    ( succ-ℕᵉ nᵉ)
    ( inl-Finᵉ nᵉ kᵉ)
    ( inl-Finᵉ nᵉ lᵉ)
    ( neqᵉ ∘ᵉ is-injective-inl-Finᵉ nᵉ)
    ( xᵉ)
cases-htpy-map-coproduct-map-transposition-id-Finᵉ nᵉ kᵉ lᵉ neqᵉ xᵉ (inlᵉ reflᵉ) _ =
  ( ( apᵉ
      ( inl-Finᵉ nᵉ)
      ( left-computation-transposition-Finᵉ nᵉ kᵉ lᵉ neqᵉ)) ∙ᵉ
    ( invᵉ
      ( left-computation-transposition-Finᵉ
        ( succ-ℕᵉ nᵉ)
        ( inl-Finᵉ nᵉ kᵉ)
        ( inl-Finᵉ nᵉ lᵉ)
        ( neqᵉ ∘ᵉ is-injective-inl-Finᵉ nᵉ))))
cases-htpy-map-coproduct-map-transposition-id-Finᵉ
  ( nᵉ)
  ( kᵉ)
  ( lᵉ)
  ( neqᵉ)
  ( xᵉ)
  ( inrᵉ _)
  ( inlᵉ reflᵉ) =
  ( ( apᵉ
      ( inl-Finᵉ nᵉ)
      ( right-computation-transposition-Finᵉ nᵉ kᵉ lᵉ neqᵉ)) ∙ᵉ
    ( invᵉ
      ( right-computation-transposition-Finᵉ
        ( succ-ℕᵉ nᵉ)
        ( inl-Finᵉ nᵉ kᵉ)
        ( inl-Finᵉ nᵉ lᵉ)
        ( neqᵉ ∘ᵉ is-injective-inl-Finᵉ nᵉ))))
cases-htpy-map-coproduct-map-transposition-id-Finᵉ
  ( nᵉ)
  ( kᵉ)
  ( lᵉ)
  ( neqᵉ)
  ( inlᵉ xᵉ)
  ( inrᵉ neqkᵉ)
  ( inrᵉ neqlᵉ) =
  ( ( apᵉ
      ( inl-Finᵉ nᵉ)
      ( is-fixed-point-transposition-Finᵉ
        ( nᵉ)
        ( kᵉ)
        ( lᵉ)
        ( neqᵉ)
        ( xᵉ)
        ( neqkᵉ ∘ᵉ (invᵉ ∘ᵉ apᵉ (inl-Finᵉ nᵉ)))
        ( neqlᵉ ∘ᵉ (invᵉ ∘ᵉ apᵉ (inl-Finᵉ nᵉ))))) ∙ᵉ
    ( invᵉ
      ( is-fixed-point-transposition-Finᵉ
        ( succ-ℕᵉ nᵉ)
        ( inl-Finᵉ nᵉ kᵉ)
        ( inl-Finᵉ nᵉ lᵉ)
        ( neqᵉ ∘ᵉ is-injective-inl-Finᵉ nᵉ)
        ( inlᵉ xᵉ)
        ( neqkᵉ ∘ᵉ invᵉ)
        ( neqlᵉ ∘ᵉ invᵉ))))
cases-htpy-map-coproduct-map-transposition-id-Finᵉ
  ( nᵉ)
  ( kᵉ)
  ( lᵉ)
  ( neqᵉ)
  ( inrᵉ starᵉ)
  ( inrᵉ neqkᵉ)
  ( inrᵉ neqlᵉ) =
  invᵉ
    ( is-fixed-point-transposition-Finᵉ
      ( succ-ℕᵉ nᵉ)
      ( inl-Finᵉ nᵉ kᵉ)
      ( inl-Finᵉ nᵉ lᵉ)
      ( neqᵉ ∘ᵉ is-injective-inl-Finᵉ nᵉ)
      ( inrᵉ starᵉ)
      ( neqkᵉ ∘ᵉ invᵉ)
      ( neqlᵉ ∘ᵉ invᵉ))

htpy-map-coproduct-map-transposition-id-Finᵉ :
  (nᵉ : ℕᵉ) → (kᵉ lᵉ : Finᵉ nᵉ) → (neqᵉ : kᵉ ≠ᵉ lᵉ) →
  htpy-equivᵉ
    ( equiv-coproductᵉ (transposition-Finᵉ nᵉ kᵉ lᵉ neqᵉ) id-equivᵉ)
    ( transposition-Finᵉ
      ( succ-ℕᵉ nᵉ)
      ( inl-Finᵉ nᵉ kᵉ)
      ( inl-Finᵉ nᵉ lᵉ)
      ( neqᵉ ∘ᵉ is-injective-inl-Finᵉ nᵉ))
htpy-map-coproduct-map-transposition-id-Finᵉ nᵉ kᵉ lᵉ neqᵉ xᵉ =
  cases-htpy-map-coproduct-map-transposition-id-Finᵉ
    ( nᵉ)
    ( kᵉ)
    ( lᵉ)
    ( neqᵉ)
    ( xᵉ)
    ( has-decidable-equality-Finᵉ (succ-ℕᵉ nᵉ) xᵉ (inl-Finᵉ nᵉ kᵉ))
    ( has-decidable-equality-Finᵉ (succ-ℕᵉ nᵉ) xᵉ (inl-Finᵉ nᵉ lᵉ))

helper-htpy-same-transposition-Finᵉ :
  (nᵉ : ℕᵉ) (kᵉ lᵉ : Finᵉ nᵉ) (neq1ᵉ : kᵉ ≠ᵉ lᵉ) (neq2ᵉ : kᵉ ≠ᵉ lᵉ) →
  (neq1ᵉ ＝ᵉ neq2ᵉ) →
  htpy-equivᵉ
    ( transposition-Finᵉ nᵉ kᵉ lᵉ neq1ᵉ)
    ( transposition-Finᵉ nᵉ kᵉ lᵉ neq2ᵉ)
helper-htpy-same-transposition-Finᵉ nᵉ kᵉ lᵉ neq1ᵉ .neq1ᵉ reflᵉ = refl-htpyᵉ

htpy-same-transposition-Finᵉ :
  {nᵉ : ℕᵉ} {kᵉ lᵉ : Finᵉ nᵉ} {neq1ᵉ : kᵉ ≠ᵉ lᵉ} {neq2ᵉ : kᵉ ≠ᵉ lᵉ} →
  htpy-equivᵉ
    ( transposition-Finᵉ nᵉ kᵉ lᵉ neq1ᵉ)
    ( transposition-Finᵉ nᵉ kᵉ lᵉ neq2ᵉ)
htpy-same-transposition-Finᵉ {nᵉ} {kᵉ} {lᵉ} {neq1ᵉ} {neq2ᵉ} =
  helper-htpy-same-transposition-Finᵉ nᵉ kᵉ lᵉ neq1ᵉ neq2ᵉ (eq-is-propᵉ is-prop-negᵉ)

htpy-adjacent-transposition-Finᵉ :
  (nᵉ : ℕᵉ) → (kᵉ : Finᵉ nᵉ) →
  htpy-equivᵉ
    ( adjacent-transposition-Finᵉ nᵉ kᵉ)
    ( transposition-Finᵉ
      ( succ-ℕᵉ nᵉ)
      ( inl-Finᵉ nᵉ kᵉ)
      ( inr-Finᵉ nᵉ kᵉ)
      ( neq-inl-Fin-inr-Finᵉ nᵉ kᵉ))
htpy-adjacent-transposition-Finᵉ (succ-ℕᵉ nᵉ) (inlᵉ xᵉ) =
  ( ( htpy-map-coproductᵉ (htpy-adjacent-transposition-Finᵉ nᵉ xᵉ) refl-htpyᵉ) ∙hᵉ
    ( ( htpy-map-coproduct-map-transposition-id-Finᵉ
        ( succ-ℕᵉ nᵉ)
        ( inl-Finᵉ nᵉ xᵉ)
        ( inr-Finᵉ nᵉ xᵉ)
        ( neq-inl-Fin-inr-Finᵉ nᵉ xᵉ)) ∙hᵉ
      ( htpy-same-transposition-Finᵉ)))
htpy-adjacent-transposition-Finᵉ (succ-ℕᵉ nᵉ) (inrᵉ starᵉ) =
  htpy-swap-two-last-elements-transposition-Finᵉ nᵉ
```

## Properties

### The transposition associated to `i` and `j` is homotopic to the one associated with `j` and `i`

```agda
cases-htpy-transposition-Fin-transposition-swap-Finᵉ :
  (nᵉ : ℕᵉ) → (iᵉ jᵉ : Finᵉ nᵉ) → (neqᵉ : iᵉ ≠ᵉ jᵉ) → (xᵉ : Finᵉ nᵉ) →
  (xᵉ ＝ᵉ iᵉ) +ᵉ (xᵉ ≠ᵉ iᵉ) →
  (xᵉ ＝ᵉ jᵉ) +ᵉ (xᵉ ≠ᵉ jᵉ) →
  map-transposition-Finᵉ nᵉ iᵉ jᵉ neqᵉ xᵉ ＝ᵉ
  map-transposition-Finᵉ nᵉ jᵉ iᵉ (neqᵉ ∘ᵉ invᵉ) xᵉ
cases-htpy-transposition-Fin-transposition-swap-Finᵉ
  ( nᵉ)
  ( iᵉ)
  ( jᵉ)
  ( neqᵉ)
  ( .iᵉ)
  ( inlᵉ reflᵉ) _ =
  left-computation-transposition-Finᵉ nᵉ iᵉ jᵉ neqᵉ ∙ᵉ
  invᵉ (right-computation-transposition-Finᵉ nᵉ jᵉ iᵉ (neqᵉ ∘ᵉ invᵉ))
cases-htpy-transposition-Fin-transposition-swap-Finᵉ
  ( nᵉ)
  ( iᵉ)
  ( jᵉ)
  ( neqᵉ)
  ( .jᵉ)
  ( inrᵉ _)
  ( inlᵉ reflᵉ) =
  right-computation-transposition-Finᵉ nᵉ iᵉ jᵉ neqᵉ ∙ᵉ
  invᵉ (left-computation-transposition-Finᵉ nᵉ jᵉ iᵉ (neqᵉ ∘ᵉ invᵉ))
cases-htpy-transposition-Fin-transposition-swap-Finᵉ
  ( nᵉ)
  ( iᵉ)
  ( jᵉ)
  ( neqᵉ)
  ( xᵉ)
  ( inrᵉ neqiᵉ)
  ( inrᵉ neqjᵉ) =
  is-fixed-point-transposition-Finᵉ
    ( nᵉ)
    ( iᵉ)
    ( jᵉ)
    ( neqᵉ)
    ( xᵉ)
    ( neqiᵉ ∘ᵉ invᵉ)
    ( neqjᵉ ∘ᵉ invᵉ) ∙ᵉ
  invᵉ
    (is-fixed-point-transposition-Finᵉ
      ( nᵉ)
      ( jᵉ)
      ( iᵉ)
      ( neqᵉ ∘ᵉ invᵉ)
      ( xᵉ)
      ( neqjᵉ ∘ᵉ invᵉ)
      ( neqiᵉ ∘ᵉ invᵉ))

htpy-transposition-Fin-transposition-swap-Finᵉ :
  (nᵉ : ℕᵉ) → (iᵉ jᵉ : Finᵉ nᵉ) → (neqᵉ : iᵉ ≠ᵉ jᵉ) →
  htpy-equivᵉ
    ( transposition-Finᵉ nᵉ iᵉ jᵉ neqᵉ)
    ( transposition-Finᵉ nᵉ jᵉ iᵉ (neqᵉ ∘ᵉ invᵉ))
htpy-transposition-Fin-transposition-swap-Finᵉ nᵉ iᵉ jᵉ neqᵉ xᵉ =
  cases-htpy-transposition-Fin-transposition-swap-Finᵉ
    ( nᵉ)
    ( iᵉ)
    ( jᵉ)
    ( neqᵉ)
    ( xᵉ)
    ( has-decidable-equality-Finᵉ nᵉ xᵉ iᵉ)
    ( has-decidable-equality-Finᵉ nᵉ xᵉ jᵉ)
```

### The conjugate of a transposition is also a transposition

```agda
htpy-conjugate-transposition-Finᵉ :
  (nᵉ : ℕᵉ) (xᵉ yᵉ zᵉ : Finᵉ nᵉ)
  (neqxyᵉ : xᵉ ≠ᵉ yᵉ)
  (neqyzᵉ : yᵉ ≠ᵉ zᵉ)
  (neqxzᵉ : xᵉ ≠ᵉ zᵉ) →
  htpy-equivᵉ
    ( transposition-Finᵉ nᵉ yᵉ zᵉ neqyzᵉ ∘eᵉ
      ( transposition-Finᵉ nᵉ xᵉ yᵉ neqxyᵉ ∘eᵉ
        transposition-Finᵉ nᵉ yᵉ zᵉ neqyzᵉ))
    ( transposition-Finᵉ nᵉ xᵉ zᵉ neqxzᵉ)
htpy-conjugate-transposition-Finᵉ nᵉ xᵉ yᵉ zᵉ neqxyᵉ neqyzᵉ neqxzᵉ =
  htpy-conjugate-transpositionᵉ
    ( has-decidable-equality-Finᵉ nᵉ)
    ( neqxyᵉ)
    ( neqyzᵉ)
    ( neqxzᵉ)

private
  htpy-whisker-conjugateᵉ :
    {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {fᵉ f'ᵉ : Aᵉ → Aᵉ} (gᵉ : Aᵉ → Aᵉ) →
    (fᵉ ~ᵉ f'ᵉ) → (fᵉ ∘ᵉ (gᵉ ∘ᵉ fᵉ)) ~ᵉ (f'ᵉ ∘ᵉ (gᵉ ∘ᵉ f'ᵉ))
  htpy-whisker-conjugateᵉ {fᵉ = fᵉ} {f'ᵉ = f'ᵉ} gᵉ Hᵉ xᵉ =
    Hᵉ (gᵉ ( fᵉ xᵉ)) ∙ᵉ apᵉ (f'ᵉ ∘ᵉ gᵉ) (Hᵉ xᵉ)

htpy-conjugate-transposition-swap-two-last-elements-transposition-Finᵉ :
  (nᵉ : ℕᵉ) (xᵉ : Finᵉ (succ-ℕᵉ nᵉ)) (neqᵉ : xᵉ ≠ᵉ neg-one-Finᵉ nᵉ) →
  htpy-equivᵉ
    ( swap-two-last-elements-transposition-Finᵉ nᵉ ∘eᵉ
      ( transposition-Finᵉ
        ( succ-ℕᵉ (succ-ℕᵉ nᵉ))
        ( inl-Finᵉ (succ-ℕᵉ nᵉ) xᵉ)
        ( neg-two-Finᵉ (succ-ℕᵉ nᵉ))
        ( neqᵉ ∘ᵉ is-injective-inl-Finᵉ (succ-ℕᵉ nᵉ)) ∘eᵉ
        swap-two-last-elements-transposition-Finᵉ nᵉ))
    ( transposition-Finᵉ
      ( succ-ℕᵉ (succ-ℕᵉ nᵉ))
      ( inl-Finᵉ (succ-ℕᵉ nᵉ) xᵉ)
      ( neg-one-Finᵉ (succ-ℕᵉ nᵉ))
      ( neq-inl-inrᵉ))
htpy-conjugate-transposition-swap-two-last-elements-transposition-Finᵉ nᵉ xᵉ neqᵉ =
  ( ( htpy-whisker-conjugateᵉ
        ( map-transposition-Finᵉ
          ( succ-ℕᵉ (succ-ℕᵉ nᵉ))
          ( inl-Finᵉ (succ-ℕᵉ nᵉ) xᵉ)
          ( neg-two-Finᵉ (succ-ℕᵉ nᵉ))
          ( neqᵉ ∘ᵉ is-injective-inl-Finᵉ (succ-ℕᵉ nᵉ)))
        ( htpy-swap-two-last-elements-transposition-Finᵉ nᵉ)) ∙hᵉ
    ( ( htpy-conjugate-transposition-Finᵉ
        ( succ-ℕᵉ (succ-ℕᵉ nᵉ))
        ( inl-Finᵉ (succ-ℕᵉ nᵉ) xᵉ)
        ( neg-two-Finᵉ (succ-ℕᵉ nᵉ))
        ( neg-one-Finᵉ (succ-ℕᵉ nᵉ))
        ( neqᵉ ∘ᵉ is-injective-inl-Finᵉ (succ-ℕᵉ nᵉ))
        ( neq-inl-inrᵉ)
        ( neq-inl-inrᵉ))))

htpy-conjugate-transposition-swap-two-last-elements-transposition-Fin'ᵉ :
  (nᵉ : ℕᵉ) (xᵉ : Finᵉ (succ-ℕᵉ nᵉ)) (neqᵉ : xᵉ ≠ᵉ neg-one-Finᵉ nᵉ) →
  htpy-equivᵉ
    ( swap-two-last-elements-transposition-Finᵉ nᵉ ∘eᵉ
      ( transposition-Finᵉ
        ( succ-ℕᵉ (succ-ℕᵉ nᵉ))
        ( neg-two-Finᵉ (succ-ℕᵉ nᵉ))
        ( inl-Finᵉ (succ-ℕᵉ nᵉ) xᵉ)
        ( neqᵉ ∘ᵉ (is-injective-inl-Finᵉ (succ-ℕᵉ nᵉ) ∘ᵉ invᵉ)) ∘eᵉ
        swap-two-last-elements-transposition-Finᵉ nᵉ))
    ( transposition-Finᵉ
      ( succ-ℕᵉ (succ-ℕᵉ nᵉ))
      ( neg-one-Finᵉ (succ-ℕᵉ nᵉ))
      ( inl-Finᵉ (succ-ℕᵉ nᵉ) xᵉ)
      ( neq-inr-inlᵉ))
htpy-conjugate-transposition-swap-two-last-elements-transposition-Fin'ᵉ nᵉ xᵉ neqᵉ =
  ( ( double-whisker-compᵉ
      ( map-swap-two-last-elements-transposition-Finᵉ nᵉ)
      ( ( htpy-transposition-Fin-transposition-swap-Finᵉ
          ( succ-ℕᵉ (succ-ℕᵉ nᵉ))
          ( neg-two-Finᵉ (succ-ℕᵉ nᵉ))
          ( inl-Finᵉ (succ-ℕᵉ nᵉ) xᵉ)
          ( neqᵉ ∘ᵉ (is-injective-inl-Finᵉ (succ-ℕᵉ nᵉ) ∘ᵉ invᵉ))) ∙hᵉ
        htpy-same-transposition-Finᵉ)
      ( map-swap-two-last-elements-transposition-Finᵉ nᵉ)) ∙hᵉ
      ( ( htpy-conjugate-transposition-swap-two-last-elements-transposition-Finᵉ
          ( nᵉ)
          ( xᵉ)
          ( neqᵉ) ∙hᵉ
        ( ( htpy-transposition-Fin-transposition-swap-Finᵉ
            ( succ-ℕᵉ (succ-ℕᵉ nᵉ))
            ( inl-Finᵉ (succ-ℕᵉ nᵉ) xᵉ)
            ( neg-one-Finᵉ (succ-ℕᵉ nᵉ))
            ( neq-inl-inrᵉ)) ∙hᵉ
          htpy-same-transposition-Finᵉ))))
```

### Every transposition is the composition of a list of adjacent transpositions

```agda
list-adjacent-transpositions-transposition-Finᵉ :
  (nᵉ : ℕᵉ) → (iᵉ jᵉ : Finᵉ (succ-ℕᵉ nᵉ)) →
  listᵉ (Finᵉ nᵉ)
list-adjacent-transpositions-transposition-Finᵉ nᵉ (inrᵉ _) (inrᵉ _) = nilᵉ
list-adjacent-transpositions-transposition-Finᵉ 0 (inlᵉ _) (inrᵉ _) = nilᵉ
list-adjacent-transpositions-transposition-Finᵉ 0 (inlᵉ _) (inlᵉ _) = nilᵉ
list-adjacent-transpositions-transposition-Finᵉ 0 (inrᵉ _) (inlᵉ _) = nilᵉ
list-adjacent-transpositions-transposition-Finᵉ
  ( succ-ℕᵉ nᵉ)
  ( inlᵉ iᵉ)
  ( inlᵉ jᵉ) =
  map-listᵉ (inl-Finᵉ nᵉ) (list-adjacent-transpositions-transposition-Finᵉ nᵉ iᵉ jᵉ)
list-adjacent-transpositions-transposition-Finᵉ
  ( succ-ℕᵉ nᵉ)
  ( inlᵉ (inrᵉ starᵉ))
  ( inrᵉ starᵉ) = consᵉ (inrᵉ starᵉ) nilᵉ
list-adjacent-transpositions-transposition-Finᵉ
  ( succ-ℕᵉ nᵉ)
  ( inlᵉ (inlᵉ iᵉ))
  ( inrᵉ starᵉ) =
  snocᵉ
    ( consᵉ
      ( inrᵉ starᵉ)
      ( map-listᵉ
        ( inl-Finᵉ nᵉ)
        ( list-adjacent-transpositions-transposition-Finᵉ nᵉ (inlᵉ iᵉ) (inrᵉ starᵉ))))
    ( inrᵉ starᵉ)
list-adjacent-transpositions-transposition-Finᵉ
  ( succ-ℕᵉ nᵉ)
  ( inrᵉ starᵉ)
  ( inlᵉ (inlᵉ jᵉ)) =
  snocᵉ
    ( consᵉ
      ( inrᵉ starᵉ)
      ( map-listᵉ
        ( inl-Finᵉ nᵉ)
        ( list-adjacent-transpositions-transposition-Finᵉ nᵉ (inrᵉ starᵉ) (inlᵉ jᵉ))))
    ( inrᵉ starᵉ)
list-adjacent-transpositions-transposition-Finᵉ
  ( succ-ℕᵉ nᵉ)
  ( inrᵉ starᵉ)
  ( inlᵉ (inrᵉ starᵉ)) = consᵉ (inrᵉ starᵉ) nilᵉ

permutation-list-adjacent-transpositionsᵉ :
  (nᵉ : ℕᵉ) → listᵉ (Finᵉ nᵉ) → Permutationᵉ (succ-ℕᵉ nᵉ)
permutation-list-adjacent-transpositionsᵉ nᵉ nilᵉ = id-equivᵉ
permutation-list-adjacent-transpositionsᵉ nᵉ (consᵉ xᵉ lᵉ) =
  adjacent-transposition-Finᵉ nᵉ xᵉ ∘eᵉ
  permutation-list-adjacent-transpositionsᵉ nᵉ lᵉ

map-permutation-list-adjacent-transpositionsᵉ :
  (nᵉ : ℕᵉ) → listᵉ (Finᵉ nᵉ) → Finᵉ (succ-ℕᵉ nᵉ) → Finᵉ (succ-ℕᵉ nᵉ)
map-permutation-list-adjacent-transpositionsᵉ nᵉ lᵉ =
  map-equivᵉ (permutation-list-adjacent-transpositionsᵉ nᵉ lᵉ)

htpy-permutation-inl-list-adjacent-transpositionsᵉ :
  (nᵉ : ℕᵉ) → (lᵉ : listᵉ (Finᵉ nᵉ)) →
  htpy-equivᵉ
    ( permutation-list-adjacent-transpositionsᵉ
      ( succ-ℕᵉ nᵉ)
      ( map-listᵉ (inl-Finᵉ nᵉ) lᵉ))
    ( equiv-coproductᵉ
      ( permutation-list-adjacent-transpositionsᵉ nᵉ lᵉ)
      ( id-equivᵉ))
htpy-permutation-inl-list-adjacent-transpositionsᵉ nᵉ nilᵉ =
  inv-htpyᵉ (id-map-coproductᵉ (Finᵉ (succ-ℕᵉ nᵉ)) unitᵉ)
htpy-permutation-inl-list-adjacent-transpositionsᵉ nᵉ (consᵉ xᵉ lᵉ) =
  ( map-coproductᵉ (map-adjacent-transposition-Finᵉ nᵉ xᵉ) idᵉ ·lᵉ
    htpy-permutation-inl-list-adjacent-transpositionsᵉ nᵉ lᵉ) ∙hᵉ
  ( inv-htpyᵉ
      ( preserves-comp-map-coproductᵉ
        ( map-permutation-list-adjacent-transpositionsᵉ nᵉ lᵉ)
        ( map-adjacent-transposition-Finᵉ nᵉ xᵉ)
        ( idᵉ)
        ( idᵉ)))

htpy-permutation-snoc-list-adjacent-transpositionsᵉ :
  (nᵉ : ℕᵉ) (lᵉ : listᵉ (Finᵉ nᵉ)) (xᵉ : Finᵉ nᵉ) →
  htpy-equivᵉ
    ( permutation-list-adjacent-transpositionsᵉ nᵉ (snocᵉ lᵉ xᵉ))
    ( permutation-list-adjacent-transpositionsᵉ nᵉ lᵉ ∘eᵉ
      adjacent-transposition-Finᵉ nᵉ xᵉ)
htpy-permutation-snoc-list-adjacent-transpositionsᵉ nᵉ nilᵉ xᵉ = refl-htpyᵉ
htpy-permutation-snoc-list-adjacent-transpositionsᵉ nᵉ (consᵉ yᵉ lᵉ) xᵉ =
  map-adjacent-transposition-Finᵉ nᵉ yᵉ ·lᵉ
  htpy-permutation-snoc-list-adjacent-transpositionsᵉ nᵉ lᵉ xᵉ

htpy-permutation-list-adjacent-transpositions-transposition-Finᵉ :
  (nᵉ : ℕᵉ) (iᵉ jᵉ : Finᵉ (succ-ℕᵉ nᵉ)) (neqᵉ : iᵉ ≠ᵉ jᵉ) →
  htpy-equivᵉ
    ( permutation-list-adjacent-transpositionsᵉ
      ( nᵉ)
      ( list-adjacent-transpositions-transposition-Finᵉ nᵉ iᵉ jᵉ))
    ( transposition-Finᵉ (succ-ℕᵉ nᵉ) iᵉ jᵉ neqᵉ)
htpy-permutation-list-adjacent-transpositions-transposition-Finᵉ
  ( 0ᵉ)
  ( inrᵉ starᵉ)
  ( inrᵉ starᵉ)
  ( neqᵉ) = ex-falsoᵉ (neqᵉ reflᵉ)
htpy-permutation-list-adjacent-transpositions-transposition-Finᵉ
  ( succ-ℕᵉ nᵉ)
  ( inlᵉ iᵉ)
  ( inlᵉ jᵉ)
  ( neqᵉ) =
  ( ( htpy-permutation-inl-list-adjacent-transpositionsᵉ
      ( nᵉ)
      ( list-adjacent-transpositions-transposition-Finᵉ nᵉ iᵉ jᵉ)) ∙hᵉ
    ( ( htpy-map-coproductᵉ
        ( htpy-permutation-list-adjacent-transpositions-transposition-Finᵉ
          ( nᵉ)
          ( iᵉ)
          ( jᵉ)
          ( neqᵉ ∘ᵉ (apᵉ (inl-Finᵉ (succ-ℕᵉ nᵉ)))))
        ( refl-htpyᵉ)) ∙hᵉ
      ( ( htpy-map-coproduct-map-transposition-id-Finᵉ
          ( succ-ℕᵉ nᵉ)
          ( iᵉ)
          ( jᵉ)
          ( neqᵉ ∘ᵉ apᵉ (inl-Finᵉ (succ-ℕᵉ nᵉ)))) ∙hᵉ
        ( htpy-same-transposition-Finᵉ))))
htpy-permutation-list-adjacent-transpositions-transposition-Finᵉ
  ( succ-ℕᵉ nᵉ)
  ( inlᵉ (inlᵉ iᵉ))
  ( inrᵉ starᵉ)
  ( neqᵉ) =
  ( ( map-swap-two-last-elements-transposition-Finᵉ nᵉ ·lᵉ
      htpy-permutation-snoc-list-adjacent-transpositionsᵉ
        ( succ-ℕᵉ nᵉ)
        ( map-listᵉ
          ( inl-Finᵉ nᵉ)
          ( list-adjacent-transpositions-transposition-Finᵉ
            ( nᵉ)
            ( inlᵉ iᵉ)
            ( inrᵉ starᵉ)))
        ( inrᵉ starᵉ)) ∙hᵉ
    ( ( double-whisker-compᵉ
        ( map-swap-two-last-elements-transposition-Finᵉ nᵉ)
        ( ( htpy-permutation-inl-list-adjacent-transpositionsᵉ
            ( nᵉ)
            ( list-adjacent-transpositions-transposition-Finᵉ
              ( nᵉ)
              ( inlᵉ iᵉ)
              ( inrᵉ starᵉ))) ∙hᵉ
          ( htpy-map-coproductᵉ
            ( htpy-permutation-list-adjacent-transpositions-transposition-Finᵉ
              ( nᵉ)
              ( inlᵉ iᵉ)
              ( inrᵉ starᵉ)
              ( neq-inl-inrᵉ))
            ( refl-htpyᵉ) ∙hᵉ
            htpy-map-coproduct-map-transposition-id-Finᵉ
              ( succ-ℕᵉ nᵉ)
              ( inlᵉ iᵉ)
              ( inrᵉ starᵉ)
              ( neq-inl-inrᵉ)))
        ( map-swap-two-last-elements-transposition-Finᵉ nᵉ)) ∙hᵉ
        ( htpy-conjugate-transposition-swap-two-last-elements-transposition-Finᵉ
          ( nᵉ)
          ( inlᵉ iᵉ)
          ( neq-inl-inrᵉ) ∙hᵉ
          htpy-same-transposition-Finᵉ)))
htpy-permutation-list-adjacent-transpositions-transposition-Finᵉ
  ( succ-ℕᵉ nᵉ)
  ( inlᵉ (inrᵉ starᵉ))
  ( inrᵉ starᵉ)
  ( neqᵉ) =
  htpy-swap-two-last-elements-transposition-Finᵉ nᵉ ∙hᵉ
  htpy-same-transposition-Finᵉ
htpy-permutation-list-adjacent-transpositions-transposition-Finᵉ
  ( succ-ℕᵉ nᵉ)
  ( inrᵉ starᵉ)
  ( inlᵉ (inlᵉ jᵉ))
  ( neqᵉ) =
  ( ( map-swap-two-last-elements-transposition-Finᵉ nᵉ ·lᵉ
      htpy-permutation-snoc-list-adjacent-transpositionsᵉ
        ( succ-ℕᵉ nᵉ)
        ( map-listᵉ
          ( inl-Finᵉ nᵉ)
          ( list-adjacent-transpositions-transposition-Finᵉ
            ( nᵉ)
            ( inrᵉ starᵉ)
            ( inlᵉ jᵉ)))
        ( inrᵉ starᵉ)) ∙hᵉ
    ( ( double-whisker-compᵉ
        ( map-swap-two-last-elements-transposition-Finᵉ nᵉ)
        ( ( htpy-permutation-inl-list-adjacent-transpositionsᵉ
            ( nᵉ)
            ( list-adjacent-transpositions-transposition-Finᵉ
              ( nᵉ)
              ( inrᵉ starᵉ)
              ( inlᵉ jᵉ))) ∙hᵉ
          ( ( htpy-map-coproductᵉ
              ( htpy-permutation-list-adjacent-transpositions-transposition-Finᵉ
                ( nᵉ)
                ( inrᵉ starᵉ)
                ( inlᵉ jᵉ)
                ( neq-inr-inlᵉ))
              ( refl-htpyᵉ)) ∙hᵉ
            ( ( htpy-map-coproduct-map-transposition-id-Finᵉ
                ( succ-ℕᵉ nᵉ)
                ( inrᵉ starᵉ)
                ( inlᵉ jᵉ)
                ( neq-inr-inlᵉ)) ∙hᵉ
              ( htpy-same-transposition-Finᵉ))))
        ( map-swap-two-last-elements-transposition-Finᵉ nᵉ)) ∙hᵉ
      ( ( htpy-conjugate-transposition-swap-two-last-elements-transposition-Fin'ᵉ
          ( nᵉ)
          ( inlᵉ jᵉ)
          ( neq-inl-inrᵉ)) ∙hᵉ
        htpy-same-transposition-Finᵉ)))
htpy-permutation-list-adjacent-transpositions-transposition-Finᵉ
  ( succ-ℕᵉ nᵉ)
  ( inrᵉ starᵉ)
  ( inlᵉ (inrᵉ starᵉ))
  ( neqᵉ) =
  htpy-swap-two-last-elements-transposition-Finᵉ nᵉ ∙hᵉ
  ( ( htpy-transposition-Fin-transposition-swap-Finᵉ
      ( succ-ℕᵉ (succ-ℕᵉ nᵉ))
      ( neg-two-Finᵉ (succ-ℕᵉ nᵉ))
      ( neg-one-Finᵉ (succ-ℕᵉ nᵉ))
      ( neq-inl-inrᵉ)) ∙hᵉ
    htpy-same-transposition-Finᵉ)
htpy-permutation-list-adjacent-transpositions-transposition-Finᵉ
  ( succ-ℕᵉ nᵉ)
  ( inrᵉ starᵉ)
  ( inrᵉ starᵉ)
  ( neqᵉ) = ex-falsoᵉ (neqᵉ reflᵉ)
```