# Pisano periods

```agda
module elementary-number-theory.pisano-periodsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.divisibility-natural-numbersᵉ
open import elementary-number-theory.fibonacci-sequenceᵉ
open import elementary-number-theory.inequality-natural-numbersᵉ
open import elementary-number-theory.lower-bounds-natural-numbersᵉ
open import elementary-number-theory.modular-arithmetic-standard-finite-typesᵉ
open import elementary-number-theory.natural-numbersᵉ
open import elementary-number-theory.strict-inequality-natural-numbersᵉ
open import elementary-number-theory.well-ordering-principle-natural-numbersᵉ

open import foundation.action-on-identifications-binary-functionsᵉ
open import foundation.action-on-identifications-functionsᵉ
open import foundation.cartesian-product-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.empty-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.identity-typesᵉ
open import foundation.injective-mapsᵉ
open import foundation.repetitions-sequencesᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ

open import univalent-combinatorics.cartesian-product-typesᵉ
open import univalent-combinatorics.countingᵉ
open import univalent-combinatorics.sequences-finite-typesᵉ
open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Theᵉ sequenceᵉ `Pᵉ : ℕᵉ → ℕ`ᵉ ofᵉ **Pisanoᵉ periods**ᵉ isᵉ theᵉ sequenceᵉ where `Pᵉ n`ᵉ isᵉ
theᵉ periodᵉ ofᵉ theᵉ Fibonacciᵉ sequenceᵉ moduloᵉ `n`.ᵉ Thisᵉ sequenceᵉ isᵉ listedᵉ asᵉ
[A001175](https://oeis.org/A001175ᵉ) in theᵉ OEIS.ᵉ

## Definitions

### The Fibonacci sequence on `Fin (k + 1) × Fin (k + 1)`

```agda
generating-map-fibonacci-pair-Finᵉ :
  (kᵉ : ℕᵉ) → Finᵉ (succ-ℕᵉ kᵉ) ×ᵉ Finᵉ (succ-ℕᵉ kᵉ) → Finᵉ (succ-ℕᵉ kᵉ) ×ᵉ Finᵉ (succ-ℕᵉ kᵉ)
generating-map-fibonacci-pair-Finᵉ kᵉ pᵉ =
  pairᵉ (pr2ᵉ pᵉ) (add-Finᵉ (succ-ℕᵉ kᵉ) (pr2ᵉ pᵉ) (pr1ᵉ pᵉ))

inv-generating-map-fibonacci-pair-Finᵉ :
  (kᵉ : ℕᵉ) → Finᵉ (succ-ℕᵉ kᵉ) ×ᵉ Finᵉ (succ-ℕᵉ kᵉ) → Finᵉ (succ-ℕᵉ kᵉ) ×ᵉ Finᵉ (succ-ℕᵉ kᵉ)
inv-generating-map-fibonacci-pair-Finᵉ kᵉ (pairᵉ xᵉ yᵉ) =
  pairᵉ (add-Finᵉ (succ-ℕᵉ kᵉ) yᵉ (neg-Finᵉ (succ-ℕᵉ kᵉ) xᵉ)) xᵉ

is-section-inv-generating-map-fibonacci-pair-Finᵉ :
  (kᵉ : ℕᵉ) (pᵉ : Finᵉ (succ-ℕᵉ kᵉ) ×ᵉ Finᵉ (succ-ℕᵉ kᵉ)) →
  Idᵉ
    ( generating-map-fibonacci-pair-Finᵉ kᵉ
      ( inv-generating-map-fibonacci-pair-Finᵉ kᵉ pᵉ))
    ( pᵉ)
is-section-inv-generating-map-fibonacci-pair-Finᵉ kᵉ (pairᵉ xᵉ yᵉ) =
  ap-binaryᵉ pairᵉ reflᵉ
    ( ( commutative-add-Finᵉ
        ( succ-ℕᵉ kᵉ)
        ( xᵉ)
        ( add-Finᵉ (succ-ℕᵉ kᵉ) yᵉ (neg-Finᵉ (succ-ℕᵉ kᵉ) xᵉ))) ∙ᵉ
      ( ( associative-add-Finᵉ (succ-ℕᵉ kᵉ) yᵉ (neg-Finᵉ (succ-ℕᵉ kᵉ) xᵉ) xᵉ) ∙ᵉ
        ( ( apᵉ (add-Finᵉ (succ-ℕᵉ kᵉ) yᵉ) (left-inverse-law-add-Finᵉ kᵉ xᵉ)) ∙ᵉ
          ( right-unit-law-add-Finᵉ kᵉ yᵉ))))

is-retraction-inv-generating-map-fibonacci-pair-Finᵉ :
  (kᵉ : ℕᵉ) (pᵉ : Finᵉ (succ-ℕᵉ kᵉ) ×ᵉ Finᵉ (succ-ℕᵉ kᵉ)) →
  Idᵉ
    ( inv-generating-map-fibonacci-pair-Finᵉ kᵉ
      ( generating-map-fibonacci-pair-Finᵉ kᵉ pᵉ))
    ( pᵉ)
is-retraction-inv-generating-map-fibonacci-pair-Finᵉ kᵉ (pairᵉ xᵉ yᵉ) =
  ap-binaryᵉ pairᵉ
    ( ( commutative-add-Finᵉ
        ( succ-ℕᵉ kᵉ)
        ( add-Finᵉ (succ-ℕᵉ kᵉ) yᵉ xᵉ)
        ( neg-Finᵉ (succ-ℕᵉ kᵉ) yᵉ)) ∙ᵉ
      ( ( invᵉ (associative-add-Finᵉ (succ-ℕᵉ kᵉ) (neg-Finᵉ (succ-ℕᵉ kᵉ) yᵉ) yᵉ xᵉ)) ∙ᵉ
        ( ( apᵉ (λ tᵉ → add-Finᵉ (succ-ℕᵉ kᵉ) tᵉ xᵉ) (left-inverse-law-add-Finᵉ kᵉ yᵉ)) ∙ᵉ
          ( left-unit-law-add-Finᵉ kᵉ xᵉ))))
    ( reflᵉ)

is-equiv-generating-map-fibonacci-pair-Finᵉ :
  (kᵉ : ℕᵉ) → is-equivᵉ (generating-map-fibonacci-pair-Finᵉ kᵉ)
is-equiv-generating-map-fibonacci-pair-Finᵉ kᵉ =
  is-equiv-is-invertibleᵉ
    ( inv-generating-map-fibonacci-pair-Finᵉ kᵉ)
    ( is-section-inv-generating-map-fibonacci-pair-Finᵉ kᵉ)
    ( is-retraction-inv-generating-map-fibonacci-pair-Finᵉ kᵉ)

fibonacci-pair-Finᵉ :
  (kᵉ : ℕᵉ) → ℕᵉ → Finᵉ (succ-ℕᵉ kᵉ) ×ᵉ Finᵉ (succ-ℕᵉ kᵉ)
fibonacci-pair-Finᵉ kᵉ zero-ℕᵉ = pairᵉ (zero-Finᵉ kᵉ) (one-Finᵉ kᵉ)
fibonacci-pair-Finᵉ kᵉ (succ-ℕᵉ nᵉ) =
  generating-map-fibonacci-pair-Finᵉ kᵉ (fibonacci-pair-Finᵉ kᵉ nᵉ)

compute-fibonacci-pair-Finᵉ :
  (kᵉ : ℕᵉ) (nᵉ : ℕᵉ) →
  Idᵉ
    ( fibonacci-pair-Finᵉ kᵉ nᵉ)
    ( mod-succ-ℕᵉ kᵉ (Fibonacci-ℕᵉ nᵉ) ,ᵉ mod-succ-ℕᵉ kᵉ (Fibonacci-ℕᵉ (succ-ℕᵉ nᵉ)))
compute-fibonacci-pair-Finᵉ kᵉ zero-ℕᵉ = reflᵉ
compute-fibonacci-pair-Finᵉ kᵉ (succ-ℕᵉ zero-ℕᵉ) =
  ap-binaryᵉ pairᵉ reflᵉ (right-unit-law-add-Finᵉ kᵉ (one-Finᵉ kᵉ))
compute-fibonacci-pair-Finᵉ kᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)) =
  ap-binaryᵉ pairᵉ
    ( apᵉ pr2ᵉ (compute-fibonacci-pair-Finᵉ kᵉ (succ-ℕᵉ nᵉ)))
    ( ( ap-binaryᵉ
        ( add-Finᵉ (succ-ℕᵉ kᵉ))
        ( apᵉ pr2ᵉ (compute-fibonacci-pair-Finᵉ kᵉ (succ-ℕᵉ nᵉ)))
        ( apᵉ pr1ᵉ (compute-fibonacci-pair-Finᵉ kᵉ (succ-ℕᵉ nᵉ)))) ∙ᵉ
      ( invᵉ
        ( mod-succ-add-ℕᵉ kᵉ
          ( Fibonacci-ℕᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)))
          ( Fibonacci-ℕᵉ (succ-ℕᵉ nᵉ)))))
```

### Repetitions in the Fibonacci sequence on `Fin (k + 1) × Fin (k + 1)`

```agda
has-ordered-repetition-fibonacci-pair-Finᵉ :
  (kᵉ : ℕᵉ) → ordered-repetition-of-values-ℕᵉ (fibonacci-pair-Finᵉ kᵉ)
has-ordered-repetition-fibonacci-pair-Finᵉ kᵉ =
  ordered-repetition-of-values-nat-to-countᵉ
    ( count-productᵉ (count-Finᵉ (succ-ℕᵉ kᵉ)) (count-Finᵉ (succ-ℕᵉ kᵉ)))
    ( fibonacci-pair-Finᵉ kᵉ)

is-ordered-repetition-fibonacci-pair-Finᵉ : ℕᵉ → ℕᵉ → UUᵉ lzero
is-ordered-repetition-fibonacci-pair-Finᵉ kᵉ xᵉ =
  Σᵉ ℕᵉ (λ yᵉ → (le-ℕᵉ yᵉ xᵉ) ×ᵉ (fibonacci-pair-Finᵉ kᵉ yᵉ ＝ᵉ fibonacci-pair-Finᵉ kᵉ xᵉ))

minimal-ordered-repetition-fibonacci-pair-Finᵉ :
  (kᵉ : ℕᵉ) → minimal-element-ℕᵉ (is-ordered-repetition-fibonacci-pair-Finᵉ kᵉ)
minimal-ordered-repetition-fibonacci-pair-Finᵉ kᵉ =
  minimal-element-repetition-of-values-sequence-countᵉ
    ( count-productᵉ (count-Finᵉ (succ-ℕᵉ kᵉ)) (count-Finᵉ (succ-ℕᵉ kᵉ)))
    ( fibonacci-pair-Finᵉ kᵉ)
```

### The Pisano periods

```agda
pisano-periodᵉ : ℕᵉ → ℕᵉ
pisano-periodᵉ kᵉ = pr1ᵉ (minimal-ordered-repetition-fibonacci-pair-Finᵉ kᵉ)

is-ordered-repetition-pisano-periodᵉ :
  (kᵉ : ℕᵉ) → is-ordered-repetition-fibonacci-pair-Finᵉ kᵉ (pisano-periodᵉ kᵉ)
is-ordered-repetition-pisano-periodᵉ kᵉ =
  pr1ᵉ (pr2ᵉ (minimal-ordered-repetition-fibonacci-pair-Finᵉ kᵉ))

is-lower-bound-pisano-periodᵉ :
  (kᵉ : ℕᵉ) →
  is-lower-bound-ℕᵉ
    ( is-ordered-repetition-fibonacci-pair-Finᵉ kᵉ)
    ( pisano-periodᵉ kᵉ)
is-lower-bound-pisano-periodᵉ kᵉ =
  pr2ᵉ (pr2ᵉ (minimal-ordered-repetition-fibonacci-pair-Finᵉ kᵉ))

cases-is-repetition-of-zero-pisano-periodᵉ :
  (kᵉ xᵉ yᵉ : ℕᵉ) → Idᵉ (pr1ᵉ (is-ordered-repetition-pisano-periodᵉ kᵉ)) xᵉ →
  Idᵉ (pisano-periodᵉ kᵉ) yᵉ → is-zero-ℕᵉ xᵉ
cases-is-repetition-of-zero-pisano-periodᵉ kᵉ zero-ℕᵉ yᵉ pᵉ qᵉ = reflᵉ
cases-is-repetition-of-zero-pisano-periodᵉ kᵉ (succ-ℕᵉ xᵉ) zero-ℕᵉ pᵉ qᵉ =
  ex-falsoᵉ
    ( concatenate-eq-le-eq-ℕᵉ
      ( invᵉ pᵉ)
      ( pr1ᵉ (pr2ᵉ (is-ordered-repetition-pisano-periodᵉ kᵉ)))
      ( qᵉ))
cases-is-repetition-of-zero-pisano-periodᵉ kᵉ (succ-ℕᵉ xᵉ) (succ-ℕᵉ yᵉ) pᵉ qᵉ =
  ex-falsoᵉ
    ( contradiction-leq-ℕᵉ yᵉ yᵉ (refl-leq-ℕᵉ yᵉ)
      ( concatenate-eq-leq-ℕᵉ yᵉ (invᵉ qᵉ) (is-lower-bound-pisano-periodᵉ kᵉ yᵉ Rᵉ)))
  where
  Rᵉ : is-ordered-repetition-fibonacci-pair-Finᵉ kᵉ yᵉ
  Rᵉ = tripleᵉ xᵉ
        ( concatenate-eq-le-eq-ℕᵉ
          ( invᵉ pᵉ)
          ( pr1ᵉ (pr2ᵉ (is-ordered-repetition-pisano-periodᵉ kᵉ)))
          ( qᵉ))
        ( is-injective-is-equivᵉ
          ( is-equiv-generating-map-fibonacci-pair-Finᵉ kᵉ)
          ( ( apᵉ (fibonacci-pair-Finᵉ kᵉ) (invᵉ pᵉ)) ∙ᵉ
            ( ( pr2ᵉ (pr2ᵉ (is-ordered-repetition-pisano-periodᵉ kᵉ))) ∙ᵉ
              ( apᵉ (fibonacci-pair-Finᵉ kᵉ) qᵉ))))

is-repetition-of-zero-pisano-periodᵉ :
  (kᵉ : ℕᵉ) → is-zero-ℕᵉ (pr1ᵉ (is-ordered-repetition-pisano-periodᵉ kᵉ))
is-repetition-of-zero-pisano-periodᵉ kᵉ =
  cases-is-repetition-of-zero-pisano-periodᵉ kᵉ
    ( pr1ᵉ (is-ordered-repetition-pisano-periodᵉ kᵉ))
    ( pisano-periodᵉ kᵉ)
    ( reflᵉ)
    ( reflᵉ)

compute-fibonacci-pair-Fin-pisano-periodᵉ :
  (kᵉ : ℕᵉ) →
  Idᵉ (fibonacci-pair-Finᵉ kᵉ (pisano-periodᵉ kᵉ)) (fibonacci-pair-Finᵉ kᵉ zero-ℕᵉ)
compute-fibonacci-pair-Fin-pisano-periodᵉ kᵉ =
  ( invᵉ (pr2ᵉ (pr2ᵉ (is-ordered-repetition-pisano-periodᵉ kᵉ)))) ∙ᵉ
  ( apᵉ (fibonacci-pair-Finᵉ kᵉ) (is-repetition-of-zero-pisano-periodᵉ kᵉ))
```

## Properties

### Pisano periods are nonzero

```agda
le-zero-pisano-periodᵉ :
  (kᵉ : ℕᵉ) → le-ℕᵉ zero-ℕᵉ (pisano-periodᵉ kᵉ)
le-zero-pisano-periodᵉ kᵉ =
  concatenate-eq-le-ℕᵉ
    { xᵉ = zero-ℕᵉ}
    { yᵉ = pr1ᵉ (is-ordered-repetition-pisano-periodᵉ kᵉ)}
    { zᵉ = pisano-periodᵉ kᵉ}
    ( invᵉ (is-repetition-of-zero-pisano-periodᵉ kᵉ))
    ( pr1ᵉ (pr2ᵉ (is-ordered-repetition-pisano-periodᵉ kᵉ)))

is-nonzero-pisano-periodᵉ :
  (kᵉ : ℕᵉ) → is-nonzero-ℕᵉ (pisano-periodᵉ kᵉ)
is-nonzero-pisano-periodᵉ kᵉ pᵉ =
  ex-falsoᵉ (concatenate-le-eq-ℕᵉ (le-zero-pisano-periodᵉ kᵉ) pᵉ)
```

### `k + 1` divides the Fibonacci number at `pisano-period k`

```agda
div-fibonacci-pisano-periodᵉ :
  (kᵉ : ℕᵉ) → div-ℕᵉ (succ-ℕᵉ kᵉ) (Fibonacci-ℕᵉ (pisano-periodᵉ kᵉ))
div-fibonacci-pisano-periodᵉ kᵉ =
  div-is-zero-mod-succ-ℕᵉ kᵉ
    ( Fibonacci-ℕᵉ (pisano-periodᵉ kᵉ))
    ( ( apᵉ pr1ᵉ (invᵉ (compute-fibonacci-pair-Finᵉ kᵉ (pisano-periodᵉ kᵉ)))) ∙ᵉ
      ( invᵉ
        ( apᵉ pr1ᵉ
          { xᵉ = fibonacci-pair-Finᵉ kᵉ zero-ℕᵉ}
          { yᵉ = fibonacci-pair-Finᵉ kᵉ (pisano-periodᵉ kᵉ)}
          ( ( apᵉ
              ( fibonacci-pair-Finᵉ kᵉ)
              ( invᵉ (is-repetition-of-zero-pisano-periodᵉ kᵉ))) ∙ᵉ
            ( pr2ᵉ (pr2ᵉ (is-ordered-repetition-pisano-periodᵉ kᵉ)))))))
```