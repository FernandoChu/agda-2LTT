# The cofibonacci sequence

```agda
module elementary-number-theory.cofibonacciᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.divisibility-natural-numbersᵉ
open import elementary-number-theory.equality-natural-numbersᵉ
open import elementary-number-theory.fibonacci-sequenceᵉ
open import elementary-number-theory.inequality-natural-numbersᵉ
open import elementary-number-theory.modular-arithmetic-standard-finite-typesᵉ
open import elementary-number-theory.natural-numbersᵉ
open import elementary-number-theory.pisano-periodsᵉ
open import elementary-number-theory.well-ordering-principle-natural-numbersᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.cartesian-product-typesᵉ
open import foundation.decidable-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.empty-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Theᵉ [**cofibonacciᵉ sequence**][1ᵉ] isᵉ theᵉ uniqueᵉ functionᵉ Gᵉ : ℕᵉ → ℕᵉ satisfyingᵉ
theᵉ propertyᵉ thatᵉ

```text
  div-ℕᵉ (Gᵉ mᵉ) nᵉ ↔ᵉ div-ℕᵉ mᵉ (Fibonacci-ℕᵉ n).ᵉ
```

## Definitions

### The predicate of being a multiple of the `m`-th cofibonacci number

```agda
is-multiple-of-cofibonacciᵉ : (mᵉ xᵉ : ℕᵉ) → UUᵉ lzero
is-multiple-of-cofibonacciᵉ mᵉ xᵉ =
  is-nonzero-ℕᵉ mᵉ → is-nonzero-ℕᵉ xᵉ ×ᵉ div-ℕᵉ mᵉ (Fibonacci-ℕᵉ xᵉ)

is-decidable-is-multiple-of-cofibonacciᵉ :
  (mᵉ xᵉ : ℕᵉ) → is-decidableᵉ (is-multiple-of-cofibonacciᵉ mᵉ xᵉ)
is-decidable-is-multiple-of-cofibonacciᵉ mᵉ xᵉ =
  is-decidable-function-typeᵉ
    ( is-decidable-is-nonzero-ℕᵉ mᵉ)
    ( is-decidable-productᵉ
      ( is-decidable-is-nonzero-ℕᵉ xᵉ)
      ( is-decidable-div-ℕᵉ mᵉ (Fibonacci-ℕᵉ xᵉ)))

cofibonacci-multipleᵉ : (mᵉ : ℕᵉ) → Σᵉ ℕᵉ (is-multiple-of-cofibonacciᵉ mᵉ)
cofibonacci-multipleᵉ zero-ℕᵉ = pairᵉ zero-ℕᵉ (λ fᵉ → (ex-falsoᵉ (fᵉ reflᵉ)))
cofibonacci-multipleᵉ (succ-ℕᵉ mᵉ) =
  pairᵉ
    ( pisano-periodᵉ mᵉ)
    ( λ fᵉ → pairᵉ (is-nonzero-pisano-periodᵉ mᵉ) (div-fibonacci-pisano-periodᵉ mᵉ))
```

### The cofibonacci sequence

```agda
least-multiple-of-cofibonacciᵉ :
  (mᵉ : ℕᵉ) → minimal-element-ℕᵉ (is-multiple-of-cofibonacciᵉ mᵉ)
least-multiple-of-cofibonacciᵉ mᵉ =
  well-ordering-principle-ℕᵉ
    ( is-multiple-of-cofibonacciᵉ mᵉ)
    ( is-decidable-is-multiple-of-cofibonacciᵉ mᵉ)
    ( cofibonacci-multipleᵉ mᵉ)

cofibonacciᵉ : ℕᵉ → ℕᵉ
cofibonacciᵉ mᵉ = pr1ᵉ (least-multiple-of-cofibonacciᵉ mᵉ)

is-multiple-of-cofibonacci-cofibonacciᵉ :
  (mᵉ : ℕᵉ) → is-multiple-of-cofibonacciᵉ mᵉ (cofibonacciᵉ mᵉ)
is-multiple-of-cofibonacci-cofibonacciᵉ mᵉ =
  pr1ᵉ (pr2ᵉ (least-multiple-of-cofibonacciᵉ mᵉ))

is-lower-bound-cofibonacciᵉ :
  (mᵉ xᵉ : ℕᵉ) → is-multiple-of-cofibonacciᵉ mᵉ xᵉ →
  cofibonacciᵉ mᵉ ≤-ℕᵉ xᵉ
is-lower-bound-cofibonacciᵉ mᵉ =
  pr2ᵉ (pr2ᵉ (least-multiple-of-cofibonacciᵉ mᵉ))
```

## Properties

### The `0`-th cofibonacci number is `0`

```agda
is-zero-cofibonacci-zero-ℕᵉ : is-zero-ℕᵉ (cofibonacciᵉ zero-ℕᵉ)
is-zero-cofibonacci-zero-ℕᵉ =
  is-zero-leq-zero-ℕᵉ
    ( cofibonacciᵉ zero-ℕᵉ)
    ( is-lower-bound-cofibonacciᵉ zero-ℕᵉ zero-ℕᵉ ( λ fᵉ → ex-falsoᵉ (fᵉ reflᵉ)))
```

### The cofibonacci sequence is left adjoint to the Fibonacci sequence

```agda
forward-is-left-adjoint-cofibonacciᵉ :
  (mᵉ nᵉ : ℕᵉ) → div-ℕᵉ (cofibonacciᵉ mᵉ) nᵉ → div-ℕᵉ mᵉ (Fibonacci-ℕᵉ nᵉ)
forward-is-left-adjoint-cofibonacciᵉ zero-ℕᵉ nᵉ Hᵉ =
  trᵉ
    ( div-ℕᵉ zero-ℕᵉ)
    ( apᵉ
      ( Fibonacci-ℕᵉ)
      ( invᵉ
        ( is-zero-div-zero-ℕᵉ nᵉ
          ( trᵉ (λ tᵉ → div-ℕᵉ tᵉ nᵉ) is-zero-cofibonacci-zero-ℕᵉ Hᵉ))))
    ( refl-div-ℕᵉ zero-ℕᵉ)
forward-is-left-adjoint-cofibonacciᵉ (succ-ℕᵉ mᵉ) zero-ℕᵉ Hᵉ =
  div-zero-ℕᵉ (succ-ℕᵉ mᵉ)
forward-is-left-adjoint-cofibonacciᵉ (succ-ℕᵉ mᵉ) (succ-ℕᵉ nᵉ) Hᵉ =
  div-Fibonacci-div-ℕᵉ
    ( succ-ℕᵉ mᵉ)
    ( cofibonacciᵉ (succ-ℕᵉ mᵉ))
    ( succ-ℕᵉ nᵉ)
    ( Hᵉ)
    ( pr2ᵉ
      ( is-multiple-of-cofibonacci-cofibonacciᵉ
        ( succ-ℕᵉ mᵉ)
        ( is-nonzero-succ-ℕᵉ mᵉ)))

{-ᵉ
converse-is-left-adjoint-cofibonacciᵉ :
  (mᵉ nᵉ : ℕᵉ) → div-ℕᵉ mᵉ (Fibonacci-ℕᵉ nᵉ) → div-ℕᵉ (cofibonacciᵉ mᵉ) nᵉ
converse-is-left-adjoint-cofibonacciᵉ mᵉ nᵉ Hᵉ = {!!ᵉ}

is-left-adjoint-cofibonacciᵉ :
  (mᵉ nᵉ : ℕᵉ) → div-ℕᵉ (cofibonacciᵉ mᵉ) nᵉ ↔ᵉ div-ℕᵉ mᵉ (Fibonacci-ℕᵉ nᵉ)
is-left-adjoint-cofibonacciᵉ mᵉ nᵉ = {!!ᵉ}
-ᵉ}
```

## External links

[1ᵉ]: https://oeis.org/A001177ᵉ