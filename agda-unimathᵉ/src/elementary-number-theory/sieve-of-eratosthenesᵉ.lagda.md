# The sieve of Eratosthenes

```agda
module elementary-number-theory.sieve-of-eratosthenesᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.decidable-typesᵉ
open import elementary-number-theory.divisibility-natural-numbersᵉ
open import elementary-number-theory.equality-natural-numbersᵉ
open import elementary-number-theory.factorialsᵉ
open import elementary-number-theory.inequality-natural-numbersᵉ
open import elementary-number-theory.modular-arithmetic-standard-finite-typesᵉ
open import elementary-number-theory.multiplication-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ
open import elementary-number-theory.strict-inequality-natural-numbersᵉ

open import foundation.cartesian-product-typesᵉ
open import foundation.coproduct-typesᵉ
open import foundation.decidable-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.empty-typesᵉ
open import foundation.function-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Theᵉ sieveᵉ ofᵉ Erathostenesᵉ isᵉ aᵉ sequenceᵉ ofᵉ subsetsᵉ ofᵉ theᵉ naturalᵉ numbersᵉ usedᵉ
to proveᵉ theᵉ infinitudeᵉ ofᵉ primes.ᵉ

## Definition

```agda
is-one-is-divisor-below-ℕᵉ : ℕᵉ → ℕᵉ → UUᵉ lzero
is-one-is-divisor-below-ℕᵉ nᵉ aᵉ =
  (xᵉ : ℕᵉ) → leq-ℕᵉ xᵉ nᵉ → div-ℕᵉ xᵉ aᵉ → is-one-ℕᵉ xᵉ

in-sieve-of-eratosthenes-ℕᵉ : ℕᵉ → ℕᵉ → UUᵉ lzero
in-sieve-of-eratosthenes-ℕᵉ nᵉ aᵉ =
  (le-ℕᵉ nᵉ aᵉ) ×ᵉ (is-one-is-divisor-below-ℕᵉ nᵉ aᵉ)

le-in-sieve-of-eratosthenes-ℕᵉ :
  (nᵉ aᵉ : ℕᵉ) → in-sieve-of-eratosthenes-ℕᵉ nᵉ aᵉ → le-ℕᵉ nᵉ aᵉ
le-in-sieve-of-eratosthenes-ℕᵉ nᵉ aᵉ = pr1ᵉ
```

## Properties

### Being in the sieve of Eratosthenes is decidable

```agda
is-decidable-in-sieve-of-eratosthenes-ℕᵉ :
  (nᵉ aᵉ : ℕᵉ) → is-decidableᵉ (in-sieve-of-eratosthenes-ℕᵉ nᵉ aᵉ)
is-decidable-in-sieve-of-eratosthenes-ℕᵉ nᵉ aᵉ =
  is-decidable-productᵉ
    ( is-decidable-le-ℕᵉ nᵉ aᵉ)
    ( is-decidable-bounded-Π-ℕᵉ
      ( λ xᵉ → leq-ℕᵉ xᵉ nᵉ)
      ( λ xᵉ → div-ℕᵉ xᵉ aᵉ → is-one-ℕᵉ xᵉ)
      ( λ xᵉ → is-decidable-leq-ℕᵉ xᵉ nᵉ)
      ( λ xᵉ →
        is-decidable-function-typeᵉ
          ( is-decidable-div-ℕᵉ xᵉ aᵉ)
          ( is-decidable-is-one-ℕᵉ xᵉ))
      ( nᵉ)
      ( λ xᵉ → idᵉ))
```

### The successor of the `n`-th factorial is in the `n`-th sieve

```agda
in-sieve-of-eratosthenes-succ-factorial-ℕᵉ :
  (nᵉ : ℕᵉ) → in-sieve-of-eratosthenes-ℕᵉ nᵉ (succ-ℕᵉ (factorial-ℕᵉ nᵉ))
pr1ᵉ (in-sieve-of-eratosthenes-succ-factorial-ℕᵉ zero-ℕᵉ) = starᵉ
pr2ᵉ (in-sieve-of-eratosthenes-succ-factorial-ℕᵉ zero-ℕᵉ) xᵉ lᵉ dᵉ =
  ex-falsoᵉ
    ( Eq-eq-ℕᵉ
      ( is-zero-is-zero-div-ℕᵉ xᵉ 2 dᵉ (is-zero-leq-zero-ℕᵉ xᵉ lᵉ)))
pr1ᵉ (in-sieve-of-eratosthenes-succ-factorial-ℕᵉ (succ-ℕᵉ nᵉ)) =
  concatenate-leq-le-ℕᵉ
    { succ-ℕᵉ nᵉ}
    { factorial-ℕᵉ (succ-ℕᵉ nᵉ)}
    { succ-ℕᵉ (factorial-ℕᵉ (succ-ℕᵉ nᵉ))}
    ( leq-factorial-ℕᵉ (succ-ℕᵉ nᵉ))
    ( succ-le-ℕᵉ (factorial-ℕᵉ (succ-ℕᵉ nᵉ)))
pr2ᵉ (in-sieve-of-eratosthenes-succ-factorial-ℕᵉ (succ-ℕᵉ nᵉ)) xᵉ lᵉ (pairᵉ yᵉ pᵉ) with
  is-decidable-is-zero-ℕᵉ xᵉ
... | inlᵉ reflᵉ =
  ex-falsoᵉ
    ( is-nonzero-succ-ℕᵉ
      ( factorial-ℕᵉ (succ-ℕᵉ nᵉ))
      ( invᵉ pᵉ ∙ᵉ (right-zero-law-mul-ℕᵉ yᵉ)))
... | inrᵉ fᵉ =
  is-one-div-ℕᵉ xᵉ
    ( factorial-ℕᵉ (succ-ℕᵉ nᵉ))
    ( div-factorial-ℕᵉ (succ-ℕᵉ nᵉ) xᵉ lᵉ fᵉ)
    ( pairᵉ yᵉ pᵉ)
```