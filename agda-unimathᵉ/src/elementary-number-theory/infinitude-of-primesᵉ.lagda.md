# The infinitude of primes

```agda
module elementary-number-theory.infinitude-of-primesᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.divisibility-natural-numbersᵉ
open import elementary-number-theory.equality-natural-numbersᵉ
open import elementary-number-theory.factorialsᵉ
open import elementary-number-theory.lower-bounds-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ
open import elementary-number-theory.prime-numbersᵉ
open import elementary-number-theory.proper-divisors-natural-numbersᵉ
open import elementary-number-theory.sieve-of-eratosthenesᵉ
open import elementary-number-theory.strict-inequality-natural-numbersᵉ
open import elementary-number-theory.well-ordering-principle-natural-numbersᵉ

open import foundation.cartesian-product-typesᵉ
open import foundation.coproduct-typesᵉ
open import foundation.decidable-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.empty-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.iterating-functionsᵉ
open import foundation.negationᵉ
open import foundation.type-arithmetic-empty-typeᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Weᵉ show,ᵉ using theᵉ sieveᵉ ofᵉ Eratosthenesᵉ andᵉ theᵉ well-orderingᵉ principleᵉ ofᵉ `ℕ`,ᵉ
thatᵉ thereᵉ areᵉ infinitelyᵉ manyᵉ primes.ᵉ Consequentlyᵉ weᵉ obtainᵉ theᵉ functionᵉ thatᵉ
returnsᵉ forᵉ eachᵉ `n`ᵉ theᵉ `n`-thᵉ prime,ᵉ andᵉ weᵉ obtainᵉ theᵉ functionᵉ thatᵉ countsᵉ
theᵉ numberᵉ ofᵉ primesᵉ belowᵉ aᵉ numberᵉ `n`.ᵉ

## Definition

Weᵉ beginᵉ byᵉ statingᵉ theᵉ infinitudeᵉ ofᵉ primesᵉ in typeᵉ theory.ᵉ

```agda
Infinitude-Of-Primes-ℕᵉ : UUᵉ lzero
Infinitude-Of-Primes-ℕᵉ = (nᵉ : ℕᵉ) → Σᵉ ℕᵉ (λ pᵉ → is-prime-ℕᵉ pᵉ ×ᵉ le-ℕᵉ nᵉ pᵉ)
```

## Theorem

### The infinitude of primes

```agda
minimal-element-in-sieve-of-eratosthenes-ℕᵉ :
  (nᵉ : ℕᵉ) → minimal-element-ℕᵉ (in-sieve-of-eratosthenes-ℕᵉ nᵉ)
minimal-element-in-sieve-of-eratosthenes-ℕᵉ nᵉ =
  well-ordering-principle-ℕᵉ
    ( in-sieve-of-eratosthenes-ℕᵉ nᵉ)
    ( is-decidable-in-sieve-of-eratosthenes-ℕᵉ nᵉ)
    ( pairᵉ
      ( succ-ℕᵉ (factorial-ℕᵉ nᵉ))
      ( in-sieve-of-eratosthenes-succ-factorial-ℕᵉ nᵉ))

larger-prime-ℕᵉ : ℕᵉ → ℕᵉ
larger-prime-ℕᵉ nᵉ = pr1ᵉ (minimal-element-in-sieve-of-eratosthenes-ℕᵉ nᵉ)

in-sieve-of-eratosthenes-larger-prime-ℕᵉ :
  (nᵉ : ℕᵉ) → in-sieve-of-eratosthenes-ℕᵉ nᵉ (larger-prime-ℕᵉ nᵉ)
in-sieve-of-eratosthenes-larger-prime-ℕᵉ nᵉ =
  pr1ᵉ (pr2ᵉ (minimal-element-in-sieve-of-eratosthenes-ℕᵉ nᵉ))

is-one-is-divisor-below-larger-prime-ℕᵉ :
  (nᵉ : ℕᵉ) → is-one-is-divisor-below-ℕᵉ nᵉ (larger-prime-ℕᵉ nᵉ)
is-one-is-divisor-below-larger-prime-ℕᵉ nᵉ =
  pr2ᵉ (in-sieve-of-eratosthenes-larger-prime-ℕᵉ nᵉ)

le-larger-prime-ℕᵉ : (nᵉ : ℕᵉ) → le-ℕᵉ nᵉ (larger-prime-ℕᵉ nᵉ)
le-larger-prime-ℕᵉ nᵉ = pr1ᵉ (in-sieve-of-eratosthenes-larger-prime-ℕᵉ nᵉ)

is-nonzero-larger-prime-ℕᵉ : (nᵉ : ℕᵉ) → is-nonzero-ℕᵉ (larger-prime-ℕᵉ nᵉ)
is-nonzero-larger-prime-ℕᵉ nᵉ =
  is-nonzero-le-ℕᵉ nᵉ (larger-prime-ℕᵉ nᵉ) (le-larger-prime-ℕᵉ nᵉ)

is-lower-bound-larger-prime-ℕᵉ :
  (nᵉ : ℕᵉ) → is-lower-bound-ℕᵉ (in-sieve-of-eratosthenes-ℕᵉ nᵉ) (larger-prime-ℕᵉ nᵉ)
is-lower-bound-larger-prime-ℕᵉ nᵉ =
  pr2ᵉ (pr2ᵉ (minimal-element-in-sieve-of-eratosthenes-ℕᵉ nᵉ))

is-not-one-larger-prime-ℕᵉ :
  (nᵉ : ℕᵉ) → is-nonzero-ℕᵉ nᵉ → is-not-one-ℕᵉ (larger-prime-ℕᵉ nᵉ)
is-not-one-larger-prime-ℕᵉ nᵉ Hᵉ pᵉ with is-successor-is-nonzero-ℕᵉ Hᵉ
... | pairᵉ kᵉ reflᵉ =
  neq-le-ℕᵉ {1ᵉ} {larger-prime-ℕᵉ nᵉ}
    ( concatenate-leq-le-ℕᵉ {1ᵉ} {succ-ℕᵉ kᵉ} {larger-prime-ℕᵉ nᵉ} starᵉ
      ( le-larger-prime-ℕᵉ (succ-ℕᵉ kᵉ)))
    ( invᵉ pᵉ)

not-in-sieve-of-eratosthenes-is-proper-divisor-larger-prime-ℕᵉ :
  (nᵉ xᵉ : ℕᵉ) → is-proper-divisor-ℕᵉ (larger-prime-ℕᵉ nᵉ) xᵉ →
  ¬ᵉ (in-sieve-of-eratosthenes-ℕᵉ nᵉ xᵉ)
not-in-sieve-of-eratosthenes-is-proper-divisor-larger-prime-ℕᵉ nᵉ xᵉ Hᵉ Kᵉ =
  ex-falsoᵉ
    ( contradiction-le-ℕᵉ xᵉ (larger-prime-ℕᵉ nᵉ)
      ( le-is-proper-divisor-ℕᵉ xᵉ (larger-prime-ℕᵉ nᵉ)
        ( is-nonzero-larger-prime-ℕᵉ nᵉ)
        ( Hᵉ))
      ( is-lower-bound-larger-prime-ℕᵉ nᵉ xᵉ Kᵉ))

is-one-is-proper-divisor-larger-prime-ℕᵉ :
  (nᵉ : ℕᵉ) → is-nonzero-ℕᵉ nᵉ → is-one-is-proper-divisor-ℕᵉ (larger-prime-ℕᵉ nᵉ)
is-one-is-proper-divisor-larger-prime-ℕᵉ nᵉ Hᵉ xᵉ (pairᵉ fᵉ Kᵉ) =
  is-one-is-divisor-below-larger-prime-ℕᵉ nᵉ xᵉ
    ( leq-not-le-ℕᵉ nᵉ xᵉ
      ( is-empty-left-factor-is-empty-productᵉ
        ( not-in-sieve-of-eratosthenes-is-proper-divisor-larger-prime-ℕᵉ nᵉ xᵉ
          ( pairᵉ fᵉ Kᵉ))
        ( λ yᵉ lᵉ dᵉ →
          is-one-is-divisor-below-larger-prime-ℕᵉ nᵉ yᵉ lᵉ
            ( transitive-div-ℕᵉ yᵉ xᵉ (larger-prime-ℕᵉ nᵉ) Kᵉ dᵉ))))
    ( Kᵉ)

is-prime-larger-prime-ℕᵉ :
  (nᵉ : ℕᵉ) → is-nonzero-ℕᵉ nᵉ → is-prime-ℕᵉ (larger-prime-ℕᵉ nᵉ)
is-prime-larger-prime-ℕᵉ nᵉ Hᵉ =
  is-prime-is-prime-easy-ℕᵉ
    ( larger-prime-ℕᵉ nᵉ)
    ( pairᵉ
      ( is-not-one-larger-prime-ℕᵉ nᵉ Hᵉ)
      ( is-one-is-proper-divisor-larger-prime-ℕᵉ nᵉ Hᵉ))

infinitude-of-primes-ℕᵉ : Infinitude-Of-Primes-ℕᵉ
infinitude-of-primes-ℕᵉ nᵉ with is-decidable-is-zero-ℕᵉ nᵉ
... | inlᵉ reflᵉ = pairᵉ 2 (pairᵉ is-prime-two-ℕᵉ starᵉ)
... | inrᵉ Hᵉ =
  pairᵉ
    ( larger-prime-ℕᵉ nᵉ)
    ( pairᵉ
      ( is-prime-larger-prime-ℕᵉ nᵉ Hᵉ)
      ( le-larger-prime-ℕᵉ nᵉ))
```

## Consequences

### The function that returns the `n`-th prime

Theᵉ functionᵉ `prime-ℕ`ᵉ isᵉ definedᵉ to startᵉ atᵉ `prime-ℕᵉ 0 :=ᵉ 2`ᵉ

```agda
prime-ℕᵉ : ℕᵉ → ℕᵉ
prime-ℕᵉ nᵉ = iterateᵉ (succ-ℕᵉ nᵉ) (λ xᵉ → pr1ᵉ (infinitude-of-primes-ℕᵉ xᵉ)) 0

is-prime-prime-ℕᵉ : (nᵉ : ℕᵉ) → is-prime-ℕᵉ (prime-ℕᵉ nᵉ)
is-prime-prime-ℕᵉ zero-ℕᵉ = pr1ᵉ (pr2ᵉ (infinitude-of-primes-ℕᵉ 0ᵉ))
is-prime-prime-ℕᵉ (succ-ℕᵉ nᵉ) = pr1ᵉ (pr2ᵉ (infinitude-of-primes-ℕᵉ (prime-ℕᵉ nᵉ)))
```

### The prime counting function

Theᵉ primeᵉ countingᵉ functionᵉ isᵉ definedᵉ suchᵉ thatᵉ `prime-counting-ℕᵉ n`ᵉ isᵉ theᵉ
numberᵉ ofᵉ primesᵉ `≤ᵉ n`ᵉ

```agda
prime-counting-succ-ℕᵉ :
  (nᵉ : ℕᵉ) → is-decidableᵉ (is-prime-ℕᵉ (succ-ℕᵉ nᵉ)) → ℕᵉ → ℕᵉ
prime-counting-succ-ℕᵉ nᵉ (inlᵉ dᵉ) xᵉ = succ-ℕᵉ xᵉ
prime-counting-succ-ℕᵉ nᵉ (inrᵉ dᵉ) xᵉ = xᵉ

prime-counting-ℕᵉ : ℕᵉ → ℕᵉ
prime-counting-ℕᵉ zero-ℕᵉ = zero-ℕᵉ
prime-counting-ℕᵉ (succ-ℕᵉ nᵉ) =
  prime-counting-succ-ℕᵉ nᵉ
    ( is-decidable-is-prime-ℕᵉ (succ-ℕᵉ nᵉ))
    ( prime-counting-ℕᵉ nᵉ)
```