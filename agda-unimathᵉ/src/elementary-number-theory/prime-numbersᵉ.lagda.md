# Prime numbers

```agda
module elementary-number-theory.prime-numbersᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.decidable-typesᵉ
open import elementary-number-theory.divisibility-natural-numbersᵉ
open import elementary-number-theory.equality-natural-numbersᵉ
open import elementary-number-theory.inequality-natural-numbersᵉ
open import elementary-number-theory.multiplication-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ
open import elementary-number-theory.proper-divisors-natural-numbersᵉ
open import elementary-number-theory.strict-inequality-natural-numbersᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.cartesian-product-typesᵉ
open import foundation.contractible-typesᵉ
open import foundation.coproduct-typesᵉ
open import foundation.decidable-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.empty-typesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.negated-equalityᵉ
open import foundation.propositionsᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Aᵉ primeᵉ numberᵉ isᵉ aᵉ naturalᵉ numberᵉ ofᵉ whichᵉ 1 isᵉ theᵉ onlyᵉ properᵉ divisor.ᵉ

## Definition

### The main definition of prime numbers

Thisᵉ isᵉ aᵉ directᵉ interpretationᵉ ofᵉ whatᵉ itᵉ meansᵉ to beᵉ prime.ᵉ

```agda
is-prime-ℕᵉ : ℕᵉ → UUᵉ lzero
is-prime-ℕᵉ nᵉ = (xᵉ : ℕᵉ) → (is-proper-divisor-ℕᵉ nᵉ xᵉ ↔ᵉ is-one-ℕᵉ xᵉ)

Prime-ℕᵉ : UUᵉ lzero
Prime-ℕᵉ = Σᵉ ℕᵉ is-prime-ℕᵉ

module _
  (pᵉ : Prime-ℕᵉ)
  where

  nat-Prime-ℕᵉ : ℕᵉ
  nat-Prime-ℕᵉ = pr1ᵉ pᵉ

  is-prime-Prime-ℕᵉ : is-prime-ℕᵉ nat-Prime-ℕᵉ
  is-prime-Prime-ℕᵉ = pr2ᵉ pᵉ
```

### Second definition of prime numbers

Thisᵉ isᵉ anᵉ implementationᵉ ofᵉ theᵉ ideaᵉ ofᵉ beingᵉ prime,ᵉ whichᵉ isᵉ usuallyᵉ takenᵉ asᵉ
theᵉ definition.ᵉ

```agda
is-one-is-proper-divisor-ℕᵉ : ℕᵉ → UUᵉ lzero
is-one-is-proper-divisor-ℕᵉ nᵉ =
  (xᵉ : ℕᵉ) → is-proper-divisor-ℕᵉ nᵉ xᵉ → is-one-ℕᵉ xᵉ

is-prime-easy-ℕᵉ : ℕᵉ → UUᵉ lzero
is-prime-easy-ℕᵉ nᵉ = (is-not-one-ℕᵉ nᵉ) ×ᵉ (is-one-is-proper-divisor-ℕᵉ nᵉ)
```

### Third definition of prime numbers

```agda
has-unique-proper-divisor-ℕᵉ : ℕᵉ → UUᵉ lzero
has-unique-proper-divisor-ℕᵉ nᵉ = is-torsorialᵉ (is-proper-divisor-ℕᵉ nᵉ)
```

## Properties

### The number `0` is not a prime

```agda
is-nonzero-is-prime-ℕᵉ :
  (nᵉ : ℕᵉ) → is-prime-ℕᵉ nᵉ → is-nonzero-ℕᵉ nᵉ
is-nonzero-is-prime-ℕᵉ nᵉ Hᵉ pᵉ =
  is-not-one-two-ℕᵉ
    ( pr1ᵉ
      ( Hᵉ 2ᵉ)
      ( trᵉ (λ kᵉ → 2 ≠ᵉ kᵉ) (invᵉ pᵉ) ( is-nonzero-two-ℕᵉ) ,ᵉ
        trᵉ (div-ℕᵉ 2ᵉ) (invᵉ pᵉ) (0ᵉ ,ᵉ reflᵉ)))
```

### The number `1` is not a prime

```agda
is-not-one-is-prime-ℕᵉ : (nᵉ : ℕᵉ) → is-prime-ℕᵉ nᵉ → is-not-one-ℕᵉ nᵉ
is-not-one-is-prime-ℕᵉ nᵉ Hᵉ pᵉ = pr1ᵉ (pr2ᵉ (Hᵉ 1ᵉ) reflᵉ) (invᵉ pᵉ)
```

### A prime is strictly greater than `1`

```agda
le-one-is-prime-ℕᵉ :
  (nᵉ : ℕᵉ) → is-prime-ℕᵉ nᵉ → le-ℕᵉ 1 nᵉ
le-one-is-prime-ℕᵉ 0 xᵉ = ex-falsoᵉ (is-nonzero-is-prime-ℕᵉ 0 xᵉ reflᵉ)
le-one-is-prime-ℕᵉ 1 xᵉ = ex-falsoᵉ (is-not-one-is-prime-ℕᵉ 1 xᵉ reflᵉ)
le-one-is-prime-ℕᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)) xᵉ = starᵉ
```

### Being a prime is a proposition

```agda
is-prop-is-prime-ℕᵉ :
  (nᵉ : ℕᵉ) → is-propᵉ (is-prime-ℕᵉ nᵉ)
is-prop-is-prime-ℕᵉ nᵉ =
  is-prop-Πᵉ
    ( λ xᵉ →
      is-prop-productᵉ
        ( is-prop-Πᵉ (λ pᵉ → is-set-ℕᵉ xᵉ 1ᵉ))
        ( is-prop-Πᵉ (λ pᵉ → is-prop-is-proper-divisor-ℕᵉ nᵉ xᵉ)))

is-prime-ℕ-Propᵉ :
  (nᵉ : ℕᵉ) → Propᵉ lzero
pr1ᵉ (is-prime-ℕ-Propᵉ nᵉ) = is-prime-ℕᵉ nᵉ
pr2ᵉ (is-prime-ℕ-Propᵉ nᵉ) = is-prop-is-prime-ℕᵉ nᵉ

is-prop-has-unique-proper-divisor-ℕᵉ :
  (nᵉ : ℕᵉ) → is-propᵉ (has-unique-proper-divisor-ℕᵉ nᵉ)
is-prop-has-unique-proper-divisor-ℕᵉ nᵉ = is-property-is-contrᵉ
```

### The three definitions of primes are equivalent

```agda
is-prime-easy-is-prime-ℕᵉ : (nᵉ : ℕᵉ) → is-prime-ℕᵉ nᵉ → is-prime-easy-ℕᵉ nᵉ
pr1ᵉ (is-prime-easy-is-prime-ℕᵉ nᵉ Hᵉ) = is-not-one-is-prime-ℕᵉ nᵉ Hᵉ
pr2ᵉ (is-prime-easy-is-prime-ℕᵉ nᵉ Hᵉ) xᵉ = pr1ᵉ (Hᵉ xᵉ)

is-prime-is-prime-easy-ℕᵉ : (nᵉ : ℕᵉ) → is-prime-easy-ℕᵉ nᵉ → is-prime-ℕᵉ nᵉ
pr1ᵉ (is-prime-is-prime-easy-ℕᵉ nᵉ Hᵉ xᵉ) = pr2ᵉ Hᵉ xᵉ
pr1ᵉ (pr2ᵉ (is-prime-is-prime-easy-ℕᵉ nᵉ Hᵉ .(succ-ℕᵉ zero-ℕᵉ)) reflᵉ) qᵉ = pr1ᵉ Hᵉ (invᵉ qᵉ)
pr2ᵉ (pr2ᵉ (is-prime-is-prime-easy-ℕᵉ nᵉ Hᵉ .(succ-ℕᵉ zero-ℕᵉ)) reflᵉ) = div-one-ℕᵉ nᵉ

has-unique-proper-divisor-is-prime-ℕᵉ :
  (nᵉ : ℕᵉ) → is-prime-ℕᵉ nᵉ → has-unique-proper-divisor-ℕᵉ nᵉ
has-unique-proper-divisor-is-prime-ℕᵉ nᵉ Hᵉ =
  fundamental-theorem-id'ᵉ
    ( λ xᵉ pᵉ → pr2ᵉ (Hᵉ xᵉ) (invᵉ pᵉ))
    ( λ xᵉ →
      is-equiv-has-converse-is-propᵉ
        ( is-set-ℕᵉ 1 xᵉ)
        ( is-prop-is-proper-divisor-ℕᵉ nᵉ xᵉ)
        ( λ pᵉ → invᵉ (pr1ᵉ (Hᵉ xᵉ) pᵉ)))

is-prime-has-unique-proper-divisor-ℕᵉ :
  (nᵉ : ℕᵉ) → has-unique-proper-divisor-ℕᵉ nᵉ → is-prime-ℕᵉ nᵉ
pr1ᵉ (is-prime-has-unique-proper-divisor-ℕᵉ nᵉ Hᵉ xᵉ) Kᵉ =
  apᵉ pr1ᵉ
    ( eq-is-contrᵉ Hᵉ
      { pairᵉ xᵉ Kᵉ}
      { pairᵉ 1 (is-proper-divisor-one-is-proper-divisor-ℕᵉ Kᵉ)})
pr2ᵉ (is-prime-has-unique-proper-divisor-ℕᵉ nᵉ Hᵉ .1ᵉ) reflᵉ =
  is-proper-divisor-one-is-proper-divisor-ℕᵉ (pr2ᵉ (centerᵉ Hᵉ))
```

### Being a prime is decidable

```agda
is-decidable-is-prime-easy-ℕᵉ : (nᵉ : ℕᵉ) → is-decidableᵉ (is-prime-easy-ℕᵉ nᵉ)
is-decidable-is-prime-easy-ℕᵉ zero-ℕᵉ =
  inrᵉ
    ( λ Hᵉ →
      is-not-one-two-ℕᵉ (pr2ᵉ Hᵉ 2 (is-proper-divisor-zero-succ-ℕᵉ 1ᵉ)))
is-decidable-is-prime-easy-ℕᵉ (succ-ℕᵉ nᵉ) =
  is-decidable-productᵉ
    ( is-decidable-negᵉ (is-decidable-is-one-ℕᵉ (succ-ℕᵉ nᵉ)))
    ( is-decidable-bounded-Π-ℕᵉ
      ( is-proper-divisor-ℕᵉ (succ-ℕᵉ nᵉ))
      ( is-one-ℕᵉ)
      ( is-decidable-is-proper-divisor-ℕᵉ (succ-ℕᵉ nᵉ))
      ( is-decidable-is-one-ℕᵉ)
      ( succ-ℕᵉ nᵉ)
      ( λ xᵉ Hᵉ → leq-div-succ-ℕᵉ xᵉ nᵉ (pr2ᵉ Hᵉ)))

is-decidable-is-prime-ℕᵉ : (nᵉ : ℕᵉ) → is-decidableᵉ (is-prime-ℕᵉ nᵉ)
is-decidable-is-prime-ℕᵉ nᵉ =
  is-decidable-iffᵉ
    ( is-prime-is-prime-easy-ℕᵉ nᵉ)
    ( is-prime-easy-is-prime-ℕᵉ nᵉ)
    ( is-decidable-is-prime-easy-ℕᵉ nᵉ)
```

### The number `2` is a prime

```agda
is-one-is-proper-divisor-two-ℕᵉ : is-one-is-proper-divisor-ℕᵉ 2
is-one-is-proper-divisor-two-ℕᵉ zero-ℕᵉ (pairᵉ fᵉ (pairᵉ kᵉ pᵉ)) =
  ex-falsoᵉ (fᵉ (invᵉ (right-zero-law-mul-ℕᵉ kᵉ) ∙ᵉ pᵉ))
is-one-is-proper-divisor-two-ℕᵉ (succ-ℕᵉ zero-ℕᵉ) (pairᵉ fᵉ Hᵉ) = reflᵉ
is-one-is-proper-divisor-two-ℕᵉ (succ-ℕᵉ (succ-ℕᵉ zero-ℕᵉ)) (pairᵉ fᵉ Hᵉ) =
  ex-falsoᵉ (fᵉ reflᵉ)
is-one-is-proper-divisor-two-ℕᵉ (succ-ℕᵉ (succ-ℕᵉ (succ-ℕᵉ xᵉ))) (pairᵉ fᵉ Hᵉ) =
  ex-falsoᵉ (leq-div-succ-ℕᵉ (succ-ℕᵉ (succ-ℕᵉ (succ-ℕᵉ xᵉ))) 1 Hᵉ)

is-prime-easy-two-ℕᵉ : is-prime-easy-ℕᵉ 2
pr1ᵉ is-prime-easy-two-ℕᵉ = Eq-eq-ℕᵉ
pr2ᵉ is-prime-easy-two-ℕᵉ = is-one-is-proper-divisor-two-ℕᵉ

is-prime-two-ℕᵉ : is-prime-ℕᵉ 2
is-prime-two-ℕᵉ =
  is-prime-is-prime-easy-ℕᵉ 2 is-prime-easy-two-ℕᵉ
```

### If a prime number `p` divides a nonzero number `x`, then `x/p < x`

```agda
le-quotient-div-is-prime-ℕᵉ :
  (pᵉ xᵉ : ℕᵉ) → is-nonzero-ℕᵉ xᵉ → is-prime-ℕᵉ pᵉ →
  (Hᵉ : div-ℕᵉ pᵉ xᵉ) → le-ℕᵉ (quotient-div-ℕᵉ pᵉ xᵉ Hᵉ) xᵉ
le-quotient-div-is-prime-ℕᵉ pᵉ xᵉ Nᵉ Pᵉ Hᵉ =
  le-quotient-div-ℕᵉ pᵉ xᵉ Nᵉ Hᵉ (is-not-one-is-prime-ℕᵉ pᵉ Pᵉ)
```

### If a prime number `p` divides a number `x + 1`, then `(x + 1)/p ≤ x`

```agda
leq-quotient-div-is-prime-ℕᵉ :
  (pᵉ xᵉ : ℕᵉ) → is-prime-ℕᵉ pᵉ →
  (Hᵉ : div-ℕᵉ pᵉ (succ-ℕᵉ xᵉ)) → leq-ℕᵉ (quotient-div-ℕᵉ pᵉ (succ-ℕᵉ xᵉ) Hᵉ) xᵉ
leq-quotient-div-is-prime-ℕᵉ pᵉ xᵉ Pᵉ Hᵉ =
  leq-le-succ-ℕᵉ
    ( quotient-div-ℕᵉ pᵉ (succ-ℕᵉ xᵉ) Hᵉ)
    ( xᵉ)
    ( le-quotient-div-is-prime-ℕᵉ pᵉ (succ-ℕᵉ xᵉ) (is-nonzero-succ-ℕᵉ xᵉ) Pᵉ Hᵉ)
```

## See also

-ᵉ Theᵉ fundamentalᵉ theoremᵉ ofᵉ arithmeticᵉ assertsᵉ thatᵉ everyᵉ positiveᵉ naturalᵉ
  numberᵉ canᵉ beᵉ writtenᵉ uniquelyᵉ asᵉ aᵉ productᵉ ofᵉ primes.ᵉ Thisᵉ theoremᵉ isᵉ provenᵉ
  in
  [`fundamental-theorem-of-arithmetic`](elementary-number-theory.fundamental-theorem-of-arithmetic.md).ᵉ