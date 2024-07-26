# Proper divisors of natural numbers

```agda
module elementary-number-theory.proper-divisors-natural-numbersᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.divisibility-natural-numbersᵉ
open import elementary-number-theory.equality-natural-numbersᵉ
open import elementary-number-theory.inequality-natural-numbersᵉ
open import elementary-number-theory.modular-arithmetic-standard-finite-typesᵉ
open import elementary-number-theory.multiplication-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ
open import elementary-number-theory.strict-inequality-natural-numbersᵉ

open import foundation.cartesian-product-typesᵉ
open import foundation.decidable-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.empty-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.negated-equalityᵉ
open import foundation.negationᵉ
open import foundation.propositionsᵉ
open import foundation.type-arithmetic-empty-typeᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Aᵉ properᵉ divisorᵉ ofᵉ aᵉ naturalᵉ numberᵉ `n`ᵉ isᵉ aᵉ naturalᵉ numberᵉ `dᵉ ≠ᵉ n`ᵉ thatᵉ
dividesᵉ `n`.ᵉ

```agda
is-proper-divisor-ℕᵉ : ℕᵉ → ℕᵉ → UUᵉ lzero
is-proper-divisor-ℕᵉ nᵉ dᵉ = (dᵉ ≠ᵉ nᵉ) ×ᵉ (div-ℕᵉ dᵉ nᵉ)

is-decidable-is-proper-divisor-ℕᵉ :
  (nᵉ dᵉ : ℕᵉ) → is-decidableᵉ (is-proper-divisor-ℕᵉ nᵉ dᵉ)
is-decidable-is-proper-divisor-ℕᵉ nᵉ dᵉ =
  is-decidable-productᵉ
    ( is-decidable-negᵉ (has-decidable-equality-ℕᵉ dᵉ nᵉ))
    ( is-decidable-div-ℕᵉ dᵉ nᵉ)

is-proper-divisor-zero-succ-ℕᵉ : (nᵉ : ℕᵉ) → is-proper-divisor-ℕᵉ zero-ℕᵉ (succ-ℕᵉ nᵉ)
pr1ᵉ (is-proper-divisor-zero-succ-ℕᵉ nᵉ) = is-nonzero-succ-ℕᵉ nᵉ
pr2ᵉ (is-proper-divisor-zero-succ-ℕᵉ nᵉ) = div-zero-ℕᵉ (succ-ℕᵉ nᵉ)

le-is-proper-divisor-ℕᵉ :
  (xᵉ yᵉ : ℕᵉ) → is-nonzero-ℕᵉ yᵉ → is-proper-divisor-ℕᵉ yᵉ xᵉ → le-ℕᵉ xᵉ yᵉ
le-is-proper-divisor-ℕᵉ xᵉ yᵉ Hᵉ Kᵉ =
  le-leq-neq-ℕᵉ (leq-div-ℕᵉ xᵉ yᵉ Hᵉ (pr2ᵉ Kᵉ)) (pr1ᵉ Kᵉ)
```

## Properties

### Being a proper divisor is a property

```agda
is-prop-is-proper-divisor-ℕᵉ : (nᵉ dᵉ : ℕᵉ) → is-propᵉ (is-proper-divisor-ℕᵉ nᵉ dᵉ)
is-prop-is-proper-divisor-ℕᵉ nᵉ zero-ℕᵉ (pairᵉ fᵉ gᵉ) =
  ex-falsoᵉ (fᵉ (invᵉ (is-zero-div-zero-ℕᵉ nᵉ gᵉ)))
is-prop-is-proper-divisor-ℕᵉ nᵉ (succ-ℕᵉ dᵉ) =
  is-prop-productᵉ is-prop-negᵉ (is-prop-div-ℕᵉ (succ-ℕᵉ dᵉ) nᵉ (is-nonzero-succ-ℕᵉ dᵉ))
```

### If a natural number has a proper divisor, then `1` is a proper divisor

```agda
is-proper-divisor-one-is-proper-divisor-ℕᵉ :
  {nᵉ xᵉ : ℕᵉ} → is-proper-divisor-ℕᵉ nᵉ xᵉ → is-proper-divisor-ℕᵉ nᵉ 1
pr1ᵉ (is-proper-divisor-one-is-proper-divisor-ℕᵉ {.1ᵉ} {xᵉ} Hᵉ) reflᵉ =
  pr1ᵉ Hᵉ (is-one-div-one-ℕᵉ xᵉ (pr2ᵉ Hᵉ))
pr1ᵉ (pr2ᵉ (is-proper-divisor-one-is-proper-divisor-ℕᵉ {nᵉ} {xᵉ} Hᵉ)) = nᵉ
pr2ᵉ (pr2ᵉ (is-proper-divisor-one-is-proper-divisor-ℕᵉ {nᵉ} {xᵉ} Hᵉ)) =
  right-unit-law-mul-ℕᵉ nᵉ
```

### If `x` is nonzero and `d | x` is a proper divisor, then `1 < x/d`

```agda
le-one-quotient-div-is-proper-divisor-ℕᵉ :
  (dᵉ xᵉ : ℕᵉ) → is-nonzero-ℕᵉ xᵉ → (Hᵉ : div-ℕᵉ dᵉ xᵉ) →
  dᵉ ≠ᵉ xᵉ → le-ℕᵉ 1 (quotient-div-ℕᵉ dᵉ xᵉ Hᵉ)
le-one-quotient-div-is-proper-divisor-ℕᵉ dᵉ xᵉ fᵉ Hᵉ gᵉ =
  map-left-unit-law-coproduct-is-emptyᵉ
    ( is-one-ℕᵉ (quotient-div-ℕᵉ dᵉ xᵉ Hᵉ))
    ( le-ℕᵉ 1 (quotient-div-ℕᵉ dᵉ xᵉ Hᵉ))
    ( map-negᵉ (eq-is-one-quotient-div-ℕᵉ dᵉ xᵉ Hᵉ) gᵉ)
    ( eq-or-le-leq-ℕ'ᵉ 1
      ( quotient-div-ℕᵉ dᵉ xᵉ Hᵉ)
      ( leq-one-quotient-div-ℕᵉ dᵉ xᵉ Hᵉ (leq-one-is-nonzero-ℕᵉ xᵉ fᵉ)))
```