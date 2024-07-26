# Relatively prime natural numbers

```agda
module elementary-number-theory.relatively-prime-natural-numbersᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbersᵉ
open import elementary-number-theory.divisibility-natural-numbersᵉ
open import elementary-number-theory.equality-natural-numbersᵉ
open import elementary-number-theory.greatest-common-divisor-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ
open import elementary-number-theory.prime-numbersᵉ

open import foundation.decidable-propositionsᵉ
open import foundation.decidable-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.negated-equalityᵉ
open import foundation.propositionsᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Twoᵉ naturalᵉ numbersᵉ `x`ᵉ andᵉ `y`ᵉ areᵉ saidᵉ to beᵉ relativelyᵉ primeᵉ ifᵉ theirᵉ
greatestᵉ commonᵉ divisorᵉ isᵉ `1`.ᵉ

## Definition

```agda
is-relatively-prime-ℕᵉ : ℕᵉ → ℕᵉ → UUᵉ lzero
is-relatively-prime-ℕᵉ xᵉ yᵉ = is-one-ℕᵉ (gcd-ℕᵉ xᵉ yᵉ)
```

## Properties

### Being relatively prime is a proposition

```agda
is-prop-is-relatively-prime-ℕᵉ : (xᵉ yᵉ : ℕᵉ) → is-propᵉ (is-relatively-prime-ℕᵉ xᵉ yᵉ)
is-prop-is-relatively-prime-ℕᵉ xᵉ yᵉ = is-set-ℕᵉ (gcd-ℕᵉ xᵉ yᵉ) 1

is-relatively-prime-ℕ-Propᵉ : ℕᵉ → ℕᵉ → Propᵉ lzero
pr1ᵉ (is-relatively-prime-ℕ-Propᵉ xᵉ yᵉ) = is-relatively-prime-ℕᵉ xᵉ yᵉ
pr2ᵉ (is-relatively-prime-ℕ-Propᵉ xᵉ yᵉ) = is-prop-is-relatively-prime-ℕᵉ xᵉ yᵉ
```

### Being relatively prime is decidable

```agda
is-decidable-is-relatively-prime-ℕᵉ :
  (xᵉ yᵉ : ℕᵉ) → is-decidableᵉ (is-relatively-prime-ℕᵉ xᵉ yᵉ)
is-decidable-is-relatively-prime-ℕᵉ xᵉ yᵉ = is-decidable-is-one-ℕᵉ (gcd-ℕᵉ xᵉ yᵉ)

is-decidable-prop-is-relatively-prime-ℕᵉ :
  (xᵉ yᵉ : ℕᵉ) → is-decidable-propᵉ (is-relatively-prime-ℕᵉ xᵉ yᵉ)
pr1ᵉ (is-decidable-prop-is-relatively-prime-ℕᵉ xᵉ yᵉ) =
  is-prop-is-relatively-prime-ℕᵉ xᵉ yᵉ
pr2ᵉ (is-decidable-prop-is-relatively-prime-ℕᵉ xᵉ yᵉ) =
  is-decidable-is-relatively-prime-ℕᵉ xᵉ yᵉ

is-relatively-prime-ℕ-Decidable-Propᵉ :
  (xᵉ yᵉ : ℕᵉ) → Decidable-Propᵉ lzero
pr1ᵉ (is-relatively-prime-ℕ-Decidable-Propᵉ xᵉ yᵉ) =
  is-relatively-prime-ℕᵉ xᵉ yᵉ
pr2ᵉ (is-relatively-prime-ℕ-Decidable-Propᵉ xᵉ yᵉ) =
  is-decidable-prop-is-relatively-prime-ℕᵉ xᵉ yᵉ
```

### `a` and `b` are relatively prime if and only if any common divisor is equal to `1`

```agda
is-one-is-common-divisor-is-relatively-prime-ℕᵉ :
  (xᵉ yᵉ dᵉ : ℕᵉ) →
  is-relatively-prime-ℕᵉ xᵉ yᵉ → is-common-divisor-ℕᵉ xᵉ yᵉ dᵉ → is-one-ℕᵉ dᵉ
is-one-is-common-divisor-is-relatively-prime-ℕᵉ xᵉ yᵉ dᵉ Hᵉ Kᵉ =
  is-one-div-one-ℕᵉ dᵉ
    ( trᵉ
      ( div-ℕᵉ dᵉ)
      ( Hᵉ)
      ( div-gcd-is-common-divisor-ℕᵉ xᵉ yᵉ dᵉ Kᵉ))

is-relatively-prime-is-one-is-common-divisor-ℕᵉ :
  (xᵉ yᵉ : ℕᵉ) →
  ((dᵉ : ℕᵉ) → is-common-divisor-ℕᵉ xᵉ yᵉ dᵉ → is-one-ℕᵉ dᵉ) → is-relatively-prime-ℕᵉ xᵉ yᵉ
is-relatively-prime-is-one-is-common-divisor-ℕᵉ xᵉ yᵉ Hᵉ =
  Hᵉ (gcd-ℕᵉ xᵉ yᵉ) (is-common-divisor-gcd-ℕᵉ xᵉ yᵉ)
```

### If `a` and `b` are relatively prime, then so are any divisors of `a` and `b`

```agda
is-relatively-prime-div-ℕᵉ :
  (aᵉ bᵉ cᵉ dᵉ : ℕᵉ) → div-ℕᵉ cᵉ aᵉ → div-ℕᵉ dᵉ bᵉ →
  is-relatively-prime-ℕᵉ aᵉ bᵉ → is-relatively-prime-ℕᵉ cᵉ dᵉ
is-relatively-prime-div-ℕᵉ aᵉ bᵉ cᵉ dᵉ Hᵉ Kᵉ Lᵉ =
  is-one-is-common-divisor-is-relatively-prime-ℕᵉ aᵉ bᵉ
    ( gcd-ℕᵉ cᵉ dᵉ)
    ( Lᵉ)
    ( transitive-div-ℕᵉ (gcd-ℕᵉ cᵉ dᵉ) cᵉ aᵉ Hᵉ (div-left-factor-gcd-ℕᵉ cᵉ dᵉ) ,ᵉ
      transitive-div-ℕᵉ (gcd-ℕᵉ cᵉ dᵉ) dᵉ bᵉ Kᵉ (div-right-factor-gcd-ℕᵉ cᵉ dᵉ))
```

### For any two natural numbers `a` and `b` such that `a + b ≠ 0`, the numbers `a/gcd(a,b)` and `b/gcd(a,b)` are relatively prime

```agda
is-relatively-prime-quotient-div-gcd-ℕᵉ :
  (aᵉ bᵉ : ℕᵉ) → is-nonzero-ℕᵉ (aᵉ +ℕᵉ bᵉ) →
  is-relatively-prime-ℕᵉ
    ( quotient-div-ℕᵉ (gcd-ℕᵉ aᵉ bᵉ) aᵉ (div-left-factor-gcd-ℕᵉ aᵉ bᵉ))
    ( quotient-div-ℕᵉ (gcd-ℕᵉ aᵉ bᵉ) bᵉ (div-right-factor-gcd-ℕᵉ aᵉ bᵉ))
is-relatively-prime-quotient-div-gcd-ℕᵉ aᵉ bᵉ nzᵉ =
  ( uniqueness-is-gcd-ℕᵉ
    ( quotient-div-ℕᵉ (gcd-ℕᵉ aᵉ bᵉ) aᵉ (div-left-factor-gcd-ℕᵉ aᵉ bᵉ))
    ( quotient-div-ℕᵉ (gcd-ℕᵉ aᵉ bᵉ) bᵉ (div-right-factor-gcd-ℕᵉ aᵉ bᵉ))
    ( gcd-ℕᵉ
      ( quotient-div-ℕᵉ (gcd-ℕᵉ aᵉ bᵉ) aᵉ (div-left-factor-gcd-ℕᵉ aᵉ bᵉ))
      ( quotient-div-ℕᵉ (gcd-ℕᵉ aᵉ bᵉ) bᵉ (div-right-factor-gcd-ℕᵉ aᵉ bᵉ)))
    ( quotient-div-ℕᵉ
      ( gcd-ℕᵉ aᵉ bᵉ)
      ( gcd-ℕᵉ aᵉ bᵉ)
      ( div-gcd-is-common-divisor-ℕᵉ aᵉ bᵉ
        ( gcd-ℕᵉ aᵉ bᵉ)
        ( is-common-divisor-gcd-ℕᵉ aᵉ bᵉ)))
    ( is-gcd-gcd-ℕᵉ
      ( quotient-div-ℕᵉ (gcd-ℕᵉ aᵉ bᵉ) aᵉ (div-left-factor-gcd-ℕᵉ aᵉ bᵉ))
      ( quotient-div-ℕᵉ (gcd-ℕᵉ aᵉ bᵉ) bᵉ (div-right-factor-gcd-ℕᵉ aᵉ bᵉ)))
    ( is-gcd-quotient-div-gcd-ℕᵉ
      ( is-nonzero-gcd-ℕᵉ aᵉ bᵉ nzᵉ)
      ( is-common-divisor-gcd-ℕᵉ aᵉ bᵉ))) ∙ᵉ
  ( is-idempotent-quotient-div-ℕᵉ
    ( gcd-ℕᵉ aᵉ bᵉ)
    ( is-nonzero-gcd-ℕᵉ aᵉ bᵉ nzᵉ)
    ( div-gcd-is-common-divisor-ℕᵉ aᵉ bᵉ
      ( gcd-ℕᵉ aᵉ bᵉ)
      ( is-common-divisor-gcd-ℕᵉ aᵉ bᵉ)))
```

### If `a` and `b` are prime and distinct, then they are relatively prime

```agda
module _
  (aᵉ bᵉ : ℕᵉ)
  (paᵉ : is-prime-ℕᵉ aᵉ)
  (pbᵉ : is-prime-ℕᵉ bᵉ)
  (nᵉ : aᵉ ≠ᵉ bᵉ)
  where

  is-one-is-common-divisor-is-prime-ℕᵉ :
    (dᵉ : ℕᵉ) → is-common-divisor-ℕᵉ aᵉ bᵉ dᵉ → is-one-ℕᵉ dᵉ
  is-one-is-common-divisor-is-prime-ℕᵉ dᵉ cᵉ =
    pr1ᵉ
      ( paᵉ dᵉ)
      ( ( λ eᵉ →
          is-not-one-is-prime-ℕᵉ
            ( aᵉ)
            ( paᵉ)
            ( pr1ᵉ (pbᵉ aᵉ) (nᵉ ,ᵉ (trᵉ (λ xᵉ → div-ℕᵉ xᵉ bᵉ) eᵉ (pr2ᵉ cᵉ))))) ,ᵉ
        ( pr1ᵉ cᵉ))

  is-relatively-prime-is-prime-ℕᵉ :
    is-relatively-prime-ℕᵉ aᵉ bᵉ
  is-relatively-prime-is-prime-ℕᵉ =
    is-relatively-prime-is-one-is-common-divisor-ℕᵉ
      ( aᵉ)
      ( bᵉ)
      ( is-one-is-common-divisor-is-prime-ℕᵉ)
```