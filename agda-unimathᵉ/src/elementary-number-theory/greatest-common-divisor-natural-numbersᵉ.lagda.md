# The greatest common divisor of natural numbers

```agda
module elementary-number-theory.greatest-common-divisor-natural-numbersᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbersᵉ
open import elementary-number-theory.decidable-typesᵉ
open import elementary-number-theory.distance-natural-numbersᵉ
open import elementary-number-theory.divisibility-natural-numbersᵉ
open import elementary-number-theory.equality-natural-numbersᵉ
open import elementary-number-theory.euclidean-division-natural-numbersᵉ
open import elementary-number-theory.inequality-natural-numbersᵉ
open import elementary-number-theory.lower-bounds-natural-numbersᵉ
open import elementary-number-theory.modular-arithmetic-standard-finite-typesᵉ
open import elementary-number-theory.multiplication-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ
open import elementary-number-theory.strict-inequality-natural-numbersᵉ
open import elementary-number-theory.well-ordering-principle-natural-numbersᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.cartesian-product-typesᵉ
open import foundation.coproduct-typesᵉ
open import foundation.decidable-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.empty-typesᵉ
open import foundation.functoriality-cartesian-product-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Theᵉ greatestᵉ commonᵉ divisorᵉ ofᵉ twoᵉ naturalᵉ numbersᵉ `x`ᵉ andᵉ `y`ᵉ isᵉ aᵉ numberᵉ
`gcdᵉ xᵉ y`ᵉ suchᵉ thatᵉ anyᵉ naturalᵉ numberᵉ `dᵉ : ℕ`ᵉ isᵉ aᵉ commonᵉ divisorᵉ ofᵉ `x`ᵉ andᵉ
`y`ᵉ ifᵉ andᵉ onlyᵉ ifᵉ itᵉ isᵉ aᵉ divisorᵉ ofᵉ `gcdᵉ xᵉ y`.ᵉ

## Definition

### Common divisors

```agda
is-common-divisor-ℕᵉ : (aᵉ bᵉ xᵉ : ℕᵉ) → UUᵉ lzero
is-common-divisor-ℕᵉ aᵉ bᵉ xᵉ = (div-ℕᵉ xᵉ aᵉ) ×ᵉ (div-ℕᵉ xᵉ bᵉ)
```

### Greatest common divisors

```agda
is-gcd-ℕᵉ : (aᵉ bᵉ dᵉ : ℕᵉ) → UUᵉ lzero
is-gcd-ℕᵉ aᵉ bᵉ dᵉ = (xᵉ : ℕᵉ) → (is-common-divisor-ℕᵉ aᵉ bᵉ xᵉ) ↔ᵉ (div-ℕᵉ xᵉ dᵉ)
```

### The predicate of being a multiple of the greatest common divisor

```agda
is-multiple-of-gcd-ℕᵉ : (aᵉ bᵉ nᵉ : ℕᵉ) → UUᵉ lzero
is-multiple-of-gcd-ℕᵉ aᵉ bᵉ nᵉ =
  is-nonzero-ℕᵉ (aᵉ +ℕᵉ bᵉ) →
  (is-nonzero-ℕᵉ nᵉ) ×ᵉ ((xᵉ : ℕᵉ) → is-common-divisor-ℕᵉ aᵉ bᵉ xᵉ → div-ℕᵉ xᵉ nᵉ)
```

## Properties

### Reflexivity for common divisors

```agda
refl-is-common-divisor-ℕᵉ :
  (xᵉ : ℕᵉ) → is-common-divisor-ℕᵉ xᵉ xᵉ xᵉ
pr1ᵉ (refl-is-common-divisor-ℕᵉ xᵉ) = refl-div-ℕᵉ xᵉ
pr2ᵉ (refl-is-common-divisor-ℕᵉ xᵉ) = refl-div-ℕᵉ xᵉ
```

### Being a common divisor is decidable

```agda
is-decidable-is-common-divisor-ℕᵉ :
  (aᵉ bᵉ : ℕᵉ) → is-decidable-famᵉ (is-common-divisor-ℕᵉ aᵉ bᵉ)
is-decidable-is-common-divisor-ℕᵉ aᵉ bᵉ xᵉ =
  is-decidable-productᵉ
    ( is-decidable-div-ℕᵉ xᵉ aᵉ)
    ( is-decidable-div-ℕᵉ xᵉ bᵉ)
```

### Any greatest common divisor is a common divisor

```agda
is-common-divisor-is-gcd-ℕᵉ :
  (aᵉ bᵉ dᵉ : ℕᵉ) → is-gcd-ℕᵉ aᵉ bᵉ dᵉ → is-common-divisor-ℕᵉ aᵉ bᵉ dᵉ
is-common-divisor-is-gcd-ℕᵉ aᵉ bᵉ dᵉ Hᵉ = pr2ᵉ (Hᵉ dᵉ) (refl-div-ℕᵉ dᵉ)
```

### Uniqueness of greatest common divisors

```agda
uniqueness-is-gcd-ℕᵉ :
  (aᵉ bᵉ dᵉ d'ᵉ : ℕᵉ) → is-gcd-ℕᵉ aᵉ bᵉ dᵉ → is-gcd-ℕᵉ aᵉ bᵉ d'ᵉ → dᵉ ＝ᵉ d'ᵉ
uniqueness-is-gcd-ℕᵉ aᵉ bᵉ dᵉ d'ᵉ Hᵉ H'ᵉ =
  antisymmetric-div-ℕᵉ dᵉ d'ᵉ
    ( pr1ᵉ (H'ᵉ dᵉ) (is-common-divisor-is-gcd-ℕᵉ aᵉ bᵉ dᵉ Hᵉ))
    ( pr1ᵉ (Hᵉ d'ᵉ) (is-common-divisor-is-gcd-ℕᵉ aᵉ bᵉ d'ᵉ H'ᵉ))
```

### If `d` is a common divisor of `a` and `b`, and `a + b ≠ 0`, then `d ≤ a + b`

```agda
leq-sum-is-common-divisor-ℕ'ᵉ :
  (aᵉ bᵉ dᵉ : ℕᵉ) →
  is-successor-ℕᵉ (aᵉ +ℕᵉ bᵉ) → is-common-divisor-ℕᵉ aᵉ bᵉ dᵉ → leq-ℕᵉ dᵉ (aᵉ +ℕᵉ bᵉ)
leq-sum-is-common-divisor-ℕ'ᵉ aᵉ zero-ℕᵉ dᵉ (pairᵉ kᵉ pᵉ) Hᵉ =
  concatenate-leq-eq-ℕᵉ dᵉ
    ( leq-div-succ-ℕᵉ dᵉ kᵉ (concatenate-div-eq-ℕᵉ (pr1ᵉ Hᵉ) pᵉ))
    ( invᵉ pᵉ)
leq-sum-is-common-divisor-ℕ'ᵉ aᵉ (succ-ℕᵉ bᵉ) dᵉ (pairᵉ kᵉ pᵉ) Hᵉ =
  leq-div-succ-ℕᵉ dᵉ (aᵉ +ℕᵉ bᵉ) (div-add-ℕᵉ dᵉ aᵉ (succ-ℕᵉ bᵉ) (pr1ᵉ Hᵉ) (pr2ᵉ Hᵉ))

leq-sum-is-common-divisor-ℕᵉ :
  (aᵉ bᵉ dᵉ : ℕᵉ) →
  is-nonzero-ℕᵉ (aᵉ +ℕᵉ bᵉ) → is-common-divisor-ℕᵉ aᵉ bᵉ dᵉ → leq-ℕᵉ dᵉ (aᵉ +ℕᵉ bᵉ)
leq-sum-is-common-divisor-ℕᵉ aᵉ bᵉ dᵉ Hᵉ =
  leq-sum-is-common-divisor-ℕ'ᵉ aᵉ bᵉ dᵉ (is-successor-is-nonzero-ℕᵉ Hᵉ)
```

### Being a multiple of the greatest common divisor is decidable

```agda
is-decidable-is-multiple-of-gcd-ℕᵉ :
  (aᵉ bᵉ : ℕᵉ) → is-decidable-famᵉ (is-multiple-of-gcd-ℕᵉ aᵉ bᵉ)
is-decidable-is-multiple-of-gcd-ℕᵉ aᵉ bᵉ nᵉ =
  is-decidable-function-type'ᵉ
    ( is-decidable-negᵉ (is-decidable-is-zero-ℕᵉ (aᵉ +ℕᵉ bᵉ)))
    ( λ npᵉ →
      is-decidable-productᵉ
        ( is-decidable-negᵉ (is-decidable-is-zero-ℕᵉ nᵉ))
        ( is-decidable-bounded-Π-ℕᵉ
          ( is-common-divisor-ℕᵉ aᵉ bᵉ)
          ( λ xᵉ → div-ℕᵉ xᵉ nᵉ)
          ( is-decidable-is-common-divisor-ℕᵉ aᵉ bᵉ)
          ( λ xᵉ → is-decidable-div-ℕᵉ xᵉ nᵉ)
          ( aᵉ +ℕᵉ bᵉ)
          ( λ xᵉ → leq-sum-is-common-divisor-ℕᵉ aᵉ bᵉ xᵉ npᵉ)))
```

### The sum of `a` and `b` is a multiple of the greatest common divisor of `a` and `b`

```agda
sum-is-multiple-of-gcd-ℕᵉ : (aᵉ bᵉ : ℕᵉ) → is-multiple-of-gcd-ℕᵉ aᵉ bᵉ (aᵉ +ℕᵉ bᵉ)
pr1ᵉ (sum-is-multiple-of-gcd-ℕᵉ aᵉ bᵉ npᵉ) = npᵉ
pr2ᵉ (sum-is-multiple-of-gcd-ℕᵉ aᵉ bᵉ npᵉ) xᵉ Hᵉ = div-add-ℕᵉ xᵉ aᵉ bᵉ (pr1ᵉ Hᵉ) (pr2ᵉ Hᵉ)
```

### The greatest common divisor exists

```agda
abstract
  GCD-ℕᵉ : (aᵉ bᵉ : ℕᵉ) → minimal-element-ℕᵉ (is-multiple-of-gcd-ℕᵉ aᵉ bᵉ)
  GCD-ℕᵉ aᵉ bᵉ =
    well-ordering-principle-ℕᵉ
      ( is-multiple-of-gcd-ℕᵉ aᵉ bᵉ)
      ( is-decidable-is-multiple-of-gcd-ℕᵉ aᵉ bᵉ)
      ( pairᵉ (aᵉ +ℕᵉ bᵉ) (sum-is-multiple-of-gcd-ℕᵉ aᵉ bᵉ))

gcd-ℕᵉ : ℕᵉ → ℕᵉ → ℕᵉ
gcd-ℕᵉ aᵉ bᵉ = pr1ᵉ (GCD-ℕᵉ aᵉ bᵉ)

is-multiple-of-gcd-gcd-ℕᵉ : (aᵉ bᵉ : ℕᵉ) → is-multiple-of-gcd-ℕᵉ aᵉ bᵉ (gcd-ℕᵉ aᵉ bᵉ)
is-multiple-of-gcd-gcd-ℕᵉ aᵉ bᵉ = pr1ᵉ (pr2ᵉ (GCD-ℕᵉ aᵉ bᵉ))

is-lower-bound-gcd-ℕᵉ :
  (aᵉ bᵉ : ℕᵉ) → is-lower-bound-ℕᵉ (is-multiple-of-gcd-ℕᵉ aᵉ bᵉ) (gcd-ℕᵉ aᵉ bᵉ)
is-lower-bound-gcd-ℕᵉ aᵉ bᵉ = pr2ᵉ (pr2ᵉ (GCD-ℕᵉ aᵉ bᵉ))
```

### `a + b = 0` if and only if `gcd a b = 0`

```agda
is-zero-gcd-ℕᵉ :
  (aᵉ bᵉ : ℕᵉ) → is-zero-ℕᵉ (aᵉ +ℕᵉ bᵉ) → is-zero-ℕᵉ (gcd-ℕᵉ aᵉ bᵉ)
is-zero-gcd-ℕᵉ aᵉ bᵉ pᵉ =
  is-zero-leq-zero-ℕᵉ
    ( gcd-ℕᵉ aᵉ bᵉ)
    ( concatenate-leq-eq-ℕᵉ
      ( gcd-ℕᵉ aᵉ bᵉ)
      ( is-lower-bound-gcd-ℕᵉ aᵉ bᵉ
        ( aᵉ +ℕᵉ bᵉ)
        ( sum-is-multiple-of-gcd-ℕᵉ aᵉ bᵉ))
      ( pᵉ))

is-zero-gcd-zero-zero-ℕᵉ : is-zero-ℕᵉ (gcd-ℕᵉ zero-ℕᵉ zero-ℕᵉ)
is-zero-gcd-zero-zero-ℕᵉ = is-zero-gcd-ℕᵉ zero-ℕᵉ zero-ℕᵉ reflᵉ

is-zero-add-is-zero-gcd-ℕᵉ :
  (aᵉ bᵉ : ℕᵉ) → is-zero-ℕᵉ (gcd-ℕᵉ aᵉ bᵉ) → is-zero-ℕᵉ (aᵉ +ℕᵉ bᵉ)
is-zero-add-is-zero-gcd-ℕᵉ aᵉ bᵉ Hᵉ =
  double-negation-elim-is-decidableᵉ
    ( is-decidable-is-zero-ℕᵉ (aᵉ +ℕᵉ bᵉ))
    ( λ fᵉ → pr1ᵉ (is-multiple-of-gcd-gcd-ℕᵉ aᵉ bᵉ fᵉ) Hᵉ)
```

### If at least one of `a` and `b` is nonzero, then their gcd is nonzero

```agda
is-nonzero-gcd-ℕᵉ :
  (aᵉ bᵉ : ℕᵉ) → is-nonzero-ℕᵉ (aᵉ +ℕᵉ bᵉ) → is-nonzero-ℕᵉ (gcd-ℕᵉ aᵉ bᵉ)
is-nonzero-gcd-ℕᵉ aᵉ bᵉ neᵉ = pr1ᵉ (is-multiple-of-gcd-gcd-ℕᵉ aᵉ bᵉ neᵉ)

is-successor-gcd-ℕᵉ :
  (aᵉ bᵉ : ℕᵉ) → is-nonzero-ℕᵉ (aᵉ +ℕᵉ bᵉ) → is-successor-ℕᵉ (gcd-ℕᵉ aᵉ bᵉ)
is-successor-gcd-ℕᵉ aᵉ bᵉ neᵉ =
  is-successor-is-nonzero-ℕᵉ (is-nonzero-gcd-ℕᵉ aᵉ bᵉ neᵉ)
```

### Any common divisor is also a divisor of the greatest common divisor

```agda
div-gcd-is-common-divisor-ℕᵉ :
  (aᵉ bᵉ xᵉ : ℕᵉ) → is-common-divisor-ℕᵉ aᵉ bᵉ xᵉ → div-ℕᵉ xᵉ (gcd-ℕᵉ aᵉ bᵉ)
div-gcd-is-common-divisor-ℕᵉ aᵉ bᵉ xᵉ Hᵉ with
  is-decidable-is-zero-ℕᵉ (aᵉ +ℕᵉ bᵉ)
... | inlᵉ pᵉ = concatenate-div-eq-ℕᵉ (div-zero-ℕᵉ xᵉ) (invᵉ (is-zero-gcd-ℕᵉ aᵉ bᵉ pᵉ))
... | inrᵉ npᵉ = pr2ᵉ (is-multiple-of-gcd-gcd-ℕᵉ aᵉ bᵉ npᵉ) xᵉ Hᵉ
```

### If every common divisor divides a number `r < gcd a b`, then `r = 0`

```agda
is-zero-is-common-divisor-le-gcd-ℕᵉ :
  (aᵉ bᵉ rᵉ : ℕᵉ) → le-ℕᵉ rᵉ (gcd-ℕᵉ aᵉ bᵉ) →
  ((xᵉ : ℕᵉ) → is-common-divisor-ℕᵉ aᵉ bᵉ xᵉ → div-ℕᵉ xᵉ rᵉ) → is-zero-ℕᵉ rᵉ
is-zero-is-common-divisor-le-gcd-ℕᵉ aᵉ bᵉ rᵉ lᵉ dᵉ with is-decidable-is-zero-ℕᵉ rᵉ
... | inlᵉ Hᵉ = Hᵉ
... | inrᵉ xᵉ =
  ex-falsoᵉ
    ( contradiction-le-ℕᵉ rᵉ (gcd-ℕᵉ aᵉ bᵉ) lᵉ
      ( is-lower-bound-gcd-ℕᵉ aᵉ bᵉ rᵉ (λ npᵉ → pairᵉ xᵉ dᵉ)))
```

### Any divisor of `gcd a b` is a common divisor of `a` and `b`

```agda
div-left-factor-div-gcd-ℕᵉ :
  (aᵉ bᵉ xᵉ : ℕᵉ) → div-ℕᵉ xᵉ (gcd-ℕᵉ aᵉ bᵉ) → div-ℕᵉ xᵉ aᵉ
div-left-factor-div-gcd-ℕᵉ aᵉ bᵉ xᵉ dᵉ with
  is-decidable-is-zero-ℕᵉ (aᵉ +ℕᵉ bᵉ)
... | inlᵉ pᵉ =
  concatenate-div-eq-ℕᵉ (div-zero-ℕᵉ xᵉ) (invᵉ (is-zero-left-is-zero-add-ℕᵉ aᵉ bᵉ pᵉ))
... | inrᵉ npᵉ =
  transitive-div-ℕᵉ xᵉ (gcd-ℕᵉ aᵉ bᵉ) aᵉ
    ( pairᵉ qᵉ
      ( ( ( αᵉ) ∙ᵉ
          ( apᵉ
            ( dist-ℕᵉ aᵉ)
            ( is-zero-is-common-divisor-le-gcd-ℕᵉ aᵉ bᵉ rᵉ Bᵉ
              ( λ xᵉ Hᵉ →
                div-right-summand-ℕᵉ xᵉ (qᵉ *ℕᵉ (gcd-ℕᵉ aᵉ bᵉ)) rᵉ
                  ( div-mul-ℕᵉ qᵉ xᵉ (gcd-ℕᵉ aᵉ bᵉ)
                    ( div-gcd-is-common-divisor-ℕᵉ aᵉ bᵉ xᵉ Hᵉ))
                  ( concatenate-div-eq-ℕᵉ (pr1ᵉ Hᵉ) (invᵉ βᵉ)))))) ∙ᵉ
        ( right-unit-law-dist-ℕᵉ aᵉ)))
    ( dᵉ)
  where
  rᵉ = remainder-euclidean-division-ℕᵉ (gcd-ℕᵉ aᵉ bᵉ) aᵉ
  qᵉ = quotient-euclidean-division-ℕᵉ (gcd-ℕᵉ aᵉ bᵉ) aᵉ
  αᵉ = eq-quotient-euclidean-division-ℕᵉ (gcd-ℕᵉ aᵉ bᵉ) aᵉ
  Bᵉ =
    strict-upper-bound-remainder-euclidean-division-ℕᵉ
      (gcd-ℕᵉ aᵉ bᵉ) aᵉ (is-nonzero-gcd-ℕᵉ aᵉ bᵉ npᵉ)
  βᵉ = eq-euclidean-division-ℕᵉ (gcd-ℕᵉ aᵉ bᵉ) aᵉ

div-right-factor-div-gcd-ℕᵉ :
  (aᵉ bᵉ xᵉ : ℕᵉ) → div-ℕᵉ xᵉ (gcd-ℕᵉ aᵉ bᵉ) → div-ℕᵉ xᵉ bᵉ
div-right-factor-div-gcd-ℕᵉ aᵉ bᵉ xᵉ dᵉ with
  is-decidable-is-zero-ℕᵉ (aᵉ +ℕᵉ bᵉ)
... | inlᵉ pᵉ =
  concatenate-div-eq-ℕᵉ (div-zero-ℕᵉ xᵉ) (invᵉ (is-zero-right-is-zero-add-ℕᵉ aᵉ bᵉ pᵉ))
... | inrᵉ npᵉ =
  transitive-div-ℕᵉ xᵉ (gcd-ℕᵉ aᵉ bᵉ) bᵉ
    ( pairᵉ qᵉ
      ( ( αᵉ ∙ᵉ
          ( apᵉ
            ( dist-ℕᵉ bᵉ)
            ( is-zero-is-common-divisor-le-gcd-ℕᵉ aᵉ bᵉ rᵉ Bᵉ
              ( λ xᵉ Hᵉ →
                div-right-summand-ℕᵉ xᵉ (qᵉ *ℕᵉ (gcd-ℕᵉ aᵉ bᵉ)) rᵉ
                  ( div-mul-ℕᵉ qᵉ xᵉ (gcd-ℕᵉ aᵉ bᵉ)
                    ( div-gcd-is-common-divisor-ℕᵉ aᵉ bᵉ xᵉ Hᵉ))
                  ( concatenate-div-eq-ℕᵉ (pr2ᵉ Hᵉ) (invᵉ βᵉ)))))) ∙ᵉ
        ( right-unit-law-dist-ℕᵉ bᵉ)))
    ( dᵉ)
  where
  rᵉ = remainder-euclidean-division-ℕᵉ (gcd-ℕᵉ aᵉ bᵉ) bᵉ
  qᵉ = quotient-euclidean-division-ℕᵉ (gcd-ℕᵉ aᵉ bᵉ) bᵉ
  αᵉ = eq-quotient-euclidean-division-ℕᵉ (gcd-ℕᵉ aᵉ bᵉ) bᵉ
  Bᵉ =
    strict-upper-bound-remainder-euclidean-division-ℕᵉ
      (gcd-ℕᵉ aᵉ bᵉ) bᵉ (is-nonzero-gcd-ℕᵉ aᵉ bᵉ npᵉ)
  βᵉ = eq-euclidean-division-ℕᵉ (gcd-ℕᵉ aᵉ bᵉ) bᵉ

is-common-divisor-div-gcd-ℕᵉ :
  (aᵉ bᵉ xᵉ : ℕᵉ) → div-ℕᵉ xᵉ (gcd-ℕᵉ aᵉ bᵉ) → is-common-divisor-ℕᵉ aᵉ bᵉ xᵉ
pr1ᵉ (is-common-divisor-div-gcd-ℕᵉ aᵉ bᵉ xᵉ dᵉ) =
  div-left-factor-div-gcd-ℕᵉ aᵉ bᵉ xᵉ dᵉ
pr2ᵉ (is-common-divisor-div-gcd-ℕᵉ aᵉ bᵉ xᵉ dᵉ) =
  div-right-factor-div-gcd-ℕᵉ aᵉ bᵉ xᵉ dᵉ
```

### The gcd of `a` and `b` is a common divisor

```agda
div-left-factor-gcd-ℕᵉ : (aᵉ bᵉ : ℕᵉ) → div-ℕᵉ (gcd-ℕᵉ aᵉ bᵉ) aᵉ
div-left-factor-gcd-ℕᵉ aᵉ bᵉ =
  div-left-factor-div-gcd-ℕᵉ aᵉ bᵉ (gcd-ℕᵉ aᵉ bᵉ) (refl-div-ℕᵉ (gcd-ℕᵉ aᵉ bᵉ))

div-right-factor-gcd-ℕᵉ : (aᵉ bᵉ : ℕᵉ) → div-ℕᵉ (gcd-ℕᵉ aᵉ bᵉ) bᵉ
div-right-factor-gcd-ℕᵉ aᵉ bᵉ =
  div-right-factor-div-gcd-ℕᵉ aᵉ bᵉ (gcd-ℕᵉ aᵉ bᵉ) (refl-div-ℕᵉ (gcd-ℕᵉ aᵉ bᵉ))

is-common-divisor-gcd-ℕᵉ : (aᵉ bᵉ : ℕᵉ) → is-common-divisor-ℕᵉ aᵉ bᵉ (gcd-ℕᵉ aᵉ bᵉ)
is-common-divisor-gcd-ℕᵉ aᵉ bᵉ =
  is-common-divisor-div-gcd-ℕᵉ aᵉ bᵉ (gcd-ℕᵉ aᵉ bᵉ) (refl-div-ℕᵉ (gcd-ℕᵉ aᵉ bᵉ))
```

### The gcd of `a` and `b` is a greatest common divisor

```agda
is-gcd-gcd-ℕᵉ : (aᵉ bᵉ : ℕᵉ) → is-gcd-ℕᵉ aᵉ bᵉ (gcd-ℕᵉ aᵉ bᵉ)
pr1ᵉ (is-gcd-gcd-ℕᵉ aᵉ bᵉ xᵉ) = div-gcd-is-common-divisor-ℕᵉ aᵉ bᵉ xᵉ
pr2ᵉ (is-gcd-gcd-ℕᵉ aᵉ bᵉ xᵉ) = is-common-divisor-div-gcd-ℕᵉ aᵉ bᵉ xᵉ
```

### The gcd is commutative

```agda
is-commutative-gcd-ℕᵉ : (aᵉ bᵉ : ℕᵉ) → gcd-ℕᵉ aᵉ bᵉ ＝ᵉ gcd-ℕᵉ bᵉ aᵉ
is-commutative-gcd-ℕᵉ aᵉ bᵉ =
  antisymmetric-div-ℕᵉ
    ( gcd-ℕᵉ aᵉ bᵉ)
    ( gcd-ℕᵉ bᵉ aᵉ)
    ( pr1ᵉ (is-gcd-gcd-ℕᵉ bᵉ aᵉ (gcd-ℕᵉ aᵉ bᵉ)) (σᵉ (is-common-divisor-gcd-ℕᵉ aᵉ bᵉ)))
    ( pr1ᵉ (is-gcd-gcd-ℕᵉ aᵉ bᵉ (gcd-ℕᵉ bᵉ aᵉ)) (σᵉ (is-common-divisor-gcd-ℕᵉ bᵉ aᵉ)))
  where
  σᵉ : {Aᵉ Bᵉ : UUᵉ lzeroᵉ} → Aᵉ ×ᵉ Bᵉ → Bᵉ ×ᵉ Aᵉ
  pr1ᵉ (σᵉ (pairᵉ xᵉ yᵉ)) = yᵉ
  pr2ᵉ (σᵉ (pairᵉ xᵉ yᵉ)) = xᵉ
```

### If `d` is a common divisor of `a` and `b`, then `kd` is a common divisor of `ka` and `kb`

```agda
preserves-is-common-divisor-mul-ℕᵉ :
  (kᵉ aᵉ bᵉ dᵉ : ℕᵉ) → is-common-divisor-ℕᵉ aᵉ bᵉ dᵉ →
  is-common-divisor-ℕᵉ (kᵉ *ℕᵉ aᵉ) (kᵉ *ℕᵉ bᵉ) (kᵉ *ℕᵉ dᵉ)
preserves-is-common-divisor-mul-ℕᵉ kᵉ aᵉ bᵉ dᵉ =
  map-productᵉ
    ( preserves-div-mul-ℕᵉ kᵉ dᵉ aᵉ)
    ( preserves-div-mul-ℕᵉ kᵉ dᵉ bᵉ)

reflects-is-common-divisor-mul-ℕᵉ :
  (kᵉ aᵉ bᵉ dᵉ : ℕᵉ) → is-nonzero-ℕᵉ kᵉ →
  is-common-divisor-ℕᵉ (kᵉ *ℕᵉ aᵉ) (kᵉ *ℕᵉ bᵉ) (kᵉ *ℕᵉ dᵉ) →
  is-common-divisor-ℕᵉ aᵉ bᵉ dᵉ
reflects-is-common-divisor-mul-ℕᵉ kᵉ aᵉ bᵉ dᵉ Hᵉ =
  map-productᵉ
    ( reflects-div-mul-ℕᵉ kᵉ dᵉ aᵉ Hᵉ)
    ( reflects-div-mul-ℕᵉ kᵉ dᵉ bᵉ Hᵉ)
```

### `gcd-ℕ 1 b ＝ 1`

```agda
is-one-is-gcd-one-ℕᵉ : {bᵉ xᵉ : ℕᵉ} → is-gcd-ℕᵉ 1 bᵉ xᵉ → is-one-ℕᵉ xᵉ
is-one-is-gcd-one-ℕᵉ {bᵉ} {xᵉ} Hᵉ =
  is-one-div-one-ℕᵉ xᵉ (pr1ᵉ (is-common-divisor-is-gcd-ℕᵉ 1 bᵉ xᵉ Hᵉ))

is-one-gcd-one-ℕᵉ : (bᵉ : ℕᵉ) → is-one-ℕᵉ (gcd-ℕᵉ 1 bᵉ)
is-one-gcd-one-ℕᵉ bᵉ = is-one-is-gcd-one-ℕᵉ (is-gcd-gcd-ℕᵉ 1 bᵉ)
```

### `gcd-ℕ a 1 ＝ 1`

```agda
is-one-is-gcd-one-ℕ'ᵉ : {aᵉ xᵉ : ℕᵉ} → is-gcd-ℕᵉ aᵉ 1 xᵉ → is-one-ℕᵉ xᵉ
is-one-is-gcd-one-ℕ'ᵉ {aᵉ} {xᵉ} Hᵉ =
  is-one-div-one-ℕᵉ xᵉ (pr2ᵉ (is-common-divisor-is-gcd-ℕᵉ aᵉ 1 xᵉ Hᵉ))

is-one-gcd-one-ℕ'ᵉ : (aᵉ : ℕᵉ) → is-one-ℕᵉ (gcd-ℕᵉ aᵉ 1ᵉ)
is-one-gcd-one-ℕ'ᵉ aᵉ = is-one-is-gcd-one-ℕ'ᵉ (is-gcd-gcd-ℕᵉ aᵉ 1ᵉ)
```

### `gcd-ℕ 0 b ＝ b`

```agda
is-id-is-gcd-zero-ℕᵉ : {bᵉ xᵉ : ℕᵉ} → gcd-ℕᵉ 0 bᵉ ＝ᵉ xᵉ → xᵉ ＝ᵉ bᵉ
is-id-is-gcd-zero-ℕᵉ {bᵉ} {xᵉ} Hᵉ = antisymmetric-div-ℕᵉ xᵉ bᵉ
  (pr2ᵉ (is-common-divisor-is-gcd-ℕᵉ 0 bᵉ xᵉ
    (trᵉ (λ tᵉ → is-gcd-ℕᵉ 0 bᵉ tᵉ) Hᵉ (is-gcd-gcd-ℕᵉ 0 bᵉ))))
  (trᵉ (λ tᵉ → div-ℕᵉ bᵉ tᵉ) Hᵉ
    (div-gcd-is-common-divisor-ℕᵉ 0 bᵉ bᵉ
      (pair'ᵉ (div-zero-ℕᵉ bᵉ) (refl-div-ℕᵉ bᵉ))))
```

### `gcd-ℕ a 0 ＝ a`

```agda
is-id-is-gcd-zero-ℕ'ᵉ : {aᵉ xᵉ : ℕᵉ} → gcd-ℕᵉ aᵉ 0 ＝ᵉ xᵉ → xᵉ ＝ᵉ aᵉ
is-id-is-gcd-zero-ℕ'ᵉ {aᵉ} {xᵉ} Hᵉ = is-id-is-gcd-zero-ℕᵉ {aᵉ} {xᵉ}
  ((is-commutative-gcd-ℕᵉ 0 aᵉ) ∙ᵉ Hᵉ)
```

### Consider a common divisor `d` of `a` and `b` and let `e` be a divisor of `d`. Then any divisor of `d/e` is a common divisor of `a/e` and `b/e`

```agda
is-common-divisor-quotients-div-quotient-ℕᵉ :
  {aᵉ bᵉ dᵉ eᵉ nᵉ : ℕᵉ} → is-nonzero-ℕᵉ eᵉ → (Hᵉ : is-common-divisor-ℕᵉ aᵉ bᵉ dᵉ)
  (Kᵉ : div-ℕᵉ eᵉ dᵉ) → div-ℕᵉ nᵉ (quotient-div-ℕᵉ eᵉ dᵉ Kᵉ) →
  (Mᵉ : is-common-divisor-ℕᵉ aᵉ bᵉ eᵉ) →
  is-common-divisor-ℕᵉ
    ( quotient-div-ℕᵉ eᵉ aᵉ (pr1ᵉ Mᵉ))
    ( quotient-div-ℕᵉ eᵉ bᵉ (pr2ᵉ Mᵉ))
    ( nᵉ)
pr1ᵉ (is-common-divisor-quotients-div-quotient-ℕᵉ nzᵉ Hᵉ Kᵉ Lᵉ Mᵉ) =
  div-quotient-div-div-quotient-div-ℕᵉ nzᵉ (pr1ᵉ Hᵉ) Kᵉ (pr1ᵉ Mᵉ) Lᵉ
pr2ᵉ (is-common-divisor-quotients-div-quotient-ℕᵉ nzᵉ Hᵉ Kᵉ Lᵉ Mᵉ) =
  div-quotient-div-div-quotient-div-ℕᵉ nzᵉ (pr2ᵉ Hᵉ) Kᵉ (pr2ᵉ Mᵉ) Lᵉ

simplify-is-common-divisor-quotient-div-ℕᵉ :
  {aᵉ bᵉ dᵉ xᵉ : ℕᵉ} → is-nonzero-ℕᵉ dᵉ → (Hᵉ : is-common-divisor-ℕᵉ aᵉ bᵉ dᵉ) →
  is-common-divisor-ℕᵉ
    ( quotient-div-ℕᵉ dᵉ aᵉ (pr1ᵉ Hᵉ))
    ( quotient-div-ℕᵉ dᵉ bᵉ (pr2ᵉ Hᵉ))
    ( xᵉ) ↔ᵉ
  is-common-divisor-ℕᵉ aᵉ bᵉ (xᵉ *ℕᵉ dᵉ)
pr1ᵉ (pr1ᵉ (simplify-is-common-divisor-quotient-div-ℕᵉ nzᵉ Hᵉ) Kᵉ) =
  forward-implicationᵉ (simplify-div-quotient-div-ℕᵉ nzᵉ (pr1ᵉ Hᵉ)) (pr1ᵉ Kᵉ)
pr2ᵉ (pr1ᵉ (simplify-is-common-divisor-quotient-div-ℕᵉ nzᵉ Hᵉ) Kᵉ) =
  forward-implicationᵉ (simplify-div-quotient-div-ℕᵉ nzᵉ (pr2ᵉ Hᵉ)) (pr2ᵉ Kᵉ)
pr1ᵉ (pr2ᵉ (simplify-is-common-divisor-quotient-div-ℕᵉ nzᵉ Hᵉ) Kᵉ) =
  backward-implicationᵉ (simplify-div-quotient-div-ℕᵉ nzᵉ (pr1ᵉ Hᵉ)) (pr1ᵉ Kᵉ)
pr2ᵉ (pr2ᵉ (simplify-is-common-divisor-quotient-div-ℕᵉ nzᵉ Hᵉ) Kᵉ) =
  backward-implicationᵉ (simplify-div-quotient-div-ℕᵉ nzᵉ (pr2ᵉ Hᵉ)) (pr2ᵉ Kᵉ)
```

### The greatest common divisor of `a/d` and `b/d` is `gcd(a,b)/d`

```agda
is-gcd-quotient-div-gcd-ℕᵉ :
  {aᵉ bᵉ dᵉ : ℕᵉ} → is-nonzero-ℕᵉ dᵉ → (Hᵉ : is-common-divisor-ℕᵉ aᵉ bᵉ dᵉ) →
  is-gcd-ℕᵉ
    ( quotient-div-ℕᵉ dᵉ aᵉ (pr1ᵉ Hᵉ))
    ( quotient-div-ℕᵉ dᵉ bᵉ (pr2ᵉ Hᵉ))
    ( quotient-div-ℕᵉ dᵉ
      ( gcd-ℕᵉ aᵉ bᵉ)
      ( div-gcd-is-common-divisor-ℕᵉ aᵉ bᵉ dᵉ Hᵉ))
is-gcd-quotient-div-gcd-ℕᵉ {aᵉ} {bᵉ} {dᵉ} nzᵉ Hᵉ xᵉ =
  logical-equivalence-reasoningᵉ
    is-common-divisor-ℕᵉ
      ( quotient-div-ℕᵉ dᵉ aᵉ (pr1ᵉ Hᵉ))
      ( quotient-div-ℕᵉ dᵉ bᵉ (pr2ᵉ Hᵉ))
      ( xᵉ)
    ↔ᵉ is-common-divisor-ℕᵉ aᵉ bᵉ (xᵉ *ℕᵉ dᵉ)
      byᵉ simplify-is-common-divisor-quotient-div-ℕᵉ nzᵉ Hᵉ
    ↔ᵉ div-ℕᵉ (xᵉ *ℕᵉ dᵉ) (gcd-ℕᵉ aᵉ bᵉ)
      byᵉ is-gcd-gcd-ℕᵉ aᵉ bᵉ (xᵉ *ℕᵉ dᵉ)
    ↔ᵉ div-ℕᵉ xᵉ
        ( quotient-div-ℕᵉ dᵉ
          ( gcd-ℕᵉ aᵉ bᵉ)
          ( div-gcd-is-common-divisor-ℕᵉ aᵉ bᵉ dᵉ Hᵉ))
      byᵉ
      inv-iffᵉ
        ( simplify-div-quotient-div-ℕᵉ nzᵉ
          ( div-gcd-is-common-divisor-ℕᵉ aᵉ bᵉ dᵉ Hᵉ))
```