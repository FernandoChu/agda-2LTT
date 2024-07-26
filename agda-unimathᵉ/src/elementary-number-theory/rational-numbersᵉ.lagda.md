# The rational numbers

```agda
module elementary-number-theory.rational-numbersᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.divisibility-integersᵉ
open import elementary-number-theory.greatest-common-divisor-integersᵉ
open import elementary-number-theory.integer-fractionsᵉ
open import elementary-number-theory.integersᵉ
open import elementary-number-theory.mediant-integer-fractionsᵉ
open import elementary-number-theory.multiplication-integersᵉ
open import elementary-number-theory.positive-and-negative-integersᵉ
open import elementary-number-theory.positive-integersᵉ
open import elementary-number-theory.reduced-integer-fractionsᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equality-cartesian-product-typesᵉ
open import foundation.equality-dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.negationᵉ
open import foundation.propositionsᵉ
open import foundation.reflecting-maps-equivalence-relationsᵉ
open import foundation.setsᵉ
open import foundation.subtypesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Theᵉ typeᵉ ofᵉ rationalᵉ numbersᵉ isᵉ theᵉ quotientᵉ ofᵉ theᵉ typeᵉ ofᵉ fractions,ᵉ byᵉ theᵉ
equivalenceᵉ relationᵉ givenᵉ byᵉ `(n/mᵉ) ~ᵉ (n'/m'ᵉ) :=ᵉ Idᵉ (nᵉ *ℤᵉ m'ᵉ) (n'ᵉ *ℤᵉ m)`.ᵉ

## Definitions

### The type of rationals

```agda
ℚᵉ : UUᵉ lzero
ℚᵉ = Σᵉ fraction-ℤᵉ is-reduced-fraction-ℤᵉ

module _
  (xᵉ : ℚᵉ)
  where

  fraction-ℚᵉ : fraction-ℤᵉ
  fraction-ℚᵉ = pr1ᵉ xᵉ

  is-reduced-fraction-ℚᵉ : is-reduced-fraction-ℤᵉ fraction-ℚᵉ
  is-reduced-fraction-ℚᵉ = pr2ᵉ xᵉ

  numerator-ℚᵉ : ℤᵉ
  numerator-ℚᵉ = numerator-fraction-ℤᵉ fraction-ℚᵉ

  positive-denominator-ℚᵉ : positive-ℤᵉ
  positive-denominator-ℚᵉ = positive-denominator-fraction-ℤᵉ fraction-ℚᵉ

  denominator-ℚᵉ : ℤᵉ
  denominator-ℚᵉ = denominator-fraction-ℤᵉ fraction-ℚᵉ

  is-positive-denominator-ℚᵉ : is-positive-ℤᵉ denominator-ℚᵉ
  is-positive-denominator-ℚᵉ = is-positive-denominator-fraction-ℤᵉ fraction-ℚᵉ
```

### Inclusion of fractions

```agda
rational-fraction-ℤᵉ : fraction-ℤᵉ → ℚᵉ
pr1ᵉ (rational-fraction-ℤᵉ xᵉ) = reduce-fraction-ℤᵉ xᵉ
pr2ᵉ (rational-fraction-ℤᵉ xᵉ) = is-reduced-reduce-fraction-ℤᵉ xᵉ
```

### Inclusion of the integers

```agda
rational-ℤᵉ : ℤᵉ → ℚᵉ
pr1ᵉ (pr1ᵉ (rational-ℤᵉ xᵉ)) = xᵉ
pr2ᵉ (pr1ᵉ (rational-ℤᵉ xᵉ)) = one-positive-ℤᵉ
pr2ᵉ (rational-ℤᵉ xᵉ) = is-one-gcd-one-ℤ'ᵉ xᵉ
```

### Negative one, zero and one

```agda
neg-one-ℚᵉ : ℚᵉ
neg-one-ℚᵉ = rational-ℤᵉ neg-one-ℤᵉ

is-neg-one-ℚᵉ : ℚᵉ → UUᵉ lzero
is-neg-one-ℚᵉ xᵉ = (xᵉ ＝ᵉ neg-one-ℚᵉ)

zero-ℚᵉ : ℚᵉ
zero-ℚᵉ = rational-ℤᵉ zero-ℤᵉ

is-zero-ℚᵉ : ℚᵉ → UUᵉ lzero
is-zero-ℚᵉ xᵉ = (xᵉ ＝ᵉ zero-ℚᵉ)

is-nonzero-ℚᵉ : ℚᵉ → UUᵉ lzero
is-nonzero-ℚᵉ kᵉ = ¬ᵉ (is-zero-ℚᵉ kᵉ)

one-ℚᵉ : ℚᵉ
one-ℚᵉ = rational-ℤᵉ one-ℤᵉ

is-one-ℚᵉ : ℚᵉ → UUᵉ lzero
is-one-ℚᵉ xᵉ = (xᵉ ＝ᵉ one-ℚᵉ)
```

### The negative of a rational number

```agda
neg-ℚᵉ : ℚᵉ → ℚᵉ
pr1ᵉ (neg-ℚᵉ (xᵉ ,ᵉ Hᵉ)) = neg-fraction-ℤᵉ xᵉ
pr2ᵉ (neg-ℚᵉ (xᵉ ,ᵉ Hᵉ)) = is-reduced-neg-fraction-ℤᵉ xᵉ Hᵉ
```

### The mediant of two rationals

```agda
mediant-ℚᵉ : ℚᵉ → ℚᵉ → ℚᵉ
mediant-ℚᵉ xᵉ yᵉ =
  rational-fraction-ℤᵉ
    ( mediant-fraction-ℤᵉ
      ( fraction-ℚᵉ xᵉ)
      ( fraction-ℚᵉ yᵉ))
```

## Properties

### The rational images of two similar integer fractions are equal

```agda
eq-ℚ-sim-fraction-ℤᵉ :
  (xᵉ yᵉ : fraction-ℤᵉ) → (Hᵉ : sim-fraction-ℤᵉ xᵉ yᵉ) →
  rational-fraction-ℤᵉ xᵉ ＝ᵉ rational-fraction-ℤᵉ yᵉ
eq-ℚ-sim-fraction-ℤᵉ xᵉ yᵉ Hᵉ =
  eq-pair-Σ'ᵉ
    ( pairᵉ
      ( unique-reduce-fraction-ℤᵉ xᵉ yᵉ Hᵉ)
      ( eq-is-propᵉ (is-prop-is-reduced-fraction-ℤᵉ (reduce-fraction-ℤᵉ yᵉ))))
```

### The type of rationals is a set

```agda
abstract
  is-set-ℚᵉ : is-setᵉ ℚᵉ
  is-set-ℚᵉ =
    is-set-Σᵉ
      ( is-set-fraction-ℤᵉ)
      ( λ xᵉ → is-set-is-propᵉ (is-prop-is-reduced-fraction-ℤᵉ xᵉ))

ℚ-Setᵉ : Setᵉ lzero
pr1ᵉ ℚ-Setᵉ = ℚᵉ
pr2ᵉ ℚ-Setᵉ = is-set-ℚᵉ

abstract
  is-retraction-rational-fraction-ℚᵉ :
    (xᵉ : ℚᵉ) → rational-fraction-ℤᵉ (fraction-ℚᵉ xᵉ) ＝ᵉ xᵉ
  is-retraction-rational-fraction-ℚᵉ (pairᵉ (pairᵉ mᵉ (pairᵉ nᵉ n-posᵉ)) pᵉ) =
    eq-pair-Σᵉ
      ( eq-pairᵉ
        ( eq-quotient-div-is-one-ℤᵉ _ _ pᵉ (div-left-gcd-ℤᵉ mᵉ nᵉ))
        ( eq-pair-Σᵉ
          ( eq-quotient-div-is-one-ℤᵉ _ _ pᵉ (div-right-gcd-ℤᵉ mᵉ nᵉ))
          ( eq-is-propᵉ (is-prop-is-positive-ℤᵉ nᵉ))))
      ( eq-is-propᵉ (is-prop-is-reduced-fraction-ℤᵉ (mᵉ ,ᵉ nᵉ ,ᵉ n-posᵉ)))
```

### Two fractions with the same numerator and same denominator are equal

```agda
module _
  ( xᵉ yᵉ : ℚᵉ)
  ( Hᵉ : numerator-ℚᵉ xᵉ ＝ᵉ numerator-ℚᵉ yᵉ)
  ( Kᵉ : denominator-ℚᵉ xᵉ ＝ᵉ denominator-ℚᵉ yᵉ)
  where

  abstract
    eq-ℚᵉ : xᵉ ＝ᵉ yᵉ
    eq-ℚᵉ =
      ( invᵉ (is-retraction-rational-fraction-ℚᵉ xᵉ)) ∙ᵉ
      ( eq-ℚ-sim-fraction-ℤᵉ
        ( fraction-ℚᵉ xᵉ)
        ( fraction-ℚᵉ yᵉ)
        ( ap-mul-ℤᵉ Hᵉ (invᵉ Kᵉ))) ∙ᵉ
      ( is-retraction-rational-fraction-ℚᵉ yᵉ)
```

### A rational number is zero if and only if its numerator is zero

```agda
module _
  (xᵉ : ℚᵉ)
  where

  abstract
    is-zero-numerator-is-zero-ℚᵉ :
      is-zero-ℚᵉ xᵉ → is-zero-ℤᵉ (numerator-ℚᵉ xᵉ)
    is-zero-numerator-is-zero-ℚᵉ = apᵉ numerator-ℚᵉ

    is-zero-is-zero-numerator-ℚᵉ :
      is-zero-ℤᵉ (numerator-ℚᵉ xᵉ) → is-zero-ℚᵉ xᵉ
    is-zero-is-zero-numerator-ℚᵉ Hᵉ =
      ( invᵉ (is-retraction-rational-fraction-ℚᵉ xᵉ)) ∙ᵉ
      ( eq-ℚ-sim-fraction-ℤᵉ
        ( fraction-ℚᵉ xᵉ)
        ( fraction-ℚᵉ zero-ℚᵉ)
        ( eq-is-zero-ℤᵉ
          ( apᵉ (mul-ℤ'ᵉ one-ℤᵉ) Hᵉ ∙ᵉ right-zero-law-mul-ℤᵉ one-ℤᵉ)
          ( left-zero-law-mul-ℤᵉ (denominator-ℚᵉ xᵉ)))) ∙ᵉ
      ( is-retraction-rational-fraction-ℚᵉ zero-ℚᵉ)
```

### The rational image of the negative of an integer is the rational negative of its image

```agda
abstract
  preserves-neg-rational-ℤᵉ :
    (kᵉ : ℤᵉ) → rational-ℤᵉ (neg-ℤᵉ kᵉ) ＝ᵉ neg-ℚᵉ (rational-ℤᵉ kᵉ)
  preserves-neg-rational-ℤᵉ kᵉ =
    eq-ℚᵉ (rational-ℤᵉ (neg-ℤᵉ kᵉ)) (neg-ℚᵉ (rational-ℤᵉ kᵉ)) reflᵉ reflᵉ
```

### The reduced fraction of the negative of an integer fraction is the negative of the reduced fraction

```agda
abstract
  preserves-neg-rational-fraction-ℤᵉ :
    (xᵉ : fraction-ℤᵉ) →
    rational-fraction-ℤᵉ (neg-fraction-ℤᵉ xᵉ) ＝ᵉ neg-ℚᵉ (rational-fraction-ℤᵉ xᵉ)
  preserves-neg-rational-fraction-ℤᵉ xᵉ =
    ( eq-ℚ-sim-fraction-ℤᵉ
      ( neg-fraction-ℤᵉ xᵉ)
      ( fraction-ℚᵉ (neg-ℚᵉ (rational-fraction-ℤᵉ xᵉ)))
      ( preserves-sim-neg-fraction-ℤᵉ
        ( xᵉ)
        ( reduce-fraction-ℤᵉ xᵉ)
        ( sim-reduced-fraction-ℤᵉ xᵉ))) ∙ᵉ
    ( is-retraction-rational-fraction-ℚᵉ (neg-ℚᵉ (rational-fraction-ℤᵉ xᵉ)))
```

### The negative function on the rational numbers is an involution

```agda
abstract
  neg-neg-ℚᵉ : (xᵉ : ℚᵉ) → neg-ℚᵉ (neg-ℚᵉ xᵉ) ＝ᵉ xᵉ
  neg-neg-ℚᵉ xᵉ = eq-ℚᵉ (neg-ℚᵉ (neg-ℚᵉ xᵉ)) xᵉ (neg-neg-ℤᵉ (numerator-ℚᵉ xᵉ)) reflᵉ
```

### The reflecting map from `fraction-ℤ` to `ℚ`

```agda
reflecting-map-sim-fractionᵉ :
  reflecting-map-equivalence-relationᵉ equivalence-relation-sim-fraction-ℤᵉ ℚᵉ
pr1ᵉ reflecting-map-sim-fractionᵉ = rational-fraction-ℤᵉ
pr2ᵉ reflecting-map-sim-fractionᵉ {xᵉ} {yᵉ} Hᵉ = eq-ℚ-sim-fraction-ℤᵉ xᵉ yᵉ Hᵉ
```