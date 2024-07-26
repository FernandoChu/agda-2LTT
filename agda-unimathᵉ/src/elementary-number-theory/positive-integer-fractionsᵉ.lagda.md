# Positive integer fractions

```agda
module elementary-number-theory.positive-integer-fractionsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integer-fractionsᵉ
open import elementary-number-theory.addition-positive-and-negative-integersᵉ
open import elementary-number-theory.integer-fractionsᵉ
open import elementary-number-theory.integersᵉ
open import elementary-number-theory.multiplication-integer-fractionsᵉ
open import elementary-number-theory.multiplication-positive-and-negative-integersᵉ
open import elementary-number-theory.positive-integersᵉ
open import elementary-number-theory.reduced-integer-fractionsᵉ

open import foundation.propositionsᵉ
open import foundation.subtypesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Anᵉ [integerᵉ fraction](elementary-number-theory.integer-fractions.mdᵉ) `x`ᵉ isᵉ saidᵉ
to beᵉ
{{#conceptᵉ "positive"ᵉ Disambiguation="integerᵉ fraction"ᵉ Agda=is-positive-fraction-ℤᵉ}}
ifᵉ itsᵉ numeratorᵉ isᵉ aᵉ
[positiveᵉ integer](elementary-number-theory.positive-integers.md).ᵉ

## Definitions

### The property of being a positive integer fraction

```agda
module _
  (xᵉ : fraction-ℤᵉ)
  where

  is-positive-fraction-ℤᵉ : UUᵉ lzero
  is-positive-fraction-ℤᵉ = is-positive-ℤᵉ (numerator-fraction-ℤᵉ xᵉ)

  is-prop-is-positive-fraction-ℤᵉ : is-propᵉ is-positive-fraction-ℤᵉ
  is-prop-is-positive-fraction-ℤᵉ =
    is-prop-is-positive-ℤᵉ (numerator-fraction-ℤᵉ xᵉ)
```

## Properties

### An integer fraction similar to a positive integer fraction is positive

```agda
is-positive-sim-fraction-ℤᵉ :
  (xᵉ yᵉ : fraction-ℤᵉ) (Sᵉ : sim-fraction-ℤᵉ xᵉ yᵉ) →
  is-positive-fraction-ℤᵉ xᵉ →
  is-positive-fraction-ℤᵉ yᵉ
is-positive-sim-fraction-ℤᵉ xᵉ yᵉ Sᵉ Pᵉ =
  is-positive-left-factor-mul-ℤᵉ
    ( is-positive-eq-ℤᵉ
      ( Sᵉ)
      ( is-positive-mul-ℤᵉ Pᵉ (is-positive-denominator-fraction-ℤᵉ yᵉ)))
    ( is-positive-denominator-fraction-ℤᵉ xᵉ)
```

### The reduced fraction of a positive integer fraction is positive

```agda
is-positive-reduce-fraction-ℤᵉ :
  {xᵉ : fraction-ℤᵉ} (Pᵉ : is-positive-fraction-ℤᵉ xᵉ) →
  is-positive-fraction-ℤᵉ (reduce-fraction-ℤᵉ xᵉ)
is-positive-reduce-fraction-ℤᵉ {xᵉ} =
  is-positive-sim-fraction-ℤᵉ
    ( xᵉ)
    ( reduce-fraction-ℤᵉ xᵉ)
    ( sim-reduced-fraction-ℤᵉ xᵉ)
```

### The sum of two positive integer fractions is positive

```agda
is-positive-add-fraction-ℤᵉ :
  {xᵉ yᵉ : fraction-ℤᵉ} →
  is-positive-fraction-ℤᵉ xᵉ →
  is-positive-fraction-ℤᵉ yᵉ →
  is-positive-fraction-ℤᵉ (add-fraction-ℤᵉ xᵉ yᵉ)
is-positive-add-fraction-ℤᵉ {xᵉ} {yᵉ} Pᵉ Qᵉ =
  is-positive-add-ℤᵉ
    ( is-positive-mul-ℤᵉ Pᵉ (is-positive-denominator-fraction-ℤᵉ yᵉ))
    ( is-positive-mul-ℤᵉ Qᵉ (is-positive-denominator-fraction-ℤᵉ xᵉ))
```

### The product of two positive integer fractions is positive

```agda
is-positive-mul-fraction-ℤᵉ :
  {xᵉ yᵉ : fraction-ℤᵉ} →
  is-positive-fraction-ℤᵉ xᵉ →
  is-positive-fraction-ℤᵉ yᵉ →
  is-positive-fraction-ℤᵉ (mul-fraction-ℤᵉ xᵉ yᵉ)
is-positive-mul-fraction-ℤᵉ {xᵉ} {yᵉ} = is-positive-mul-ℤᵉ
```