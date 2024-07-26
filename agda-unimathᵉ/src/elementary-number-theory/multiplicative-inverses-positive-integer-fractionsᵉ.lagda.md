# Multiplicative inverses of positive integer fractions

```agda
module elementary-number-theory.multiplicative-inverses-positive-integer-fractionsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.greatest-common-divisor-integersᵉ
open import elementary-number-theory.integer-fractionsᵉ
open import elementary-number-theory.integersᵉ
open import elementary-number-theory.multiplication-integer-fractionsᵉ
open import elementary-number-theory.multiplication-integersᵉ
open import elementary-number-theory.positive-integer-fractionsᵉ
open import elementary-number-theory.reduced-integer-fractionsᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.transport-along-identificationsᵉ
```

</details>

## Idea

Theᵉ integerᵉ fractionᵉ obtainedᵉ byᵉ swappingᵉ theᵉ numeratorᵉ andᵉ theᵉ denominatorᵉ ofᵉ aᵉ
[positiveᵉ integerᵉ fraction](elementary-number-theory.positive-integer-fractions.mdᵉ)
isᵉ aᵉ
[multiplicative](elementary-number-theory.multiplication-integer-fractions.mdᵉ)
inverseᵉ ofᵉ theᵉ originalᵉ fractionᵉ upᵉ to theᵉ canonicalᵉ similarityᵉ relationᵉ onᵉ
[integerᵉ fractions](elementary-number-theory.integer-fractions.mdᵉ): itsᵉ
multiplicationᵉ with theᵉ originalᵉ fractionᵉ isᵉ similarᵉ to one.ᵉ

## Definitions

### The inverse of a positive integer fraction

```agda
module _
  (xᵉ : fraction-ℤᵉ) (Hᵉ : is-positive-fraction-ℤᵉ xᵉ)
  where

  inv-is-positive-fraction-ℤᵉ : fraction-ℤᵉ
  pr1ᵉ inv-is-positive-fraction-ℤᵉ = denominator-fraction-ℤᵉ xᵉ
  pr1ᵉ (pr2ᵉ inv-is-positive-fraction-ℤᵉ) = numerator-fraction-ℤᵉ xᵉ
  pr2ᵉ (pr2ᵉ inv-is-positive-fraction-ℤᵉ) = Hᵉ
```

## Properties

### The inverse of a positive reduced integer fraction is reduced

```agda
module _
  (xᵉ : fraction-ℤᵉ) (Pᵉ : is-positive-fraction-ℤᵉ xᵉ)
  where

  is-reduced-inv-is-positive-fraction-ℤᵉ :
    is-reduced-fraction-ℤᵉ xᵉ →
    is-reduced-fraction-ℤᵉ (inv-is-positive-fraction-ℤᵉ xᵉ Pᵉ)
  is-reduced-inv-is-positive-fraction-ℤᵉ =
    inv-trᵉ
      ( is-one-ℤᵉ)
      ( is-commutative-gcd-ℤᵉ
        ( denominator-fraction-ℤᵉ xᵉ)
        ( numerator-fraction-ℤᵉ xᵉ))
```

### The multiplication of a positive integer fraction with its inverse is similar to one

```agda
module _
  (xᵉ : fraction-ℤᵉ) (Pᵉ : is-positive-fraction-ℤᵉ xᵉ)
  where

  left-inverse-law-mul-is-positive-fraction-ℤᵉ :
    sim-fraction-ℤᵉ
      (mul-fraction-ℤᵉ (inv-is-positive-fraction-ℤᵉ xᵉ Pᵉ) xᵉ)
      (one-fraction-ℤᵉ)
  left-inverse-law-mul-is-positive-fraction-ℤᵉ =
    ( right-unit-law-mul-ℤᵉ _) ∙ᵉ
    ( commutative-mul-ℤᵉ
      ( denominator-fraction-ℤᵉ xᵉ)
      ( numerator-fraction-ℤᵉ xᵉ)) ∙ᵉ
    ( invᵉ (left-unit-law-mul-ℤᵉ _))

  right-inverse-law-mul-is-positive-fraction-ℤᵉ :
    sim-fraction-ℤᵉ
      (mul-fraction-ℤᵉ xᵉ (inv-is-positive-fraction-ℤᵉ xᵉ Pᵉ))
      (one-fraction-ℤᵉ)
  right-inverse-law-mul-is-positive-fraction-ℤᵉ =
    ( right-unit-law-mul-ℤᵉ _) ∙ᵉ
    ( commutative-mul-ℤᵉ
      ( numerator-fraction-ℤᵉ xᵉ)
      ( denominator-fraction-ℤᵉ xᵉ)) ∙ᵉ
    ( invᵉ (left-unit-law-mul-ℤᵉ _))
```