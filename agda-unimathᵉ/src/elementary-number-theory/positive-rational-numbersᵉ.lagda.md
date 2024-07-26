# Positive rational numbers

```agda
{-# OPTIONSᵉ --lossy-unificationᵉ #-}

module elementary-number-theory.positive-rational-numbersᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integer-fractionsᵉ
open import elementary-number-theory.addition-rational-numbersᵉ
open import elementary-number-theory.additive-group-of-rational-numbersᵉ
open import elementary-number-theory.cross-multiplication-difference-integer-fractionsᵉ
open import elementary-number-theory.integer-fractionsᵉ
open import elementary-number-theory.integersᵉ
open import elementary-number-theory.multiplication-integer-fractionsᵉ
open import elementary-number-theory.multiplication-integersᵉ
open import elementary-number-theory.multiplication-rational-numbersᵉ
open import elementary-number-theory.multiplicative-inverses-positive-integer-fractionsᵉ
open import elementary-number-theory.multiplicative-monoid-of-rational-numbersᵉ
open import elementary-number-theory.negative-integersᵉ
open import elementary-number-theory.nonzero-rational-numbersᵉ
open import elementary-number-theory.positive-and-negative-integersᵉ
open import elementary-number-theory.positive-integer-fractionsᵉ
open import elementary-number-theory.positive-integersᵉ
open import elementary-number-theory.rational-numbersᵉ
open import elementary-number-theory.reduced-integer-fractionsᵉ
open import elementary-number-theory.strict-inequality-rational-numbersᵉ

open import foundation.cartesian-product-typesᵉ
open import foundation.coproduct-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.function-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.negationᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.subtypesᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.commutative-monoidsᵉ
open import group-theory.invertible-elements-monoidsᵉ
open import group-theory.monoidsᵉ
open import group-theory.semigroupsᵉ
open import group-theory.submonoidsᵉ
open import group-theory.submonoids-commutative-monoidsᵉ
open import group-theory.subsemigroupsᵉ
```

</details>

## Idea

Aᵉ [rationalᵉ number](elementary-number-theory.rational-numbers.mdᵉ) `x`ᵉ isᵉ saidᵉ to
beᵉ {{#conceptᵉ "positive"ᵉ Disambiguation="rationalᵉ number"ᵉ Agda=is-positive-ℚᵉ}}
ifᵉ itsᵉ underlyingᵉ fractionᵉ isᵉ
[positive](elementary-number-theory.positive-integer-fractions.md).ᵉ

Positiveᵉ rationalᵉ numbersᵉ areᵉ aᵉ [subsemigroup](group-theory.subsemigroups.mdᵉ) ofᵉ
theᵉ
[additiveᵉ monoidᵉ ofᵉ rationalᵉ numbers](elementary-number-theory.additive-group-of-rational-numbers.mdᵉ)
andᵉ aᵉ [submonoid](group-theory.submonoids.mdᵉ) ofᵉ theᵉ
[multiplicativeᵉ monoidᵉ ofᵉ rationalᵉ numbers](elementary-number-theory.multiplicative-monoid-of-rational-numbers.md).ᵉ

## Definitions

### The property of being a positive rational number

```agda
module _
  (xᵉ : ℚᵉ)
  where

  is-positive-ℚᵉ : UUᵉ lzero
  is-positive-ℚᵉ = is-positive-fraction-ℤᵉ (fraction-ℚᵉ xᵉ)

  is-prop-is-positive-ℚᵉ : is-propᵉ is-positive-ℚᵉ
  is-prop-is-positive-ℚᵉ = is-prop-is-positive-fraction-ℤᵉ (fraction-ℚᵉ xᵉ)

  is-positive-prop-ℚᵉ : Propᵉ lzero
  pr1ᵉ is-positive-prop-ℚᵉ = is-positive-ℚᵉ
  pr2ᵉ is-positive-prop-ℚᵉ = is-prop-is-positive-ℚᵉ
```

### The type of positive rational numbers

```agda
positive-ℚᵉ : UUᵉ lzero
positive-ℚᵉ = type-subtypeᵉ is-positive-prop-ℚᵉ

ℚ⁺ᵉ : UUᵉ lzero
ℚ⁺ᵉ = positive-ℚᵉ

module _
  (xᵉ : positive-ℚᵉ)
  where

  rational-ℚ⁺ᵉ : ℚᵉ
  rational-ℚ⁺ᵉ = pr1ᵉ xᵉ

  fraction-ℚ⁺ᵉ : fraction-ℤᵉ
  fraction-ℚ⁺ᵉ = fraction-ℚᵉ rational-ℚ⁺ᵉ

  numerator-ℚ⁺ᵉ : ℤᵉ
  numerator-ℚ⁺ᵉ = numerator-ℚᵉ rational-ℚ⁺ᵉ

  denominator-ℚ⁺ᵉ : ℤᵉ
  denominator-ℚ⁺ᵉ = denominator-ℚᵉ rational-ℚ⁺ᵉ

  is-positive-rational-ℚ⁺ᵉ : is-positive-ℚᵉ rational-ℚ⁺ᵉ
  is-positive-rational-ℚ⁺ᵉ = pr2ᵉ xᵉ

  is-positive-fraction-ℚ⁺ᵉ : is-positive-fraction-ℤᵉ fraction-ℚ⁺ᵉ
  is-positive-fraction-ℚ⁺ᵉ = is-positive-rational-ℚ⁺ᵉ

  is-positive-numerator-ℚ⁺ᵉ : is-positive-ℤᵉ numerator-ℚ⁺ᵉ
  is-positive-numerator-ℚ⁺ᵉ = is-positive-rational-ℚ⁺ᵉ

  is-positive-denominator-ℚ⁺ᵉ : is-positive-ℤᵉ denominator-ℚ⁺ᵉ
  is-positive-denominator-ℚ⁺ᵉ = is-positive-denominator-ℚᵉ rational-ℚ⁺ᵉ

abstract
  eq-ℚ⁺ᵉ : {xᵉ yᵉ : ℚ⁺ᵉ} → rational-ℚ⁺ᵉ xᵉ ＝ᵉ rational-ℚ⁺ᵉ yᵉ → xᵉ ＝ᵉ yᵉ
  eq-ℚ⁺ᵉ {xᵉ} {yᵉ} = eq-type-subtypeᵉ is-positive-prop-ℚᵉ
```

## Properties

### The positive rational numbers form a set

```agda
is-set-ℚ⁺ᵉ : is-setᵉ ℚ⁺ᵉ
is-set-ℚ⁺ᵉ = is-set-type-subtypeᵉ is-positive-prop-ℚᵉ is-set-ℚᵉ
```

### The rational image of a positive integer is positive

```agda
abstract
  is-positive-rational-ℤᵉ :
    (xᵉ : ℤᵉ) → is-positive-ℤᵉ xᵉ → is-positive-ℚᵉ (rational-ℤᵉ xᵉ)
  is-positive-rational-ℤᵉ xᵉ Pᵉ = Pᵉ

one-ℚ⁺ᵉ : ℚ⁺ᵉ
one-ℚ⁺ᵉ = (one-ℚᵉ ,ᵉ is-positive-int-positive-ℤᵉ one-positive-ℤᵉ)
```

### The rational image of a positive integer fraction is positive

```agda
abstract
  is-positive-rational-fraction-ℤᵉ :
    {xᵉ : fraction-ℤᵉ} (Pᵉ : is-positive-fraction-ℤᵉ xᵉ) →
    is-positive-ℚᵉ (rational-fraction-ℤᵉ xᵉ)
  is-positive-rational-fraction-ℤᵉ = is-positive-reduce-fraction-ℤᵉ
```

### A rational number `x` is positive if and only if `0 < x`

```agda
module _
  (xᵉ : ℚᵉ)
  where

  abstract
    le-zero-is-positive-ℚᵉ : is-positive-ℚᵉ xᵉ → le-ℚᵉ zero-ℚᵉ xᵉ
    le-zero-is-positive-ℚᵉ =
      is-positive-eq-ℤᵉ (invᵉ (cross-mul-diff-zero-fraction-ℤᵉ (fraction-ℚᵉ xᵉ)))

    is-positive-le-zero-ℚᵉ : le-ℚᵉ zero-ℚᵉ xᵉ → is-positive-ℚᵉ xᵉ
    is-positive-le-zero-ℚᵉ =
      is-positive-eq-ℤᵉ (cross-mul-diff-zero-fraction-ℤᵉ (fraction-ℚᵉ xᵉ))
```

### A nonzero rational number or its negative is positive

```agda
decide-is-negative-is-positive-is-nonzero-ℚᵉ :
  {xᵉ : ℚᵉ} → is-nonzero-ℚᵉ xᵉ → is-positive-ℚᵉ (neg-ℚᵉ xᵉ) +ᵉ is-positive-ℚᵉ xᵉ
decide-is-negative-is-positive-is-nonzero-ℚᵉ {xᵉ} Hᵉ =
  rec-coproductᵉ
    ( inlᵉ ∘ᵉ is-positive-neg-is-negative-ℤᵉ)
    ( inrᵉ)
    ( decide-sign-nonzero-ℤᵉ
      { numerator-ℚᵉ xᵉ}
      (is-nonzero-numerator-is-nonzero-ℚᵉ xᵉ Hᵉ))
```

### A rational and its negative are not both positive

```agda
abstract
  not-is-negative-is-positive-ℚᵉ :
    (xᵉ : ℚᵉ) → ¬ᵉ (is-positive-ℚᵉ (neg-ℚᵉ xᵉ) ×ᵉ is-positive-ℚᵉ xᵉ)
  not-is-negative-is-positive-ℚᵉ xᵉ (Nᵉ ,ᵉ Pᵉ) =
    is-not-negative-and-positive-ℤᵉ
      ( numerator-ℚᵉ xᵉ)
      ( ( is-negative-eq-ℤᵉ
          (neg-neg-ℤᵉ (numerator-ℚᵉ xᵉ))
          (is-negative-neg-is-positive-ℤᵉ {numerator-ℚᵉ (neg-ℚᵉ xᵉ)} Nᵉ)) ,ᵉ
        ( Pᵉ))
```

### Positive rational numbers are nonzero

```agda
abstract
  is-nonzero-is-positive-ℚᵉ : {xᵉ : ℚᵉ} → is-positive-ℚᵉ xᵉ → is-nonzero-ℚᵉ xᵉ
  is-nonzero-is-positive-ℚᵉ {xᵉ} Hᵉ =
    is-nonzero-is-nonzero-numerator-ℚᵉ xᵉ
      ( is-nonzero-is-positive-ℤᵉ
        { numerator-ℚᵉ xᵉ}
        ( Hᵉ))

nonzero-ℚ⁺ᵉ : positive-ℚᵉ → nonzero-ℚᵉ
nonzero-ℚ⁺ᵉ (xᵉ ,ᵉ Pᵉ) = (xᵉ ,ᵉ is-nonzero-is-positive-ℚᵉ Pᵉ)
```

### The sum of two positive rational numbers is positive

```agda
abstract
  is-positive-add-ℚᵉ :
    {xᵉ yᵉ : ℚᵉ} → is-positive-ℚᵉ xᵉ → is-positive-ℚᵉ yᵉ → is-positive-ℚᵉ (xᵉ +ℚᵉ yᵉ)
  is-positive-add-ℚᵉ {xᵉ} {yᵉ} Pᵉ Qᵉ =
    is-positive-rational-fraction-ℤᵉ
      ( is-positive-add-fraction-ℤᵉ
        { fraction-ℚᵉ xᵉ}
        { fraction-ℚᵉ yᵉ}
        ( Pᵉ)
        ( Qᵉ))
```

### The positive rational numbers are an additive subsemigroup of the rational numbers

```agda
subsemigroup-add-ℚ⁺ᵉ : Subsemigroupᵉ lzero semigroup-add-ℚᵉ
pr1ᵉ subsemigroup-add-ℚ⁺ᵉ = is-positive-prop-ℚᵉ
pr2ᵉ subsemigroup-add-ℚ⁺ᵉ {xᵉ} {yᵉ} = is-positive-add-ℚᵉ {xᵉ} {yᵉ}

semigroup-add-ℚ⁺ᵉ : Semigroupᵉ lzero
semigroup-add-ℚ⁺ᵉ =
  semigroup-Subsemigroupᵉ semigroup-add-ℚᵉ subsemigroup-add-ℚ⁺ᵉ
```

### The positive sum of two positive rational numbers

```agda
add-ℚ⁺ᵉ : ℚ⁺ᵉ → ℚ⁺ᵉ → ℚ⁺ᵉ
add-ℚ⁺ᵉ = mul-Subsemigroupᵉ semigroup-add-ℚᵉ subsemigroup-add-ℚ⁺ᵉ

infixl 35 _+ℚ⁺ᵉ_
_+ℚ⁺ᵉ_ = add-ℚ⁺ᵉ
```

### The positive sum of positive rational numbers is associative

```agda
associative-add-ℚ⁺ᵉ : (xᵉ yᵉ zᵉ : ℚ⁺ᵉ) → ((xᵉ +ℚ⁺ᵉ yᵉ) +ℚ⁺ᵉ zᵉ) ＝ᵉ (xᵉ +ℚ⁺ᵉ (yᵉ +ℚ⁺ᵉ zᵉ))
associative-add-ℚ⁺ᵉ =
  associative-mul-Subsemigroupᵉ semigroup-add-ℚᵉ subsemigroup-add-ℚ⁺ᵉ
```

### The positive sum of positive rational numbers is commutative

```agda
commutative-add-ℚ⁺ᵉ : (xᵉ yᵉ : ℚ⁺ᵉ) → (xᵉ +ℚ⁺ᵉ yᵉ) ＝ᵉ (yᵉ +ℚ⁺ᵉ xᵉ)
commutative-add-ℚ⁺ᵉ xᵉ yᵉ =
  eq-ℚ⁺ᵉ (commutative-add-ℚᵉ (rational-ℚ⁺ᵉ xᵉ) (rational-ℚ⁺ᵉ yᵉ))
```

### The product of two positive rational numbers is positive

```agda
abstract
  is-positive-mul-ℚᵉ :
    {xᵉ yᵉ : ℚᵉ} → is-positive-ℚᵉ xᵉ → is-positive-ℚᵉ yᵉ → is-positive-ℚᵉ (xᵉ *ℚᵉ yᵉ)
  is-positive-mul-ℚᵉ {xᵉ} {yᵉ} Pᵉ Qᵉ =
    is-positive-rational-fraction-ℤᵉ
      ( is-positive-mul-fraction-ℤᵉ
        { fraction-ℚᵉ xᵉ}
        { fraction-ℚᵉ yᵉ}
        ( Pᵉ)
        ( Qᵉ))
```

### The positive rational numbers are a multiplicative submonoid of the rational numbers

```agda
is-submonoid-mul-ℚ⁺ᵉ :
  is-submonoid-subset-Monoidᵉ monoid-mul-ℚᵉ is-positive-prop-ℚᵉ
pr1ᵉ is-submonoid-mul-ℚ⁺ᵉ = is-positive-rational-ℚ⁺ᵉ one-ℚ⁺ᵉ
pr2ᵉ is-submonoid-mul-ℚ⁺ᵉ xᵉ yᵉ = is-positive-mul-ℚᵉ {xᵉ} {yᵉ}

submonoid-mul-ℚ⁺ᵉ : Submonoidᵉ lzero monoid-mul-ℚᵉ
pr1ᵉ submonoid-mul-ℚ⁺ᵉ = is-positive-prop-ℚᵉ
pr2ᵉ submonoid-mul-ℚ⁺ᵉ = is-submonoid-mul-ℚ⁺ᵉ

monoid-mul-ℚ⁺ᵉ : Monoidᵉ lzero
monoid-mul-ℚ⁺ᵉ = monoid-Submonoidᵉ monoid-mul-ℚᵉ submonoid-mul-ℚ⁺ᵉ

commutative-monoid-mul-ℚ⁺ᵉ : Commutative-Monoidᵉ lzero
commutative-monoid-mul-ℚ⁺ᵉ =
  commutative-monoid-Commutative-Submonoidᵉ
    commutative-monoid-mul-ℚᵉ
    submonoid-mul-ℚ⁺ᵉ
```

### The positive product of two positive rational numbers

```agda
mul-ℚ⁺ᵉ : ℚ⁺ᵉ → ℚ⁺ᵉ → ℚ⁺ᵉ
mul-ℚ⁺ᵉ = mul-Submonoidᵉ monoid-mul-ℚᵉ submonoid-mul-ℚ⁺ᵉ

infixl 40 _*ℚ⁺ᵉ_
_*ℚ⁺ᵉ_ = mul-ℚ⁺ᵉ
```

### The positive product of positive rational numbers is associative

```agda
associative-mul-ℚ⁺ᵉ : (xᵉ yᵉ zᵉ : ℚ⁺ᵉ) → ((xᵉ *ℚ⁺ᵉ yᵉ) *ℚ⁺ᵉ zᵉ) ＝ᵉ (xᵉ *ℚ⁺ᵉ (yᵉ *ℚ⁺ᵉ zᵉ))
associative-mul-ℚ⁺ᵉ =
  associative-mul-Submonoidᵉ monoid-mul-ℚᵉ submonoid-mul-ℚ⁺ᵉ
```

### The positive product of positive rational numbers is commutative

```agda
commutative-mul-ℚ⁺ᵉ : (xᵉ yᵉ : ℚ⁺ᵉ) → (xᵉ *ℚ⁺ᵉ yᵉ) ＝ᵉ (yᵉ *ℚ⁺ᵉ xᵉ)
commutative-mul-ℚ⁺ᵉ =
  commutative-mul-Commutative-Submonoidᵉ
    commutative-monoid-mul-ℚᵉ
    submonoid-mul-ℚ⁺ᵉ
```

### Multiplicative unit laws for positive multiplication of positive rational numbers

```agda
left-unit-law-mul-ℚ⁺ᵉ : (xᵉ : ℚ⁺ᵉ) → one-ℚ⁺ᵉ *ℚ⁺ᵉ xᵉ ＝ᵉ xᵉ
left-unit-law-mul-ℚ⁺ᵉ =
  left-unit-law-mul-Submonoidᵉ monoid-mul-ℚᵉ submonoid-mul-ℚ⁺ᵉ

right-unit-law-mul-ℚ⁺ᵉ : (xᵉ : ℚ⁺ᵉ) → xᵉ *ℚ⁺ᵉ one-ℚ⁺ᵉ ＝ᵉ xᵉ
right-unit-law-mul-ℚ⁺ᵉ =
  right-unit-law-mul-Submonoidᵉ monoid-mul-ℚᵉ submonoid-mul-ℚ⁺ᵉ
```

### The positive rational numbers are invertible elements of the multiplicative monoid of rational numbers

```agda
module _
  (xᵉ : ℚᵉ) (Pᵉ : is-positive-ℚᵉ xᵉ)
  where

  inv-is-positive-ℚᵉ : ℚᵉ
  pr1ᵉ inv-is-positive-ℚᵉ = inv-is-positive-fraction-ℤᵉ (fraction-ℚᵉ xᵉ) Pᵉ
  pr2ᵉ inv-is-positive-ℚᵉ =
    is-reduced-inv-is-positive-fraction-ℤᵉ
      ( fraction-ℚᵉ xᵉ)
      ( Pᵉ)
      ( is-reduced-fraction-ℚᵉ xᵉ)

  abstract
    left-inverse-law-mul-is-positive-ℚᵉ : inv-is-positive-ℚᵉ *ℚᵉ xᵉ ＝ᵉ one-ℚᵉ
    left-inverse-law-mul-is-positive-ℚᵉ =
      ( eq-ℚ-sim-fraction-ℤᵉ
        ( mul-fraction-ℤᵉ
          ( inv-is-positive-fraction-ℤᵉ (fraction-ℚᵉ xᵉ) Pᵉ)
          ( fraction-ℚᵉ xᵉ))
        ( one-fraction-ℤᵉ)
        ( left-inverse-law-mul-is-positive-fraction-ℤᵉ (fraction-ℚᵉ xᵉ) Pᵉ)) ∙ᵉ
      ( is-retraction-rational-fraction-ℚᵉ one-ℚᵉ)

    right-inverse-law-mul-is-positive-ℚᵉ : xᵉ *ℚᵉ inv-is-positive-ℚᵉ ＝ᵉ one-ℚᵉ
    right-inverse-law-mul-is-positive-ℚᵉ =
      (commutative-mul-ℚᵉ xᵉ _) ∙ᵉ (left-inverse-law-mul-is-positive-ℚᵉ)

  is-mul-invertible-is-positive-ℚᵉ : is-invertible-element-Monoidᵉ monoid-mul-ℚᵉ xᵉ
  pr1ᵉ is-mul-invertible-is-positive-ℚᵉ = inv-is-positive-ℚᵉ
  pr1ᵉ (pr2ᵉ is-mul-invertible-is-positive-ℚᵉ) =
    right-inverse-law-mul-is-positive-ℚᵉ
  pr2ᵉ (pr2ᵉ is-mul-invertible-is-positive-ℚᵉ) =
    left-inverse-law-mul-is-positive-ℚᵉ
```

### The strict inequality on positive rational numbers

```agda
le-prop-ℚ⁺ᵉ : ℚ⁺ᵉ → ℚ⁺ᵉ → Propᵉ lzero
le-prop-ℚ⁺ᵉ xᵉ yᵉ = le-ℚ-Propᵉ (rational-ℚ⁺ᵉ xᵉ) (rational-ℚ⁺ᵉ yᵉ)

le-ℚ⁺ᵉ : ℚ⁺ᵉ → ℚ⁺ᵉ → UUᵉ lzero
le-ℚ⁺ᵉ xᵉ yᵉ = type-Propᵉ (le-prop-ℚ⁺ᵉ xᵉ yᵉ)

is-prop-le-ℚ⁺ᵉ : (xᵉ yᵉ : ℚ⁺ᵉ) → is-propᵉ (le-ℚ⁺ᵉ xᵉ yᵉ)
is-prop-le-ℚ⁺ᵉ xᵉ yᵉ = is-prop-type-Propᵉ (le-prop-ℚ⁺ᵉ xᵉ yᵉ)
```

### The sum of two positive rational numbers is greater than each of them

```agda
module _
  (xᵉ yᵉ : ℚ⁺ᵉ)
  where

  le-left-add-ℚ⁺ᵉ : le-ℚ⁺ᵉ xᵉ (xᵉ +ℚ⁺ᵉ yᵉ)
  le-left-add-ℚ⁺ᵉ =
    trᵉ
      ( λ zᵉ → le-ℚᵉ zᵉ ((rational-ℚ⁺ᵉ xᵉ) +ℚᵉ (rational-ℚ⁺ᵉ yᵉ)))
      ( right-unit-law-add-ℚᵉ (rational-ℚ⁺ᵉ xᵉ))
      ( preserves-le-right-add-ℚᵉ
        ( rational-ℚ⁺ᵉ xᵉ)
        ( zero-ℚᵉ)
        ( rational-ℚ⁺ᵉ yᵉ)
        ( le-zero-is-positive-ℚᵉ
          ( rational-ℚ⁺ᵉ yᵉ)
          ( is-positive-rational-ℚ⁺ᵉ yᵉ)))

  le-right-add-ℚ⁺ᵉ : le-ℚ⁺ᵉ yᵉ (xᵉ +ℚ⁺ᵉ yᵉ)
  le-right-add-ℚ⁺ᵉ =
    trᵉ
      ( λ zᵉ → le-ℚᵉ zᵉ ((rational-ℚ⁺ᵉ xᵉ) +ℚᵉ (rational-ℚ⁺ᵉ yᵉ)))
      ( left-unit-law-add-ℚᵉ (rational-ℚ⁺ᵉ yᵉ))
      ( preserves-le-left-add-ℚᵉ
        ( rational-ℚ⁺ᵉ yᵉ)
        ( zero-ℚᵉ)
        ( rational-ℚ⁺ᵉ xᵉ)
        ( le-zero-is-positive-ℚᵉ
          ( rational-ℚ⁺ᵉ xᵉ)
          ( is-positive-rational-ℚ⁺ᵉ xᵉ)))
```