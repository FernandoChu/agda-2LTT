# The positive, negative, nonnegative and nonpositive integers

```agda
module elementary-number-theory.positive-and-negative-integersᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.integersᵉ
open import elementary-number-theory.natural-numbersᵉ
open import elementary-number-theory.negative-integersᵉ
open import elementary-number-theory.nonnegative-integersᵉ
open import elementary-number-theory.nonpositive-integersᵉ
open import elementary-number-theory.nonzero-integersᵉ
open import elementary-number-theory.positive-integersᵉ

open import foundation.cartesian-product-typesᵉ
open import foundation.coproduct-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.empty-typesᵉ
open import foundation.function-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.negated-equalityᵉ
open import foundation.negationᵉ
open import foundation.unit-typeᵉ
```

</details>

## Idea

Inᵉ thisᵉ file,ᵉ weᵉ outlineᵉ basicᵉ relationsᵉ betweenᵉ negative,ᵉ nonpositive,ᵉ
nonnegative,ᵉ andᵉ positiveᵉ integers.ᵉ

## Properties

### The only nonnegative and nonpositive integer is zero

```agda
is-zero-is-nonnegative-is-nonpositive-ℤᵉ :
  {xᵉ : ℤᵉ} → is-nonnegative-ℤᵉ xᵉ → is-nonpositive-ℤᵉ xᵉ → is-zero-ℤᵉ xᵉ
is-zero-is-nonnegative-is-nonpositive-ℤᵉ {inrᵉ (inlᵉ xᵉ)} Hᵉ Kᵉ = reflᵉ
```

### No integer is both positive and negative

```agda
is-not-negative-and-positive-ℤᵉ : (xᵉ : ℤᵉ) → ¬ᵉ (is-negative-ℤᵉ xᵉ ×ᵉ is-positive-ℤᵉ xᵉ)
is-not-negative-and-positive-ℤᵉ (inlᵉ xᵉ) (Hᵉ ,ᵉ Kᵉ) = Kᵉ
is-not-negative-and-positive-ℤᵉ (inrᵉ xᵉ) (Hᵉ ,ᵉ Kᵉ) = Hᵉ
```

### Dichotomies

#### A nonzero integer is either negative or positive

```agda
decide-sign-nonzero-ℤᵉ :
  {xᵉ : ℤᵉ} → xᵉ ≠ᵉ zero-ℤᵉ → is-negative-ℤᵉ xᵉ +ᵉ is-positive-ℤᵉ xᵉ
decide-sign-nonzero-ℤᵉ {inlᵉ xᵉ} Hᵉ = inlᵉ starᵉ
decide-sign-nonzero-ℤᵉ {inrᵉ (inlᵉ xᵉ)} Hᵉ = ex-falsoᵉ (Hᵉ reflᵉ)
decide-sign-nonzero-ℤᵉ {inrᵉ (inrᵉ xᵉ)} Hᵉ = inrᵉ starᵉ
```

#### An integer is either positive or nonpositive

```agda
decide-is-positive-is-nonpositive-ℤᵉ :
  {xᵉ : ℤᵉ} → is-positive-ℤᵉ xᵉ +ᵉ is-nonpositive-ℤᵉ xᵉ
decide-is-positive-is-nonpositive-ℤᵉ {inlᵉ xᵉ} = inrᵉ starᵉ
decide-is-positive-is-nonpositive-ℤᵉ {inrᵉ (inlᵉ xᵉ)} = inrᵉ starᵉ
decide-is-positive-is-nonpositive-ℤᵉ {inrᵉ (inrᵉ xᵉ)} = inlᵉ starᵉ
```

#### An integer is either negative or nonnegative

```agda
decide-is-negative-is-nonnegative-ℤᵉ :
  {xᵉ : ℤᵉ} → is-negative-ℤᵉ xᵉ +ᵉ is-nonnegative-ℤᵉ xᵉ
decide-is-negative-is-nonnegative-ℤᵉ {inlᵉ xᵉ} = inlᵉ starᵉ
decide-is-negative-is-nonnegative-ℤᵉ {inrᵉ xᵉ} = inrᵉ starᵉ
```

#### An integer or its negative is nonnegative

```agda
decide-is-nonnegative-is-nonnegative-neg-ℤᵉ :
  {xᵉ : ℤᵉ} → (is-nonnegative-ℤᵉ xᵉ) +ᵉ (is-nonnegative-ℤᵉ (neg-ℤᵉ xᵉ))
decide-is-nonnegative-is-nonnegative-neg-ℤᵉ {inlᵉ xᵉ} = inrᵉ starᵉ
decide-is-nonnegative-is-nonnegative-neg-ℤᵉ {inrᵉ xᵉ} = inlᵉ starᵉ
```

#### An integer or its negative is nonpositive

```agda
decide-is-nonpositive-is-nonpositive-neg-ℤᵉ :
  {xᵉ : ℤᵉ} → (is-nonpositive-ℤᵉ xᵉ) +ᵉ (is-nonpositive-ℤᵉ (neg-ℤᵉ xᵉ))
decide-is-nonpositive-is-nonpositive-neg-ℤᵉ {inlᵉ xᵉ} = inlᵉ starᵉ
decide-is-nonpositive-is-nonpositive-neg-ℤᵉ {inrᵉ (inlᵉ xᵉ)} = inlᵉ starᵉ
decide-is-nonpositive-is-nonpositive-neg-ℤᵉ {inrᵉ (inrᵉ xᵉ)} = inrᵉ starᵉ
```

### Positive integers are nonnegative

```agda
is-nonnegative-is-positive-ℤᵉ : {xᵉ : ℤᵉ} → is-positive-ℤᵉ xᵉ → is-nonnegative-ℤᵉ xᵉ
is-nonnegative-is-positive-ℤᵉ {inrᵉ (inrᵉ xᵉ)} Hᵉ = Hᵉ

nonnegative-positive-ℤᵉ : positive-ℤᵉ → nonnegative-ℤᵉ
nonnegative-positive-ℤᵉ (xᵉ ,ᵉ Hᵉ) = (xᵉ ,ᵉ is-nonnegative-is-positive-ℤᵉ Hᵉ)
```

### Negative integers are nonpositive

```agda
is-nonpositive-is-negative-ℤᵉ : {xᵉ : ℤᵉ} → is-negative-ℤᵉ xᵉ → is-nonpositive-ℤᵉ xᵉ
is-nonpositive-is-negative-ℤᵉ {inlᵉ xᵉ} Hᵉ = Hᵉ

nonpositive-negative-ℤᵉ : negative-ℤᵉ → nonpositive-ℤᵉ
nonpositive-negative-ℤᵉ (xᵉ ,ᵉ Hᵉ) = (xᵉ ,ᵉ is-nonpositive-is-negative-ℤᵉ Hᵉ)
```

### Determining the sign of the successor of an integer

#### The successor of a nonnegative integer is positive

```agda
is-positive-succ-is-nonnegative-ℤᵉ :
  {xᵉ : ℤᵉ} → is-nonnegative-ℤᵉ xᵉ → is-positive-ℤᵉ (succ-ℤᵉ xᵉ)
is-positive-succ-is-nonnegative-ℤᵉ {inrᵉ (inlᵉ xᵉ)} Hᵉ = Hᵉ
is-positive-succ-is-nonnegative-ℤᵉ {inrᵉ (inrᵉ xᵉ)} Hᵉ = Hᵉ
```

#### The successor of a negative integer is nonpositive

```agda
is-nonpositive-succ-is-negative-ℤᵉ :
  {xᵉ : ℤᵉ} → is-negative-ℤᵉ xᵉ → is-nonpositive-ℤᵉ (succ-ℤᵉ xᵉ)
is-nonpositive-succ-is-negative-ℤᵉ {inlᵉ zero-ℕᵉ} Hᵉ = Hᵉ
is-nonpositive-succ-is-negative-ℤᵉ {inlᵉ (succ-ℕᵉ xᵉ)} Hᵉ = Hᵉ
```

### Determining the sign of the predecessor of an integer

#### The predecessor of a positive integer is nonnegative

```agda
is-nonnegative-pred-is-positive-ℤᵉ :
  {xᵉ : ℤᵉ} → is-positive-ℤᵉ xᵉ → is-nonnegative-ℤᵉ (pred-ℤᵉ xᵉ)
is-nonnegative-pred-is-positive-ℤᵉ {inrᵉ (inrᵉ zero-ℕᵉ)} Hᵉ = Hᵉ
is-nonnegative-pred-is-positive-ℤᵉ {inrᵉ (inrᵉ (succ-ℕᵉ xᵉ))} Hᵉ = Hᵉ
```

#### The predecessor of a nonpositive integer is negative

```agda
is-negative-pred-is-nonpositive-ℤᵉ :
  {xᵉ : ℤᵉ} → is-nonpositive-ℤᵉ xᵉ → is-negative-ℤᵉ (pred-ℤᵉ xᵉ)
is-negative-pred-is-nonpositive-ℤᵉ {inlᵉ xᵉ} Hᵉ = Hᵉ
is-negative-pred-is-nonpositive-ℤᵉ {inrᵉ (inlᵉ xᵉ)} Hᵉ = Hᵉ
```

### Determining the sign of the negative of an integer

#### The negative of a nonnegative integer is nonpositive

```agda
is-nonpositive-neg-is-nonnegative-ℤᵉ :
  {xᵉ : ℤᵉ} → is-nonnegative-ℤᵉ xᵉ → is-nonpositive-ℤᵉ (neg-ℤᵉ xᵉ)
is-nonpositive-neg-is-nonnegative-ℤᵉ {inrᵉ (inlᵉ xᵉ)} Hᵉ = Hᵉ
is-nonpositive-neg-is-nonnegative-ℤᵉ {inrᵉ (inrᵉ xᵉ)} Hᵉ = Hᵉ

neg-nonnegative-ℤᵉ : nonnegative-ℤᵉ → nonpositive-ℤᵉ
neg-nonnegative-ℤᵉ (xᵉ ,ᵉ Hᵉ) = neg-ℤᵉ xᵉ ,ᵉ is-nonpositive-neg-is-nonnegative-ℤᵉ Hᵉ
```

#### The negative of a nonpositive integer is nonnegative

```agda
is-nonnegative-neg-is-nonpositive-ℤᵉ :
  {xᵉ : ℤᵉ} → is-nonpositive-ℤᵉ xᵉ → is-nonnegative-ℤᵉ (neg-ℤᵉ xᵉ)
is-nonnegative-neg-is-nonpositive-ℤᵉ {inlᵉ xᵉ} Hᵉ = Hᵉ
is-nonnegative-neg-is-nonpositive-ℤᵉ {inrᵉ (inlᵉ xᵉ)} Hᵉ = Hᵉ

neg-nonpositive-ℤᵉ : nonpositive-ℤᵉ → nonnegative-ℤᵉ
neg-nonpositive-ℤᵉ (xᵉ ,ᵉ Hᵉ) = neg-ℤᵉ xᵉ ,ᵉ is-nonnegative-neg-is-nonpositive-ℤᵉ Hᵉ
```

#### The negative of a positive integer is negative

```agda
is-negative-neg-is-positive-ℤᵉ :
  {xᵉ : ℤᵉ} → is-positive-ℤᵉ xᵉ → is-negative-ℤᵉ (neg-ℤᵉ xᵉ)
is-negative-neg-is-positive-ℤᵉ {inrᵉ (inrᵉ xᵉ)} Hᵉ = Hᵉ

neg-positive-ℤᵉ : positive-ℤᵉ → negative-ℤᵉ
neg-positive-ℤᵉ (xᵉ ,ᵉ Hᵉ) = (neg-ℤᵉ xᵉ ,ᵉ is-negative-neg-is-positive-ℤᵉ Hᵉ)
```

#### The negative of a negative integer is positive

```agda
is-positive-neg-is-negative-ℤᵉ :
  {xᵉ : ℤᵉ} → is-negative-ℤᵉ xᵉ → is-positive-ℤᵉ (neg-ℤᵉ xᵉ)
is-positive-neg-is-negative-ℤᵉ {inlᵉ xᵉ} Hᵉ = Hᵉ

neg-negative-ℤᵉ : negative-ℤᵉ → positive-ℤᵉ
neg-negative-ℤᵉ (xᵉ ,ᵉ Hᵉ) = (neg-ℤᵉ xᵉ ,ᵉ is-positive-neg-is-negative-ℤᵉ Hᵉ)
```

### Negated properties

#### Nonpositivity is negated positivity

```agda
is-not-positive-is-nonpositive-ℤᵉ :
  {xᵉ : ℤᵉ} → is-nonpositive-ℤᵉ xᵉ → ¬ᵉ (is-positive-ℤᵉ xᵉ)
is-not-positive-is-nonpositive-ℤᵉ {inrᵉ (inlᵉ xᵉ)} _ qᵉ = qᵉ
is-not-positive-is-nonpositive-ℤᵉ {inrᵉ (inrᵉ xᵉ)} pᵉ _ = pᵉ

is-nonpositive-is-not-positive-ℤᵉ :
  {xᵉ : ℤᵉ} → ¬ᵉ (is-positive-ℤᵉ xᵉ) → is-nonpositive-ℤᵉ xᵉ
is-nonpositive-is-not-positive-ℤᵉ {xᵉ} Hᵉ =
  rec-coproductᵉ
    ( λ Kᵉ → ex-falsoᵉ (Hᵉ Kᵉ))
    ( idᵉ)
    ( decide-is-positive-is-nonpositive-ℤᵉ)
```

#### Nonnegativity is negated negativity

```agda
is-not-negative-is-nonnegative-ℤᵉ :
  {xᵉ : ℤᵉ} → is-nonnegative-ℤᵉ xᵉ → ¬ᵉ (is-negative-ℤᵉ xᵉ)
is-not-negative-is-nonnegative-ℤᵉ {xᵉ} Hᵉ Kᵉ =
  is-not-positive-is-nonpositive-ℤᵉ
    ( is-nonpositive-neg-is-nonnegative-ℤᵉ Hᵉ)
    ( is-positive-neg-is-negative-ℤᵉ Kᵉ)

is-nonnegative-is-not-negative-ℤᵉ :
  {xᵉ : ℤᵉ} → ¬ᵉ (is-negative-ℤᵉ xᵉ) → is-nonnegative-ℤᵉ xᵉ
is-nonnegative-is-not-negative-ℤᵉ {xᵉ} Hᵉ =
  rec-coproductᵉ
    ( λ Kᵉ → ex-falsoᵉ (Hᵉ Kᵉ))
    ( idᵉ)
    ( decide-is-negative-is-nonnegative-ℤᵉ)
```