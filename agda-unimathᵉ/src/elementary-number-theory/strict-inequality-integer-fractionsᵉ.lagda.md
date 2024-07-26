# Strict inequality on the integer fractions

```agda
module elementary-number-theory.strict-inequality-integer-fractionsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integer-fractionsᵉ
open import elementary-number-theory.addition-integersᵉ
open import elementary-number-theory.addition-positive-and-negative-integersᵉ
open import elementary-number-theory.cross-multiplication-difference-integer-fractionsᵉ
open import elementary-number-theory.difference-integersᵉ
open import elementary-number-theory.inequality-integer-fractionsᵉ
open import elementary-number-theory.inequality-integersᵉ
open import elementary-number-theory.integer-fractionsᵉ
open import elementary-number-theory.integersᵉ
open import elementary-number-theory.mediant-integer-fractionsᵉ
open import elementary-number-theory.multiplication-integersᵉ
open import elementary-number-theory.multiplication-positive-and-negative-integersᵉ
open import elementary-number-theory.nonnegative-integersᵉ
open import elementary-number-theory.nonpositive-integersᵉ
open import elementary-number-theory.positive-and-negative-integersᵉ
open import elementary-number-theory.positive-integersᵉ
open import elementary-number-theory.strict-inequality-integersᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.cartesian-product-typesᵉ
open import foundation.conjunctionᵉ
open import foundation.coproduct-typesᵉ
open import foundation.decidable-propositionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.disjunctionᵉ
open import foundation.existential-quantificationᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-coproduct-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.negationᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.propositionsᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Anᵉ [integerᵉ fraction](elementary-number-theory.integer-fractions.mdᵉ) `m/n`ᵉ isᵉ
_strictlyᵉ lessᵉ thanᵉ_ theᵉ fractionᵉ `m'/n'`ᵉ ifᵉ theᵉ
[integerᵉ product](elementary-number-theory.multiplication-integers.mdᵉ) `mᵉ *ᵉ n'`ᵉ
isᵉ [strictlyᵉ less](elementary-number-theory.strict-inequality-integers.mdᵉ) thanᵉ
`m'ᵉ *ᵉ n`.ᵉ

## Definition

### Strict inequality on the integer fractions

```agda
le-fraction-ℤ-Propᵉ : fraction-ℤᵉ → fraction-ℤᵉ → Propᵉ lzero
le-fraction-ℤ-Propᵉ (mᵉ ,ᵉ nᵉ ,ᵉ pᵉ) (m'ᵉ ,ᵉ n'ᵉ ,ᵉ p'ᵉ) =
  le-ℤ-Propᵉ (mᵉ *ℤᵉ n'ᵉ) (m'ᵉ *ℤᵉ nᵉ)

le-fraction-ℤᵉ : fraction-ℤᵉ → fraction-ℤᵉ → UUᵉ lzero
le-fraction-ℤᵉ xᵉ yᵉ = type-Propᵉ (le-fraction-ℤ-Propᵉ xᵉ yᵉ)

is-prop-le-fraction-ℤᵉ : (xᵉ yᵉ : fraction-ℤᵉ) → is-propᵉ (le-fraction-ℤᵉ xᵉ yᵉ)
is-prop-le-fraction-ℤᵉ xᵉ yᵉ = is-prop-type-Propᵉ (le-fraction-ℤ-Propᵉ xᵉ yᵉ)
```

## Properties

### Strict inequality on the integer fractions is decidable

```agda
is-decidable-le-fraction-ℤᵉ :
  (xᵉ yᵉ : fraction-ℤᵉ) → (le-fraction-ℤᵉ xᵉ yᵉ) +ᵉ ¬ᵉ (le-fraction-ℤᵉ xᵉ yᵉ)
is-decidable-le-fraction-ℤᵉ xᵉ yᵉ =
  is-decidable-le-ℤᵉ
    ( numerator-fraction-ℤᵉ xᵉ *ℤᵉ denominator-fraction-ℤᵉ yᵉ)
    ( numerator-fraction-ℤᵉ yᵉ *ℤᵉ denominator-fraction-ℤᵉ xᵉ)

le-fraction-ℤ-Decidable-Propᵉ : (xᵉ yᵉ : fraction-ℤᵉ) → Decidable-Propᵉ lzero
le-fraction-ℤ-Decidable-Propᵉ xᵉ yᵉ =
  ( le-fraction-ℤᵉ xᵉ yᵉ ,ᵉ
    is-prop-le-fraction-ℤᵉ xᵉ yᵉ ,ᵉ
    is-decidable-le-fraction-ℤᵉ xᵉ yᵉ)

decide-le-leq-fraction-ℤᵉ :
  (xᵉ yᵉ : fraction-ℤᵉ) → le-fraction-ℤᵉ xᵉ yᵉ +ᵉ leq-fraction-ℤᵉ yᵉ xᵉ
decide-le-leq-fraction-ℤᵉ xᵉ yᵉ =
  map-coproductᵉ
    ( idᵉ)
    ( λ Hᵉ →
      is-nonnegative-eq-ℤᵉ
        ( skew-commutative-cross-mul-diff-fraction-ℤᵉ xᵉ yᵉ)
        ( is-nonnegative-neg-is-nonpositive-ℤᵉ Hᵉ))
    ( decide-is-positive-is-nonpositive-ℤᵉ)
```

### Strict inequality on the integer fractions implies inequality

```agda
leq-le-fraction-ℤᵉ : {xᵉ yᵉ : fraction-ℤᵉ} → le-fraction-ℤᵉ xᵉ yᵉ → leq-fraction-ℤᵉ xᵉ yᵉ
leq-le-fraction-ℤᵉ {xᵉ} {yᵉ} =
  leq-le-ℤᵉ
    { mul-ℤᵉ (numerator-fraction-ℤᵉ xᵉ) (denominator-fraction-ℤᵉ yᵉ)}
    { mul-ℤᵉ (numerator-fraction-ℤᵉ yᵉ) (denominator-fraction-ℤᵉ xᵉ)}
```

### Strict inequality on the integer fractions is asymmetric

```agda
module _
  (xᵉ yᵉ : fraction-ℤᵉ)
  where

  asymmetric-le-fraction-ℤᵉ :
    le-fraction-ℤᵉ xᵉ yᵉ → ¬ᵉ (le-fraction-ℤᵉ yᵉ xᵉ)
  asymmetric-le-fraction-ℤᵉ =
    asymmetric-le-ℤᵉ
      ( mul-ℤᵉ
        ( numerator-fraction-ℤᵉ xᵉ)
        ( denominator-fraction-ℤᵉ yᵉ))
      ( mul-ℤᵉ
        ( numerator-fraction-ℤᵉ yᵉ)
        ( denominator-fraction-ℤᵉ xᵉ))
```

### Strict inequality on the integer fractions is transitive

```agda
transitive-le-fraction-ℤᵉ :
  (pᵉ qᵉ rᵉ : fraction-ℤᵉ) →
  le-fraction-ℤᵉ qᵉ rᵉ →
  le-fraction-ℤᵉ pᵉ qᵉ →
  le-fraction-ℤᵉ pᵉ rᵉ
transitive-le-fraction-ℤᵉ pᵉ qᵉ rᵉ Hᵉ H'ᵉ =
  is-positive-right-factor-mul-ℤᵉ
    ( is-positive-eq-ℤᵉ
      ( lemma-add-cross-mul-diff-fraction-ℤᵉ pᵉ qᵉ rᵉ)
      ( is-positive-add-ℤᵉ
        ( is-positive-mul-ℤᵉ
          ( is-positive-denominator-fraction-ℤᵉ pᵉ)
          ( Hᵉ))
        ( is-positive-mul-ℤᵉ
          ( is-positive-denominator-fraction-ℤᵉ rᵉ)
          ( H'ᵉ))))
      ( is-positive-denominator-fraction-ℤᵉ qᵉ)
```

### Chaining rules for inequality and strict inequality on the integer fractions

```agda
module _
  (pᵉ qᵉ rᵉ : fraction-ℤᵉ)
  where

  concatenate-le-leq-fraction-ℤᵉ :
    le-fraction-ℤᵉ pᵉ qᵉ →
    leq-fraction-ℤᵉ qᵉ rᵉ →
    le-fraction-ℤᵉ pᵉ rᵉ
  concatenate-le-leq-fraction-ℤᵉ Hᵉ H'ᵉ =
    is-positive-right-factor-mul-ℤᵉ
      ( is-positive-eq-ℤᵉ
        ( lemma-add-cross-mul-diff-fraction-ℤᵉ pᵉ qᵉ rᵉ)
        ( is-positive-add-nonnegative-positive-ℤᵉ
          ( is-nonnegative-mul-ℤᵉ
            ( is-nonnegative-is-positive-ℤᵉ
              ( is-positive-denominator-fraction-ℤᵉ pᵉ))
            ( H'ᵉ))
          ( is-positive-mul-ℤᵉ
            ( is-positive-denominator-fraction-ℤᵉ rᵉ)
            ( Hᵉ))))
      ( is-positive-denominator-fraction-ℤᵉ qᵉ)

  concatenate-leq-le-fraction-ℤᵉ :
    leq-fraction-ℤᵉ pᵉ qᵉ →
    le-fraction-ℤᵉ qᵉ rᵉ →
    le-fraction-ℤᵉ pᵉ rᵉ
  concatenate-leq-le-fraction-ℤᵉ Hᵉ H'ᵉ =
    is-positive-right-factor-mul-ℤᵉ
      ( is-positive-eq-ℤᵉ
        ( lemma-add-cross-mul-diff-fraction-ℤᵉ pᵉ qᵉ rᵉ)
        ( is-positive-add-positive-nonnegative-ℤᵉ
          ( is-positive-mul-ℤᵉ
            ( is-positive-denominator-fraction-ℤᵉ pᵉ)
            ( H'ᵉ))
          ( is-nonnegative-mul-ℤᵉ
            ( is-nonnegative-is-positive-ℤᵉ
              ( is-positive-denominator-fraction-ℤᵉ rᵉ))
            ( Hᵉ))))
      ( is-positive-denominator-fraction-ℤᵉ qᵉ)
```

### Chaining rules for similarity and strict inequality on the integer fractions

```agda
module _
  (pᵉ qᵉ rᵉ : fraction-ℤᵉ)
  where

  concatenate-sim-le-fraction-ℤᵉ :
    sim-fraction-ℤᵉ pᵉ qᵉ →
    le-fraction-ℤᵉ qᵉ rᵉ →
    le-fraction-ℤᵉ pᵉ rᵉ
  concatenate-sim-le-fraction-ℤᵉ Hᵉ H'ᵉ =
    is-positive-right-factor-mul-ℤᵉ
      ( is-positive-eq-ℤᵉ
        ( lemma-left-sim-cross-mul-diff-fraction-ℤᵉ pᵉ qᵉ rᵉ Hᵉ)
        ( is-positive-mul-ℤᵉ
          ( is-positive-denominator-fraction-ℤᵉ pᵉ)
          ( H'ᵉ)))
      ( is-positive-denominator-fraction-ℤᵉ qᵉ)

  concatenate-le-sim-fraction-ℤᵉ :
    le-fraction-ℤᵉ pᵉ qᵉ →
    sim-fraction-ℤᵉ qᵉ rᵉ →
    le-fraction-ℤᵉ pᵉ rᵉ
  concatenate-le-sim-fraction-ℤᵉ Hᵉ H'ᵉ =
    is-positive-right-factor-mul-ℤᵉ
      ( is-positive-eq-ℤᵉ
        ( invᵉ ( lemma-right-sim-cross-mul-diff-fraction-ℤᵉ pᵉ qᵉ rᵉ H'ᵉ))
        ( is-positive-mul-ℤᵉ
          ( is-positive-denominator-fraction-ℤᵉ rᵉ)
          ( Hᵉ)))
      ( is-positive-denominator-fraction-ℤᵉ qᵉ)
```

### The similarity of integer fractions preserves strict inequality

```agda
module _
  (pᵉ qᵉ p'ᵉ q'ᵉ : fraction-ℤᵉ) (Hᵉ : sim-fraction-ℤᵉ pᵉ p'ᵉ) (Kᵉ : sim-fraction-ℤᵉ qᵉ q'ᵉ)
  where

  preserves-le-sim-fraction-ℤᵉ : le-fraction-ℤᵉ pᵉ qᵉ → le-fraction-ℤᵉ p'ᵉ q'ᵉ
  preserves-le-sim-fraction-ℤᵉ Iᵉ =
    concatenate-sim-le-fraction-ℤᵉ p'ᵉ pᵉ q'ᵉ
      ( symmetric-sim-fraction-ℤᵉ pᵉ p'ᵉ Hᵉ)
      ( concatenate-le-sim-fraction-ℤᵉ pᵉ qᵉ q'ᵉ Iᵉ Kᵉ)
```

### Fractions with equal denominator compare the same as their numerators

```agda
module _
  (xᵉ yᵉ : fraction-ℤᵉ) (Hᵉ : denominator-fraction-ℤᵉ xᵉ ＝ᵉ denominator-fraction-ℤᵉ yᵉ)
  where

  le-fraction-le-numerator-fraction-ℤᵉ :
    le-ℤᵉ (numerator-fraction-ℤᵉ xᵉ) (numerator-fraction-ℤᵉ yᵉ) →
    le-fraction-ℤᵉ xᵉ yᵉ
  le-fraction-le-numerator-fraction-ℤᵉ H'ᵉ =
    trᵉ
      ( λ (kᵉ : ℤᵉ) →
        le-ℤᵉ
          ( numerator-fraction-ℤᵉ xᵉ *ℤᵉ kᵉ)
          ( numerator-fraction-ℤᵉ yᵉ *ℤᵉ denominator-fraction-ℤᵉ xᵉ))
      ( Hᵉ)
      ( preserves-le-left-mul-positive-ℤᵉ
        ( positive-denominator-fraction-ℤᵉ xᵉ)
        ( numerator-fraction-ℤᵉ xᵉ)
        ( numerator-fraction-ℤᵉ yᵉ)
        ( H'ᵉ))
```

### The mediant of two distinct fractions lies strictly between them

```agda
module _
  (xᵉ yᵉ : fraction-ℤᵉ)
  where

  le-left-mediant-fraction-ℤᵉ :
    le-fraction-ℤᵉ xᵉ yᵉ →
    le-fraction-ℤᵉ xᵉ (mediant-fraction-ℤᵉ xᵉ yᵉ)
  le-left-mediant-fraction-ℤᵉ =
    is-positive-eq-ℤᵉ (cross-mul-diff-left-mediant-fraction-ℤᵉ xᵉ yᵉ)

  le-right-mediant-fraction-ℤᵉ :
    le-fraction-ℤᵉ xᵉ yᵉ →
    le-fraction-ℤᵉ (mediant-fraction-ℤᵉ xᵉ yᵉ) yᵉ
  le-right-mediant-fraction-ℤᵉ =
    is-positive-eq-ℤᵉ (cross-mul-diff-right-mediant-fraction-ℤᵉ xᵉ yᵉ)
```

### Strict inequality on the integer fractions is dense

```agda
module _
  (xᵉ yᵉ : fraction-ℤᵉ) (Hᵉ : le-fraction-ℤᵉ xᵉ yᵉ)
  where

  dense-le-fraction-ℤᵉ :
    existsᵉ fraction-ℤᵉ (λ rᵉ → le-fraction-ℤ-Propᵉ xᵉ rᵉ ∧ᵉ le-fraction-ℤ-Propᵉ rᵉ yᵉ)
  dense-le-fraction-ℤᵉ =
    intro-existsᵉ
      ( mediant-fraction-ℤᵉ xᵉ yᵉ)
      ( le-left-mediant-fraction-ℤᵉ xᵉ yᵉ Hᵉ ,ᵉ le-right-mediant-fraction-ℤᵉ xᵉ yᵉ Hᵉ)
```

### Strict inequality on the integer fractions is located

```agda
module _
  (xᵉ yᵉ zᵉ : fraction-ℤᵉ)
  where

  located-le-fraction-ℤᵉ :
    le-fraction-ℤᵉ yᵉ zᵉ →
    type-disjunction-Propᵉ (le-fraction-ℤ-Propᵉ yᵉ xᵉ) (le-fraction-ℤ-Propᵉ xᵉ zᵉ)
  located-le-fraction-ℤᵉ Hᵉ =
    unit-trunc-Propᵉ
      ( map-coproductᵉ
        ( idᵉ)
        ( λ pᵉ → concatenate-leq-le-fraction-ℤᵉ xᵉ yᵉ zᵉ pᵉ Hᵉ)
        ( decide-le-leq-fraction-ℤᵉ yᵉ xᵉ))
```

### `x < y` if and only if `0 < y - x`

```agda
module _
  (xᵉ yᵉ : fraction-ℤᵉ)
  where

  eq-translate-diff-le-zero-fraction-ℤᵉ :
    le-fraction-ℤᵉ zero-fraction-ℤᵉ (yᵉ +fraction-ℤᵉ (neg-fraction-ℤᵉ xᵉ)) ＝ᵉ
    le-fraction-ℤᵉ xᵉ yᵉ
  eq-translate-diff-le-zero-fraction-ℤᵉ =
    apᵉ
      ( is-positive-ℤᵉ)
      ( ( cross-mul-diff-zero-fraction-ℤᵉ (yᵉ +fraction-ℤᵉ (neg-fraction-ℤᵉ xᵉ))) ∙ᵉ
        ( apᵉ
          ( add-ℤᵉ ( (numerator-fraction-ℤᵉ yᵉ) *ℤᵉ (denominator-fraction-ℤᵉ xᵉ)))
          ( left-negative-law-mul-ℤᵉ
            ( numerator-fraction-ℤᵉ xᵉ)
            ( denominator-fraction-ℤᵉ yᵉ))))
```