# Inequality on integer fractions

```agda
module elementary-number-theory.inequality-integer-fractionsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integersᵉ
open import elementary-number-theory.addition-positive-and-negative-integersᵉ
open import elementary-number-theory.cross-multiplication-difference-integer-fractionsᵉ
open import elementary-number-theory.difference-integersᵉ
open import elementary-number-theory.inequality-integersᵉ
open import elementary-number-theory.integer-fractionsᵉ
open import elementary-number-theory.integersᵉ
open import elementary-number-theory.multiplication-integersᵉ
open import elementary-number-theory.multiplication-positive-and-negative-integersᵉ
open import elementary-number-theory.nonnegative-integersᵉ
open import elementary-number-theory.nonpositive-integersᵉ
open import elementary-number-theory.positive-and-negative-integersᵉ
open import elementary-number-theory.positive-integersᵉ
open import elementary-number-theory.strict-inequality-integersᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.cartesian-product-typesᵉ
open import foundation.coproduct-typesᵉ
open import foundation.decidable-propositionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.function-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.negationᵉ
open import foundation.propositionsᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Anᵉ [integerᵉ fraction](elementary-number-theory.integer-fractions.mdᵉ) `m/n`ᵉ isᵉ
{{#conceptᵉ "lessᵉ orᵉ equal"ᵉ Disambiguation="integerᵉ fraction"ᵉ Agda=leq-fraction-ℤᵉ}}
to aᵉ fractionᵉ `m'/n'`ᵉ ifᵉ theᵉ
[integerᵉ product](elementary-number-theory.multiplication-integers.mdᵉ) `mᵉ *ᵉ n'`ᵉ
isᵉ [lessᵉ orᵉ equal](elementary-number-theory.inequality-integers.mdᵉ) to `m'ᵉ *ᵉ n`.ᵉ

## Definition

### Inequality on integer fractions

```agda
leq-fraction-ℤ-Propᵉ : fraction-ℤᵉ → fraction-ℤᵉ → Propᵉ lzero
leq-fraction-ℤ-Propᵉ (mᵉ ,ᵉ nᵉ ,ᵉ pᵉ) (m'ᵉ ,ᵉ n'ᵉ ,ᵉ p'ᵉ) =
  leq-ℤ-Propᵉ (mᵉ *ℤᵉ n'ᵉ) (m'ᵉ *ℤᵉ nᵉ)

leq-fraction-ℤᵉ : fraction-ℤᵉ → fraction-ℤᵉ → UUᵉ lzero
leq-fraction-ℤᵉ xᵉ yᵉ = type-Propᵉ (leq-fraction-ℤ-Propᵉ xᵉ yᵉ)

is-prop-leq-fraction-ℤᵉ : (xᵉ yᵉ : fraction-ℤᵉ) → is-propᵉ (leq-fraction-ℤᵉ xᵉ yᵉ)
is-prop-leq-fraction-ℤᵉ xᵉ yᵉ = is-prop-type-Propᵉ (leq-fraction-ℤ-Propᵉ xᵉ yᵉ)
```

## Properties

### Inequality on integer fractions is decidable

```agda
is-decidable-leq-fraction-ℤᵉ :
  (xᵉ yᵉ : fraction-ℤᵉ) → (leq-fraction-ℤᵉ xᵉ yᵉ) +ᵉ ¬ᵉ (leq-fraction-ℤᵉ xᵉ yᵉ)
is-decidable-leq-fraction-ℤᵉ xᵉ yᵉ =
  is-decidable-leq-ℤᵉ
    ( numerator-fraction-ℤᵉ xᵉ *ℤᵉ denominator-fraction-ℤᵉ yᵉ)
    ( numerator-fraction-ℤᵉ yᵉ *ℤᵉ denominator-fraction-ℤᵉ xᵉ)

leq-fraction-ℤ-Decidable-Propᵉ : (xᵉ yᵉ : fraction-ℤᵉ) → Decidable-Propᵉ lzero
leq-fraction-ℤ-Decidable-Propᵉ xᵉ yᵉ =
  ( leq-fraction-ℤᵉ xᵉ yᵉ ,ᵉ
    is-prop-leq-fraction-ℤᵉ xᵉ yᵉ ,ᵉ
    is-decidable-leq-fraction-ℤᵉ xᵉ yᵉ)
```

### Inequality on integer fractions is antisymmetric with respect to the similarity relation

```agda
module _
  (xᵉ yᵉ : fraction-ℤᵉ)
  where

  is-sim-antisymmetric-leq-fraction-ℤᵉ :
    leq-fraction-ℤᵉ xᵉ yᵉ →
    leq-fraction-ℤᵉ yᵉ xᵉ →
    sim-fraction-ℤᵉ xᵉ yᵉ
  is-sim-antisymmetric-leq-fraction-ℤᵉ Hᵉ H'ᵉ =
    sim-is-zero-coss-mul-diff-fraction-ℤᵉ xᵉ yᵉ
      ( is-zero-is-nonnegative-is-nonpositive-ℤᵉ
        ( Hᵉ)
        ( is-nonpositive-eq-ℤᵉ
          ( skew-commutative-cross-mul-diff-fraction-ℤᵉ yᵉ xᵉ)
          ( is-nonpositive-neg-is-nonnegative-ℤᵉ
            ( H'ᵉ))))
```

### Inequality on integer fractions is transitive

```agda
transitive-leq-fraction-ℤᵉ :
  (pᵉ qᵉ rᵉ : fraction-ℤᵉ) →
  leq-fraction-ℤᵉ qᵉ rᵉ →
  leq-fraction-ℤᵉ pᵉ qᵉ →
  leq-fraction-ℤᵉ pᵉ rᵉ
transitive-leq-fraction-ℤᵉ pᵉ qᵉ rᵉ Hᵉ H'ᵉ =
  is-nonnegative-right-factor-mul-ℤᵉ
    ( is-nonnegative-eq-ℤᵉ
      ( lemma-add-cross-mul-diff-fraction-ℤᵉ pᵉ qᵉ rᵉ)
        ( is-nonnegative-add-ℤᵉ
          ( is-nonnegative-mul-ℤᵉ
            ( is-nonnegative-is-positive-ℤᵉ
              ( is-positive-denominator-fraction-ℤᵉ pᵉ))
            ( Hᵉ))
          ( is-nonnegative-mul-ℤᵉ
            ( is-nonnegative-is-positive-ℤᵉ
              ( is-positive-denominator-fraction-ℤᵉ rᵉ))
            ( H'ᵉ))))
    ( is-positive-denominator-fraction-ℤᵉ qᵉ)
```