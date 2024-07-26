# Inequality on the rational numbers

```agda
module elementary-number-theory.inequality-rational-numbersᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.cross-multiplication-difference-integer-fractionsᵉ
open import elementary-number-theory.difference-integersᵉ
open import elementary-number-theory.inequality-integer-fractionsᵉ
open import elementary-number-theory.inequality-integersᵉ
open import elementary-number-theory.integer-fractionsᵉ
open import elementary-number-theory.integersᵉ
open import elementary-number-theory.multiplication-integersᵉ
open import elementary-number-theory.nonnegative-integersᵉ
open import elementary-number-theory.nonpositive-integersᵉ
open import elementary-number-theory.positive-and-negative-integersᵉ
open import elementary-number-theory.positive-integersᵉ
open import elementary-number-theory.rational-numbersᵉ

open import foundation.cartesian-product-typesᵉ
open import foundation.conjunctionᵉ
open import foundation.coproduct-typesᵉ
open import foundation.decidable-propositionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-coproduct-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.negationᵉ
open import foundation.propositionsᵉ
open import foundation.universe-levelsᵉ

open import order-theory.posetsᵉ
open import order-theory.preordersᵉ
```

</details>

## Idea

Theᵉ
{{#conceptᵉ "standardᵉ ordering"ᵉ Disambiguation="rationalᵉ numbers"ᵉ Agda=leq-ℚᵉ}} onᵉ
theᵉ [rationalᵉ numbers](elementary-number-theory.rational-numbers.mdᵉ) isᵉ
inheritedᵉ fromᵉ theᵉ
[standardᵉ ordering](elementary-number-theory.inequality-integer-fractions.mdᵉ) onᵉ
[integerᵉ fractions](elementary-number-theory.integer-fractions.mdᵉ): theᵉ rationalᵉ
numberᵉ `mᵉ /ᵉ n`ᵉ isᵉ _lessᵉ thanᵉ orᵉ equalᵉ toᵉ_ `m'ᵉ /ᵉ n'`ᵉ ifᵉ theᵉ
[integerᵉ product](elementary-number-theory.multiplication-integers.mdᵉ) `mᵉ *ᵉ n'`ᵉ
isᵉ [lessᵉ thanᵉ orᵉ equal](elementary-number-theory.inequality-integers.mdᵉ) to
`m'ᵉ *ᵉ n`.ᵉ

## Definition

### Inequality on the rational numbers

```agda
leq-ℚ-Propᵉ : ℚᵉ → ℚᵉ → Propᵉ lzero
leq-ℚ-Propᵉ (xᵉ ,ᵉ pxᵉ) (yᵉ ,ᵉ pyᵉ) = leq-fraction-ℤ-Propᵉ xᵉ yᵉ

leq-ℚᵉ : ℚᵉ → ℚᵉ → UUᵉ lzero
leq-ℚᵉ xᵉ yᵉ = type-Propᵉ (leq-ℚ-Propᵉ xᵉ yᵉ)

is-prop-leq-ℚᵉ : (xᵉ yᵉ : ℚᵉ) → is-propᵉ (leq-ℚᵉ xᵉ yᵉ)
is-prop-leq-ℚᵉ xᵉ yᵉ = is-prop-type-Propᵉ (leq-ℚ-Propᵉ xᵉ yᵉ)

infix 30 _≤-ℚᵉ_
_≤-ℚᵉ_ = leq-ℚᵉ
```

## Properties

### Inequality on the rational numbers is decidable

```agda
is-decidable-leq-ℚᵉ : (xᵉ yᵉ : ℚᵉ) → (leq-ℚᵉ xᵉ yᵉ) +ᵉ ¬ᵉ (leq-ℚᵉ xᵉ yᵉ)
is-decidable-leq-ℚᵉ xᵉ yᵉ =
  is-decidable-leq-fraction-ℤᵉ (fraction-ℚᵉ xᵉ) (fraction-ℚᵉ yᵉ)

leq-ℚ-Decidable-Propᵉ : (xᵉ yᵉ : ℚᵉ) → Decidable-Propᵉ lzero
leq-ℚ-Decidable-Propᵉ xᵉ yᵉ =
  ( leq-ℚᵉ xᵉ yᵉ ,ᵉ
    is-prop-leq-ℚᵉ xᵉ yᵉ ,ᵉ
    is-decidable-leq-ℚᵉ xᵉ yᵉ)
```

### Inequality on the rational numbers is reflexive

```agda
refl-leq-ℚᵉ : (xᵉ : ℚᵉ) → leq-ℚᵉ xᵉ xᵉ
refl-leq-ℚᵉ xᵉ =
  refl-leq-ℤᵉ (numerator-ℚᵉ xᵉ *ℤᵉ denominator-ℚᵉ xᵉ)
```

### Inequality on the rational numbers is antisymmetric

```agda
antisymmetric-leq-ℚᵉ : (xᵉ yᵉ : ℚᵉ) → leq-ℚᵉ xᵉ yᵉ → leq-ℚᵉ yᵉ xᵉ → xᵉ ＝ᵉ yᵉ
antisymmetric-leq-ℚᵉ xᵉ yᵉ Hᵉ H'ᵉ =
  ( invᵉ (is-retraction-rational-fraction-ℚᵉ xᵉ)) ∙ᵉ
  ( eq-ℚ-sim-fraction-ℤᵉ
    ( fraction-ℚᵉ xᵉ)
    ( fraction-ℚᵉ yᵉ)
    ( is-sim-antisymmetric-leq-fraction-ℤᵉ
      ( fraction-ℚᵉ xᵉ)
      ( fraction-ℚᵉ yᵉ)
      ( Hᵉ)
      ( H'ᵉ))) ∙ᵉ
  ( is-retraction-rational-fraction-ℚᵉ yᵉ)
```

### Inequality on the rational numbers is linear

```agda
linear-leq-ℚᵉ : (xᵉ yᵉ : ℚᵉ) → (leq-ℚᵉ xᵉ yᵉ) +ᵉ (leq-ℚᵉ yᵉ xᵉ)
linear-leq-ℚᵉ xᵉ yᵉ =
  map-coproductᵉ
    ( idᵉ)
    ( is-nonnegative-eq-ℤᵉ
      (distributive-neg-diff-ℤᵉ
        ( numerator-ℚᵉ yᵉ *ℤᵉ denominator-ℚᵉ xᵉ)
        ( numerator-ℚᵉ xᵉ *ℤᵉ denominator-ℚᵉ yᵉ)))
    ( decide-is-nonnegative-is-nonnegative-neg-ℤᵉ
      { cross-mul-diff-fraction-ℤᵉ (fraction-ℚᵉ xᵉ) (fraction-ℚᵉ yᵉ)})
```

### Inequality on the rational numbers is transitive

```agda
module _
  (xᵉ yᵉ zᵉ : ℚᵉ)
  where

  transitive-leq-ℚᵉ : leq-ℚᵉ yᵉ zᵉ → leq-ℚᵉ xᵉ yᵉ → leq-ℚᵉ xᵉ zᵉ
  transitive-leq-ℚᵉ =
    transitive-leq-fraction-ℤᵉ
      ( fraction-ℚᵉ xᵉ)
      ( fraction-ℚᵉ yᵉ)
      ( fraction-ℚᵉ zᵉ)
```

### The partially ordered set of rational numbers ordered by inequality

```agda
ℚ-Preorderᵉ : Preorderᵉ lzero lzero
ℚ-Preorderᵉ =
  (ℚᵉ ,ᵉ leq-ℚ-Propᵉ ,ᵉ refl-leq-ℚᵉ ,ᵉ transitive-leq-ℚᵉ)

ℚ-Posetᵉ : Posetᵉ lzero lzero
ℚ-Posetᵉ = (ℚ-Preorderᵉ ,ᵉ antisymmetric-leq-ℚᵉ)
```

## See also

-ᵉ Theᵉ decidableᵉ totalᵉ orderᵉ onᵉ theᵉ rationalᵉ numbersᵉ isᵉ definedᵉ in
  [`decidable-total-order-rational-numbers`](elementary-number-theory.decidable-total-order-rational-numbers.mdᵉ)
-ᵉ Theᵉ strictᵉ orderingᵉ onᵉ theᵉ rationalᵉ numbersᵉ isᵉ definedᵉ in
  [`strict-inequality-rational-numbers`](elementary-number-theory.strict-inequality-rational-numbers.mdᵉ)