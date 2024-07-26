# Strict inequality on the rational numbers

```agda
module elementary-number-theory.strict-inequality-rational-numbersᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integer-fractionsᵉ
open import elementary-number-theory.addition-rational-numbersᵉ
open import elementary-number-theory.cross-multiplication-difference-integer-fractionsᵉ
open import elementary-number-theory.difference-integersᵉ
open import elementary-number-theory.difference-rational-numbersᵉ
open import elementary-number-theory.inequality-integer-fractionsᵉ
open import elementary-number-theory.inequality-integersᵉ
open import elementary-number-theory.inequality-rational-numbersᵉ
open import elementary-number-theory.integer-fractionsᵉ
open import elementary-number-theory.integersᵉ
open import elementary-number-theory.mediant-integer-fractionsᵉ
open import elementary-number-theory.multiplication-integersᵉ
open import elementary-number-theory.nonnegative-integersᵉ
open import elementary-number-theory.nonpositive-integersᵉ
open import elementary-number-theory.positive-and-negative-integersᵉ
open import elementary-number-theory.positive-integersᵉ
open import elementary-number-theory.rational-numbersᵉ
open import elementary-number-theory.reduced-integer-fractionsᵉ
open import elementary-number-theory.strict-inequality-integer-fractionsᵉ
open import elementary-number-theory.strict-inequality-integersᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.binary-relationsᵉ
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
open import foundation.logical-equivalencesᵉ
open import foundation.negationᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.propositionsᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Theᵉ
{{#conceptᵉ "standardᵉ strictᵉ ordering"ᵉ Disambiguation="rationalᵉ numbers"ᵉ Agda=le-ℚᵉ}}
onᵉ theᵉ [rationalᵉ numbers](elementary-number-theory.rational-numbers.mdᵉ) isᵉ
inheritedᵉ fromᵉ theᵉ
[standardᵉ strictᵉ ordering](elementary-number-theory.strict-inequality-integer-fractions.mdᵉ)
onᵉ [integerᵉ fractions](elementary-number-theory.integer-fractions.mdᵉ): theᵉ
rationalᵉ numberᵉ `mᵉ /ᵉ n`ᵉ isᵉ _strictlyᵉ lessᵉ thanᵉ_ `m'ᵉ /ᵉ n'`ᵉ ifᵉ theᵉ
[integerᵉ product](elementary-number-theory.multiplication-integers.mdᵉ) `mᵉ *ᵉ n'`ᵉ
isᵉ [strictlyᵉ less](elementary-number-theory.strict-inequality-integers.mdᵉ) thanᵉ
`m'ᵉ *ᵉ n`.ᵉ

## Definition

### The standard strict inequality on the rational numbers

```agda
le-ℚ-Propᵉ : ℚᵉ → ℚᵉ → Propᵉ lzero
le-ℚ-Propᵉ (xᵉ ,ᵉ pxᵉ) (yᵉ ,ᵉ pyᵉ) = le-fraction-ℤ-Propᵉ xᵉ yᵉ

le-ℚᵉ : ℚᵉ → ℚᵉ → UUᵉ lzero
le-ℚᵉ xᵉ yᵉ = type-Propᵉ (le-ℚ-Propᵉ xᵉ yᵉ)

is-prop-le-ℚᵉ : (xᵉ yᵉ : ℚᵉ) → is-propᵉ (le-ℚᵉ xᵉ yᵉ)
is-prop-le-ℚᵉ xᵉ yᵉ = is-prop-type-Propᵉ (le-ℚ-Propᵉ xᵉ yᵉ)
```

## Properties

### Strict inequality on the rational numbers is decidable

```agda
is-decidable-le-ℚᵉ : (xᵉ yᵉ : ℚᵉ) → (le-ℚᵉ xᵉ yᵉ) +ᵉ ¬ᵉ (le-ℚᵉ xᵉ yᵉ)
is-decidable-le-ℚᵉ xᵉ yᵉ =
  is-decidable-le-fraction-ℤᵉ (fraction-ℚᵉ xᵉ) (fraction-ℚᵉ yᵉ)

le-ℚ-Decidable-Propᵉ : (xᵉ yᵉ : ℚᵉ) → Decidable-Propᵉ lzero
le-ℚ-Decidable-Propᵉ xᵉ yᵉ =
  ( le-ℚᵉ xᵉ yᵉ ,ᵉ
    is-prop-le-ℚᵉ xᵉ yᵉ ,ᵉ
    is-decidable-le-ℚᵉ xᵉ yᵉ)
```

### Strict inequality on the rational numbers implies inequality

```agda
leq-le-ℚᵉ : {xᵉ yᵉ : ℚᵉ} → le-ℚᵉ xᵉ yᵉ → leq-ℚᵉ xᵉ yᵉ
leq-le-ℚᵉ {xᵉ} {yᵉ} = leq-le-fraction-ℤᵉ {fraction-ℚᵉ xᵉ} {fraction-ℚᵉ yᵉ}
```

### Strict inequality on the rationals is asymmetric

```agda
asymmetric-le-ℚᵉ : (xᵉ yᵉ : ℚᵉ) → le-ℚᵉ xᵉ yᵉ → ¬ᵉ (le-ℚᵉ yᵉ xᵉ)
asymmetric-le-ℚᵉ xᵉ yᵉ =
  asymmetric-le-fraction-ℤᵉ
    ( fraction-ℚᵉ xᵉ)
    ( fraction-ℚᵉ yᵉ)

irreflexive-le-ℚᵉ : (xᵉ : ℚᵉ) → ¬ᵉ (le-ℚᵉ xᵉ xᵉ)
irreflexive-le-ℚᵉ =
  is-irreflexive-is-asymmetricᵉ le-ℚᵉ asymmetric-le-ℚᵉ
```

### Strict inequality on the rationals is transitive

```agda
module _
  (xᵉ yᵉ zᵉ : ℚᵉ)
  where

  transitive-le-ℚᵉ : le-ℚᵉ yᵉ zᵉ → le-ℚᵉ xᵉ yᵉ → le-ℚᵉ xᵉ zᵉ
  transitive-le-ℚᵉ =
    transitive-le-fraction-ℤᵉ
      ( fraction-ℚᵉ xᵉ)
      ( fraction-ℚᵉ yᵉ)
      ( fraction-ℚᵉ zᵉ)
```

### Concatenation rules for inequality and strict inequality on the rational numbers

```agda
module _
  (xᵉ yᵉ zᵉ : ℚᵉ)
  where

  concatenate-le-leq-ℚᵉ : le-ℚᵉ xᵉ yᵉ → leq-ℚᵉ yᵉ zᵉ → le-ℚᵉ xᵉ zᵉ
  concatenate-le-leq-ℚᵉ =
    concatenate-le-leq-fraction-ℤᵉ
      ( fraction-ℚᵉ xᵉ)
      ( fraction-ℚᵉ yᵉ)
      ( fraction-ℚᵉ zᵉ)

  concatenate-leq-le-ℚᵉ : leq-ℚᵉ xᵉ yᵉ → le-ℚᵉ yᵉ zᵉ → le-ℚᵉ xᵉ zᵉ
  concatenate-leq-le-ℚᵉ =
    concatenate-leq-le-fraction-ℤᵉ
      ( fraction-ℚᵉ xᵉ)
      ( fraction-ℚᵉ yᵉ)
      ( fraction-ℚᵉ zᵉ)
```

### The canonical map from integer fractions to the rational numbers preserves strict inequality

```agda
module _
  (pᵉ qᵉ : fraction-ℤᵉ)
  where

  preserves-le-rational-fraction-ℤᵉ :
    le-fraction-ℤᵉ pᵉ qᵉ → le-ℚᵉ (rational-fraction-ℤᵉ pᵉ) (rational-fraction-ℤᵉ qᵉ)
  preserves-le-rational-fraction-ℤᵉ =
    preserves-le-sim-fraction-ℤᵉ
      ( pᵉ)
      ( qᵉ)
      ( reduce-fraction-ℤᵉ pᵉ)
      ( reduce-fraction-ℤᵉ qᵉ)
      ( sim-reduced-fraction-ℤᵉ pᵉ)
      ( sim-reduced-fraction-ℤᵉ qᵉ)

module _
  (xᵉ : ℚᵉ) (pᵉ : fraction-ℤᵉ)
  where

  preserves-le-right-rational-fraction-ℤᵉ :
    le-fraction-ℤᵉ (fraction-ℚᵉ xᵉ) pᵉ → le-ℚᵉ xᵉ (rational-fraction-ℤᵉ pᵉ)
  preserves-le-right-rational-fraction-ℤᵉ Hᵉ =
    concatenate-le-sim-fraction-ℤᵉ
      ( fraction-ℚᵉ xᵉ)
      ( pᵉ)
      ( fraction-ℚᵉ ( rational-fraction-ℤᵉ pᵉ))
      ( Hᵉ)
      ( sim-reduced-fraction-ℤᵉ pᵉ)

  reflects-le-right-rational-fraction-ℤᵉ :
    le-ℚᵉ xᵉ (rational-fraction-ℤᵉ pᵉ) → le-fraction-ℤᵉ (fraction-ℚᵉ xᵉ) pᵉ
  reflects-le-right-rational-fraction-ℤᵉ Hᵉ =
    concatenate-le-sim-fraction-ℤᵉ
      ( fraction-ℚᵉ xᵉ)
      ( reduce-fraction-ℤᵉ pᵉ)
      ( pᵉ)
      ( Hᵉ)
      ( symmetric-sim-fraction-ℤᵉ
        ( pᵉ)
        ( reduce-fraction-ℤᵉ pᵉ)
        ( sim-reduced-fraction-ℤᵉ pᵉ))

  iff-le-right-rational-fraction-ℤᵉ :
    le-fraction-ℤᵉ (fraction-ℚᵉ xᵉ) pᵉ ↔ᵉ le-ℚᵉ xᵉ (rational-fraction-ℤᵉ pᵉ)
  pr1ᵉ iff-le-right-rational-fraction-ℤᵉ = preserves-le-right-rational-fraction-ℤᵉ
  pr2ᵉ iff-le-right-rational-fraction-ℤᵉ = reflects-le-right-rational-fraction-ℤᵉ

  preserves-le-left-rational-fraction-ℤᵉ :
    le-fraction-ℤᵉ pᵉ (fraction-ℚᵉ xᵉ) → le-ℚᵉ (rational-fraction-ℤᵉ pᵉ) xᵉ
  preserves-le-left-rational-fraction-ℤᵉ =
    concatenate-sim-le-fraction-ℤᵉ
      ( fraction-ℚᵉ ( rational-fraction-ℤᵉ pᵉ))
      ( pᵉ)
      ( fraction-ℚᵉ xᵉ)
      ( symmetric-sim-fraction-ℤᵉ
        ( pᵉ)
        ( fraction-ℚᵉ ( rational-fraction-ℤᵉ pᵉ))
        ( sim-reduced-fraction-ℤᵉ pᵉ))

  reflects-le-left-rational-fraction-ℤᵉ :
    le-ℚᵉ (rational-fraction-ℤᵉ pᵉ) xᵉ → le-fraction-ℤᵉ pᵉ (fraction-ℚᵉ xᵉ)
  reflects-le-left-rational-fraction-ℤᵉ =
    concatenate-sim-le-fraction-ℤᵉ
      ( pᵉ)
      ( reduce-fraction-ℤᵉ pᵉ)
      ( fraction-ℚᵉ xᵉ)
      ( sim-reduced-fraction-ℤᵉ pᵉ)

  iff-le-left-rational-fraction-ℤᵉ :
    le-fraction-ℤᵉ pᵉ (fraction-ℚᵉ xᵉ) ↔ᵉ le-ℚᵉ (rational-fraction-ℤᵉ pᵉ) xᵉ
  pr1ᵉ iff-le-left-rational-fraction-ℤᵉ = preserves-le-left-rational-fraction-ℤᵉ
  pr2ᵉ iff-le-left-rational-fraction-ℤᵉ = reflects-le-left-rational-fraction-ℤᵉ
```

### `x < y` if and only if `0 < y - x`

```agda
module _
  (xᵉ yᵉ : ℚᵉ)
  where

  iff-translate-diff-le-zero-ℚᵉ : le-ℚᵉ zero-ℚᵉ (yᵉ -ℚᵉ xᵉ) ↔ᵉ le-ℚᵉ xᵉ yᵉ
  iff-translate-diff-le-zero-ℚᵉ =
    logical-equivalence-reasoningᵉ
      le-ℚᵉ zero-ℚᵉ (yᵉ -ℚᵉ xᵉ)
      ↔ᵉ le-fraction-ℤᵉ
        ( zero-fraction-ℤᵉ)
        ( add-fraction-ℤᵉ (fraction-ℚᵉ yᵉ) (neg-fraction-ℤᵉ (fraction-ℚᵉ xᵉ)))
        byᵉ
          inv-iffᵉ
            ( iff-le-right-rational-fraction-ℤᵉ
              ( zero-ℚᵉ)
              ( add-fraction-ℤᵉ (fraction-ℚᵉ yᵉ) (neg-fraction-ℤᵉ (fraction-ℚᵉ xᵉ))))
      ↔ᵉ le-ℚᵉ xᵉ yᵉ
        byᵉ
          inv-trᵉ
            ( _↔ᵉ le-ℚᵉ xᵉ yᵉ)
            ( eq-translate-diff-le-zero-fraction-ℤᵉ
              ( fraction-ℚᵉ xᵉ)
              ( fraction-ℚᵉ yᵉ))
            ( id-iffᵉ)
```

### Strict inequality on the rational numbers is invariant by translation

```agda
module _
  (zᵉ xᵉ yᵉ : ℚᵉ)
  where

  iff-translate-left-le-ℚᵉ : le-ℚᵉ (zᵉ +ℚᵉ xᵉ) (zᵉ +ℚᵉ yᵉ) ↔ᵉ le-ℚᵉ xᵉ yᵉ
  iff-translate-left-le-ℚᵉ =
    logical-equivalence-reasoningᵉ
      le-ℚᵉ (zᵉ +ℚᵉ xᵉ) (zᵉ +ℚᵉ yᵉ)
      ↔ᵉ le-ℚᵉ zero-ℚᵉ ((zᵉ +ℚᵉ yᵉ) -ℚᵉ (zᵉ +ℚᵉ xᵉ))
        byᵉ (inv-iffᵉ (iff-translate-diff-le-zero-ℚᵉ (zᵉ +ℚᵉ xᵉ) (zᵉ +ℚᵉ yᵉ)))
      ↔ᵉ le-ℚᵉ zero-ℚᵉ (yᵉ -ℚᵉ xᵉ)
        byᵉ
          ( inv-trᵉ
            ( _↔ᵉ le-ℚᵉ zero-ℚᵉ (yᵉ -ℚᵉ xᵉ))
            ( apᵉ (le-ℚᵉ zero-ℚᵉ) (left-translation-diff-ℚᵉ yᵉ xᵉ zᵉ))
            ( id-iffᵉ))
      ↔ᵉ le-ℚᵉ xᵉ yᵉ
        byᵉ (iff-translate-diff-le-zero-ℚᵉ xᵉ yᵉ)

  iff-translate-right-le-ℚᵉ : le-ℚᵉ (xᵉ +ℚᵉ zᵉ) (yᵉ +ℚᵉ zᵉ) ↔ᵉ le-ℚᵉ xᵉ yᵉ
  iff-translate-right-le-ℚᵉ =
    logical-equivalence-reasoningᵉ
      le-ℚᵉ (xᵉ +ℚᵉ zᵉ) (yᵉ +ℚᵉ zᵉ)
      ↔ᵉ le-ℚᵉ zero-ℚᵉ ((yᵉ +ℚᵉ zᵉ) -ℚᵉ (xᵉ +ℚᵉ zᵉ))
        byᵉ (inv-iffᵉ (iff-translate-diff-le-zero-ℚᵉ (xᵉ +ℚᵉ zᵉ) (yᵉ +ℚᵉ zᵉ)))
      ↔ᵉ le-ℚᵉ zero-ℚᵉ (yᵉ -ℚᵉ xᵉ)
        byᵉ
          ( inv-trᵉ
            ( _↔ᵉ le-ℚᵉ zero-ℚᵉ (yᵉ -ℚᵉ xᵉ))
            ( apᵉ (le-ℚᵉ zero-ℚᵉ) (right-translation-diff-ℚᵉ yᵉ xᵉ zᵉ))
            ( id-iffᵉ))
      ↔ᵉ le-ℚᵉ xᵉ yᵉ byᵉ (iff-translate-diff-le-zero-ℚᵉ xᵉ yᵉ)

  preserves-le-left-add-ℚᵉ : le-ℚᵉ xᵉ yᵉ → le-ℚᵉ (xᵉ +ℚᵉ zᵉ) (yᵉ +ℚᵉ zᵉ)
  preserves-le-left-add-ℚᵉ = backward-implicationᵉ iff-translate-right-le-ℚᵉ

  preserves-le-right-add-ℚᵉ : le-ℚᵉ xᵉ yᵉ → le-ℚᵉ (zᵉ +ℚᵉ xᵉ) (zᵉ +ℚᵉ yᵉ)
  preserves-le-right-add-ℚᵉ = backward-implicationᵉ iff-translate-left-le-ℚᵉ

  reflects-le-left-add-ℚᵉ : le-ℚᵉ (xᵉ +ℚᵉ zᵉ) (yᵉ +ℚᵉ zᵉ) → le-ℚᵉ xᵉ yᵉ
  reflects-le-left-add-ℚᵉ = forward-implicationᵉ iff-translate-right-le-ℚᵉ

  reflects-le-right-add-ℚᵉ : le-ℚᵉ (zᵉ +ℚᵉ xᵉ) (zᵉ +ℚᵉ yᵉ) → le-ℚᵉ xᵉ yᵉ
  reflects-le-right-add-ℚᵉ = forward-implicationᵉ iff-translate-left-le-ℚᵉ
```

### Addition on the rational numbers preserves strict inequality

```agda
preserves-le-add-ℚᵉ :
  {aᵉ bᵉ cᵉ dᵉ : ℚᵉ} → le-ℚᵉ aᵉ bᵉ → le-ℚᵉ cᵉ dᵉ → le-ℚᵉ (aᵉ +ℚᵉ cᵉ) (bᵉ +ℚᵉ dᵉ)
preserves-le-add-ℚᵉ {aᵉ} {bᵉ} {cᵉ} {dᵉ} Hᵉ Kᵉ =
  transitive-le-ℚᵉ
    ( aᵉ +ℚᵉ cᵉ)
    ( bᵉ +ℚᵉ cᵉ)
    ( bᵉ +ℚᵉ dᵉ)
    ( preserves-le-right-add-ℚᵉ bᵉ cᵉ dᵉ Kᵉ)
    ( preserves-le-left-add-ℚᵉ cᵉ aᵉ bᵉ Hᵉ)
```

### The rational numbers have no lower or upper bound

```agda
module _
  (xᵉ : ℚᵉ)
  where

  exists-lesser-ℚᵉ : existsᵉ ℚᵉ (λ qᵉ → le-ℚ-Propᵉ qᵉ xᵉ)
  exists-lesser-ℚᵉ =
    intro-existsᵉ
      ( rational-fraction-ℤᵉ fracᵉ)
      ( preserves-le-left-rational-fraction-ℤᵉ xᵉ fracᵉ
        ( le-fraction-le-numerator-fraction-ℤᵉ
          ( fracᵉ)
          ( fraction-ℚᵉ xᵉ)
          ( reflᵉ)
          ( le-pred-ℤᵉ (numerator-ℚᵉ xᵉ))))
    where
    fracᵉ : fraction-ℤᵉ
    fracᵉ = (pred-ℤᵉ (numerator-ℚᵉ xᵉ) ,ᵉ positive-denominator-ℚᵉ xᵉ)

  exists-greater-ℚᵉ : existsᵉ ℚᵉ (λ rᵉ → le-ℚ-Propᵉ xᵉ rᵉ)
  exists-greater-ℚᵉ =
    intro-existsᵉ
      ( rational-fraction-ℤᵉ fracᵉ)
      ( preserves-le-right-rational-fraction-ℤᵉ xᵉ fracᵉ
        ( le-fraction-le-numerator-fraction-ℤᵉ
          ( fraction-ℚᵉ xᵉ)
          ( fracᵉ)
          ( reflᵉ)
          ( le-succ-ℤᵉ (numerator-ℚᵉ xᵉ))))
    where
    fracᵉ : fraction-ℤᵉ
    fracᵉ = (succ-ℤᵉ (numerator-ℚᵉ xᵉ) ,ᵉ positive-denominator-ℚᵉ xᵉ)
```

### For any two rational numbers `x` and `y`, either `x < y` or `y ≤ x`

```agda
decide-le-leq-ℚᵉ : (xᵉ yᵉ : ℚᵉ) → le-ℚᵉ xᵉ yᵉ +ᵉ leq-ℚᵉ yᵉ xᵉ
decide-le-leq-ℚᵉ xᵉ yᵉ =
  map-coproductᵉ
    ( idᵉ)
    ( λ Hᵉ →
      is-nonnegative-eq-ℤᵉ
        ( skew-commutative-cross-mul-diff-fraction-ℤᵉ
          ( fraction-ℚᵉ xᵉ)
          ( fraction-ℚᵉ yᵉ))
        ( is-nonnegative-neg-is-nonpositive-ℤᵉ Hᵉ))
    ( decide-is-positive-is-nonpositive-ℤᵉ)
```

### Trichotomy on the rationals

```agda
trichotomy-le-ℚᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} (xᵉ yᵉ : ℚᵉ) →
  ( le-ℚᵉ xᵉ yᵉ → Aᵉ) →
  ( Idᵉ xᵉ yᵉ → Aᵉ) →
  ( le-ℚᵉ yᵉ xᵉ → Aᵉ) →
  Aᵉ
trichotomy-le-ℚᵉ xᵉ yᵉ leftᵉ eqᵉ rightᵉ with decide-le-leq-ℚᵉ xᵉ yᵉ | decide-le-leq-ℚᵉ yᵉ xᵉ
... | inlᵉ Iᵉ | _ = leftᵉ Iᵉ
... | inrᵉ Iᵉ | inlᵉ I'ᵉ = rightᵉ I'ᵉ
... | inrᵉ Iᵉ | inrᵉ I'ᵉ = eqᵉ (antisymmetric-leq-ℚᵉ xᵉ yᵉ I'ᵉ Iᵉ)
```

### The mediant of two distinct rationals is strictly between them

```agda
module _
  (xᵉ yᵉ : ℚᵉ) (Hᵉ : le-ℚᵉ xᵉ yᵉ)
  where

  le-left-mediant-ℚᵉ : le-ℚᵉ xᵉ (mediant-ℚᵉ xᵉ yᵉ)
  le-left-mediant-ℚᵉ =
    preserves-le-right-rational-fraction-ℤᵉ xᵉ
      ( mediant-fraction-ℤᵉ (fraction-ℚᵉ xᵉ) (fraction-ℚᵉ yᵉ))
      ( le-left-mediant-fraction-ℤᵉ (fraction-ℚᵉ xᵉ) (fraction-ℚᵉ yᵉ) Hᵉ)

  le-right-mediant-ℚᵉ : le-ℚᵉ (mediant-ℚᵉ xᵉ yᵉ) yᵉ
  le-right-mediant-ℚᵉ =
    preserves-le-left-rational-fraction-ℤᵉ yᵉ
      ( mediant-fraction-ℤᵉ (fraction-ℚᵉ xᵉ) (fraction-ℚᵉ yᵉ))
      ( le-right-mediant-fraction-ℤᵉ (fraction-ℚᵉ xᵉ) (fraction-ℚᵉ yᵉ) Hᵉ)
```

### Strict inequality on the rational numbers is dense

```agda
module _
  (xᵉ yᵉ : ℚᵉ) (Hᵉ : le-ℚᵉ xᵉ yᵉ)
  where

  dense-le-ℚᵉ : existsᵉ ℚᵉ (λ rᵉ → le-ℚ-Propᵉ xᵉ rᵉ ∧ᵉ le-ℚ-Propᵉ rᵉ yᵉ)
  dense-le-ℚᵉ =
    intro-existsᵉ
      ( mediant-ℚᵉ xᵉ yᵉ)
      ( le-left-mediant-ℚᵉ xᵉ yᵉ Hᵉ ,ᵉ le-right-mediant-ℚᵉ xᵉ yᵉ Hᵉ)
```

### Strict inequality on the rational numbers is located

```agda
located-le-ℚᵉ :
  (xᵉ yᵉ zᵉ : ℚᵉ) → le-ℚᵉ yᵉ zᵉ → type-disjunction-Propᵉ (le-ℚ-Propᵉ yᵉ xᵉ) (le-ℚ-Propᵉ xᵉ zᵉ)
located-le-ℚᵉ xᵉ yᵉ zᵉ Hᵉ =
  unit-trunc-Propᵉ
    ( map-coproductᵉ
      ( idᵉ)
      ( λ pᵉ → concatenate-leq-le-ℚᵉ xᵉ yᵉ zᵉ pᵉ Hᵉ)
      ( decide-le-leq-ℚᵉ yᵉ xᵉ))
```