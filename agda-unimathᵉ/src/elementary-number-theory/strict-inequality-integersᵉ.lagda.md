# Strict inequality on the integers

```agda
module elementary-number-theory.strict-inequality-integersᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integersᵉ
open import elementary-number-theory.addition-positive-and-negative-integersᵉ
open import elementary-number-theory.difference-integersᵉ
open import elementary-number-theory.inequality-integersᵉ
open import elementary-number-theory.inequality-natural-numbersᵉ
open import elementary-number-theory.integersᵉ
open import elementary-number-theory.natural-numbersᵉ
open import elementary-number-theory.negative-integersᵉ
open import elementary-number-theory.nonnegative-integersᵉ
open import elementary-number-theory.nonpositive-integersᵉ
open import elementary-number-theory.positive-and-negative-integersᵉ
open import elementary-number-theory.positive-integersᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.coproduct-typesᵉ
open import foundation.decidable-propositionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-coproduct-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.negated-equalityᵉ
open import foundation.negationᵉ
open import foundation.propositionsᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import order-theory.posetsᵉ
open import order-theory.preordersᵉ
```

</details>

## Idea

Anᵉ [integer](elementary-number-theory.integers.mdᵉ) `x`ᵉ isᵉ _strictlyᵉ lessᵉ thanᵉ_
theᵉ integerᵉ `y`ᵉ ifᵉ theᵉ
[difference](elementary-number-theory.difference-integers.mdᵉ) `yᵉ -ᵉ x`ᵉ isᵉ
[positive](elementary-number-theory.positive-integers.md).ᵉ Thisᵉ relationᵉ definesᵉ
theᵉ {{#conceptᵉ "standardᵉ strictᵉ ordering"ᵉ Disambiguation="integers"ᵉ Agda=leq-ℤᵉ}}
onᵉ theᵉ integers.ᵉ

## Definition

### Strict inequality on the integers

```agda
le-ℤ-Propᵉ : ℤᵉ → ℤᵉ → Propᵉ lzero
le-ℤ-Propᵉ xᵉ yᵉ = subtype-positive-ℤᵉ (yᵉ -ℤᵉ xᵉ)

le-ℤᵉ : ℤᵉ → ℤᵉ → UUᵉ lzero
le-ℤᵉ xᵉ yᵉ = type-Propᵉ (le-ℤ-Propᵉ xᵉ yᵉ)

is-prop-le-ℤᵉ : (xᵉ yᵉ : ℤᵉ) → is-propᵉ (le-ℤᵉ xᵉ yᵉ)
is-prop-le-ℤᵉ xᵉ yᵉ = is-prop-type-Propᵉ (le-ℤ-Propᵉ xᵉ yᵉ)
```

## Properties

### Strict inequality on the integers implies inequality

```agda
leq-le-ℤᵉ : {xᵉ yᵉ : ℤᵉ} → le-ℤᵉ xᵉ yᵉ → leq-ℤᵉ xᵉ yᵉ
leq-le-ℤᵉ {xᵉ} {yᵉ} = is-nonnegative-is-positive-ℤᵉ
```

### Strict inequality on the integers is decidable

```agda
is-decidable-le-ℤᵉ : (xᵉ yᵉ : ℤᵉ) → (le-ℤᵉ xᵉ yᵉ) +ᵉ ¬ᵉ (le-ℤᵉ xᵉ yᵉ)
is-decidable-le-ℤᵉ xᵉ yᵉ = is-decidable-is-positive-ℤᵉ (yᵉ -ℤᵉ xᵉ)

le-ℤ-Decidable-Propᵉ : (xᵉ yᵉ : ℤᵉ) → Decidable-Propᵉ lzero
le-ℤ-Decidable-Propᵉ xᵉ yᵉ =
  ( le-ℤᵉ xᵉ yᵉ ,ᵉ
    is-prop-le-ℤᵉ xᵉ yᵉ ,ᵉ
    is-decidable-le-ℤᵉ xᵉ yᵉ)
```

### Strict inequality on the integers is transitive

```agda
transitive-le-ℤᵉ : (kᵉ lᵉ mᵉ : ℤᵉ) → le-ℤᵉ lᵉ mᵉ → le-ℤᵉ kᵉ lᵉ → le-ℤᵉ kᵉ mᵉ
transitive-le-ℤᵉ kᵉ lᵉ mᵉ Hᵉ Kᵉ =
  is-positive-eq-ℤᵉ
    ( triangle-diff-ℤᵉ mᵉ lᵉ kᵉ)
    ( is-positive-add-ℤᵉ Hᵉ Kᵉ)
```

### Strict inequality on the integers is asymmetric

```agda
asymmetric-le-ℤᵉ : (xᵉ yᵉ : ℤᵉ) → le-ℤᵉ xᵉ yᵉ → ¬ᵉ (le-ℤᵉ yᵉ xᵉ)
asymmetric-le-ℤᵉ xᵉ yᵉ pᵉ =
  is-not-positive-is-nonpositive-ℤᵉ
    ( is-nonpositive-eq-ℤᵉ
      ( distributive-neg-diff-ℤᵉ yᵉ xᵉ)
      ( is-nonpositive-neg-is-nonnegative-ℤᵉ
        ( is-nonnegative-is-positive-ℤᵉ pᵉ)))
```

### Strict inequality on the integers is connected

```agda
connected-le-ℤᵉ : (xᵉ yᵉ : ℤᵉ) → xᵉ ≠ᵉ yᵉ → le-ℤᵉ xᵉ yᵉ +ᵉ le-ℤᵉ yᵉ xᵉ
connected-le-ℤᵉ xᵉ yᵉ Hᵉ =
  map-coproductᵉ
    ( λ Kᵉ →
      is-positive-eq-ℤᵉ
        ( distributive-neg-diff-ℤᵉ xᵉ yᵉ)
        ( is-positive-neg-is-negative-ℤᵉ Kᵉ))
    ( idᵉ)
    ( decide-sign-nonzero-ℤᵉ (Hᵉ ∘ᵉ eq-diff-ℤᵉ))
```

### Any integer is strictly greater than its predecessor

```agda
le-pred-ℤᵉ : (xᵉ : ℤᵉ) → le-ℤᵉ (pred-ℤᵉ xᵉ) xᵉ
le-pred-ℤᵉ xᵉ =
  is-positive-eq-ℤᵉ
    ( invᵉ (right-predecessor-law-diff-ℤᵉ xᵉ xᵉ ∙ᵉ apᵉ succ-ℤᵉ (is-zero-diff-ℤ'ᵉ xᵉ)))
    ( is-positive-int-positive-ℤᵉ one-positive-ℤᵉ)
```

### Any integer is strictly lesser than its successor

```agda
le-succ-ℤᵉ : (xᵉ : ℤᵉ) → le-ℤᵉ xᵉ (succ-ℤᵉ xᵉ)
le-succ-ℤᵉ xᵉ =
  is-positive-eq-ℤᵉ
    ( invᵉ (left-successor-law-diff-ℤᵉ xᵉ xᵉ ∙ᵉ apᵉ succ-ℤᵉ (is-zero-diff-ℤ'ᵉ xᵉ)))
    ( is-positive-int-positive-ℤᵉ one-positive-ℤᵉ)
```

### Strict inequality on the integers is invariant by translation

```agda
module _
  (zᵉ xᵉ yᵉ : ℤᵉ)
  where

  eq-translate-left-le-ℤᵉ : le-ℤᵉ (zᵉ +ℤᵉ xᵉ) (zᵉ +ℤᵉ yᵉ) ＝ᵉ le-ℤᵉ xᵉ yᵉ
  eq-translate-left-le-ℤᵉ = apᵉ is-positive-ℤᵉ (left-translation-diff-ℤᵉ yᵉ xᵉ zᵉ)

  eq-translate-right-le-ℤᵉ : le-ℤᵉ (xᵉ +ℤᵉ zᵉ) (yᵉ +ℤᵉ zᵉ) ＝ᵉ le-ℤᵉ xᵉ yᵉ
  eq-translate-right-le-ℤᵉ = apᵉ is-positive-ℤᵉ (right-translation-diff-ℤᵉ yᵉ xᵉ zᵉ)
```

### Addition on the integers preserves strict inequality

```agda
preserves-le-left-add-ℤᵉ :
  (zᵉ xᵉ yᵉ : ℤᵉ) → le-ℤᵉ xᵉ yᵉ → le-ℤᵉ (xᵉ +ℤᵉ zᵉ) (yᵉ +ℤᵉ zᵉ)
preserves-le-left-add-ℤᵉ zᵉ xᵉ yᵉ =
  is-positive-eq-ℤᵉ (invᵉ (right-translation-diff-ℤᵉ yᵉ xᵉ zᵉ))

preserves-le-right-add-ℤᵉ :
  (zᵉ xᵉ yᵉ : ℤᵉ) → le-ℤᵉ xᵉ yᵉ → le-ℤᵉ (zᵉ +ℤᵉ xᵉ) (zᵉ +ℤᵉ yᵉ)
preserves-le-right-add-ℤᵉ zᵉ xᵉ yᵉ =
  is-positive-eq-ℤᵉ (invᵉ (left-translation-diff-ℤᵉ yᵉ xᵉ zᵉ))

preserves-le-add-ℤᵉ :
  {aᵉ bᵉ cᵉ dᵉ : ℤᵉ} → le-ℤᵉ aᵉ bᵉ → le-ℤᵉ cᵉ dᵉ → le-ℤᵉ (aᵉ +ℤᵉ cᵉ) (bᵉ +ℤᵉ dᵉ)
preserves-le-add-ℤᵉ {aᵉ} {bᵉ} {cᵉ} {dᵉ} Hᵉ Kᵉ =
  transitive-le-ℤᵉ
    ( aᵉ +ℤᵉ cᵉ)
    ( bᵉ +ℤᵉ cᵉ)
    ( bᵉ +ℤᵉ dᵉ)
    ( preserves-le-right-add-ℤᵉ bᵉ cᵉ dᵉ Kᵉ)
    ( preserves-le-left-add-ℤᵉ cᵉ aᵉ bᵉ Hᵉ)
```

### Addition on the integers reflects strict inequality

```agda
reflects-le-left-add-ℤᵉ :
  (zᵉ xᵉ yᵉ : ℤᵉ) → le-ℤᵉ (xᵉ +ℤᵉ zᵉ) (yᵉ +ℤᵉ zᵉ) → le-ℤᵉ xᵉ yᵉ
reflects-le-left-add-ℤᵉ zᵉ xᵉ yᵉ =
  is-positive-eq-ℤᵉ (right-translation-diff-ℤᵉ yᵉ xᵉ zᵉ)

reflects-le-right-add-ℤᵉ :
  (zᵉ xᵉ yᵉ : ℤᵉ) → le-ℤᵉ (zᵉ +ℤᵉ xᵉ) (zᵉ +ℤᵉ yᵉ) → le-ℤᵉ xᵉ yᵉ
reflects-le-right-add-ℤᵉ zᵉ xᵉ yᵉ =
  is-positive-eq-ℤᵉ (left-translation-diff-ℤᵉ yᵉ xᵉ zᵉ)
```

### An integer `x` is positive if and only if `0 < x`

```agda
module _
  (xᵉ : ℤᵉ)
  where

  abstract
    le-zero-is-positive-ℤᵉ : is-positive-ℤᵉ xᵉ → le-ℤᵉ zero-ℤᵉ xᵉ
    le-zero-is-positive-ℤᵉ = is-positive-eq-ℤᵉ (invᵉ (right-zero-law-diff-ℤᵉ xᵉ))

    is-positive-le-zero-ℤᵉ : le-ℤᵉ zero-ℤᵉ xᵉ → is-positive-ℤᵉ xᵉ
    is-positive-le-zero-ℤᵉ = is-positive-eq-ℤᵉ (right-zero-law-diff-ℤᵉ xᵉ)

    eq-le-zero-is-positive-ℤᵉ : is-positive-ℤᵉ xᵉ ＝ᵉ le-ℤᵉ zero-ℤᵉ xᵉ
    eq-le-zero-is-positive-ℤᵉ = apᵉ is-positive-ℤᵉ (invᵉ (right-zero-law-diff-ℤᵉ xᵉ))
```

### If an integer is greater than a positive integer it is positive

```agda
module _
  (xᵉ yᵉ : ℤᵉ) (Iᵉ : le-ℤᵉ xᵉ yᵉ)
  where

  abstract
    is-positive-le-positive-ℤᵉ : is-positive-ℤᵉ xᵉ → is-positive-ℤᵉ yᵉ
    is-positive-le-positive-ℤᵉ Hᵉ =
      is-positive-le-zero-ℤᵉ yᵉ
        ( transitive-le-ℤᵉ
          ( zero-ℤᵉ)
          ( xᵉ)
          ( yᵉ)
          ( Iᵉ)
          ( le-zero-is-positive-ℤᵉ xᵉ Hᵉ))
```

### An integer `x` is negative if and only if `x < 0`

```agda
module _
  (xᵉ : ℤᵉ)
  where

  abstract
    le-zero-is-negative-ℤᵉ : is-negative-ℤᵉ xᵉ → le-ℤᵉ xᵉ zero-ℤᵉ
    le-zero-is-negative-ℤᵉ = is-positive-neg-is-negative-ℤᵉ

    is-negative-le-zero-ℤᵉ : le-ℤᵉ xᵉ zero-ℤᵉ → is-negative-ℤᵉ xᵉ
    is-negative-le-zero-ℤᵉ Hᵉ =
      is-negative-eq-ℤᵉ
        ( neg-neg-ℤᵉ xᵉ)
        ( is-negative-neg-is-positive-ℤᵉ Hᵉ)
```

### If an integer is lesser than a negative integer it is negative

```agda
module _
  (xᵉ yᵉ : ℤᵉ) (Iᵉ : le-ℤᵉ xᵉ yᵉ)
  where

  abstract
    is-negative-le-negative-ℤᵉ : is-negative-ℤᵉ yᵉ → is-negative-ℤᵉ xᵉ
    is-negative-le-negative-ℤᵉ Hᵉ =
      is-negative-le-zero-ℤᵉ xᵉ
        ( transitive-le-ℤᵉ
          ( xᵉ)
          ( yᵉ)
          ( zero-ℤᵉ)
          ( le-zero-is-negative-ℤᵉ yᵉ Hᵉ)
          ( Iᵉ))
```