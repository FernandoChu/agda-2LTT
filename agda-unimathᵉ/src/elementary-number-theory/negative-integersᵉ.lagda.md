# The negative integers

```agda
module elementary-number-theory.negative-integersᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.integersᵉ
open import elementary-number-theory.natural-numbersᵉ
open import elementary-number-theory.nonzero-integersᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.coproduct-typesᵉ
open import foundation.decidable-subtypesᵉ
open import foundation.decidable-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.empty-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.retractionsᵉ
open import foundation.sectionsᵉ
open import foundation.setsᵉ
open import foundation.subtypesᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Theᵉ [integers](elementary-number-theory.integers.mdᵉ) areᵉ definedᵉ asᵉ aᵉ
[disjointᵉ sum](foundation-core.coproduct-types.mdᵉ) ofᵉ threeᵉ components.ᵉ Aᵉ singleᵉ
elementᵉ componentᵉ containingᵉ theᵉ integerᵉ _zero_,ᵉ andᵉ twoᵉ copiesᵉ ofᵉ theᵉ
[naturalᵉ numbers](elementary-number-theory.natural-numbers.md),ᵉ oneᵉ copyᵉ forᵉ theᵉ
_negativeᵉ integersᵉ_ andᵉ oneᵉ copyᵉ forᵉ theᵉ
[positiveᵉ integers](elementary-number-theory.positive-integers.md).ᵉ Arrangedᵉ onᵉ
aᵉ numberᵉ line,ᵉ weᵉ haveᵉ

```text
  ⋯ᵉ  -4  -3  -2  -1   0   1   2   3   4   ⋯ᵉ
  <---+---+---+---ᵉ]   |   [---+---+---+--->ᵉ
```

Weᵉ sayᵉ anᵉ integerᵉ isᵉ
{{#conceptᵉ "negative"ᵉ Disambiguation="integer"ᵉ Agda=is-negative-ℤᵉ}} ifᵉ itᵉ isᵉ anᵉ
elementᵉ ofᵉ theᵉ negativeᵉ componentᵉ ofᵉ theᵉ integers.ᵉ

## Definitions

### Negative integers

```agda
is-negative-ℤᵉ : ℤᵉ → UUᵉ lzero
is-negative-ℤᵉ (inlᵉ kᵉ) = unitᵉ
is-negative-ℤᵉ (inrᵉ kᵉ) = emptyᵉ

is-prop-is-negative-ℤᵉ : (xᵉ : ℤᵉ) → is-propᵉ (is-negative-ℤᵉ xᵉ)
is-prop-is-negative-ℤᵉ (inlᵉ xᵉ) = is-prop-unitᵉ
is-prop-is-negative-ℤᵉ (inrᵉ xᵉ) = is-prop-emptyᵉ

subtype-negative-ℤᵉ : subtypeᵉ lzero ℤᵉ
subtype-negative-ℤᵉ xᵉ = (is-negative-ℤᵉ xᵉ ,ᵉ is-prop-is-negative-ℤᵉ xᵉ)

negative-ℤᵉ : UUᵉ lzero
negative-ℤᵉ = type-subtypeᵉ subtype-negative-ℤᵉ

is-negative-eq-ℤᵉ : {xᵉ yᵉ : ℤᵉ} → xᵉ ＝ᵉ yᵉ → is-negative-ℤᵉ xᵉ → is-negative-ℤᵉ yᵉ
is-negative-eq-ℤᵉ = trᵉ is-negative-ℤᵉ

module _
  (pᵉ : negative-ℤᵉ)
  where

  int-negative-ℤᵉ : ℤᵉ
  int-negative-ℤᵉ = pr1ᵉ pᵉ

  is-negative-int-negative-ℤᵉ : is-negative-ℤᵉ int-negative-ℤᵉ
  is-negative-int-negative-ℤᵉ = pr2ᵉ pᵉ
```

### Negative constants

```agda
neg-one-negative-ℤᵉ : negative-ℤᵉ
neg-one-negative-ℤᵉ = (neg-one-ℤᵉ ,ᵉ starᵉ)
```

## Properties

### Negativity is decidable

```agda
is-decidable-is-negative-ℤᵉ : is-decidable-famᵉ is-negative-ℤᵉ
is-decidable-is-negative-ℤᵉ (inlᵉ xᵉ) = inlᵉ starᵉ
is-decidable-is-negative-ℤᵉ (inrᵉ xᵉ) = inrᵉ idᵉ

decidable-subtype-negative-ℤᵉ : decidable-subtypeᵉ lzero ℤᵉ
decidable-subtype-negative-ℤᵉ xᵉ =
  ( is-negative-ℤᵉ xᵉ ,ᵉ
    is-prop-is-negative-ℤᵉ xᵉ ,ᵉ
    is-decidable-is-negative-ℤᵉ xᵉ)
```

### Negative integers are nonzero

```agda
is-nonzero-is-negative-ℤᵉ : {xᵉ : ℤᵉ} → is-negative-ℤᵉ xᵉ → is-nonzero-ℤᵉ xᵉ
is-nonzero-is-negative-ℤᵉ {inlᵉ xᵉ} Hᵉ ()
```

### The negative integers form a set

```agda
is-set-negative-ℤᵉ : is-setᵉ negative-ℤᵉ
is-set-negative-ℤᵉ =
  is-set-type-subtypeᵉ (subtype-negative-ℤᵉ) (is-set-ℤᵉ)
```

### The predecessor of a negative integer is negative

```agda
is-negative-pred-is-negative-ℤᵉ :
  {xᵉ : ℤᵉ} → is-negative-ℤᵉ xᵉ → is-negative-ℤᵉ (pred-ℤᵉ xᵉ)
is-negative-pred-is-negative-ℤᵉ {inlᵉ xᵉ} Hᵉ = Hᵉ

pred-negative-ℤᵉ : negative-ℤᵉ → negative-ℤᵉ
pred-negative-ℤᵉ (xᵉ ,ᵉ Hᵉ) = (pred-ℤᵉ xᵉ ,ᵉ is-negative-pred-is-negative-ℤᵉ Hᵉ)
```

### The canonical equivalence between natural numbers and negative integers

```agda
negative-int-ℕᵉ : ℕᵉ → negative-ℤᵉ
negative-int-ℕᵉ = rec-ℕᵉ neg-one-negative-ℤᵉ (λ _ → pred-negative-ℤᵉ)

nat-negative-ℤᵉ : negative-ℤᵉ → ℕᵉ
nat-negative-ℤᵉ (inlᵉ xᵉ ,ᵉ Hᵉ) = xᵉ

eq-nat-negative-pred-negative-ℤᵉ :
  (xᵉ : negative-ℤᵉ) →
  nat-negative-ℤᵉ (pred-negative-ℤᵉ xᵉ) ＝ᵉ succ-ℕᵉ (nat-negative-ℤᵉ xᵉ)
eq-nat-negative-pred-negative-ℤᵉ (inlᵉ xᵉ ,ᵉ Hᵉ) = reflᵉ

is-section-nat-negative-ℤᵉ :
  (xᵉ : negative-ℤᵉ) → negative-int-ℕᵉ (nat-negative-ℤᵉ xᵉ) ＝ᵉ xᵉ
is-section-nat-negative-ℤᵉ (inlᵉ zero-ℕᵉ ,ᵉ Hᵉ) = reflᵉ
is-section-nat-negative-ℤᵉ (inlᵉ (succ-ℕᵉ xᵉ) ,ᵉ Hᵉ) =
  apᵉ pred-negative-ℤᵉ (is-section-nat-negative-ℤᵉ (inlᵉ xᵉ ,ᵉ Hᵉ))

is-retraction-nat-negative-ℤᵉ :
  (nᵉ : ℕᵉ) → nat-negative-ℤᵉ (negative-int-ℕᵉ nᵉ) ＝ᵉ nᵉ
is-retraction-nat-negative-ℤᵉ zero-ℕᵉ = reflᵉ
is-retraction-nat-negative-ℤᵉ (succ-ℕᵉ nᵉ) =
  eq-nat-negative-pred-negative-ℤᵉ (negative-int-ℕᵉ nᵉ) ∙ᵉ
  apᵉ succ-ℕᵉ (is-retraction-nat-negative-ℤᵉ nᵉ)

is-equiv-negative-int-ℕᵉ : is-equivᵉ negative-int-ℕᵉ
pr1ᵉ (pr1ᵉ is-equiv-negative-int-ℕᵉ) = nat-negative-ℤᵉ
pr2ᵉ (pr1ᵉ is-equiv-negative-int-ℕᵉ) = is-section-nat-negative-ℤᵉ
pr1ᵉ (pr2ᵉ is-equiv-negative-int-ℕᵉ) = nat-negative-ℤᵉ
pr2ᵉ (pr2ᵉ is-equiv-negative-int-ℕᵉ) = is-retraction-nat-negative-ℤᵉ

equiv-negative-int-ℕᵉ : ℕᵉ ≃ᵉ negative-ℤᵉ
pr1ᵉ equiv-negative-int-ℕᵉ = negative-int-ℕᵉ
pr2ᵉ equiv-negative-int-ℕᵉ = is-equiv-negative-int-ℕᵉ
```

## See also

-ᵉ Relationsᵉ betweenᵉ negativeᵉ andᵉ positive,ᵉ nonnegativeᵉ andᵉ nonnpositiveᵉ integersᵉ
  areᵉ derivedᵉ in
  [`positive-and-negative-integers`](elementary-number-theory.positive-and-negative-integers.mdᵉ)