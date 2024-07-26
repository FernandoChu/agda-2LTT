# The positive integers

```agda
module elementary-number-theory.positive-integersᵉ where
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
[negativeᵉ integers](elementary-number-theory.negative-integers.mdᵉ) andᵉ oneᵉ copyᵉ
forᵉ theᵉ _positiveᵉ integers_.ᵉ Arrangedᵉ onᵉ aᵉ numberᵉ line,ᵉ weᵉ haveᵉ

```text
  ⋯ᵉ  -4  -3  -2  -1   0   1   2   3   4   ⋯ᵉ
  <---+---+---+---ᵉ]   |   [---+---+---+--->ᵉ
```

Weᵉ sayᵉ anᵉ integerᵉ isᵉ
{{#conceptᵉ "positive"ᵉ Disambiguation="integer"ᵉ Agda=is-positive-ℤᵉ}} ifᵉ itᵉ isᵉ anᵉ
elementᵉ ofᵉ theᵉ positiveᵉ componentᵉ ofᵉ theᵉ integers.ᵉ

## Definitions

### Positive integers

```agda
is-positive-ℤᵉ : ℤᵉ → UUᵉ lzero
is-positive-ℤᵉ (inlᵉ xᵉ) = emptyᵉ
is-positive-ℤᵉ (inrᵉ (inlᵉ xᵉ)) = emptyᵉ
is-positive-ℤᵉ (inrᵉ (inrᵉ xᵉ)) = unitᵉ

is-prop-is-positive-ℤᵉ : (xᵉ : ℤᵉ) → is-propᵉ (is-positive-ℤᵉ xᵉ)
is-prop-is-positive-ℤᵉ (inlᵉ xᵉ) = is-prop-emptyᵉ
is-prop-is-positive-ℤᵉ (inrᵉ (inlᵉ xᵉ)) = is-prop-emptyᵉ
is-prop-is-positive-ℤᵉ (inrᵉ (inrᵉ xᵉ)) = is-prop-unitᵉ

subtype-positive-ℤᵉ : subtypeᵉ lzero ℤᵉ
subtype-positive-ℤᵉ xᵉ = (is-positive-ℤᵉ xᵉ ,ᵉ is-prop-is-positive-ℤᵉ xᵉ)

positive-ℤᵉ : UUᵉ lzero
positive-ℤᵉ = type-subtypeᵉ subtype-positive-ℤᵉ

is-positive-eq-ℤᵉ : {xᵉ yᵉ : ℤᵉ} → xᵉ ＝ᵉ yᵉ → is-positive-ℤᵉ xᵉ → is-positive-ℤᵉ yᵉ
is-positive-eq-ℤᵉ = trᵉ is-positive-ℤᵉ

module _
  (pᵉ : positive-ℤᵉ)
  where

  int-positive-ℤᵉ : ℤᵉ
  int-positive-ℤᵉ = pr1ᵉ pᵉ

  is-positive-int-positive-ℤᵉ : is-positive-ℤᵉ int-positive-ℤᵉ
  is-positive-int-positive-ℤᵉ = pr2ᵉ pᵉ
```

### Positive constants

```agda
one-positive-ℤᵉ : positive-ℤᵉ
one-positive-ℤᵉ = (one-ℤᵉ ,ᵉ starᵉ)
```

## Properties

### Positivity is decidable

```agda
is-decidable-is-positive-ℤᵉ : is-decidable-famᵉ is-positive-ℤᵉ
is-decidable-is-positive-ℤᵉ (inlᵉ xᵉ) = inrᵉ idᵉ
is-decidable-is-positive-ℤᵉ (inrᵉ (inlᵉ xᵉ)) = inrᵉ idᵉ
is-decidable-is-positive-ℤᵉ (inrᵉ (inrᵉ xᵉ)) = inlᵉ starᵉ

decidable-subtype-positive-ℤᵉ : decidable-subtypeᵉ lzero ℤᵉ
decidable-subtype-positive-ℤᵉ xᵉ =
  ( is-positive-ℤᵉ xᵉ ,ᵉ
    is-prop-is-positive-ℤᵉ xᵉ ,ᵉ
    is-decidable-is-positive-ℤᵉ xᵉ)
```

### Positive integers are nonzero

```agda
is-nonzero-is-positive-ℤᵉ : {xᵉ : ℤᵉ} → is-positive-ℤᵉ xᵉ → is-nonzero-ℤᵉ xᵉ
is-nonzero-is-positive-ℤᵉ {inrᵉ (inrᵉ xᵉ)} Hᵉ ()
```

### The positive integers form a set

```agda
is-set-positive-ℤᵉ : is-setᵉ positive-ℤᵉ
is-set-positive-ℤᵉ =
  is-set-type-subtypeᵉ subtype-positive-ℤᵉ is-set-ℤᵉ
```

### The successor of a positive integer is positive

```agda
is-positive-succ-is-positive-ℤᵉ :
  {xᵉ : ℤᵉ} → is-positive-ℤᵉ xᵉ → is-positive-ℤᵉ (succ-ℤᵉ xᵉ)
is-positive-succ-is-positive-ℤᵉ {inrᵉ (inrᵉ xᵉ)} Hᵉ = Hᵉ

succ-positive-ℤᵉ : positive-ℤᵉ → positive-ℤᵉ
succ-positive-ℤᵉ (xᵉ ,ᵉ Hᵉ) = (succ-ℤᵉ xᵉ ,ᵉ is-positive-succ-is-positive-ℤᵉ Hᵉ)
```

### The integer image of a nonzero natural number is positive

```agda
is-positive-int-is-nonzero-ℕᵉ :
  (xᵉ : ℕᵉ) → is-nonzero-ℕᵉ xᵉ → is-positive-ℤᵉ (int-ℕᵉ xᵉ)
is-positive-int-is-nonzero-ℕᵉ zero-ℕᵉ Hᵉ = ex-falsoᵉ (Hᵉ reflᵉ)
is-positive-int-is-nonzero-ℕᵉ (succ-ℕᵉ xᵉ) Hᵉ = starᵉ
```

### The canonical equivalence between natural numbers and positive integers

```agda
positive-int-ℕᵉ : ℕᵉ → positive-ℤᵉ
positive-int-ℕᵉ = rec-ℕᵉ one-positive-ℤᵉ (λ _ → succ-positive-ℤᵉ)

nat-positive-ℤᵉ : positive-ℤᵉ → ℕᵉ
nat-positive-ℤᵉ (inrᵉ (inrᵉ xᵉ) ,ᵉ Hᵉ) = xᵉ

eq-nat-positive-succ-positive-ℤᵉ :
  (xᵉ : positive-ℤᵉ) →
  nat-positive-ℤᵉ (succ-positive-ℤᵉ xᵉ) ＝ᵉ succ-ℕᵉ (nat-positive-ℤᵉ xᵉ)
eq-nat-positive-succ-positive-ℤᵉ (inrᵉ (inrᵉ xᵉ) ,ᵉ Hᵉ) = reflᵉ

is-section-nat-positive-ℤᵉ :
  (xᵉ : positive-ℤᵉ) → positive-int-ℕᵉ (nat-positive-ℤᵉ xᵉ) ＝ᵉ xᵉ
is-section-nat-positive-ℤᵉ (inrᵉ (inrᵉ zero-ℕᵉ) ,ᵉ Hᵉ) = reflᵉ
is-section-nat-positive-ℤᵉ (inrᵉ (inrᵉ (succ-ℕᵉ xᵉ)) ,ᵉ Hᵉ) =
  apᵉ succ-positive-ℤᵉ (is-section-nat-positive-ℤᵉ ( inrᵉ (inrᵉ xᵉ) ,ᵉ Hᵉ))

is-retraction-nat-positive-ℤᵉ :
  (nᵉ : ℕᵉ) → nat-positive-ℤᵉ (positive-int-ℕᵉ nᵉ) ＝ᵉ nᵉ
is-retraction-nat-positive-ℤᵉ zero-ℕᵉ = reflᵉ
is-retraction-nat-positive-ℤᵉ (succ-ℕᵉ nᵉ) =
  eq-nat-positive-succ-positive-ℤᵉ (positive-int-ℕᵉ nᵉ) ∙ᵉ
  apᵉ succ-ℕᵉ (is-retraction-nat-positive-ℤᵉ nᵉ)

is-equiv-positive-int-ℕᵉ : is-equivᵉ positive-int-ℕᵉ
pr1ᵉ (pr1ᵉ is-equiv-positive-int-ℕᵉ) = nat-positive-ℤᵉ
pr2ᵉ (pr1ᵉ is-equiv-positive-int-ℕᵉ) = is-section-nat-positive-ℤᵉ
pr1ᵉ (pr2ᵉ is-equiv-positive-int-ℕᵉ) = nat-positive-ℤᵉ
pr2ᵉ (pr2ᵉ is-equiv-positive-int-ℕᵉ) = is-retraction-nat-positive-ℤᵉ

equiv-positive-int-ℕᵉ : ℕᵉ ≃ᵉ positive-ℤᵉ
pr1ᵉ equiv-positive-int-ℕᵉ = positive-int-ℕᵉ
pr2ᵉ equiv-positive-int-ℕᵉ = is-equiv-positive-int-ℕᵉ
```

## See also

-ᵉ Theᵉ relationsᵉ betweenᵉ positiveᵉ andᵉ nonnegative,ᵉ negativeᵉ andᵉ nonnpositiveᵉ
  integersᵉ areᵉ derivedᵉ in
  [`positive-and-negative-integers`](elementary-number-theory.positive-and-negative-integers.mdᵉ)