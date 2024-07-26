# The nonpositive integers

```agda
module elementary-number-theory.nonpositive-integersᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.integersᵉ
open import elementary-number-theory.natural-numbersᵉ

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
forᵉ theᵉ [positiveᵉ integers](elementary-number-theory.positive-integers.md).ᵉ
Arrangedᵉ onᵉ aᵉ numberᵉ line,ᵉ weᵉ haveᵉ

```text
  ⋯ᵉ  -4  -3  -2  -1   0   1   2   3   4   ⋯ᵉ
  <---+---+---+---ᵉ]   |   [---+---+---+--->ᵉ
```

Theᵉ {{#conceptᵉ "nonpositive"ᵉ Disambiguation="integer"ᵉ Agda=is-nonpositive-ℤᵉ}}
integersᵉ areᵉ `zero-ℤ`ᵉ andᵉ theᵉ negativeᵉ componentᵉ ofᵉ theᵉ integers.ᵉ

## Definitions

### Nonnpositive integers

```agda
is-nonpositive-ℤᵉ : ℤᵉ → UUᵉ lzero
is-nonpositive-ℤᵉ (inlᵉ kᵉ) = unitᵉ
is-nonpositive-ℤᵉ (inrᵉ (inlᵉ xᵉ)) = unitᵉ
is-nonpositive-ℤᵉ (inrᵉ (inrᵉ xᵉ)) = emptyᵉ

is-prop-is-nonpositive-ℤᵉ : (xᵉ : ℤᵉ) → is-propᵉ (is-nonpositive-ℤᵉ xᵉ)
is-prop-is-nonpositive-ℤᵉ (inlᵉ xᵉ) = is-prop-unitᵉ
is-prop-is-nonpositive-ℤᵉ (inrᵉ (inlᵉ xᵉ)) = is-prop-unitᵉ
is-prop-is-nonpositive-ℤᵉ (inrᵉ (inrᵉ xᵉ)) = is-prop-emptyᵉ

subtype-nonpositive-ℤᵉ : subtypeᵉ lzero ℤᵉ
subtype-nonpositive-ℤᵉ xᵉ = (is-nonpositive-ℤᵉ xᵉ ,ᵉ is-prop-is-nonpositive-ℤᵉ xᵉ)

nonpositive-ℤᵉ : UUᵉ lzero
nonpositive-ℤᵉ = type-subtypeᵉ subtype-nonpositive-ℤᵉ

is-nonpositive-eq-ℤᵉ :
  {xᵉ yᵉ : ℤᵉ} → xᵉ ＝ᵉ yᵉ → is-nonpositive-ℤᵉ xᵉ → is-nonpositive-ℤᵉ yᵉ
is-nonpositive-eq-ℤᵉ = trᵉ is-nonpositive-ℤᵉ

module _
  (pᵉ : nonpositive-ℤᵉ)
  where

  int-nonpositive-ℤᵉ : ℤᵉ
  int-nonpositive-ℤᵉ = pr1ᵉ pᵉ

  is-nonpositive-int-nonpositive-ℤᵉ : is-nonpositive-ℤᵉ int-nonpositive-ℤᵉ
  is-nonpositive-int-nonpositive-ℤᵉ = pr2ᵉ pᵉ
```

### Nonpositive constants

```agda
zero-nonpositive-ℤᵉ : nonpositive-ℤᵉ
zero-nonpositive-ℤᵉ = (zero-ℤᵉ ,ᵉ starᵉ)

neg-one-nonpositive-ℤᵉ : nonpositive-ℤᵉ
neg-one-nonpositive-ℤᵉ = (neg-one-ℤᵉ ,ᵉ starᵉ)
```

## Properties

### Nonpositivity is decidable

```agda
is-decidable-is-nonpositive-ℤᵉ : is-decidable-famᵉ is-nonpositive-ℤᵉ
is-decidable-is-nonpositive-ℤᵉ (inlᵉ xᵉ) = inlᵉ starᵉ
is-decidable-is-nonpositive-ℤᵉ (inrᵉ (inlᵉ xᵉ)) = inlᵉ starᵉ
is-decidable-is-nonpositive-ℤᵉ (inrᵉ (inrᵉ xᵉ)) = inrᵉ idᵉ

decidable-subtype-nonpositive-ℤᵉ : decidable-subtypeᵉ lzero ℤᵉ
decidable-subtype-nonpositive-ℤᵉ xᵉ =
  ( is-nonpositive-ℤᵉ xᵉ ,ᵉ
    is-prop-is-nonpositive-ℤᵉ xᵉ ,ᵉ
    is-decidable-is-nonpositive-ℤᵉ xᵉ)
```

### The nonpositive integers form a set

```agda
is-set-nonpositive-ℤᵉ : is-setᵉ nonpositive-ℤᵉ
is-set-nonpositive-ℤᵉ =
  is-set-embᵉ
    ( emb-subtypeᵉ subtype-nonpositive-ℤᵉ)
    ( is-set-ℤᵉ)
```

### The only nonpositive integer with a nonpositive negative is zero

```agda
is-zero-is-nonpositive-neg-is-nonpositive-ℤᵉ :
  {xᵉ : ℤᵉ} → is-nonpositive-ℤᵉ xᵉ → is-nonpositive-ℤᵉ (neg-ℤᵉ xᵉ) → is-zero-ℤᵉ xᵉ
is-zero-is-nonpositive-neg-is-nonpositive-ℤᵉ {inrᵉ (inlᵉ starᵉ)} nonnegᵉ nonposᵉ =
  reflᵉ
```

### The predecessor of a nonpositive integer is nonpositive

```agda
is-nonpositive-pred-is-nonpositive-ℤᵉ :
  {xᵉ : ℤᵉ} → is-nonpositive-ℤᵉ xᵉ → is-nonpositive-ℤᵉ (pred-ℤᵉ xᵉ)
is-nonpositive-pred-is-nonpositive-ℤᵉ {inlᵉ xᵉ} Hᵉ = Hᵉ
is-nonpositive-pred-is-nonpositive-ℤᵉ {inrᵉ (inlᵉ xᵉ)} Hᵉ = Hᵉ

pred-nonpositive-ℤᵉ : nonpositive-ℤᵉ → nonpositive-ℤᵉ
pred-nonpositive-ℤᵉ (xᵉ ,ᵉ Hᵉ) = pred-ℤᵉ xᵉ ,ᵉ is-nonpositive-pred-is-nonpositive-ℤᵉ Hᵉ
```

### The canonical equivalence between natural numbers and positive integers

```agda
nonpositive-int-ℕᵉ : ℕᵉ → nonpositive-ℤᵉ
nonpositive-int-ℕᵉ = rec-ℕᵉ zero-nonpositive-ℤᵉ (λ _ → pred-nonpositive-ℤᵉ)

nat-nonpositive-ℤᵉ : nonpositive-ℤᵉ → ℕᵉ
nat-nonpositive-ℤᵉ (inlᵉ xᵉ ,ᵉ Hᵉ) = succ-ℕᵉ xᵉ
nat-nonpositive-ℤᵉ (inrᵉ xᵉ ,ᵉ Hᵉ) = zero-ℕᵉ

eq-nat-nonpositive-pred-nonpositive-ℤᵉ :
  (xᵉ : nonpositive-ℤᵉ) →
  nat-nonpositive-ℤᵉ (pred-nonpositive-ℤᵉ xᵉ) ＝ᵉ succ-ℕᵉ (nat-nonpositive-ℤᵉ xᵉ)
eq-nat-nonpositive-pred-nonpositive-ℤᵉ (inlᵉ xᵉ ,ᵉ Hᵉ) = reflᵉ
eq-nat-nonpositive-pred-nonpositive-ℤᵉ (inrᵉ (inlᵉ xᵉ) ,ᵉ Hᵉ) = reflᵉ

is-section-nat-nonpositive-ℤᵉ :
  (xᵉ : nonpositive-ℤᵉ) → nonpositive-int-ℕᵉ (nat-nonpositive-ℤᵉ xᵉ) ＝ᵉ xᵉ
is-section-nat-nonpositive-ℤᵉ (inlᵉ zero-ℕᵉ ,ᵉ Hᵉ) = reflᵉ
is-section-nat-nonpositive-ℤᵉ (inlᵉ (succ-ℕᵉ xᵉ) ,ᵉ Hᵉ) =
  apᵉ pred-nonpositive-ℤᵉ (is-section-nat-nonpositive-ℤᵉ (inlᵉ xᵉ ,ᵉ Hᵉ))
is-section-nat-nonpositive-ℤᵉ (inrᵉ (inlᵉ xᵉ) ,ᵉ Hᵉ) = reflᵉ

is-retraction-nat-nonpositive-ℤᵉ :
  (nᵉ : ℕᵉ) → nat-nonpositive-ℤᵉ (nonpositive-int-ℕᵉ nᵉ) ＝ᵉ nᵉ
is-retraction-nat-nonpositive-ℤᵉ zero-ℕᵉ = reflᵉ
is-retraction-nat-nonpositive-ℤᵉ (succ-ℕᵉ nᵉ) =
  eq-nat-nonpositive-pred-nonpositive-ℤᵉ (nonpositive-int-ℕᵉ nᵉ) ∙ᵉ
  apᵉ succ-ℕᵉ (is-retraction-nat-nonpositive-ℤᵉ nᵉ)

is-equiv-nonpositive-int-ℕᵉ : is-equivᵉ nonpositive-int-ℕᵉ
pr1ᵉ (pr1ᵉ is-equiv-nonpositive-int-ℕᵉ) = nat-nonpositive-ℤᵉ
pr2ᵉ (pr1ᵉ is-equiv-nonpositive-int-ℕᵉ) = is-section-nat-nonpositive-ℤᵉ
pr1ᵉ (pr2ᵉ is-equiv-nonpositive-int-ℕᵉ) = nat-nonpositive-ℤᵉ
pr2ᵉ (pr2ᵉ is-equiv-nonpositive-int-ℕᵉ) = is-retraction-nat-nonpositive-ℤᵉ

equiv-nonpositive-int-ℕᵉ : ℕᵉ ≃ᵉ nonpositive-ℤᵉ
pr1ᵉ equiv-nonpositive-int-ℕᵉ = nonpositive-int-ℕᵉ
pr2ᵉ equiv-nonpositive-int-ℕᵉ = is-equiv-nonpositive-int-ℕᵉ
```

## See also

-ᵉ Theᵉ relationsᵉ betweenᵉ nonpositiveᵉ andᵉ positive,ᵉ nonnegativeᵉ andᵉ negativeᵉ
  integersᵉ areᵉ derivedᵉ in
  [`positive-and-negative-integers`](elementary-number-theory.positive-and-negative-integers.mdᵉ)