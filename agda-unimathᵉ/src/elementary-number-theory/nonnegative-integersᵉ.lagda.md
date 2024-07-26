# The nonnegative integers

```agda
module elementary-number-theory.nonnegative-integersᵉ where
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

Theᵉ {{#conceptᵉ "nonnegative"ᵉ Disambiguation="integer"ᵉ Agda=is-nonnegative-ℤᵉ}}
integersᵉ areᵉ `zero-ℤ`ᵉ andᵉ theᵉ positiveᵉ componentᵉ ofᵉ theᵉ integers.ᵉ

## Definitions

### Nonnegative integers

```agda
is-nonnegative-ℤᵉ : ℤᵉ → UUᵉ lzero
is-nonnegative-ℤᵉ (inlᵉ xᵉ) = emptyᵉ
is-nonnegative-ℤᵉ (inrᵉ xᵉ) = unitᵉ

is-prop-is-nonnegative-ℤᵉ : (xᵉ : ℤᵉ) → is-propᵉ (is-nonnegative-ℤᵉ xᵉ)
is-prop-is-nonnegative-ℤᵉ (inlᵉ xᵉ) = is-prop-emptyᵉ
is-prop-is-nonnegative-ℤᵉ (inrᵉ xᵉ) = is-prop-unitᵉ

subtype-nonnegative-ℤᵉ : subtypeᵉ lzero ℤᵉ
subtype-nonnegative-ℤᵉ xᵉ = (is-nonnegative-ℤᵉ xᵉ ,ᵉ is-prop-is-nonnegative-ℤᵉ xᵉ)

nonnegative-ℤᵉ : UUᵉ lzero
nonnegative-ℤᵉ = type-subtypeᵉ subtype-nonnegative-ℤᵉ

is-nonnegative-eq-ℤᵉ :
  {xᵉ yᵉ : ℤᵉ} → xᵉ ＝ᵉ yᵉ → is-nonnegative-ℤᵉ xᵉ → is-nonnegative-ℤᵉ yᵉ
is-nonnegative-eq-ℤᵉ = trᵉ is-nonnegative-ℤᵉ

module _
  (pᵉ : nonnegative-ℤᵉ)
  where

  int-nonnegative-ℤᵉ : ℤᵉ
  int-nonnegative-ℤᵉ = pr1ᵉ pᵉ

  is-nonnegative-int-nonnegative-ℤᵉ : is-nonnegative-ℤᵉ int-nonnegative-ℤᵉ
  is-nonnegative-int-nonnegative-ℤᵉ = pr2ᵉ pᵉ
```

### Nonnegative integer constants

```agda
zero-nonnegative-ℤᵉ : nonnegative-ℤᵉ
zero-nonnegative-ℤᵉ = (zero-ℤᵉ ,ᵉ starᵉ)

one-nonnegative-ℤᵉ : nonnegative-ℤᵉ
one-nonnegative-ℤᵉ = (one-ℤᵉ ,ᵉ starᵉ)
```

## Properties

### Nonnegativity is decidable

```agda
is-decidable-is-nonnegative-ℤᵉ : is-decidable-famᵉ is-nonnegative-ℤᵉ
is-decidable-is-nonnegative-ℤᵉ (inlᵉ xᵉ) = inrᵉ idᵉ
is-decidable-is-nonnegative-ℤᵉ (inrᵉ xᵉ) = inlᵉ starᵉ

decidable-subtype-nonnegative-ℤᵉ : decidable-subtypeᵉ lzero ℤᵉ
decidable-subtype-nonnegative-ℤᵉ xᵉ =
  ( is-nonnegative-ℤᵉ xᵉ ,ᵉ
    is-prop-is-nonnegative-ℤᵉ xᵉ ,ᵉ
    is-decidable-is-nonnegative-ℤᵉ xᵉ)
```

### The nonnegative integers form a set

```agda
is-set-nonnegative-ℤᵉ : is-setᵉ nonnegative-ℤᵉ
is-set-nonnegative-ℤᵉ =
  is-set-embᵉ
    ( emb-subtypeᵉ subtype-nonnegative-ℤᵉ)
    ( is-set-ℤᵉ)
```

### The only nonnegative integer with a nonnegative negative is zero

```agda
is-zero-is-nonnegative-neg-is-nonnegative-ℤᵉ :
  {xᵉ : ℤᵉ} → is-nonnegative-ℤᵉ xᵉ → is-nonnegative-ℤᵉ (neg-ℤᵉ xᵉ) → is-zero-ℤᵉ xᵉ
is-zero-is-nonnegative-neg-is-nonnegative-ℤᵉ {inrᵉ (inlᵉ starᵉ)} nonnegᵉ nonposᵉ =
  reflᵉ
```

### The successor of a nonnegative integer is nonnegative

```agda
is-nonnegative-succ-is-nonnegative-ℤᵉ :
  {xᵉ : ℤᵉ} → is-nonnegative-ℤᵉ xᵉ → is-nonnegative-ℤᵉ (succ-ℤᵉ xᵉ)
is-nonnegative-succ-is-nonnegative-ℤᵉ {inrᵉ (inlᵉ xᵉ)} Hᵉ = Hᵉ
is-nonnegative-succ-is-nonnegative-ℤᵉ {inrᵉ (inrᵉ xᵉ)} Hᵉ = Hᵉ

succ-nonnegative-ℤᵉ : nonnegative-ℤᵉ → nonnegative-ℤᵉ
succ-nonnegative-ℤᵉ (xᵉ ,ᵉ Hᵉ) = succ-ℤᵉ xᵉ ,ᵉ is-nonnegative-succ-is-nonnegative-ℤᵉ Hᵉ
```

### The integer image of a natural number is nonnegative

```agda
is-nonnegative-int-ℕᵉ : (nᵉ : ℕᵉ) → is-nonnegative-ℤᵉ (int-ℕᵉ nᵉ)
is-nonnegative-int-ℕᵉ zero-ℕᵉ = starᵉ
is-nonnegative-int-ℕᵉ (succ-ℕᵉ nᵉ) = starᵉ
```

### The canonical equivalence between natural numbers and nonnegative integers

```agda
nonnegative-int-ℕᵉ : ℕᵉ → nonnegative-ℤᵉ
nonnegative-int-ℕᵉ nᵉ = int-ℕᵉ nᵉ ,ᵉ is-nonnegative-int-ℕᵉ nᵉ

nat-nonnegative-ℤᵉ : nonnegative-ℤᵉ → ℕᵉ
nat-nonnegative-ℤᵉ (inrᵉ (inlᵉ xᵉ) ,ᵉ Hᵉ) = zero-ℕᵉ
nat-nonnegative-ℤᵉ (inrᵉ (inrᵉ xᵉ) ,ᵉ Hᵉ) = succ-ℕᵉ xᵉ

eq-nat-nonnegative-succ-nonnnegative-ℤᵉ :
  (xᵉ : nonnegative-ℤᵉ) →
  nat-nonnegative-ℤᵉ (succ-nonnegative-ℤᵉ xᵉ) ＝ᵉ succ-ℕᵉ (nat-nonnegative-ℤᵉ xᵉ)
eq-nat-nonnegative-succ-nonnnegative-ℤᵉ (inrᵉ (inlᵉ xᵉ) ,ᵉ Hᵉ) = reflᵉ
eq-nat-nonnegative-succ-nonnnegative-ℤᵉ (inrᵉ (inrᵉ xᵉ) ,ᵉ Hᵉ) = reflᵉ

is-section-nat-nonnegative-ℤᵉ :
  (xᵉ : nonnegative-ℤᵉ) → nonnegative-int-ℕᵉ (nat-nonnegative-ℤᵉ xᵉ) ＝ᵉ xᵉ
is-section-nat-nonnegative-ℤᵉ ((inrᵉ (inlᵉ starᵉ)) ,ᵉ Hᵉ) = reflᵉ
is-section-nat-nonnegative-ℤᵉ ((inrᵉ (inrᵉ xᵉ)) ,ᵉ Hᵉ) = reflᵉ

is-retraction-nat-nonnegative-ℤᵉ :
  (nᵉ : ℕᵉ) → nat-nonnegative-ℤᵉ (nonnegative-int-ℕᵉ nᵉ) ＝ᵉ nᵉ
is-retraction-nat-nonnegative-ℤᵉ zero-ℕᵉ = reflᵉ
is-retraction-nat-nonnegative-ℤᵉ (succ-ℕᵉ nᵉ) = reflᵉ

is-equiv-nat-nonnegative-ℤᵉ : is-equivᵉ nat-nonnegative-ℤᵉ
pr1ᵉ (pr1ᵉ is-equiv-nat-nonnegative-ℤᵉ) = nonnegative-int-ℕᵉ
pr2ᵉ (pr1ᵉ is-equiv-nat-nonnegative-ℤᵉ) = is-retraction-nat-nonnegative-ℤᵉ
pr1ᵉ (pr2ᵉ is-equiv-nat-nonnegative-ℤᵉ) = nonnegative-int-ℕᵉ
pr2ᵉ (pr2ᵉ is-equiv-nat-nonnegative-ℤᵉ) = is-section-nat-nonnegative-ℤᵉ

is-equiv-nonnegative-int-ℕᵉ : is-equivᵉ nonnegative-int-ℕᵉ
pr1ᵉ (pr1ᵉ is-equiv-nonnegative-int-ℕᵉ) = nat-nonnegative-ℤᵉ
pr2ᵉ (pr1ᵉ is-equiv-nonnegative-int-ℕᵉ) = is-section-nat-nonnegative-ℤᵉ
pr1ᵉ (pr2ᵉ is-equiv-nonnegative-int-ℕᵉ) = nat-nonnegative-ℤᵉ
pr2ᵉ (pr2ᵉ is-equiv-nonnegative-int-ℕᵉ) = is-retraction-nat-nonnegative-ℤᵉ

equiv-nonnegative-int-ℕᵉ : ℕᵉ ≃ᵉ nonnegative-ℤᵉ
pr1ᵉ equiv-nonnegative-int-ℕᵉ = nonnegative-int-ℕᵉ
pr2ᵉ equiv-nonnegative-int-ℕᵉ = is-equiv-nonnegative-int-ℕᵉ
```

## See also

-ᵉ Theᵉ relationsᵉ betweenᵉ nonnegativeᵉ andᵉ positive,ᵉ negativeᵉ andᵉ nonpositiveᵉ
  integersᵉ areᵉ derivedᵉ in
  [`positive-and-negative-integers`](elementary-number-theory.positive-and-negative-integers.mdᵉ)