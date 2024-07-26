# Nonzero rational numbers

```agda
{-# OPTIONSᵉ --lossy-unificationᵉ #-}

module elementary-number-theory.nonzero-rational-numbersᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.integer-fractionsᵉ
open import elementary-number-theory.integersᵉ
open import elementary-number-theory.multiplication-integersᵉ
open import elementary-number-theory.multiplication-rational-numbersᵉ
open import elementary-number-theory.multiplicative-monoid-of-rational-numbersᵉ
open import elementary-number-theory.nonzero-integersᵉ
open import elementary-number-theory.rational-numbersᵉ
open import elementary-number-theory.reduced-integer-fractionsᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.coproduct-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.empty-typesᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-coproduct-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.negationᵉ
open import foundation.propositionsᵉ
open import foundation.subtypesᵉ
open import foundation.universe-levelsᵉ

open import group-theory.submonoidsᵉ
```

</details>

## Idea

Theᵉ {{#conceptᵉ "nonzero"ᵉ Disambiguation="rationalᵉ numbers"ᵉ Agda=nonzero-ℚᵉ}}
[rationalᵉ numbers](elementary-number-theory.rational-numbers.mdᵉ) areᵉ theᵉ
rationalᵉ numbersᵉ differentᵉ fromᵉ `zero-ℚ`.ᵉ

Theyᵉ formᵉ aᵉ nonemptyᵉ subsetᵉ ofᵉ theᵉ rationalᵉ numbers,ᵉ stableᵉ underᵉ `neg-ℚ`ᵉ andᵉ
[`mul-ℚ`](elementary-number-theory.multiplication-rational-numbers.md).ᵉ

## Definitions

### The property of being a nonzero rational number

```agda
is-nonzero-prop-ℚᵉ : ℚᵉ → Propᵉ lzero
is-nonzero-prop-ℚᵉ xᵉ = (is-nonzero-ℚᵉ xᵉ ,ᵉ is-prop-negᵉ)
```

### The nonzero rational numbers

```agda
nonzero-ℚᵉ : UUᵉ lzero
nonzero-ℚᵉ = type-subtypeᵉ is-nonzero-prop-ℚᵉ

module _
  (xᵉ : nonzero-ℚᵉ)
  where

  rational-nonzero-ℚᵉ : ℚᵉ
  rational-nonzero-ℚᵉ = pr1ᵉ xᵉ

  is-nonzero-rational-nonzero-ℚᵉ : is-nonzero-ℚᵉ rational-nonzero-ℚᵉ
  is-nonzero-rational-nonzero-ℚᵉ = pr2ᵉ xᵉ

abstract
  eq-nonzero-ℚᵉ :
    {xᵉ yᵉ : nonzero-ℚᵉ} → rational-nonzero-ℚᵉ xᵉ ＝ᵉ rational-nonzero-ℚᵉ yᵉ → xᵉ ＝ᵉ yᵉ
  eq-nonzero-ℚᵉ {xᵉ} {yᵉ} = eq-type-subtypeᵉ is-nonzero-prop-ℚᵉ
```

## Properties

### A rational number is nonzero if and only if its numerator is a nonzero integer

```agda
module _
  (xᵉ : ℚᵉ)
  where

  abstract
    is-nonzero-numerator-is-nonzero-ℚᵉ :
      is-nonzero-ℚᵉ xᵉ → is-nonzero-ℤᵉ (numerator-ℚᵉ xᵉ)
    is-nonzero-numerator-is-nonzero-ℚᵉ Hᵉ =
      Hᵉ ∘ᵉ (is-zero-is-zero-numerator-ℚᵉ xᵉ)

    is-nonzero-is-nonzero-numerator-ℚᵉ :
      is-nonzero-ℤᵉ (numerator-ℚᵉ xᵉ) → is-nonzero-ℚᵉ xᵉ
    is-nonzero-is-nonzero-numerator-ℚᵉ Hᵉ = Hᵉ ∘ᵉ (apᵉ numerator-ℚᵉ)
```

### one-ℚ is nonzero

```agda
abstract
  is-nonzero-one-ℚᵉ : is-nonzero-ℚᵉ one-ℚᵉ
  is-nonzero-one-ℚᵉ =
    is-nonzero-is-nonzero-numerator-ℚᵉ
      ( one-ℚᵉ)
      ( is-nonzero-one-ℤᵉ)

one-nonzero-ℚᵉ : nonzero-ℚᵉ
one-nonzero-ℚᵉ = (one-ℚᵉ ,ᵉ is-nonzero-one-ℚᵉ)
```

### The negative of a nonzero rational number is nonzero

```agda
abstract
  is-nonzero-neg-ℚᵉ : {xᵉ : ℚᵉ} → is-nonzero-ℚᵉ xᵉ → is-nonzero-ℚᵉ (neg-ℚᵉ xᵉ)
  is-nonzero-neg-ℚᵉ {xᵉ} Hᵉ =
    is-nonzero-is-nonzero-numerator-ℚᵉ
      ( neg-ℚᵉ xᵉ)
      ( is-nonzero-neg-nonzero-ℤᵉ
        ( numerator-ℚᵉ xᵉ)
        ( is-nonzero-numerator-is-nonzero-ℚᵉ xᵉ Hᵉ))
```

### The nonzero negative of a nonzero rational number

```agda
neg-nonzero-ℚᵉ : nonzero-ℚᵉ → nonzero-ℚᵉ
neg-nonzero-ℚᵉ (xᵉ ,ᵉ Hᵉ) = (neg-ℚᵉ xᵉ ,ᵉ is-nonzero-neg-ℚᵉ Hᵉ)
```

### The product of two nonzero rational numbers is nonzero

```agda
abstract
  is-nonzero-mul-ℚᵉ :
    {xᵉ yᵉ : ℚᵉ} → is-nonzero-ℚᵉ xᵉ → is-nonzero-ℚᵉ yᵉ → is-nonzero-ℚᵉ (xᵉ *ℚᵉ yᵉ)
  is-nonzero-mul-ℚᵉ {xᵉ} {yᵉ} Hᵉ Kᵉ =
    rec-coproductᵉ Hᵉ Kᵉ ∘ᵉ (decide-is-zero-factor-is-zero-mul-ℚᵉ xᵉ yᵉ)
```

### The nonzero rational numbers are a multiplicative submonoid of the rational numbers

```agda
is-submonoid-mul-nonzero-ℚᵉ :
  is-submonoid-subset-Monoidᵉ monoid-mul-ℚᵉ is-nonzero-prop-ℚᵉ
pr1ᵉ is-submonoid-mul-nonzero-ℚᵉ = is-nonzero-one-ℚᵉ
pr2ᵉ is-submonoid-mul-nonzero-ℚᵉ xᵉ yᵉ = is-nonzero-mul-ℚᵉ {xᵉ} {yᵉ}

submonoid-mul-nonzero-ℚᵉ : Submonoidᵉ lzero monoid-mul-ℚᵉ
pr1ᵉ submonoid-mul-nonzero-ℚᵉ = is-nonzero-prop-ℚᵉ
pr2ᵉ submonoid-mul-nonzero-ℚᵉ = is-submonoid-mul-nonzero-ℚᵉ
```

### The factors of a nonzero product of rational numbers are nonzero

```agda
abstract
  is-nonzero-left-factor-mul-ℚᵉ :
    (xᵉ yᵉ : ℚᵉ) → is-nonzero-ℚᵉ (xᵉ *ℚᵉ yᵉ) → is-nonzero-ℚᵉ xᵉ
  is-nonzero-left-factor-mul-ℚᵉ xᵉ yᵉ Hᵉ Zᵉ =
    Hᵉ (apᵉ (_*ℚᵉ yᵉ) Zᵉ ∙ᵉ left-zero-law-mul-ℚᵉ yᵉ)

  is-nonzero-right-factor-mul-ℚᵉ :
    (xᵉ yᵉ : ℚᵉ) → is-nonzero-ℚᵉ (xᵉ *ℚᵉ yᵉ) → is-nonzero-ℚᵉ yᵉ
  is-nonzero-right-factor-mul-ℚᵉ xᵉ yᵉ Hᵉ Zᵉ =
    Hᵉ (apᵉ (xᵉ *ℚᵉ_) Zᵉ ∙ᵉ right-zero-law-mul-ℚᵉ xᵉ)
```