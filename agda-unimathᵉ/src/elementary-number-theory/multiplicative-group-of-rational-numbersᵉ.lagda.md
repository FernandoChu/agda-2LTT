# The multiplicative group of rational numbers

```agda
{-# OPTIONSᵉ --lossy-unificationᵉ #-}

module elementary-number-theory.multiplicative-group-of-rational-numbersᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.multiplicative-monoid-of-rational-numbersᵉ
open import elementary-number-theory.nonzero-rational-numbersᵉ
open import elementary-number-theory.positive-rational-numbersᵉ
open import elementary-number-theory.rational-numbersᵉ
open import elementary-number-theory.ring-of-rational-numbersᵉ

open import foundation.coproduct-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.function-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.subtypesᵉ
open import foundation.universe-levelsᵉ

open import group-theory.abelian-groupsᵉ
open import group-theory.cores-monoidsᵉ
open import group-theory.groupsᵉ
open import group-theory.submonoids-commutative-monoidsᵉ

open import ring-theory.groups-of-units-ringsᵉ
open import ring-theory.invertible-elements-ringsᵉ
open import ring-theory.trivial-ringsᵉ
```

</details>

## Idea

Theᵉ multiplicativeᵉ groupᵉ ofᵉ rationalᵉ numbersᵉ isᵉ theᵉ
[groupᵉ ofᵉ units](ring-theory.groups-of-units-rings.mdᵉ) ofᵉ theᵉ
[ringᵉ ofᵉ rationalᵉ numbers](elementary-number-theory.ring-of-rational-numbers.md),ᵉ
in otherᵉ words,ᵉ itᵉ isᵉ theᵉ [core](group-theory.cores-monoids.mdᵉ) ofᵉ theᵉ
[multiplicativeᵉ monoidᵉ ofᵉ rationalᵉ numbers](elementary-number-theory.multiplicative-monoid-of-rational-numbers.md).ᵉ

## Definitions

### The multiplicative group of rational numbers

```agda
group-of-units-ℚᵉ : Groupᵉ lzero
group-of-units-ℚᵉ = group-of-units-Ringᵉ ring-ℚᵉ

group-mul-ℚˣᵉ : Groupᵉ lzero
group-mul-ℚˣᵉ = group-of-units-Ringᵉ ring-ℚᵉ
```

### The type of invertible rational numbers

```agda
ℚˣᵉ : UUᵉ lzero
ℚˣᵉ = type-group-of-units-Ringᵉ ring-ℚᵉ

one-ℚˣᵉ : ℚˣᵉ
one-ℚˣᵉ = unit-group-of-units-Ringᵉ ring-ℚᵉ
```

### Operations of the multiplicative group of rational numbers

```agda
mul-ℚˣᵉ : ℚˣᵉ → ℚˣᵉ → ℚˣᵉ
mul-ℚˣᵉ = mul-group-of-units-Ringᵉ ring-ℚᵉ

infixl 40 _*ℚˣᵉ_
_*ℚˣᵉ_ = mul-ℚˣᵉ

inv-ℚˣᵉ : ℚˣᵉ → ℚˣᵉ
inv-ℚˣᵉ = inv-group-of-units-Ringᵉ ring-ℚᵉ
```

### Inverse laws in the multiplicative group of rational numbers

```agda
left-inverse-law-mul-ℚˣᵉ : (xᵉ : ℚˣᵉ) → (inv-ℚˣᵉ xᵉ) *ℚˣᵉ xᵉ ＝ᵉ one-ℚˣᵉ
left-inverse-law-mul-ℚˣᵉ = left-inverse-law-mul-group-of-units-Ringᵉ ring-ℚᵉ

right-inverse-law-mul-ℚˣᵉ : (xᵉ : ℚˣᵉ) → xᵉ *ℚˣᵉ (inv-ℚˣᵉ xᵉ) ＝ᵉ one-ℚˣᵉ
right-inverse-law-mul-ℚˣᵉ = right-inverse-law-mul-group-of-units-Ringᵉ ring-ℚᵉ
```

### Associativity law in the multiplicative group of rational numbers

```agda
associative-mul-ℚˣᵉ : (xᵉ yᵉ zᵉ : ℚˣᵉ) → ((xᵉ *ℚˣᵉ yᵉ) *ℚˣᵉ zᵉ) ＝ᵉ (xᵉ *ℚˣᵉ (yᵉ *ℚˣᵉ zᵉ))
associative-mul-ℚˣᵉ = associative-mul-Groupᵉ group-mul-ℚˣᵉ
```

## Properties

### The multiplicative group of rational numbers is commutative

```agda
commutative-mul-ℚˣᵉ : (xᵉ yᵉ : ℚˣᵉ) → (xᵉ *ℚˣᵉ yᵉ) ＝ᵉ (yᵉ *ℚˣᵉ xᵉ)
commutative-mul-ℚˣᵉ =
  commutative-mul-Commutative-Submonoidᵉ
    ( commutative-monoid-mul-ℚᵉ)
    ( submonoid-core-Monoidᵉ monoid-mul-ℚᵉ)

abelian-group-mul-ℚˣᵉ : Abᵉ lzero
pr1ᵉ abelian-group-mul-ℚˣᵉ = group-mul-ℚˣᵉ
pr2ᵉ abelian-group-mul-ℚˣᵉ = commutative-mul-ℚˣᵉ
```

### The elements of the multiplicative group of the rational numbers are the nonzero rational numbers

```agda
module _
  (xᵉ : ℚᵉ)
  where

  is-nonzero-is-invertible-element-ring-ℚᵉ :
    is-invertible-element-Ringᵉ ring-ℚᵉ xᵉ → is-nonzero-ℚᵉ xᵉ
  is-nonzero-is-invertible-element-ring-ℚᵉ Hᵉ Kᵉ =
    is-nonzero-is-invertible-element-nontrivial-Ringᵉ
      ( ring-ℚᵉ)
      ( is-nonzero-one-ℚᵉ ∘ᵉ invᵉ)
      ( xᵉ)
      ( Hᵉ)
      ( invᵉ Kᵉ)

  is-invertible-element-ring-is-nonzero-ℚᵉ :
    is-nonzero-ℚᵉ xᵉ → is-invertible-element-Ringᵉ ring-ℚᵉ xᵉ
  is-invertible-element-ring-is-nonzero-ℚᵉ Hᵉ =
    rec-coproductᵉ
      ( ( is-invertible-element-neg-Ring'ᵉ ring-ℚᵉ xᵉ) ∘ᵉ
        ( is-mul-invertible-is-positive-ℚᵉ (neg-ℚᵉ xᵉ)))
      ( is-mul-invertible-is-positive-ℚᵉ xᵉ)
      ( decide-is-negative-is-positive-is-nonzero-ℚᵉ Hᵉ)

eq-is-invertible-element-prop-is-nonzero-prop-ℚᵉ :
  is-nonzero-prop-ℚᵉ ＝ᵉ is-invertible-element-prop-Ringᵉ ring-ℚᵉ
eq-is-invertible-element-prop-is-nonzero-prop-ℚᵉ =
  antisymmetric-leq-subtypeᵉ
    ( is-nonzero-prop-ℚᵉ)
    ( is-invertible-element-prop-Ringᵉ ring-ℚᵉ)
    ( is-invertible-element-ring-is-nonzero-ℚᵉ)
    ( is-nonzero-is-invertible-element-ring-ℚᵉ)
```