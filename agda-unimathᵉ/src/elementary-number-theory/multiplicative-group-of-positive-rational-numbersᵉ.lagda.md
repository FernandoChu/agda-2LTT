# The multiplicative group of positive rational numbers

```agda
{-# OPTIONSᵉ --lossy-unificationᵉ #-}

module elementary-number-theory.multiplicative-group-of-positive-rational-numbersᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.multiplication-rational-numbersᵉ
open import elementary-number-theory.multiplicative-monoid-of-rational-numbersᵉ
open import elementary-number-theory.positive-rational-numbersᵉ
open import elementary-number-theory.rational-numbersᵉ

open import foundation.cartesian-product-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ

open import group-theory.abelian-groupsᵉ
open import group-theory.groupsᵉ
open import group-theory.monoidsᵉ
open import group-theory.submonoidsᵉ
```

</details>

## Idea

Theᵉ [submonoid](group-theory.submonoids.mdᵉ) ofᵉ
[positiveᵉ rationalᵉ numbers](elementary-number-theory.positive-rational-numbers.mdᵉ)
in theᵉ
[multiplicativeᵉ monoidᵉ ofᵉ rationalᵉ numbers](elementary-number-theory.multiplicative-monoid-of-rational-numbers.mdᵉ)
isᵉ aᵉ [commutativeᵉ group](group-theory.abelian-groups.md).ᵉ

## Definitions

### The positive inverse of a positive rational number

```agda
inv-ℚ⁺ᵉ : ℚ⁺ᵉ → ℚ⁺ᵉ
pr1ᵉ (inv-ℚ⁺ᵉ (xᵉ ,ᵉ Pᵉ)) = inv-is-positive-ℚᵉ xᵉ Pᵉ
pr2ᵉ (inv-ℚ⁺ᵉ (xᵉ ,ᵉ Pᵉ)) = is-positive-denominator-ℚᵉ xᵉ
```

### The multiplicative group of positive rational numbers

```agda
group-mul-ℚ⁺ᵉ : Groupᵉ lzero
pr1ᵉ group-mul-ℚ⁺ᵉ = semigroup-Submonoidᵉ monoid-mul-ℚᵉ submonoid-mul-ℚ⁺ᵉ
pr1ᵉ (pr2ᵉ group-mul-ℚ⁺ᵉ) = is-unital-Monoidᵉ monoid-mul-ℚ⁺ᵉ
pr1ᵉ (pr2ᵉ (pr2ᵉ group-mul-ℚ⁺ᵉ)) = inv-ℚ⁺ᵉ
pr1ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ group-mul-ℚ⁺ᵉ))) xᵉ =
  eq-ℚ⁺ᵉ
    ( left-inverse-law-mul-is-positive-ℚᵉ
      ( rational-ℚ⁺ᵉ xᵉ)
      ( is-positive-rational-ℚ⁺ᵉ xᵉ))
pr2ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ group-mul-ℚ⁺ᵉ))) xᵉ =
  eq-ℚ⁺ᵉ
    ( right-inverse-law-mul-is-positive-ℚᵉ
      ( rational-ℚ⁺ᵉ xᵉ)
      ( is-positive-rational-ℚ⁺ᵉ xᵉ))
```

### Inverse laws in the multiplicative group of positive rational numbers

```agda
left-inverse-law-mul-ℚ⁺ᵉ : (xᵉ : ℚ⁺ᵉ) → (inv-ℚ⁺ᵉ xᵉ) *ℚ⁺ᵉ xᵉ ＝ᵉ one-ℚ⁺ᵉ
left-inverse-law-mul-ℚ⁺ᵉ = left-inverse-law-mul-Groupᵉ group-mul-ℚ⁺ᵉ

right-inverse-law-mul-ℚ⁺ᵉ : (xᵉ : ℚ⁺ᵉ) → xᵉ *ℚ⁺ᵉ (inv-ℚ⁺ᵉ xᵉ) ＝ᵉ one-ℚ⁺ᵉ
right-inverse-law-mul-ℚ⁺ᵉ = right-inverse-law-mul-Groupᵉ group-mul-ℚ⁺ᵉ
```

## Properties

### The multiplicative group of positive rational numbers is commutative

```agda
abelian-group-mul-ℚ⁺ᵉ : Abᵉ lzero
pr1ᵉ abelian-group-mul-ℚ⁺ᵉ = group-mul-ℚ⁺ᵉ
pr2ᵉ abelian-group-mul-ℚ⁺ᵉ = commutative-mul-ℚ⁺ᵉ
```