# The multiplicative monoid of rational numbers

```agda
{-# OPTIONSᵉ --lossy-unificationᵉ #-}

module elementary-number-theory.multiplicative-monoid-of-rational-numbersᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.multiplication-rational-numbersᵉ
open import elementary-number-theory.rational-numbersᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.unital-binary-operationsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.commutative-monoidsᵉ
open import group-theory.monoidsᵉ
open import group-theory.semigroupsᵉ
```

</details>

## Idea

Theᵉ typeᵉ ofᵉ [rationalᵉ numbers](elementary-number-theory.rational-numbers.mdᵉ)
equippedᵉ with
[multiplication](elementary-number-theory.addition-rational-numbers.mdᵉ) isᵉ aᵉ
[commutativeᵉ monoid](group-theory.commutative-monoids.mdᵉ) with unitᵉ `one-ℚ`.ᵉ

## Definitions

### The multiplicative monoid of rational numbers

```agda
semigroup-mul-ℚᵉ : Semigroupᵉ lzero
pr1ᵉ semigroup-mul-ℚᵉ = ℚ-Setᵉ
pr1ᵉ (pr2ᵉ semigroup-mul-ℚᵉ) = mul-ℚᵉ
pr2ᵉ (pr2ᵉ semigroup-mul-ℚᵉ) = associative-mul-ℚᵉ

is-unital-mul-ℚᵉ : is-unitalᵉ mul-ℚᵉ
pr1ᵉ is-unital-mul-ℚᵉ = one-ℚᵉ
pr1ᵉ (pr2ᵉ is-unital-mul-ℚᵉ) = left-unit-law-mul-ℚᵉ
pr2ᵉ (pr2ᵉ is-unital-mul-ℚᵉ) = right-unit-law-mul-ℚᵉ

monoid-mul-ℚᵉ : Monoidᵉ lzero
pr1ᵉ monoid-mul-ℚᵉ = semigroup-mul-ℚᵉ
pr2ᵉ monoid-mul-ℚᵉ = is-unital-mul-ℚᵉ
```

## Properties

### The multiplicative monoid of rational numbers is commutative

```agda
commutative-monoid-mul-ℚᵉ : Commutative-Monoidᵉ lzero
pr1ᵉ commutative-monoid-mul-ℚᵉ = monoid-mul-ℚᵉ
pr2ᵉ commutative-monoid-mul-ℚᵉ = commutative-mul-ℚᵉ
```