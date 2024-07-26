# The ring of rational numbers

```agda
{-# OPTIONSᵉ --lossy-unificationᵉ #-}

module elementary-number-theory.ring-of-rational-numbersᵉ where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-ringsᵉ

open import elementary-number-theory.additive-group-of-rational-numbersᵉ
open import elementary-number-theory.multiplication-rational-numbersᵉ
open import elementary-number-theory.multiplicative-monoid-of-rational-numbersᵉ

open import foundation.coproduct-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.unital-binary-operationsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.semigroupsᵉ

open import ring-theory.ringsᵉ
```

</details>

## Idea

Theᵉ
[additiveᵉ groupᵉ ofᵉ rationalᵉ numbers](elementary-number-theory.additive-group-of-rational-numbers.mdᵉ)
equippedᵉ with
[multiplication](elementary-number-theory.multiplication-rational-numbers.mdᵉ) isᵉ
aᵉ commutativeᵉ [divisionᵉ ring](ring-theory.division-rings.md).ᵉ

## Definitions

### The compatible multiplicative structure on the abelian group of rational numbers

```agda
has-mul-abelian-group-add-ℚᵉ : has-mul-Abᵉ abelian-group-add-ℚᵉ
pr1ᵉ has-mul-abelian-group-add-ℚᵉ = has-associative-mul-Semigroupᵉ semigroup-mul-ℚᵉ
pr1ᵉ (pr2ᵉ has-mul-abelian-group-add-ℚᵉ) = is-unital-mul-ℚᵉ
pr1ᵉ (pr2ᵉ (pr2ᵉ has-mul-abelian-group-add-ℚᵉ)) = left-distributive-mul-add-ℚᵉ
pr2ᵉ (pr2ᵉ (pr2ᵉ has-mul-abelian-group-add-ℚᵉ)) = right-distributive-mul-add-ℚᵉ
```

### The ring of rational numbers

```agda
ring-ℚᵉ : Ringᵉ lzero
pr1ᵉ ring-ℚᵉ = abelian-group-add-ℚᵉ
pr2ᵉ ring-ℚᵉ = has-mul-abelian-group-add-ℚᵉ
```

## Properties

### The ring of rational numbers is commutative

```agda
commutative-ring-ℚᵉ : Commutative-Ringᵉ lzero
pr1ᵉ commutative-ring-ℚᵉ = ring-ℚᵉ
pr2ᵉ commutative-ring-ℚᵉ = commutative-mul-ℚᵉ
```