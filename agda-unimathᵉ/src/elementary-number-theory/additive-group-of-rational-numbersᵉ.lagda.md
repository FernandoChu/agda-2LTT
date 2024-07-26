# The additive group of rational numbers

```agda
{-# OPTIONSᵉ --lossy-unificationᵉ #-}

module elementary-number-theory.additive-group-of-rational-numbersᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-rational-numbersᵉ
open import elementary-number-theory.rational-numbersᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.unital-binary-operationsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.abelian-groupsᵉ
open import group-theory.groupsᵉ
open import group-theory.monoidsᵉ
open import group-theory.semigroupsᵉ
```

</details>

## Idea

Theᵉ typeᵉ ofᵉ [rationalᵉ numbers](elementary-number-theory.rational-numbers.mdᵉ)
equippedᵉ with [addition](elementary-number-theory.addition-rational-numbers.mdᵉ)
isᵉ aᵉ [commutativeᵉ group](group-theory.abelian-groups.mdᵉ) with unitᵉ `zero-ℚ`ᵉ andᵉ
inverseᵉ givenᵉ by`neg-ℚ`.ᵉ

## Definitions

### The additive abelian group of rational numbers

```agda
semigroup-add-ℚᵉ : Semigroupᵉ lzero
pr1ᵉ semigroup-add-ℚᵉ = ℚ-Setᵉ
pr1ᵉ (pr2ᵉ semigroup-add-ℚᵉ) = add-ℚᵉ
pr2ᵉ (pr2ᵉ semigroup-add-ℚᵉ) = associative-add-ℚᵉ

is-unital-add-ℚᵉ : is-unitalᵉ add-ℚᵉ
pr1ᵉ is-unital-add-ℚᵉ = zero-ℚᵉ
pr1ᵉ (pr2ᵉ is-unital-add-ℚᵉ) = left-unit-law-add-ℚᵉ
pr2ᵉ (pr2ᵉ is-unital-add-ℚᵉ) = right-unit-law-add-ℚᵉ

monoid-add-ℚᵉ : Monoidᵉ lzero
pr1ᵉ monoid-add-ℚᵉ = semigroup-add-ℚᵉ
pr2ᵉ monoid-add-ℚᵉ = is-unital-add-ℚᵉ

group-add-ℚᵉ : Groupᵉ lzero
pr1ᵉ group-add-ℚᵉ = semigroup-add-ℚᵉ
pr1ᵉ (pr2ᵉ group-add-ℚᵉ) = is-unital-add-ℚᵉ
pr1ᵉ (pr2ᵉ (pr2ᵉ group-add-ℚᵉ)) = neg-ℚᵉ
pr1ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ group-add-ℚᵉ))) = left-inverse-law-add-ℚᵉ
pr2ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ group-add-ℚᵉ))) = right-inverse-law-add-ℚᵉ
```

## Properties

### Tha additive group of rational numbers is commutative

```agda
abelian-group-add-ℚᵉ : Abᵉ lzero
pr1ᵉ abelian-group-add-ℚᵉ = group-add-ℚᵉ
pr2ᵉ abelian-group-add-ℚᵉ = commutative-add-ℚᵉ
```