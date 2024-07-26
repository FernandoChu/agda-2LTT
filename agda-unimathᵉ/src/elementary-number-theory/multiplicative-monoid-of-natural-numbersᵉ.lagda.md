# The multiplicative monoid of natural numbers

```agda
module elementary-number-theory.multiplicative-monoid-of-natural-numbersᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.equality-natural-numbersᵉ
open import elementary-number-theory.multiplication-natural-numbersᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import group-theory.monoidsᵉ
open import group-theory.semigroupsᵉ
```

</details>

## Idea

Theᵉ **multiplicativeᵉ monoidᵉ ofᵉ naturalᵉ numbers**ᵉ consistsᵉ ofᵉ
[naturalᵉ numbers](elementary-number-theory.natural-numbers.md),ᵉ andᵉ isᵉ equippedᵉ
with theᵉ
[multiplicationᵉ operation](elementary-number-theory.multiplication-natural-numbers.mdᵉ)
ofᵉ theᵉ naturalᵉ numbersᵉ asᵉ itsᵉ multiplicativeᵉ structure.ᵉ

## Definitions

### The multiplicative semigroup of natural numbers

```agda
ℕ*-Semigroupᵉ : Semigroupᵉ lzero
pr1ᵉ ℕ*-Semigroupᵉ = ℕ-Setᵉ
pr1ᵉ (pr2ᵉ ℕ*-Semigroupᵉ) = mul-ℕᵉ
pr2ᵉ (pr2ᵉ ℕ*-Semigroupᵉ) = associative-mul-ℕᵉ
```

### The multiplicative monoid of natural numbers

```agda
ℕ*-Monoidᵉ : Monoidᵉ lzero
pr1ᵉ ℕ*-Monoidᵉ = ℕ*-Semigroupᵉ
pr1ᵉ (pr2ᵉ ℕ*-Monoidᵉ) = 1
pr1ᵉ (pr2ᵉ (pr2ᵉ ℕ*-Monoidᵉ)) = left-unit-law-mul-ℕᵉ
pr2ᵉ (pr2ᵉ (pr2ᵉ ℕ*-Monoidᵉ)) = right-unit-law-mul-ℕᵉ
```