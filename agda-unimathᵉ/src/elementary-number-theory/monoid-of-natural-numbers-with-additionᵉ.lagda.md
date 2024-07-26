# The monoid of natural numbers with addition

```agda
module elementary-number-theory.monoid-of-natural-numbers-with-additionᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbersᵉ
open import elementary-number-theory.equality-natural-numbersᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import group-theory.commutative-monoidsᵉ
open import group-theory.monoidsᵉ
open import group-theory.semigroupsᵉ
```

</details>

## Idea

Theᵉ naturalᵉ numbersᵉ equippedᵉ with `0`ᵉ andᵉ additionᵉ isᵉ aᵉ commutativeᵉ monoid.ᵉ

## Definitions

### The Semigroup of natural numbers

```agda
ℕ-Semigroupᵉ : Semigroupᵉ lzero
pr1ᵉ ℕ-Semigroupᵉ = ℕ-Setᵉ
pr1ᵉ (pr2ᵉ ℕ-Semigroupᵉ) = add-ℕᵉ
pr2ᵉ (pr2ᵉ ℕ-Semigroupᵉ) = associative-add-ℕᵉ
```

### The monoid of natural numbers

```agda
ℕ-Monoidᵉ : Monoidᵉ lzero
pr1ᵉ ℕ-Monoidᵉ = ℕ-Semigroupᵉ
pr1ᵉ (pr2ᵉ ℕ-Monoidᵉ) = 0
pr1ᵉ (pr2ᵉ (pr2ᵉ ℕ-Monoidᵉ)) = left-unit-law-add-ℕᵉ
pr2ᵉ (pr2ᵉ (pr2ᵉ ℕ-Monoidᵉ)) = right-unit-law-add-ℕᵉ
```

### The commutative monoid of natural numbers

```agda
ℕ-Commutative-Monoidᵉ : Commutative-Monoidᵉ lzero
pr1ᵉ ℕ-Commutative-Monoidᵉ = ℕ-Monoidᵉ
pr2ᵉ ℕ-Commutative-Monoidᵉ = commutative-add-ℕᵉ
```