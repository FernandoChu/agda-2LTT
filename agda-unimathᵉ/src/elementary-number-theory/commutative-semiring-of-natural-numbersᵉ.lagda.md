# The commutative semiring of natural numbers

```agda
module elementary-number-theory.commutative-semiring-of-natural-numbersᵉ where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-semiringsᵉ

open import elementary-number-theory.monoid-of-natural-numbers-with-additionᵉ
open import elementary-number-theory.multiplication-natural-numbersᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import ring-theory.semiringsᵉ
```

</details>

## Definition

### The commutative semiring of natural numbers

```agda
has-mul-ℕ-Commutative-Monoidᵉ :
  has-mul-Commutative-Monoidᵉ ℕ-Commutative-Monoidᵉ
pr1ᵉ (pr1ᵉ has-mul-ℕ-Commutative-Monoidᵉ) = mul-ℕᵉ
pr2ᵉ (pr1ᵉ has-mul-ℕ-Commutative-Monoidᵉ) = associative-mul-ℕᵉ
pr1ᵉ (pr1ᵉ (pr2ᵉ has-mul-ℕ-Commutative-Monoidᵉ)) = 1
pr1ᵉ (pr2ᵉ (pr1ᵉ (pr2ᵉ has-mul-ℕ-Commutative-Monoidᵉ))) = left-unit-law-mul-ℕᵉ
pr2ᵉ (pr2ᵉ (pr1ᵉ (pr2ᵉ has-mul-ℕ-Commutative-Monoidᵉ))) = right-unit-law-mul-ℕᵉ
pr1ᵉ (pr2ᵉ (pr2ᵉ has-mul-ℕ-Commutative-Monoidᵉ)) = left-distributive-mul-add-ℕᵉ
pr2ᵉ (pr2ᵉ (pr2ᵉ has-mul-ℕ-Commutative-Monoidᵉ)) = right-distributive-mul-add-ℕᵉ

ℕ-Semiringᵉ : Semiringᵉ lzero
pr1ᵉ ℕ-Semiringᵉ = ℕ-Commutative-Monoidᵉ
pr1ᵉ (pr2ᵉ ℕ-Semiringᵉ) = has-mul-ℕ-Commutative-Monoidᵉ
pr1ᵉ (pr2ᵉ (pr2ᵉ ℕ-Semiringᵉ)) = left-zero-law-mul-ℕᵉ
pr2ᵉ (pr2ᵉ (pr2ᵉ ℕ-Semiringᵉ)) = right-zero-law-mul-ℕᵉ

ℕ-Commutative-Semiringᵉ : Commutative-Semiringᵉ lzero
pr1ᵉ ℕ-Commutative-Semiringᵉ = ℕ-Semiringᵉ
pr2ᵉ ℕ-Commutative-Semiringᵉ = commutative-mul-ℕᵉ
```