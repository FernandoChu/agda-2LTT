# The binomial theorem for the natural numbers

```agda
module elementary-number-theory.binomial-theorem-natural-numbersᵉ where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.binomial-theorem-commutative-semiringsᵉ

open import elementary-number-theory.addition-natural-numbersᵉ
open import elementary-number-theory.commutative-semiring-of-natural-numbersᵉ
open import elementary-number-theory.distance-natural-numbersᵉ
open import elementary-number-theory.exponentiation-natural-numbersᵉ
open import elementary-number-theory.multiplication-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ

open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ

open import linear-algebra.vectorsᵉ

open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Theᵉ binomialᵉ theoremᵉ forᵉ naturalᵉ numbersᵉ assertsᵉ thatᵉ forᵉ anyᵉ twoᵉ naturalᵉ
numbersᵉ `x`ᵉ andᵉ `y`ᵉ andᵉ anyᵉ naturalᵉ numberᵉ `n`,ᵉ weᵉ haveᵉ

```text
  (xᵉ +ᵉ y)ⁿᵉ = ∑_{0ᵉ ≤ᵉ iᵉ <ᵉ n+1ᵉ} (nᵉ chooseᵉ iᵉ) xⁱᵉ yⁿ⁻ⁱ.ᵉ
```

## Definitions

### Binomial sums

```agda
binomial-sum-ℕᵉ : (nᵉ : ℕᵉ) (fᵉ : functional-vecᵉ ℕᵉ (succ-ℕᵉ nᵉ)) → ℕᵉ
binomial-sum-ℕᵉ = binomial-sum-Commutative-Semiringᵉ ℕ-Commutative-Semiringᵉ
```

## Properties

### Binomial sums of one and two elements

```agda
binomial-sum-one-element-ℕᵉ :
  (fᵉ : functional-vecᵉ ℕᵉ 1ᵉ) → binomial-sum-ℕᵉ 0 fᵉ ＝ᵉ head-functional-vecᵉ 0 fᵉ
binomial-sum-one-element-ℕᵉ =
  binomial-sum-one-element-Commutative-Semiringᵉ ℕ-Commutative-Semiringᵉ

binomial-sum-two-elements-ℕᵉ :
  (fᵉ : functional-vecᵉ ℕᵉ 2ᵉ) →
  binomial-sum-ℕᵉ 1 fᵉ ＝ᵉ (fᵉ (zero-Finᵉ 1ᵉ)) +ℕᵉ (fᵉ (one-Finᵉ 1ᵉ))
binomial-sum-two-elements-ℕᵉ =
  binomial-sum-two-elements-Commutative-Semiringᵉ ℕ-Commutative-Semiringᵉ
```

### Binomial sums are homotopy invariant

```agda
htpy-binomial-sum-ℕᵉ :
  (nᵉ : ℕᵉ) {fᵉ gᵉ : functional-vecᵉ ℕᵉ (succ-ℕᵉ nᵉ)} →
  (fᵉ ~ᵉ gᵉ) → binomial-sum-ℕᵉ nᵉ fᵉ ＝ᵉ binomial-sum-ℕᵉ nᵉ gᵉ
htpy-binomial-sum-ℕᵉ =
  htpy-binomial-sum-Commutative-Semiringᵉ ℕ-Commutative-Semiringᵉ
```

### Multiplication distributes over sums

```agda
left-distributive-mul-binomial-sum-ℕᵉ :
  (nᵉ : ℕᵉ) (xᵉ : ℕᵉ) (fᵉ : functional-vecᵉ ℕᵉ (succ-ℕᵉ nᵉ)) →
  xᵉ *ℕᵉ (binomial-sum-ℕᵉ nᵉ fᵉ) ＝ᵉ binomial-sum-ℕᵉ nᵉ (λ iᵉ → xᵉ *ℕᵉ (fᵉ iᵉ))
left-distributive-mul-binomial-sum-ℕᵉ =
  left-distributive-mul-binomial-sum-Commutative-Semiringᵉ ℕ-Commutative-Semiringᵉ

right-distributive-mul-binomial-sum-ℕᵉ :
  (nᵉ : ℕᵉ) (fᵉ : functional-vecᵉ ℕᵉ (succ-ℕᵉ nᵉ)) (xᵉ : ℕᵉ) →
  (binomial-sum-ℕᵉ nᵉ fᵉ) *ℕᵉ xᵉ ＝ᵉ binomial-sum-ℕᵉ nᵉ (λ iᵉ → (fᵉ iᵉ) *ℕᵉ xᵉ)
right-distributive-mul-binomial-sum-ℕᵉ =
  right-distributive-mul-binomial-sum-Commutative-Semiringᵉ
    ℕ-Commutative-Semiringᵉ
```

## Theorem

### Binomial theorem for the natural numbers

```agda
binomial-theorem-ℕᵉ :
  (nᵉ : ℕᵉ) (xᵉ yᵉ : ℕᵉ) →
  power-ℕᵉ nᵉ (xᵉ +ℕᵉ yᵉ) ＝ᵉ
  binomial-sum-ℕᵉ nᵉ
    ( λ iᵉ →
      ( power-ℕᵉ (nat-Finᵉ (succ-ℕᵉ nᵉ) iᵉ) xᵉ) *ℕᵉ
      ( power-ℕᵉ (dist-ℕᵉ (nat-Finᵉ (succ-ℕᵉ nᵉ) iᵉ) nᵉ) yᵉ))
binomial-theorem-ℕᵉ =
  binomial-theorem-Commutative-Semiringᵉ ℕ-Commutative-Semiringᵉ
```