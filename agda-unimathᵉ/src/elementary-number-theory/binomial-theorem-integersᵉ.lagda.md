# The binomial theorem for the integers

```agda
module elementary-number-theory.binomial-theorem-integersᵉ where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.binomial-theorem-commutative-ringsᵉ

open import elementary-number-theory.addition-integersᵉ
open import elementary-number-theory.distance-natural-numbersᵉ
open import elementary-number-theory.integersᵉ
open import elementary-number-theory.multiplication-integersᵉ
open import elementary-number-theory.natural-numbersᵉ
open import elementary-number-theory.powers-integersᵉ
open import elementary-number-theory.ring-of-integersᵉ

open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ

open import linear-algebra.vectorsᵉ

open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Theᵉ binomialᵉ theoremᵉ forᵉ theᵉ integersᵉ assertsᵉ thatᵉ forᵉ anyᵉ twoᵉ integersᵉ `x`ᵉ andᵉ
`y`ᵉ andᵉ anyᵉ naturalᵉ numberᵉ `n`,ᵉ weᵉ haveᵉ

```text
  (xᵉ +ᵉ y)ⁿᵉ = ∑_{0ᵉ ≤ᵉ iᵉ <ᵉ n+1ᵉ} (nᵉ chooseᵉ iᵉ) xⁱᵉ yⁿ⁻ⁱ.ᵉ
```

## Definitions

### Binomial sums

```agda
binomial-sum-ℤᵉ : (nᵉ : ℕᵉ) (fᵉ : functional-vecᵉ ℤᵉ (succ-ℕᵉ nᵉ)) → ℤᵉ
binomial-sum-ℤᵉ = binomial-sum-Commutative-Ringᵉ ℤ-Commutative-Ringᵉ
```

## Properties

### Binomial sums of one and two elements

```agda
binomial-sum-one-element-ℤᵉ :
  (fᵉ : functional-vecᵉ ℤᵉ 1ᵉ) → binomial-sum-ℤᵉ 0 fᵉ ＝ᵉ head-functional-vecᵉ 0 fᵉ
binomial-sum-one-element-ℤᵉ =
  binomial-sum-one-element-Commutative-Ringᵉ ℤ-Commutative-Ringᵉ

binomial-sum-two-elements-ℤᵉ :
  (fᵉ : functional-vecᵉ ℤᵉ 2ᵉ) →
  binomial-sum-ℤᵉ 1 fᵉ ＝ᵉ (fᵉ (zero-Finᵉ 1ᵉ)) +ℤᵉ (fᵉ (one-Finᵉ 1ᵉ))
binomial-sum-two-elements-ℤᵉ =
  binomial-sum-two-elements-Commutative-Ringᵉ ℤ-Commutative-Ringᵉ
```

### Binomial sums are homotopy invariant

```agda
htpy-binomial-sum-ℤᵉ :
  (nᵉ : ℕᵉ) {fᵉ gᵉ : functional-vecᵉ ℤᵉ (succ-ℕᵉ nᵉ)} →
  (fᵉ ~ᵉ gᵉ) → binomial-sum-ℤᵉ nᵉ fᵉ ＝ᵉ binomial-sum-ℤᵉ nᵉ gᵉ
htpy-binomial-sum-ℤᵉ =
  htpy-binomial-sum-Commutative-Ringᵉ ℤ-Commutative-Ringᵉ
```

### Multiplication distributes over sums

```agda
left-distributive-mul-binomial-sum-ℤᵉ :
  (nᵉ : ℕᵉ) (xᵉ : ℤᵉ) (fᵉ : functional-vecᵉ ℤᵉ (succ-ℕᵉ nᵉ)) →
  xᵉ *ℤᵉ (binomial-sum-ℤᵉ nᵉ fᵉ) ＝ᵉ binomial-sum-ℤᵉ nᵉ (λ iᵉ → xᵉ *ℤᵉ (fᵉ iᵉ))
left-distributive-mul-binomial-sum-ℤᵉ =
  left-distributive-mul-binomial-sum-Commutative-Ringᵉ ℤ-Commutative-Ringᵉ

right-distributive-mul-binomial-sum-ℤᵉ :
  (nᵉ : ℕᵉ) (fᵉ : functional-vecᵉ ℤᵉ (succ-ℕᵉ nᵉ)) (xᵉ : ℤᵉ) →
  (binomial-sum-ℤᵉ nᵉ fᵉ) *ℤᵉ xᵉ ＝ᵉ binomial-sum-ℤᵉ nᵉ (λ iᵉ → (fᵉ iᵉ) *ℤᵉ xᵉ)
right-distributive-mul-binomial-sum-ℤᵉ =
  right-distributive-mul-binomial-sum-Commutative-Ringᵉ
    ℤ-Commutative-Ringᵉ
```

## Theorem

### Binomial theorem for the integers

```agda
binomial-theorem-ℤᵉ :
  (nᵉ : ℕᵉ) (xᵉ yᵉ : ℤᵉ) →
  power-ℤᵉ nᵉ (xᵉ +ℤᵉ yᵉ) ＝ᵉ
  binomial-sum-ℤᵉ nᵉ
    ( λ iᵉ →
        ( power-ℤᵉ (nat-Finᵉ (succ-ℕᵉ nᵉ) iᵉ) xᵉ) *ℤᵉ
        ( power-ℤᵉ (dist-ℕᵉ (nat-Finᵉ (succ-ℕᵉ nᵉ) iᵉ) nᵉ) yᵉ))
binomial-theorem-ℤᵉ = binomial-theorem-Commutative-Ringᵉ ℤ-Commutative-Ringᵉ
```