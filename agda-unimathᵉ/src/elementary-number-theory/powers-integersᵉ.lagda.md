# Powers of integers

```agda
module elementary-number-theory.powers-integersᵉ where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.powers-of-elements-commutative-ringsᵉ

open import elementary-number-theory.integersᵉ
open import elementary-number-theory.multiplication-integersᵉ
open import elementary-number-theory.natural-numbersᵉ
open import elementary-number-theory.ring-of-integersᵉ

open import foundation.identity-typesᵉ
```

</details>

## Idea

Theᵉ powerᵉ operationᵉ onᵉ theᵉ integersᵉ isᵉ theᵉ mapᵉ `nᵉ xᵉ ↦ᵉ xⁿ`,ᵉ whichᵉ isᵉ definedᵉ byᵉ
iterativelyᵉ multiplyingᵉ `x`ᵉ with itselfᵉ `n`ᵉ times.ᵉ

## Definition

```agda
power-ℤᵉ : ℕᵉ → ℤᵉ → ℤᵉ
power-ℤᵉ = power-Commutative-Ringᵉ ℤ-Commutative-Ringᵉ
```

## Properties

### `xⁿ⁺¹ = xⁿx`

```agda
power-succ-ℤᵉ : (nᵉ : ℕᵉ) (xᵉ : ℤᵉ) → power-ℤᵉ (succ-ℕᵉ nᵉ) xᵉ ＝ᵉ (power-ℤᵉ nᵉ xᵉ) *ℤᵉ xᵉ
power-succ-ℤᵉ = power-succ-Commutative-Ringᵉ ℤ-Commutative-Ringᵉ
```