# Powers of elements in commutative rings

```agda
module commutative-algebra.powers-of-elements-commutative-ringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-ringsᵉ

open import elementary-number-theory.addition-natural-numbersᵉ
open import elementary-number-theory.multiplication-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ
open import elementary-number-theory.parity-natural-numbersᵉ

open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ

open import ring-theory.powers-of-elements-ringsᵉ
```

</details>

## Idea

Theᵉ **powerᵉ operation**ᵉ onᵉ aᵉ commutativeᵉ ringᵉ isᵉ theᵉ mapᵉ `nᵉ xᵉ ↦ᵉ xⁿ`,ᵉ whichᵉ isᵉ
definedᵉ byᵉ iterativelyᵉ multiplyingᵉ `x`ᵉ with itselfᵉ `n`ᵉ times.ᵉ

## Definition

```agda
power-Commutative-Ringᵉ :
  {lᵉ : Level} (Aᵉ : Commutative-Ringᵉ lᵉ) →
  ℕᵉ → type-Commutative-Ringᵉ Aᵉ → type-Commutative-Ringᵉ Aᵉ
power-Commutative-Ringᵉ Aᵉ = power-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)
```

## Properties

### `xⁿ⁺¹ = xⁿx` and `xⁿ⁺¹ ＝ xxⁿ`

```agda
module _
  {lᵉ : Level} (Aᵉ : Commutative-Ringᵉ lᵉ)
  where

  power-succ-Commutative-Ringᵉ :
    (nᵉ : ℕᵉ) (xᵉ : type-Commutative-Ringᵉ Aᵉ) →
    power-Commutative-Ringᵉ Aᵉ (succ-ℕᵉ nᵉ) xᵉ ＝ᵉ
    mul-Commutative-Ringᵉ Aᵉ (power-Commutative-Ringᵉ Aᵉ nᵉ xᵉ) xᵉ
  power-succ-Commutative-Ringᵉ =
    power-succ-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)

  power-succ-Commutative-Ring'ᵉ :
    (nᵉ : ℕᵉ) (xᵉ : type-Commutative-Ringᵉ Aᵉ) →
    power-Commutative-Ringᵉ Aᵉ (succ-ℕᵉ nᵉ) xᵉ ＝ᵉ
    mul-Commutative-Ringᵉ Aᵉ xᵉ (power-Commutative-Ringᵉ Aᵉ nᵉ xᵉ)
  power-succ-Commutative-Ring'ᵉ =
    power-succ-Ring'ᵉ (ring-Commutative-Ringᵉ Aᵉ)
```

### Powers by sums of natural numbers are products of powers

```agda
module _
  {lᵉ : Level} (Aᵉ : Commutative-Ringᵉ lᵉ)
  where

  distributive-power-add-Commutative-Ringᵉ :
    (mᵉ nᵉ : ℕᵉ) {xᵉ : type-Commutative-Ringᵉ Aᵉ} →
    power-Commutative-Ringᵉ Aᵉ (mᵉ +ℕᵉ nᵉ) xᵉ ＝ᵉ
    mul-Commutative-Ringᵉ Aᵉ
      ( power-Commutative-Ringᵉ Aᵉ mᵉ xᵉ)
      ( power-Commutative-Ringᵉ Aᵉ nᵉ xᵉ)
  distributive-power-add-Commutative-Ringᵉ =
    distributive-power-add-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)
```

### Powers by products of natural numbers are iterated powers

```agda
module _
  {lᵉ : Level} (Aᵉ : Commutative-Ringᵉ lᵉ)
  where

  power-mul-Commutative-Ringᵉ :
    (mᵉ nᵉ : ℕᵉ) {xᵉ : type-Commutative-Ringᵉ Aᵉ} →
    power-Commutative-Ringᵉ Aᵉ (mᵉ *ℕᵉ nᵉ) xᵉ ＝ᵉ
    power-Commutative-Ringᵉ Aᵉ nᵉ (power-Commutative-Ringᵉ Aᵉ mᵉ xᵉ)
  power-mul-Commutative-Ringᵉ =
    power-mul-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)
```

### Powers distribute over multiplication

```agda
module _
  {lᵉ : Level} (Aᵉ : Commutative-Ringᵉ lᵉ)
  where

  distributive-power-mul-Commutative-Ringᵉ :
    (nᵉ : ℕᵉ) (xᵉ yᵉ : type-Commutative-Ringᵉ Aᵉ) →
    power-Commutative-Ringᵉ Aᵉ nᵉ (mul-Commutative-Ringᵉ Aᵉ xᵉ yᵉ) ＝ᵉ
    mul-Commutative-Ringᵉ Aᵉ
      ( power-Commutative-Ringᵉ Aᵉ nᵉ xᵉ)
      ( power-Commutative-Ringᵉ Aᵉ nᵉ yᵉ)
  distributive-power-mul-Commutative-Ringᵉ nᵉ xᵉ yᵉ =
    distributive-power-mul-Ringᵉ
      ( ring-Commutative-Ringᵉ Aᵉ)
      ( nᵉ)
      ( commutative-mul-Commutative-Ringᵉ Aᵉ xᵉ yᵉ)
```

### `(-x)ⁿ = (-1)ⁿxⁿ`

```agda
module _
  {lᵉ : Level} (Aᵉ : Commutative-Ringᵉ lᵉ)
  where

  power-neg-Commutative-Ringᵉ :
    (nᵉ : ℕᵉ) (xᵉ : type-Commutative-Ringᵉ Aᵉ) →
    power-Commutative-Ringᵉ Aᵉ nᵉ (neg-Commutative-Ringᵉ Aᵉ xᵉ) ＝ᵉ
    mul-Commutative-Ringᵉ Aᵉ
      ( power-Commutative-Ringᵉ Aᵉ nᵉ (neg-one-Commutative-Ringᵉ Aᵉ))
      ( power-Commutative-Ringᵉ Aᵉ nᵉ xᵉ)
  power-neg-Commutative-Ringᵉ =
    power-neg-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)

  even-power-neg-Commutative-Ringᵉ :
    (nᵉ : ℕᵉ) (xᵉ : type-Commutative-Ringᵉ Aᵉ) →
    is-even-ℕᵉ nᵉ →
    power-Commutative-Ringᵉ Aᵉ nᵉ (neg-Commutative-Ringᵉ Aᵉ xᵉ) ＝ᵉ
    power-Commutative-Ringᵉ Aᵉ nᵉ xᵉ
  even-power-neg-Commutative-Ringᵉ =
    even-power-neg-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)

  odd-power-neg-Commutative-Ringᵉ :
    (nᵉ : ℕᵉ) (xᵉ : type-Commutative-Ringᵉ Aᵉ) →
    is-odd-ℕᵉ nᵉ →
    power-Commutative-Ringᵉ Aᵉ nᵉ (neg-Commutative-Ringᵉ Aᵉ xᵉ) ＝ᵉ
    neg-Commutative-Ringᵉ Aᵉ (power-Commutative-Ringᵉ Aᵉ nᵉ xᵉ)
  odd-power-neg-Commutative-Ringᵉ =
    odd-power-neg-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)
```