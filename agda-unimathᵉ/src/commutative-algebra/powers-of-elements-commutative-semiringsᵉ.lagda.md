# Powers of elements in commutative semirings

```agda
module commutative-algebra.powers-of-elements-commutative-semiringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-semiringsᵉ

open import elementary-number-theory.addition-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ

open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ

open import ring-theory.powers-of-elements-semiringsᵉ
```

</details>

## Idea

Theᵉ **powerᵉ operation**ᵉ onᵉ aᵉ commutativeᵉ semiringᵉ isᵉ theᵉ mapᵉ `nᵉ xᵉ ↦ᵉ xⁿ`,ᵉ whichᵉ
isᵉ definedᵉ byᵉ iterativelyᵉ multiplyingᵉ `x`ᵉ with itselfᵉ `n`ᵉ times.ᵉ

## Definition

```agda
power-Commutative-Semiringᵉ :
  {lᵉ : Level} (Aᵉ : Commutative-Semiringᵉ lᵉ) →
  ℕᵉ → type-Commutative-Semiringᵉ Aᵉ → type-Commutative-Semiringᵉ Aᵉ
power-Commutative-Semiringᵉ Aᵉ = power-Semiringᵉ (semiring-Commutative-Semiringᵉ Aᵉ)
```

## Properties

### `xⁿ⁺¹ = xⁿx`

```agda
module _
  {lᵉ : Level} (Aᵉ : Commutative-Semiringᵉ lᵉ)
  where

  power-succ-Commutative-Semiringᵉ :
    (nᵉ : ℕᵉ) (xᵉ : type-Commutative-Semiringᵉ Aᵉ) →
    power-Commutative-Semiringᵉ Aᵉ (succ-ℕᵉ nᵉ) xᵉ ＝ᵉ
    mul-Commutative-Semiringᵉ Aᵉ (power-Commutative-Semiringᵉ Aᵉ nᵉ xᵉ) xᵉ
  power-succ-Commutative-Semiringᵉ =
    power-succ-Semiringᵉ (semiring-Commutative-Semiringᵉ Aᵉ)
```

### Powers by sums of natural numbers are products of powers

```agda
module _
  {lᵉ : Level} (Aᵉ : Commutative-Semiringᵉ lᵉ)
  where

  distributive-power-add-Commutative-Semiringᵉ :
    (mᵉ nᵉ : ℕᵉ) {xᵉ : type-Commutative-Semiringᵉ Aᵉ} →
    power-Commutative-Semiringᵉ Aᵉ (mᵉ +ℕᵉ nᵉ) xᵉ ＝ᵉ
    mul-Commutative-Semiringᵉ Aᵉ
      ( power-Commutative-Semiringᵉ Aᵉ mᵉ xᵉ)
      ( power-Commutative-Semiringᵉ Aᵉ nᵉ xᵉ)
  distributive-power-add-Commutative-Semiringᵉ =
    distributive-power-add-Semiringᵉ (semiring-Commutative-Semiringᵉ Aᵉ)
```

### If `x` commutes with `y`, then powers distribute over the product of `x` and `y`

```agda
module _
  {lᵉ : Level} (Aᵉ : Commutative-Semiringᵉ lᵉ)
  where

  distributive-power-mul-Commutative-Semiringᵉ :
    (nᵉ : ℕᵉ) (xᵉ yᵉ : type-Commutative-Semiringᵉ Aᵉ) →
    power-Commutative-Semiringᵉ Aᵉ nᵉ (mul-Commutative-Semiringᵉ Aᵉ xᵉ yᵉ) ＝ᵉ
    mul-Commutative-Semiringᵉ Aᵉ
      ( power-Commutative-Semiringᵉ Aᵉ nᵉ xᵉ)
      ( power-Commutative-Semiringᵉ Aᵉ nᵉ yᵉ)
  distributive-power-mul-Commutative-Semiringᵉ nᵉ xᵉ yᵉ =
    distributive-power-mul-Semiringᵉ
      ( semiring-Commutative-Semiringᵉ Aᵉ)
      ( nᵉ)
      ( commutative-mul-Commutative-Semiringᵉ Aᵉ xᵉ yᵉ)
```