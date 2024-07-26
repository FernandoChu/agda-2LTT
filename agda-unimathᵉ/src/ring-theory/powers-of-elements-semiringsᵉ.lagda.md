# Powers of elements in semirings

```agda
module ring-theory.powers-of-elements-semiringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbersᵉ
open import elementary-number-theory.multiplication-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ

open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ

open import group-theory.powers-of-elements-monoidsᵉ

open import ring-theory.semiringsᵉ
```

</details>

## Idea

Theᵉ powerᵉ operationᵉ onᵉ aᵉ semiringᵉ isᵉ theᵉ mapᵉ `nᵉ xᵉ ↦ᵉ xⁿ`,ᵉ whichᵉ isᵉ definedᵉ byᵉ
iterativelyᵉ multiplyingᵉ `x`ᵉ with itselfᵉ `n`ᵉ times.ᵉ

## Definition

```agda
power-Semiringᵉ :
  {lᵉ : Level} (Rᵉ : Semiringᵉ lᵉ) → ℕᵉ → type-Semiringᵉ Rᵉ → type-Semiringᵉ Rᵉ
power-Semiringᵉ Rᵉ nᵉ xᵉ = power-Monoidᵉ (multiplicative-monoid-Semiringᵉ Rᵉ) nᵉ xᵉ
```

## Properties

### `1ⁿ ＝ 1`

```agda
module _
  {lᵉ : Level} (Rᵉ : Semiringᵉ lᵉ)
  where

  power-one-Semiringᵉ :
    (nᵉ : ℕᵉ) → power-Semiringᵉ Rᵉ nᵉ (one-Semiringᵉ Rᵉ) ＝ᵉ one-Semiringᵉ Rᵉ
  power-one-Semiringᵉ = power-unit-Monoidᵉ (multiplicative-monoid-Semiringᵉ Rᵉ)
```

### `xⁿ⁺¹ = xⁿx`

```agda
module _
  {lᵉ : Level} (Rᵉ : Semiringᵉ lᵉ)
  where

  power-succ-Semiringᵉ :
    (nᵉ : ℕᵉ) (xᵉ : type-Semiringᵉ Rᵉ) →
    power-Semiringᵉ Rᵉ (succ-ℕᵉ nᵉ) xᵉ ＝ᵉ mul-Semiringᵉ Rᵉ (power-Semiringᵉ Rᵉ nᵉ xᵉ) xᵉ
  power-succ-Semiringᵉ = power-succ-Monoidᵉ (multiplicative-monoid-Semiringᵉ Rᵉ)
```

### `xⁿ⁺¹ ＝ xxⁿ`

```agda
module _
  {lᵉ : Level} (Rᵉ : Semiringᵉ lᵉ)
  where

  power-succ-Semiring'ᵉ :
    (nᵉ : ℕᵉ) (xᵉ : type-Semiringᵉ Rᵉ) →
    power-Semiringᵉ Rᵉ (succ-ℕᵉ nᵉ) xᵉ ＝ᵉ mul-Semiringᵉ Rᵉ xᵉ (power-Semiringᵉ Rᵉ nᵉ xᵉ)
  power-succ-Semiring'ᵉ = power-succ-Monoid'ᵉ (multiplicative-monoid-Semiringᵉ Rᵉ)
```

### Powers by sums of natural numbers are products of powers

```agda
module _
  {lᵉ : Level} (Rᵉ : Semiringᵉ lᵉ)
  where

  distributive-power-add-Semiringᵉ :
    (mᵉ nᵉ : ℕᵉ) {xᵉ : type-Semiringᵉ Rᵉ} →
    power-Semiringᵉ Rᵉ (mᵉ +ℕᵉ nᵉ) xᵉ ＝ᵉ
    mul-Semiringᵉ Rᵉ (power-Semiringᵉ Rᵉ mᵉ xᵉ) (power-Semiringᵉ Rᵉ nᵉ xᵉ)
  distributive-power-add-Semiringᵉ =
    distributive-power-add-Monoidᵉ (multiplicative-monoid-Semiringᵉ Rᵉ)
```

### If `x` commutes with `y` then so do their powers

```agda
module _
  {lᵉ : Level} (Rᵉ : Semiringᵉ lᵉ)
  where

  commute-powers-Semiring'ᵉ :
    (nᵉ : ℕᵉ) {xᵉ yᵉ : type-Semiringᵉ Rᵉ} →
    ( mul-Semiringᵉ Rᵉ xᵉ yᵉ ＝ᵉ mul-Semiringᵉ Rᵉ yᵉ xᵉ) →
    ( mul-Semiringᵉ Rᵉ (power-Semiringᵉ Rᵉ nᵉ xᵉ) yᵉ) ＝ᵉ
    ( mul-Semiringᵉ Rᵉ yᵉ (power-Semiringᵉ Rᵉ nᵉ xᵉ))
  commute-powers-Semiring'ᵉ =
    commute-powers-Monoid'ᵉ (multiplicative-monoid-Semiringᵉ Rᵉ)

  commute-powers-Semiringᵉ :
    (mᵉ nᵉ : ℕᵉ) {xᵉ yᵉ : type-Semiringᵉ Rᵉ} →
    ( mul-Semiringᵉ Rᵉ xᵉ yᵉ ＝ᵉ mul-Semiringᵉ Rᵉ yᵉ xᵉ) →
    ( mul-Semiringᵉ Rᵉ
      ( power-Semiringᵉ Rᵉ mᵉ xᵉ)
      ( power-Semiringᵉ Rᵉ nᵉ yᵉ)) ＝ᵉ
    ( mul-Semiringᵉ Rᵉ
      ( power-Semiringᵉ Rᵉ nᵉ yᵉ)
      ( power-Semiringᵉ Rᵉ mᵉ xᵉ))
  commute-powers-Semiringᵉ =
    commute-powers-Monoidᵉ (multiplicative-monoid-Semiringᵉ Rᵉ)
```

### If `x` commutes with `y`, then powers distribute over the product of `x` and `y`

```agda
module _
  {lᵉ : Level} (Rᵉ : Semiringᵉ lᵉ)
  where

  distributive-power-mul-Semiringᵉ :
    (nᵉ : ℕᵉ) {xᵉ yᵉ : type-Semiringᵉ Rᵉ} →
    (Hᵉ : mul-Semiringᵉ Rᵉ xᵉ yᵉ ＝ᵉ mul-Semiringᵉ Rᵉ yᵉ xᵉ) →
    power-Semiringᵉ Rᵉ nᵉ (mul-Semiringᵉ Rᵉ xᵉ yᵉ) ＝ᵉ
    mul-Semiringᵉ Rᵉ (power-Semiringᵉ Rᵉ nᵉ xᵉ) (power-Semiringᵉ Rᵉ nᵉ yᵉ)
  distributive-power-mul-Semiringᵉ =
    distributive-power-mul-Monoidᵉ (multiplicative-monoid-Semiringᵉ Rᵉ)
```

### Powers by products of natural numbers are iterated powers

```agda
module _
  {lᵉ : Level} (Rᵉ : Semiringᵉ lᵉ)
  where

  power-mul-Semiringᵉ :
    (mᵉ nᵉ : ℕᵉ) {xᵉ : type-Semiringᵉ Rᵉ} →
    power-Semiringᵉ Rᵉ (mᵉ *ℕᵉ nᵉ) xᵉ ＝ᵉ power-Semiringᵉ Rᵉ nᵉ (power-Semiringᵉ Rᵉ mᵉ xᵉ)
  power-mul-Semiringᵉ = power-mul-Monoidᵉ (multiplicative-monoid-Semiringᵉ Rᵉ)
```