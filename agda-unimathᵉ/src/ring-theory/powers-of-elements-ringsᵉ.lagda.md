# Powers of elements in rings

```agda
module ring-theory.powers-of-elements-ringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbersᵉ
open import elementary-number-theory.multiplication-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ
open import elementary-number-theory.parity-natural-numbersᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.empty-typesᵉ
open import foundation.function-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ

open import ring-theory.central-elements-ringsᵉ
open import ring-theory.powers-of-elements-semiringsᵉ
open import ring-theory.ringsᵉ
```

</details>

## Idea

Theᵉ powerᵉ operationᵉ onᵉ aᵉ ringᵉ isᵉ theᵉ mapᵉ `nᵉ xᵉ ↦ᵉ xⁿ`,ᵉ whichᵉ isᵉ definedᵉ byᵉ
iterativelyᵉ multiplyingᵉ `x`ᵉ with itselfᵉ `n`ᵉ times.ᵉ

## Definition

```agda
power-Ringᵉ : {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ) → ℕᵉ → type-Ringᵉ Rᵉ → type-Ringᵉ Rᵉ
power-Ringᵉ Rᵉ = power-Semiringᵉ (semiring-Ringᵉ Rᵉ)
```

## Properties

### `xⁿ⁺¹ = xⁿx` and `xⁿ⁺¹ ＝ xxⁿ`

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  power-succ-Ringᵉ :
    (nᵉ : ℕᵉ) (xᵉ : type-Ringᵉ Rᵉ) →
    power-Ringᵉ Rᵉ (succ-ℕᵉ nᵉ) xᵉ ＝ᵉ mul-Ringᵉ Rᵉ (power-Ringᵉ Rᵉ nᵉ xᵉ) xᵉ
  power-succ-Ringᵉ = power-succ-Semiringᵉ (semiring-Ringᵉ Rᵉ)

  power-succ-Ring'ᵉ :
    (nᵉ : ℕᵉ) (xᵉ : type-Ringᵉ Rᵉ) →
    power-Ringᵉ Rᵉ (succ-ℕᵉ nᵉ) xᵉ ＝ᵉ mul-Ringᵉ Rᵉ xᵉ (power-Ringᵉ Rᵉ nᵉ xᵉ)
  power-succ-Ring'ᵉ = power-succ-Semiring'ᵉ (semiring-Ringᵉ Rᵉ)
```

### Powers by sums of natural numbers are products of powers

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  distributive-power-add-Ringᵉ :
    (mᵉ nᵉ : ℕᵉ) {xᵉ : type-Ringᵉ Rᵉ} →
    power-Ringᵉ Rᵉ (mᵉ +ℕᵉ nᵉ) xᵉ ＝ᵉ
    mul-Ringᵉ Rᵉ (power-Ringᵉ Rᵉ mᵉ xᵉ) (power-Ringᵉ Rᵉ nᵉ xᵉ)
  distributive-power-add-Ringᵉ =
    distributive-power-add-Semiringᵉ (semiring-Ringᵉ Rᵉ)
```

### Powers by products of natural numbers are iterated powers

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  power-mul-Ringᵉ :
    (mᵉ nᵉ : ℕᵉ) {xᵉ : type-Ringᵉ Rᵉ} →
    power-Ringᵉ Rᵉ (mᵉ *ℕᵉ nᵉ) xᵉ ＝ᵉ power-Ringᵉ Rᵉ nᵉ (power-Ringᵉ Rᵉ mᵉ xᵉ)
  power-mul-Ringᵉ = power-mul-Semiringᵉ (semiring-Ringᵉ Rᵉ)
```

### If `x` commutes with `y` then so do their powers

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  commute-powers-Ring'ᵉ :
    (nᵉ : ℕᵉ) {xᵉ yᵉ : type-Ringᵉ Rᵉ} →
    ( mul-Ringᵉ Rᵉ xᵉ yᵉ ＝ᵉ mul-Ringᵉ Rᵉ yᵉ xᵉ) →
    ( mul-Ringᵉ Rᵉ (power-Ringᵉ Rᵉ nᵉ xᵉ) yᵉ) ＝ᵉ
    ( mul-Ringᵉ Rᵉ yᵉ (power-Ringᵉ Rᵉ nᵉ xᵉ))
  commute-powers-Ring'ᵉ = commute-powers-Semiring'ᵉ (semiring-Ringᵉ Rᵉ)

  commute-powers-Ringᵉ :
    (mᵉ nᵉ : ℕᵉ) {xᵉ yᵉ : type-Ringᵉ Rᵉ} → mul-Ringᵉ Rᵉ xᵉ yᵉ ＝ᵉ mul-Ringᵉ Rᵉ yᵉ xᵉ →
    ( mul-Ringᵉ Rᵉ (power-Ringᵉ Rᵉ mᵉ xᵉ) (power-Ringᵉ Rᵉ nᵉ yᵉ)) ＝ᵉ
    ( mul-Ringᵉ Rᵉ (power-Ringᵉ Rᵉ nᵉ yᵉ) (power-Ringᵉ Rᵉ mᵉ xᵉ))
  commute-powers-Ringᵉ = commute-powers-Semiringᵉ (semiring-Ringᵉ Rᵉ)
```

### If `x` commutes with `y`, then powers distribute over the product of `x` and `y`

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  distributive-power-mul-Ringᵉ :
    (nᵉ : ℕᵉ) {xᵉ yᵉ : type-Ringᵉ Rᵉ} → mul-Ringᵉ Rᵉ xᵉ yᵉ ＝ᵉ mul-Ringᵉ Rᵉ yᵉ xᵉ →
    power-Ringᵉ Rᵉ nᵉ (mul-Ringᵉ Rᵉ xᵉ yᵉ) ＝ᵉ
    mul-Ringᵉ Rᵉ (power-Ringᵉ Rᵉ nᵉ xᵉ) (power-Ringᵉ Rᵉ nᵉ yᵉ)
  distributive-power-mul-Ringᵉ =
    distributive-power-mul-Semiringᵉ (semiring-Ringᵉ Rᵉ)
```

### `(-x)ⁿ = (-1)ⁿxⁿ`

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  power-neg-Ringᵉ :
    (nᵉ : ℕᵉ) (xᵉ : type-Ringᵉ Rᵉ) →
    power-Ringᵉ Rᵉ nᵉ (neg-Ringᵉ Rᵉ xᵉ) ＝ᵉ
    mul-Ringᵉ Rᵉ (power-Ringᵉ Rᵉ nᵉ (neg-one-Ringᵉ Rᵉ)) (power-Ringᵉ Rᵉ nᵉ xᵉ)
  power-neg-Ringᵉ nᵉ xᵉ =
    ( apᵉ (power-Ringᵉ Rᵉ nᵉ) (invᵉ (mul-neg-one-Ringᵉ Rᵉ xᵉ))) ∙ᵉ
    ( distributive-power-mul-Ringᵉ Rᵉ nᵉ (is-central-element-neg-one-Ringᵉ Rᵉ xᵉ))

  even-power-neg-Ringᵉ :
    (nᵉ : ℕᵉ) (xᵉ : type-Ringᵉ Rᵉ) →
    is-even-ℕᵉ nᵉ → power-Ringᵉ Rᵉ nᵉ (neg-Ringᵉ Rᵉ xᵉ) ＝ᵉ power-Ringᵉ Rᵉ nᵉ xᵉ
  even-power-neg-Ringᵉ zero-ℕᵉ xᵉ Hᵉ = reflᵉ
  even-power-neg-Ringᵉ (succ-ℕᵉ zero-ℕᵉ) xᵉ Hᵉ = ex-falsoᵉ (is-odd-one-ℕᵉ Hᵉ)
  even-power-neg-Ringᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)) xᵉ Hᵉ =
    ( right-negative-law-mul-Ringᵉ Rᵉ
      ( power-Ringᵉ Rᵉ (succ-ℕᵉ nᵉ) (neg-Ringᵉ Rᵉ xᵉ))
      ( xᵉ)) ∙ᵉ
    ( ( apᵉ
        ( neg-Ringᵉ Rᵉ)
        ( ( apᵉ
            ( mul-Ring'ᵉ Rᵉ xᵉ)
            ( ( power-succ-Ringᵉ Rᵉ nᵉ (neg-Ringᵉ Rᵉ xᵉ)) ∙ᵉ
              ( ( right-negative-law-mul-Ringᵉ Rᵉ
                  ( power-Ringᵉ Rᵉ nᵉ (neg-Ringᵉ Rᵉ xᵉ))
                  ( xᵉ)) ∙ᵉ
                ( apᵉ
                  ( neg-Ringᵉ Rᵉ)
                  ( ( apᵉ
                      ( mul-Ring'ᵉ Rᵉ xᵉ)
                      ( even-power-neg-Ringᵉ nᵉ xᵉ
                        ( is-even-is-even-succ-succ-ℕᵉ nᵉ Hᵉ))) ∙ᵉ
                    ( invᵉ (power-succ-Ringᵉ Rᵉ nᵉ xᵉ))))))) ∙ᵉ
          ( left-negative-law-mul-Ringᵉ Rᵉ (power-Ringᵉ Rᵉ (succ-ℕᵉ nᵉ) xᵉ) xᵉ))) ∙ᵉ
      ( neg-neg-Ringᵉ Rᵉ (power-Ringᵉ Rᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)) xᵉ)))

  odd-power-neg-Ringᵉ :
    (nᵉ : ℕᵉ) (xᵉ : type-Ringᵉ Rᵉ) →
    is-odd-ℕᵉ nᵉ → power-Ringᵉ Rᵉ nᵉ (neg-Ringᵉ Rᵉ xᵉ) ＝ᵉ neg-Ringᵉ Rᵉ (power-Ringᵉ Rᵉ nᵉ xᵉ)
  odd-power-neg-Ringᵉ zero-ℕᵉ xᵉ Hᵉ = ex-falsoᵉ (Hᵉ is-even-zero-ℕᵉ)
  odd-power-neg-Ringᵉ (succ-ℕᵉ zero-ℕᵉ) xᵉ Hᵉ = reflᵉ
  odd-power-neg-Ringᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)) xᵉ Hᵉ =
    ( right-negative-law-mul-Ringᵉ Rᵉ
      ( power-Ringᵉ Rᵉ (succ-ℕᵉ nᵉ) (neg-Ringᵉ Rᵉ xᵉ))
      ( xᵉ)) ∙ᵉ
    ( apᵉ
      ( neg-Ringᵉ Rᵉ ∘ᵉ mul-Ring'ᵉ Rᵉ xᵉ)
      ( ( power-succ-Ringᵉ Rᵉ nᵉ (neg-Ringᵉ Rᵉ xᵉ)) ∙ᵉ
        ( ( right-negative-law-mul-Ringᵉ Rᵉ
            ( power-Ringᵉ Rᵉ nᵉ (neg-Ringᵉ Rᵉ xᵉ))
            ( xᵉ)) ∙ᵉ
          ( ( apᵉ
              ( neg-Ringᵉ Rᵉ)
              ( ( apᵉ
                  ( mul-Ring'ᵉ Rᵉ xᵉ)
                  ( odd-power-neg-Ringᵉ nᵉ xᵉ
                    ( is-odd-is-odd-succ-succ-ℕᵉ nᵉ Hᵉ))) ∙ᵉ
                ( ( left-negative-law-mul-Ringᵉ Rᵉ (power-Ringᵉ Rᵉ nᵉ xᵉ) xᵉ) ∙ᵉ
                  ( apᵉ (neg-Ringᵉ Rᵉ) (invᵉ (power-succ-Ringᵉ Rᵉ nᵉ xᵉ)))))) ∙ᵉ
            ( neg-neg-Ringᵉ Rᵉ (power-Ringᵉ Rᵉ (succ-ℕᵉ nᵉ) xᵉ))))))
```