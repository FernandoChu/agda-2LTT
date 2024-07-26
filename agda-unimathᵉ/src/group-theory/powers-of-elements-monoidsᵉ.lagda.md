# Powers of elements in monoids

```agda
module group-theory.powers-of-elements-monoidsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbersᵉ
open import elementary-number-theory.multiplication-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.existential-quantificationᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.homomorphisms-monoidsᵉ
open import group-theory.monoidsᵉ
```

</details>

## Idea

Theᵉ **powerᵉ operation**ᵉ onᵉ aᵉ [monoid](group-theory.monoids.mdᵉ) isᵉ theᵉ mapᵉ
`nᵉ xᵉ ↦ᵉ xⁿ`,ᵉ whichᵉ isᵉ definedᵉ byᵉ [iteratively](foundation.iterating-functions.mdᵉ)
multiplyingᵉ `x`ᵉ with itselfᵉ `n`ᵉ times.ᵉ

## Definitions

### Powers of elements of monoids

```agda
module _
  {lᵉ : Level} (Mᵉ : Monoidᵉ lᵉ)
  where

  power-Monoidᵉ : ℕᵉ → type-Monoidᵉ Mᵉ → type-Monoidᵉ Mᵉ
  power-Monoidᵉ zero-ℕᵉ xᵉ = unit-Monoidᵉ Mᵉ
  power-Monoidᵉ (succ-ℕᵉ zero-ℕᵉ) xᵉ = xᵉ
  power-Monoidᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)) xᵉ =
    mul-Monoidᵉ Mᵉ (power-Monoidᵉ (succ-ℕᵉ nᵉ) xᵉ) xᵉ
```

### The predicate of being a power of an element of a monoid

Weᵉ sayᵉ thatᵉ anᵉ elementᵉ `y`ᵉ **isᵉ aᵉ power**ᵉ ofᵉ anᵉ elementᵉ `x`ᵉ ifᵉ thereᵉ
[exists](foundation.existential-quantification.mdᵉ) aᵉ numberᵉ `n`ᵉ suchᵉ thatᵉ
`xⁿᵉ ＝ᵉ y`.ᵉ

```agda
module _
  {lᵉ : Level} (Mᵉ : Monoidᵉ lᵉ)
  where

  is-power-of-element-prop-Monoidᵉ : (xᵉ yᵉ : type-Monoidᵉ Mᵉ) → Propᵉ lᵉ
  is-power-of-element-prop-Monoidᵉ xᵉ yᵉ =
    exists-structure-Propᵉ ℕᵉ (λ nᵉ → power-Monoidᵉ Mᵉ nᵉ xᵉ ＝ᵉ yᵉ)

  is-power-of-element-Monoidᵉ : (xᵉ yᵉ : type-Monoidᵉ Mᵉ) → UUᵉ lᵉ
  is-power-of-element-Monoidᵉ xᵉ yᵉ =
    type-Propᵉ (is-power-of-element-prop-Monoidᵉ xᵉ yᵉ)

  is-prop-is-power-of-element-Monoidᵉ :
    (xᵉ yᵉ : type-Monoidᵉ Mᵉ) → is-propᵉ (is-power-of-element-Monoidᵉ xᵉ yᵉ)
  is-prop-is-power-of-element-Monoidᵉ xᵉ yᵉ =
    is-prop-type-Propᵉ (is-power-of-element-prop-Monoidᵉ xᵉ yᵉ)
```

## Properties

### `1ⁿ ＝ 1`

```agda
module _
  {lᵉ : Level} (Mᵉ : Monoidᵉ lᵉ)
  where

  power-unit-Monoidᵉ :
    (nᵉ : ℕᵉ) →
    power-Monoidᵉ Mᵉ nᵉ (unit-Monoidᵉ Mᵉ) ＝ᵉ unit-Monoidᵉ Mᵉ
  power-unit-Monoidᵉ zero-ℕᵉ = reflᵉ
  power-unit-Monoidᵉ (succ-ℕᵉ zero-ℕᵉ) = reflᵉ
  power-unit-Monoidᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)) =
    right-unit-law-mul-Monoidᵉ Mᵉ _ ∙ᵉ power-unit-Monoidᵉ (succ-ℕᵉ nᵉ)
```

### `xⁿ⁺¹ = xⁿx`

```agda
module _
  {lᵉ : Level} (Mᵉ : Monoidᵉ lᵉ)
  where

  power-succ-Monoidᵉ :
    (nᵉ : ℕᵉ) (xᵉ : type-Monoidᵉ Mᵉ) →
    power-Monoidᵉ Mᵉ (succ-ℕᵉ nᵉ) xᵉ ＝ᵉ mul-Monoidᵉ Mᵉ (power-Monoidᵉ Mᵉ nᵉ xᵉ) xᵉ
  power-succ-Monoidᵉ zero-ℕᵉ xᵉ = invᵉ (left-unit-law-mul-Monoidᵉ Mᵉ xᵉ)
  power-succ-Monoidᵉ (succ-ℕᵉ nᵉ) xᵉ = reflᵉ
```

### `xⁿ⁺¹ ＝ xxⁿ`

```agda
module _
  {lᵉ : Level} (Mᵉ : Monoidᵉ lᵉ)
  where

  power-succ-Monoid'ᵉ :
    (nᵉ : ℕᵉ) (xᵉ : type-Monoidᵉ Mᵉ) →
    power-Monoidᵉ Mᵉ (succ-ℕᵉ nᵉ) xᵉ ＝ᵉ mul-Monoidᵉ Mᵉ xᵉ (power-Monoidᵉ Mᵉ nᵉ xᵉ)
  power-succ-Monoid'ᵉ zero-ℕᵉ xᵉ = invᵉ (right-unit-law-mul-Monoidᵉ Mᵉ xᵉ)
  power-succ-Monoid'ᵉ (succ-ℕᵉ zero-ℕᵉ) xᵉ = reflᵉ
  power-succ-Monoid'ᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)) xᵉ =
    ( apᵉ (mul-Monoid'ᵉ Mᵉ xᵉ) (power-succ-Monoid'ᵉ (succ-ℕᵉ nᵉ) xᵉ)) ∙ᵉ
    ( associative-mul-Monoidᵉ Mᵉ xᵉ (power-Monoidᵉ Mᵉ (succ-ℕᵉ nᵉ) xᵉ) xᵉ)
```

### Powers by sums of natural numbers are products of powers

```agda
module _
  {lᵉ : Level} (Mᵉ : Monoidᵉ lᵉ)
  where

  distributive-power-add-Monoidᵉ :
    (mᵉ nᵉ : ℕᵉ) {xᵉ : type-Monoidᵉ Mᵉ} →
    power-Monoidᵉ Mᵉ (mᵉ +ℕᵉ nᵉ) xᵉ ＝ᵉ
    mul-Monoidᵉ Mᵉ (power-Monoidᵉ Mᵉ mᵉ xᵉ) (power-Monoidᵉ Mᵉ nᵉ xᵉ)
  distributive-power-add-Monoidᵉ mᵉ zero-ℕᵉ {xᵉ} =
    invᵉ
      ( right-unit-law-mul-Monoidᵉ Mᵉ
        ( power-Monoidᵉ Mᵉ mᵉ xᵉ))
  distributive-power-add-Monoidᵉ mᵉ (succ-ℕᵉ nᵉ) {xᵉ} =
    ( power-succ-Monoidᵉ Mᵉ (mᵉ +ℕᵉ nᵉ) xᵉ) ∙ᵉ
    ( apᵉ (mul-Monoid'ᵉ Mᵉ xᵉ) (distributive-power-add-Monoidᵉ mᵉ nᵉ)) ∙ᵉ
    ( associative-mul-Monoidᵉ Mᵉ
      ( power-Monoidᵉ Mᵉ mᵉ xᵉ)
      ( power-Monoidᵉ Mᵉ nᵉ xᵉ)
      ( xᵉ)) ∙ᵉ
    ( apᵉ
      ( mul-Monoidᵉ Mᵉ (power-Monoidᵉ Mᵉ mᵉ xᵉ))
      ( invᵉ (power-succ-Monoidᵉ Mᵉ nᵉ xᵉ)))
```

### If `x` commutes with `y` then so do their powers

```agda
module _
  {lᵉ : Level} (Mᵉ : Monoidᵉ lᵉ)
  where

  commute-powers-Monoid'ᵉ :
    (nᵉ : ℕᵉ) {xᵉ yᵉ : type-Monoidᵉ Mᵉ} →
    ( mul-Monoidᵉ Mᵉ xᵉ yᵉ ＝ᵉ mul-Monoidᵉ Mᵉ yᵉ xᵉ) →
    ( mul-Monoidᵉ Mᵉ (power-Monoidᵉ Mᵉ nᵉ xᵉ) yᵉ) ＝ᵉ
    ( mul-Monoidᵉ Mᵉ yᵉ (power-Monoidᵉ Mᵉ nᵉ xᵉ))
  commute-powers-Monoid'ᵉ zero-ℕᵉ Hᵉ =
    left-unit-law-mul-Monoidᵉ Mᵉ _ ∙ᵉ invᵉ (right-unit-law-mul-Monoidᵉ Mᵉ _)
  commute-powers-Monoid'ᵉ (succ-ℕᵉ zero-ℕᵉ) {xᵉ} {yᵉ} Hᵉ = Hᵉ
  commute-powers-Monoid'ᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)) {xᵉ} {yᵉ} Hᵉ =
    ( associative-mul-Monoidᵉ Mᵉ (power-Monoidᵉ Mᵉ (succ-ℕᵉ nᵉ) xᵉ) xᵉ yᵉ) ∙ᵉ
    ( apᵉ (mul-Monoidᵉ Mᵉ (power-Monoidᵉ Mᵉ (succ-ℕᵉ nᵉ) xᵉ)) Hᵉ) ∙ᵉ
    ( invᵉ (associative-mul-Monoidᵉ Mᵉ (power-Monoidᵉ Mᵉ (succ-ℕᵉ nᵉ) xᵉ) yᵉ xᵉ)) ∙ᵉ
    ( apᵉ (mul-Monoid'ᵉ Mᵉ xᵉ) (commute-powers-Monoid'ᵉ (succ-ℕᵉ nᵉ) Hᵉ)) ∙ᵉ
    ( associative-mul-Monoidᵉ Mᵉ yᵉ (power-Monoidᵉ Mᵉ (succ-ℕᵉ nᵉ) xᵉ) xᵉ)

  commute-powers-Monoidᵉ :
    (mᵉ nᵉ : ℕᵉ) {xᵉ yᵉ : type-Monoidᵉ Mᵉ} →
    ( mul-Monoidᵉ Mᵉ xᵉ yᵉ ＝ᵉ mul-Monoidᵉ Mᵉ yᵉ xᵉ) →
    ( mul-Monoidᵉ Mᵉ
      ( power-Monoidᵉ Mᵉ mᵉ xᵉ)
      ( power-Monoidᵉ Mᵉ nᵉ yᵉ)) ＝ᵉ
    ( mul-Monoidᵉ Mᵉ
      ( power-Monoidᵉ Mᵉ nᵉ yᵉ)
      ( power-Monoidᵉ Mᵉ mᵉ xᵉ))
  commute-powers-Monoidᵉ zero-ℕᵉ zero-ℕᵉ Hᵉ = reflᵉ
  commute-powers-Monoidᵉ zero-ℕᵉ (succ-ℕᵉ nᵉ) Hᵉ =
    ( left-unit-law-mul-Monoidᵉ Mᵉ (power-Monoidᵉ Mᵉ (succ-ℕᵉ nᵉ) _)) ∙ᵉ
    ( invᵉ (right-unit-law-mul-Monoidᵉ Mᵉ (power-Monoidᵉ Mᵉ (succ-ℕᵉ nᵉ) _)))
  commute-powers-Monoidᵉ (succ-ℕᵉ mᵉ) zero-ℕᵉ Hᵉ =
    ( right-unit-law-mul-Monoidᵉ Mᵉ (power-Monoidᵉ Mᵉ (succ-ℕᵉ mᵉ) _)) ∙ᵉ
    ( invᵉ (left-unit-law-mul-Monoidᵉ Mᵉ (power-Monoidᵉ Mᵉ (succ-ℕᵉ mᵉ) _)))
  commute-powers-Monoidᵉ (succ-ℕᵉ mᵉ) (succ-ℕᵉ nᵉ) {xᵉ} {yᵉ} Hᵉ =
    ( ap-mul-Monoidᵉ Mᵉ (power-succ-Monoidᵉ Mᵉ mᵉ xᵉ) (power-succ-Monoidᵉ Mᵉ nᵉ yᵉ)) ∙ᵉ
    ( associative-mul-Monoidᵉ Mᵉ
      ( power-Monoidᵉ Mᵉ mᵉ xᵉ)
      ( xᵉ)
      ( mul-Monoidᵉ Mᵉ (power-Monoidᵉ Mᵉ nᵉ yᵉ) yᵉ)) ∙ᵉ
    ( apᵉ
      ( mul-Monoidᵉ Mᵉ (power-Monoidᵉ Mᵉ mᵉ xᵉ))
      ( ( invᵉ (associative-mul-Monoidᵉ Mᵉ xᵉ (power-Monoidᵉ Mᵉ nᵉ yᵉ) yᵉ)) ∙ᵉ
        ( apᵉ
          ( mul-Monoid'ᵉ Mᵉ yᵉ)
          ( invᵉ (commute-powers-Monoid'ᵉ nᵉ (invᵉ Hᵉ)))) ∙ᵉ
        ( associative-mul-Monoidᵉ Mᵉ (power-Monoidᵉ Mᵉ nᵉ yᵉ) xᵉ yᵉ) ∙ᵉ
        ( apᵉ (mul-Monoidᵉ Mᵉ (power-Monoidᵉ Mᵉ nᵉ yᵉ)) Hᵉ) ∙ᵉ
        ( invᵉ (associative-mul-Monoidᵉ Mᵉ (power-Monoidᵉ Mᵉ nᵉ yᵉ) yᵉ xᵉ)))) ∙ᵉ
    ( invᵉ
      ( associative-mul-Monoidᵉ Mᵉ
        ( power-Monoidᵉ Mᵉ mᵉ xᵉ)
        ( mul-Monoidᵉ Mᵉ (power-Monoidᵉ Mᵉ nᵉ yᵉ) yᵉ)
        ( xᵉ))) ∙ᵉ
    ( apᵉ
      ( mul-Monoid'ᵉ Mᵉ xᵉ)
      ( ( invᵉ
          ( associative-mul-Monoidᵉ Mᵉ
            ( power-Monoidᵉ Mᵉ mᵉ xᵉ)
            ( power-Monoidᵉ Mᵉ nᵉ yᵉ)
            ( yᵉ))) ∙ᵉ
        ( apᵉ
          ( mul-Monoid'ᵉ Mᵉ yᵉ)
          ( commute-powers-Monoidᵉ mᵉ nᵉ Hᵉ)) ∙ᵉ
        ( associative-mul-Monoidᵉ Mᵉ
          ( power-Monoidᵉ Mᵉ nᵉ yᵉ)
          ( power-Monoidᵉ Mᵉ mᵉ xᵉ)
          ( yᵉ)) ∙ᵉ
        ( apᵉ
          ( mul-Monoidᵉ Mᵉ (power-Monoidᵉ Mᵉ nᵉ yᵉ))
          ( commute-powers-Monoid'ᵉ mᵉ Hᵉ)) ∙ᵉ
        ( invᵉ
          ( associative-mul-Monoidᵉ Mᵉ
            ( power-Monoidᵉ Mᵉ nᵉ yᵉ)
            ( yᵉ)
            ( power-Monoidᵉ Mᵉ mᵉ xᵉ))) ∙ᵉ
        ( apᵉ
          ( mul-Monoid'ᵉ Mᵉ (power-Monoidᵉ Mᵉ mᵉ xᵉ))
          ( invᵉ (power-succ-Monoidᵉ Mᵉ nᵉ yᵉ))))) ∙ᵉ
      ( associative-mul-Monoidᵉ Mᵉ
        ( power-Monoidᵉ Mᵉ (succ-ℕᵉ nᵉ) yᵉ)
        ( power-Monoidᵉ Mᵉ mᵉ xᵉ)
        ( xᵉ)) ∙ᵉ
      ( apᵉ
        ( mul-Monoidᵉ Mᵉ (power-Monoidᵉ Mᵉ (succ-ℕᵉ nᵉ) yᵉ))
        ( invᵉ (power-succ-Monoidᵉ Mᵉ mᵉ xᵉ)))
```

### If `x` commutes with `y`, then powers distribute over the product of `x` and `y`

```agda
module _
  {lᵉ : Level} (Mᵉ : Monoidᵉ lᵉ)
  where

  distributive-power-mul-Monoidᵉ :
    (nᵉ : ℕᵉ) {xᵉ yᵉ : type-Monoidᵉ Mᵉ} →
    (Hᵉ : mul-Monoidᵉ Mᵉ xᵉ yᵉ ＝ᵉ mul-Monoidᵉ Mᵉ yᵉ xᵉ) →
    power-Monoidᵉ Mᵉ nᵉ (mul-Monoidᵉ Mᵉ xᵉ yᵉ) ＝ᵉ
    mul-Monoidᵉ Mᵉ (power-Monoidᵉ Mᵉ nᵉ xᵉ) (power-Monoidᵉ Mᵉ nᵉ yᵉ)
  distributive-power-mul-Monoidᵉ zero-ℕᵉ Hᵉ =
    invᵉ (left-unit-law-mul-Monoidᵉ Mᵉ (unit-Monoidᵉ Mᵉ))
  distributive-power-mul-Monoidᵉ (succ-ℕᵉ nᵉ) {xᵉ} {yᵉ} Hᵉ =
    ( power-succ-Monoidᵉ Mᵉ nᵉ (mul-Monoidᵉ Mᵉ xᵉ yᵉ)) ∙ᵉ
    ( apᵉ
      ( mul-Monoid'ᵉ Mᵉ (mul-Monoidᵉ Mᵉ xᵉ yᵉ))
      ( distributive-power-mul-Monoidᵉ nᵉ Hᵉ)) ∙ᵉ
    ( invᵉ
      ( associative-mul-Monoidᵉ Mᵉ
        ( mul-Monoidᵉ Mᵉ (power-Monoidᵉ Mᵉ nᵉ xᵉ) (power-Monoidᵉ Mᵉ nᵉ yᵉ))
        ( xᵉ)
        ( yᵉ))) ∙ᵉ
    ( apᵉ
      ( mul-Monoid'ᵉ Mᵉ yᵉ)
      ( ( associative-mul-Monoidᵉ Mᵉ
          ( power-Monoidᵉ Mᵉ nᵉ xᵉ)
          ( power-Monoidᵉ Mᵉ nᵉ yᵉ)
          ( xᵉ)) ∙ᵉ
        ( apᵉ
          ( mul-Monoidᵉ Mᵉ (power-Monoidᵉ Mᵉ nᵉ xᵉ))
          ( commute-powers-Monoid'ᵉ Mᵉ nᵉ (invᵉ Hᵉ))) ∙ᵉ
        ( invᵉ
          ( associative-mul-Monoidᵉ Mᵉ
            ( power-Monoidᵉ Mᵉ nᵉ xᵉ)
            ( xᵉ)
            ( power-Monoidᵉ Mᵉ nᵉ yᵉ))))) ∙ᵉ
    ( associative-mul-Monoidᵉ Mᵉ
      ( mul-Monoidᵉ Mᵉ (power-Monoidᵉ Mᵉ nᵉ xᵉ) xᵉ)
      ( power-Monoidᵉ Mᵉ nᵉ yᵉ)
      ( yᵉ)) ∙ᵉ
    ( ap-mul-Monoidᵉ Mᵉ
      ( invᵉ (power-succ-Monoidᵉ Mᵉ nᵉ xᵉ))
      ( invᵉ (power-succ-Monoidᵉ Mᵉ nᵉ yᵉ)))
```

### Powers by products of natural numbers are iterated powers

```agda
module _
  {lᵉ : Level} (Mᵉ : Monoidᵉ lᵉ)
  where

  power-mul-Monoidᵉ :
    (mᵉ nᵉ : ℕᵉ) {xᵉ : type-Monoidᵉ Mᵉ} →
    power-Monoidᵉ Mᵉ (mᵉ *ℕᵉ nᵉ) xᵉ ＝ᵉ
    power-Monoidᵉ Mᵉ nᵉ (power-Monoidᵉ Mᵉ mᵉ xᵉ)
  power-mul-Monoidᵉ zero-ℕᵉ nᵉ {xᵉ} =
    invᵉ (power-unit-Monoidᵉ Mᵉ nᵉ)
  power-mul-Monoidᵉ (succ-ℕᵉ zero-ℕᵉ) nᵉ {xᵉ} =
    apᵉ (λ tᵉ → power-Monoidᵉ Mᵉ tᵉ xᵉ) (left-unit-law-add-ℕᵉ nᵉ)
  power-mul-Monoidᵉ (succ-ℕᵉ (succ-ℕᵉ mᵉ)) nᵉ {xᵉ} =
    ( distributive-power-add-Monoidᵉ Mᵉ (succ-ℕᵉ mᵉ *ℕᵉ nᵉ) nᵉ) ∙ᵉ
    ( apᵉ
      ( mul-Monoid'ᵉ Mᵉ (power-Monoidᵉ Mᵉ nᵉ xᵉ))
      ( power-mul-Monoidᵉ (succ-ℕᵉ mᵉ) nᵉ)) ∙ᵉ
    ( invᵉ
      ( distributive-power-mul-Monoidᵉ Mᵉ nᵉ
        ( commute-powers-Monoid'ᵉ Mᵉ (succ-ℕᵉ mᵉ) reflᵉ)))
```

### Monoid homomorphisms preserve powers

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Mᵉ : Monoidᵉ l1ᵉ) (Nᵉ : Monoidᵉ l2ᵉ) (fᵉ : hom-Monoidᵉ Mᵉ Nᵉ)
  where

  preserves-powers-hom-Monoidᵉ :
    (nᵉ : ℕᵉ) (xᵉ : type-Monoidᵉ Mᵉ) →
    map-hom-Monoidᵉ Mᵉ Nᵉ fᵉ (power-Monoidᵉ Mᵉ nᵉ xᵉ) ＝ᵉ
    power-Monoidᵉ Nᵉ nᵉ (map-hom-Monoidᵉ Mᵉ Nᵉ fᵉ xᵉ)
  preserves-powers-hom-Monoidᵉ zero-ℕᵉ xᵉ = preserves-unit-hom-Monoidᵉ Mᵉ Nᵉ fᵉ
  preserves-powers-hom-Monoidᵉ (succ-ℕᵉ zero-ℕᵉ) xᵉ = reflᵉ
  preserves-powers-hom-Monoidᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)) xᵉ =
    ( preserves-mul-hom-Monoidᵉ Mᵉ Nᵉ fᵉ) ∙ᵉ
    ( apᵉ (mul-Monoid'ᵉ Nᵉ _) (preserves-powers-hom-Monoidᵉ (succ-ℕᵉ nᵉ) xᵉ))
```