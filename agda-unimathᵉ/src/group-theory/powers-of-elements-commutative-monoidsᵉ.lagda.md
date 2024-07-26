# Powers of elements in commutative monoids

```agda
module group-theory.powers-of-elements-commutative-monoidsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbersᵉ
open import elementary-number-theory.multiplication-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ

open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.commutative-monoidsᵉ
open import group-theory.homomorphisms-commutative-monoidsᵉ
open import group-theory.powers-of-elements-monoidsᵉ
```

</details>

Theᵉ **powerᵉ operation**ᵉ onᵉ aᵉ [monoid](group-theory.monoids.mdᵉ) isᵉ theᵉ mapᵉ
`nᵉ xᵉ ↦ᵉ xⁿ`,ᵉ whichᵉ isᵉ definedᵉ byᵉ [iteratively](foundation.iterating-functions.mdᵉ)
multiplyingᵉ `x`ᵉ with itselfᵉ `n`ᵉ times.ᵉ

## Definitions

### Powers of elements in commutative monoids

```agda
module _
  {lᵉ : Level} (Mᵉ : Commutative-Monoidᵉ lᵉ)
  where

  power-Commutative-Monoidᵉ :
    ℕᵉ → type-Commutative-Monoidᵉ Mᵉ → type-Commutative-Monoidᵉ Mᵉ
  power-Commutative-Monoidᵉ = power-Monoidᵉ (monoid-Commutative-Monoidᵉ Mᵉ)
```

### The predicate of being a power of an element in a commutative monoid

Weᵉ sayᵉ thatᵉ anᵉ elementᵉ `y`ᵉ **isᵉ aᵉ power**ᵉ ofᵉ anᵉ elementᵉ `x`ᵉ ifᵉ thereᵉ
[exists](foundation.existential-quantification.mdᵉ) aᵉ numberᵉ `n`ᵉ suchᵉ thatᵉ
`xⁿᵉ ＝ᵉ y`.ᵉ

```agda
module _
  {lᵉ : Level} (Mᵉ : Commutative-Monoidᵉ lᵉ)
  where

  is-power-of-element-prop-Commutative-Monoidᵉ :
    (xᵉ yᵉ : type-Commutative-Monoidᵉ Mᵉ) → Propᵉ lᵉ
  is-power-of-element-prop-Commutative-Monoidᵉ =
    is-power-of-element-prop-Monoidᵉ (monoid-Commutative-Monoidᵉ Mᵉ)

  is-power-of-element-Commutative-Monoidᵉ :
    (xᵉ yᵉ : type-Commutative-Monoidᵉ Mᵉ) → UUᵉ lᵉ
  is-power-of-element-Commutative-Monoidᵉ =
    is-power-of-element-Monoidᵉ (monoid-Commutative-Monoidᵉ Mᵉ)

  is-prop-is-power-of-element-Commutative-Monoidᵉ :
    (xᵉ yᵉ : type-Commutative-Monoidᵉ Mᵉ) →
    is-propᵉ (is-power-of-element-Commutative-Monoidᵉ xᵉ yᵉ)
  is-prop-is-power-of-element-Commutative-Monoidᵉ =
    is-prop-is-power-of-element-Monoidᵉ (monoid-Commutative-Monoidᵉ Mᵉ)
```

## Properties

### `1ⁿ ＝ 1`

```agda
module _
  {lᵉ : Level} (Mᵉ : Commutative-Monoidᵉ lᵉ)
  where

  power-unit-Commutative-Monoidᵉ :
    (nᵉ : ℕᵉ) →
    power-Commutative-Monoidᵉ Mᵉ nᵉ (unit-Commutative-Monoidᵉ Mᵉ) ＝ᵉ
    unit-Commutative-Monoidᵉ Mᵉ
  power-unit-Commutative-Monoidᵉ zero-ℕᵉ = reflᵉ
  power-unit-Commutative-Monoidᵉ (succ-ℕᵉ zero-ℕᵉ) = reflᵉ
  power-unit-Commutative-Monoidᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)) =
    right-unit-law-mul-Commutative-Monoidᵉ Mᵉ _ ∙ᵉ
    power-unit-Commutative-Monoidᵉ (succ-ℕᵉ nᵉ)
```

### `xⁿ⁺¹ = xⁿx`

```agda
module _
  {lᵉ : Level} (Mᵉ : Commutative-Monoidᵉ lᵉ)
  where

  power-succ-Commutative-Monoidᵉ :
    (nᵉ : ℕᵉ) (xᵉ : type-Commutative-Monoidᵉ Mᵉ) →
    power-Commutative-Monoidᵉ Mᵉ (succ-ℕᵉ nᵉ) xᵉ ＝ᵉ
    mul-Commutative-Monoidᵉ Mᵉ (power-Commutative-Monoidᵉ Mᵉ nᵉ xᵉ) xᵉ
  power-succ-Commutative-Monoidᵉ =
    power-succ-Monoidᵉ (monoid-Commutative-Monoidᵉ Mᵉ)
```

### `xⁿ⁺¹ ＝ xxⁿ`

```agda
module _
  {lᵉ : Level} (Mᵉ : Commutative-Monoidᵉ lᵉ)
  where

  power-succ-Commutative-Monoid'ᵉ :
    (nᵉ : ℕᵉ) (xᵉ : type-Commutative-Monoidᵉ Mᵉ) →
    power-Commutative-Monoidᵉ Mᵉ (succ-ℕᵉ nᵉ) xᵉ ＝ᵉ
    mul-Commutative-Monoidᵉ Mᵉ xᵉ (power-Commutative-Monoidᵉ Mᵉ nᵉ xᵉ)
  power-succ-Commutative-Monoid'ᵉ =
    power-succ-Monoid'ᵉ (monoid-Commutative-Monoidᵉ Mᵉ)
```

### Powers by sums of natural numbers are products of powers

```agda
module _
  {lᵉ : Level} (Mᵉ : Commutative-Monoidᵉ lᵉ)
  where

  distributive-power-add-Commutative-Monoidᵉ :
    (mᵉ nᵉ : ℕᵉ) {xᵉ : type-Commutative-Monoidᵉ Mᵉ} →
    power-Commutative-Monoidᵉ Mᵉ (mᵉ +ℕᵉ nᵉ) xᵉ ＝ᵉ
    mul-Commutative-Monoidᵉ Mᵉ
      ( power-Commutative-Monoidᵉ Mᵉ mᵉ xᵉ)
      ( power-Commutative-Monoidᵉ Mᵉ nᵉ xᵉ)
  distributive-power-add-Commutative-Monoidᵉ =
    distributive-power-add-Monoidᵉ (monoid-Commutative-Monoidᵉ Mᵉ)
```

### If `x` commutes with `y`, then powers distribute over the product of `x` and `y`

```agda
module _
  {lᵉ : Level} (Mᵉ : Commutative-Monoidᵉ lᵉ)
  where

  distributive-power-mul-Commutative-Monoidᵉ :
    (nᵉ : ℕᵉ) {xᵉ yᵉ : type-Commutative-Monoidᵉ Mᵉ} →
    (Hᵉ : mul-Commutative-Monoidᵉ Mᵉ xᵉ yᵉ ＝ᵉ mul-Commutative-Monoidᵉ Mᵉ yᵉ xᵉ) →
    power-Commutative-Monoidᵉ Mᵉ nᵉ (mul-Commutative-Monoidᵉ Mᵉ xᵉ yᵉ) ＝ᵉ
    mul-Commutative-Monoidᵉ Mᵉ
      ( power-Commutative-Monoidᵉ Mᵉ nᵉ xᵉ)
      ( power-Commutative-Monoidᵉ Mᵉ nᵉ yᵉ)
  distributive-power-mul-Commutative-Monoidᵉ =
    distributive-power-mul-Monoidᵉ (monoid-Commutative-Monoidᵉ Mᵉ)
```

### Powers by products of natural numbers are iterated powers

```agda
module _
  {lᵉ : Level} (Mᵉ : Commutative-Monoidᵉ lᵉ)
  where

  power-mul-Commutative-Monoidᵉ :
    (mᵉ nᵉ : ℕᵉ) {xᵉ : type-Commutative-Monoidᵉ Mᵉ} →
    power-Commutative-Monoidᵉ Mᵉ (mᵉ *ℕᵉ nᵉ) xᵉ ＝ᵉ
    power-Commutative-Monoidᵉ Mᵉ nᵉ (power-Commutative-Monoidᵉ Mᵉ mᵉ xᵉ)
  power-mul-Commutative-Monoidᵉ =
    power-mul-Monoidᵉ (monoid-Commutative-Monoidᵉ Mᵉ)
```

### Commutative-Monoid homomorphisms preserve powers

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Mᵉ : Commutative-Monoidᵉ l1ᵉ)
  (Nᵉ : Commutative-Monoidᵉ l2ᵉ) (fᵉ : hom-Commutative-Monoidᵉ Mᵉ Nᵉ)
  where

  preserves-powers-hom-Commutative-Monoidᵉ :
    (nᵉ : ℕᵉ) (xᵉ : type-Commutative-Monoidᵉ Mᵉ) →
    map-hom-Commutative-Monoidᵉ Mᵉ Nᵉ fᵉ (power-Commutative-Monoidᵉ Mᵉ nᵉ xᵉ) ＝ᵉ
    power-Commutative-Monoidᵉ Nᵉ nᵉ (map-hom-Commutative-Monoidᵉ Mᵉ Nᵉ fᵉ xᵉ)
  preserves-powers-hom-Commutative-Monoidᵉ =
    preserves-powers-hom-Monoidᵉ
      ( monoid-Commutative-Monoidᵉ Mᵉ)
      ( monoid-Commutative-Monoidᵉ Nᵉ)
      ( fᵉ)
```