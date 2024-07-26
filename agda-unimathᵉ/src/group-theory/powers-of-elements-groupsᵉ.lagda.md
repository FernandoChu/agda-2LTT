# Powers of elements in groups

```agda
module group-theory.powers-of-elements-groupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbersᵉ
open import elementary-number-theory.multiplication-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ

open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.commuting-elements-groupsᵉ
open import group-theory.groupsᵉ
open import group-theory.homomorphisms-groupsᵉ
open import group-theory.powers-of-elements-monoidsᵉ
```

</details>

## Idea

Theᵉ powerᵉ operationᵉ onᵉ aᵉ groupᵉ isᵉ theᵉ mapᵉ `nᵉ xᵉ ↦ᵉ xⁿ`,ᵉ whichᵉ isᵉ definedᵉ byᵉ
iterativelyᵉ multiplyingᵉ `x`ᵉ with itselfᵉ `n`ᵉ times.ᵉ Weᵉ defineᵉ thisᵉ operationᵉ
where `n`ᵉ rangesᵉ overᵉ theᵉ naturalᵉ numbers,ᵉ asᵉ wellᵉ asᵉ where `n`ᵉ rangesᵉ overᵉ theᵉ
integers.ᵉ

## Definition

### Powers by natural numbers of group elements

```agda
module _
  {lᵉ : Level} (Gᵉ : Groupᵉ lᵉ)
  where

  power-Groupᵉ : ℕᵉ → type-Groupᵉ Gᵉ → type-Groupᵉ Gᵉ
  power-Groupᵉ = power-Monoidᵉ (monoid-Groupᵉ Gᵉ)
```

### The predicate of being a power of an element in a group

Weᵉ sayᵉ thatᵉ anᵉ elementᵉ `y`ᵉ **isᵉ aᵉ power**ᵉ ofᵉ anᵉ elementᵉ `x`ᵉ ifᵉ thereᵉ
[exists](foundation.existential-quantification.mdᵉ) aᵉ numberᵉ `n`ᵉ suchᵉ thatᵉ
`xⁿᵉ ＝ᵉ y`.ᵉ

```agda
module _
  {lᵉ : Level} (Gᵉ : Groupᵉ lᵉ)
  where

  is-power-of-element-prop-Groupᵉ :
    (xᵉ yᵉ : type-Groupᵉ Gᵉ) → Propᵉ lᵉ
  is-power-of-element-prop-Groupᵉ =
    is-power-of-element-prop-Monoidᵉ (monoid-Groupᵉ Gᵉ)

  is-power-of-element-Groupᵉ :
    (xᵉ yᵉ : type-Groupᵉ Gᵉ) → UUᵉ lᵉ
  is-power-of-element-Groupᵉ =
    is-power-of-element-Monoidᵉ (monoid-Groupᵉ Gᵉ)

  is-prop-is-power-of-element-Groupᵉ :
    (xᵉ yᵉ : type-Groupᵉ Gᵉ) →
    is-propᵉ (is-power-of-element-Groupᵉ xᵉ yᵉ)
  is-prop-is-power-of-element-Groupᵉ =
    is-prop-is-power-of-element-Monoidᵉ (monoid-Groupᵉ Gᵉ)
```

## Properties

### `1ⁿ ＝ 1`

```agda
module _
  {lᵉ : Level} (Gᵉ : Groupᵉ lᵉ)
  where

  power-unit-Groupᵉ :
    (nᵉ : ℕᵉ) → power-Groupᵉ Gᵉ nᵉ (unit-Groupᵉ Gᵉ) ＝ᵉ unit-Groupᵉ Gᵉ
  power-unit-Groupᵉ = power-unit-Monoidᵉ (monoid-Groupᵉ Gᵉ)
```

### `xⁿ⁺¹ = xⁿx`

```agda
module _
  {lᵉ : Level} (Gᵉ : Groupᵉ lᵉ)
  where

  power-succ-Groupᵉ :
    (nᵉ : ℕᵉ) (xᵉ : type-Groupᵉ Gᵉ) →
    power-Groupᵉ Gᵉ (succ-ℕᵉ nᵉ) xᵉ ＝ᵉ mul-Groupᵉ Gᵉ (power-Groupᵉ Gᵉ nᵉ xᵉ) xᵉ
  power-succ-Groupᵉ = power-succ-Monoidᵉ (monoid-Groupᵉ Gᵉ)
```

### `xⁿ⁺¹ ＝ xxⁿ`

```agda
module _
  {lᵉ : Level} (Gᵉ : Groupᵉ lᵉ)
  where

  power-succ-Group'ᵉ :
    (nᵉ : ℕᵉ) (xᵉ : type-Groupᵉ Gᵉ) →
    power-Groupᵉ Gᵉ (succ-ℕᵉ nᵉ) xᵉ ＝ᵉ mul-Groupᵉ Gᵉ xᵉ (power-Groupᵉ Gᵉ nᵉ xᵉ)
  power-succ-Group'ᵉ = power-succ-Monoid'ᵉ (monoid-Groupᵉ Gᵉ)
```

### Powers by sums of natural numbers are products of powers

```agda
module _
  {lᵉ : Level} (Gᵉ : Groupᵉ lᵉ)
  where

  distributive-power-add-Groupᵉ :
    (mᵉ nᵉ : ℕᵉ) {xᵉ : type-Groupᵉ Gᵉ} →
    power-Groupᵉ Gᵉ (mᵉ +ℕᵉ nᵉ) xᵉ ＝ᵉ
    mul-Groupᵉ Gᵉ (power-Groupᵉ Gᵉ mᵉ xᵉ) (power-Groupᵉ Gᵉ nᵉ xᵉ)
  distributive-power-add-Groupᵉ = distributive-power-add-Monoidᵉ (monoid-Groupᵉ Gᵉ)
```

### If `x` commutes with `y` then so do their powers

```agda
module _
  {lᵉ : Level} (Gᵉ : Groupᵉ lᵉ)
  where

  commute-powers-Group'ᵉ :
    (nᵉ : ℕᵉ) {xᵉ yᵉ : type-Groupᵉ Gᵉ} →
    commute-Groupᵉ Gᵉ xᵉ yᵉ → commute-Groupᵉ Gᵉ (power-Groupᵉ Gᵉ nᵉ xᵉ) yᵉ
  commute-powers-Group'ᵉ = commute-powers-Monoid'ᵉ (monoid-Groupᵉ Gᵉ)

  commute-powers-Groupᵉ :
    (mᵉ nᵉ : ℕᵉ) {xᵉ yᵉ : type-Groupᵉ Gᵉ} →
    commute-Groupᵉ Gᵉ xᵉ yᵉ →
    commute-Groupᵉ Gᵉ (power-Groupᵉ Gᵉ mᵉ xᵉ) (power-Groupᵉ Gᵉ nᵉ yᵉ)
  commute-powers-Groupᵉ = commute-powers-Monoidᵉ (monoid-Groupᵉ Gᵉ)
```

### If `x` commutes with `y`, then powers distribute over the product of `x` and `y`

```agda
module _
  {lᵉ : Level} (Gᵉ : Groupᵉ lᵉ)
  where

  distributive-power-mul-Groupᵉ :
    (nᵉ : ℕᵉ) {xᵉ yᵉ : type-Groupᵉ Gᵉ} →
    (Hᵉ : mul-Groupᵉ Gᵉ xᵉ yᵉ ＝ᵉ mul-Groupᵉ Gᵉ yᵉ xᵉ) →
    power-Groupᵉ Gᵉ nᵉ (mul-Groupᵉ Gᵉ xᵉ yᵉ) ＝ᵉ
    mul-Groupᵉ Gᵉ (power-Groupᵉ Gᵉ nᵉ xᵉ) (power-Groupᵉ Gᵉ nᵉ yᵉ)
  distributive-power-mul-Groupᵉ =
    distributive-power-mul-Monoidᵉ (monoid-Groupᵉ Gᵉ)
```

### Powers by products of natural numbers are iterated powers

```agda
module _
  {lᵉ : Level} (Gᵉ : Groupᵉ lᵉ)
  where

  power-mul-Groupᵉ :
    (mᵉ nᵉ : ℕᵉ) {xᵉ : type-Groupᵉ Gᵉ} →
    power-Groupᵉ Gᵉ (mᵉ *ℕᵉ nᵉ) xᵉ ＝ᵉ power-Groupᵉ Gᵉ nᵉ (power-Groupᵉ Gᵉ mᵉ xᵉ)
  power-mul-Groupᵉ = power-mul-Monoidᵉ (monoid-Groupᵉ Gᵉ)
```

### Group homomorphisms preserve powers

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Hᵉ : Groupᵉ l2ᵉ) (fᵉ : hom-Groupᵉ Gᵉ Hᵉ)
  where

  preserves-powers-hom-Groupᵉ :
    (nᵉ : ℕᵉ) (xᵉ : type-Groupᵉ Gᵉ) →
    map-hom-Groupᵉ Gᵉ Hᵉ fᵉ (power-Groupᵉ Gᵉ nᵉ xᵉ) ＝ᵉ
    power-Groupᵉ Hᵉ nᵉ (map-hom-Groupᵉ Gᵉ Hᵉ fᵉ xᵉ)
  preserves-powers-hom-Groupᵉ =
    preserves-powers-hom-Monoidᵉ
      ( monoid-Groupᵉ Gᵉ)
      ( monoid-Groupᵉ Hᵉ)
      ( hom-monoid-hom-Groupᵉ Gᵉ Hᵉ fᵉ)
```