# Multiples of elements in rings

```agda
module ring-theory.multiples-of-elements-ringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbersᵉ
open import elementary-number-theory.multiplication-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ

open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.multiples-of-elements-abelian-groupsᵉ

open import ring-theory.ringsᵉ
```

</details>

## Idea

Forᵉ anyᵉ [ring](ring-theory.rings.mdᵉ) `R`ᵉ thereᵉ isᵉ aᵉ multiplicationᵉ operationᵉ
`ℕᵉ → Rᵉ → R`,ᵉ whichᵉ weᵉ writeᵉ informallyᵉ asᵉ `nᵉ xᵉ ↦ᵉ nᵉ ·ᵉ x`.ᵉ Thisᵉ operationᵉ isᵉ
definedᵉ byᵉ [iteratively](foundation.iterating-functions.mdᵉ) addingᵉ `x`ᵉ with
itselfᵉ `n`ᵉ times.ᵉ

## Definition

### Natural number multiples of ring elements

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  multiple-Ringᵉ : ℕᵉ → type-Ringᵉ Rᵉ → type-Ringᵉ Rᵉ
  multiple-Ringᵉ = multiple-Abᵉ (ab-Ringᵉ Rᵉ)
```

### The predicate of being a natural multiple of an element in an ring

Weᵉ sayᵉ thatᵉ anᵉ elementᵉ `y`ᵉ **isᵉ aᵉ multiple**ᵉ ofᵉ anᵉ elementᵉ `x`ᵉ ifᵉ thereᵉ
[exists](foundation.existential-quantification.mdᵉ) aᵉ numberᵉ `n`ᵉ suchᵉ thatᵉ
`nxᵉ ＝ᵉ y`.ᵉ

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  is-multiple-of-element-prop-Ringᵉ :
    (xᵉ yᵉ : type-Ringᵉ Rᵉ) → Propᵉ lᵉ
  is-multiple-of-element-prop-Ringᵉ =
    is-multiple-of-element-prop-Abᵉ (ab-Ringᵉ Rᵉ)

  is-multiple-of-element-Ringᵉ :
    (xᵉ yᵉ : type-Ringᵉ Rᵉ) → UUᵉ lᵉ
  is-multiple-of-element-Ringᵉ =
    is-multiple-of-element-Abᵉ (ab-Ringᵉ Rᵉ)

  is-prop-is-multiple-of-element-Ringᵉ :
    (xᵉ yᵉ : type-Ringᵉ Rᵉ) →
    is-propᵉ (is-multiple-of-element-Ringᵉ xᵉ yᵉ)
  is-prop-is-multiple-of-element-Ringᵉ =
    is-prop-is-multiple-of-element-Abᵉ (ab-Ringᵉ Rᵉ)
```

## Properties

### `n · 0 ＝ 0`

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  multiple-zero-Ringᵉ :
    (nᵉ : ℕᵉ) → multiple-Ringᵉ Rᵉ nᵉ (zero-Ringᵉ Rᵉ) ＝ᵉ zero-Ringᵉ Rᵉ
  multiple-zero-Ringᵉ = multiple-zero-Abᵉ (ab-Ringᵉ Rᵉ)
```

### `(n + 1) · x = n · x + x`

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  multiple-succ-Ringᵉ :
    (nᵉ : ℕᵉ) (xᵉ : type-Ringᵉ Rᵉ) →
    multiple-Ringᵉ Rᵉ (succ-ℕᵉ nᵉ) xᵉ ＝ᵉ add-Ringᵉ Rᵉ (multiple-Ringᵉ Rᵉ nᵉ xᵉ) xᵉ
  multiple-succ-Ringᵉ = multiple-succ-Abᵉ (ab-Ringᵉ Rᵉ)
```

### `(n + 1) · x ＝ x + n · x`

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  multiple-succ-Ring'ᵉ :
    (nᵉ : ℕᵉ) (xᵉ : type-Ringᵉ Rᵉ) →
    multiple-Ringᵉ Rᵉ (succ-ℕᵉ nᵉ) xᵉ ＝ᵉ add-Ringᵉ Rᵉ xᵉ (multiple-Ringᵉ Rᵉ nᵉ xᵉ)
  multiple-succ-Ring'ᵉ = multiple-succ-Ab'ᵉ (ab-Ringᵉ Rᵉ)
```

### Multiples by sums of natural numbers are products of multiples

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  right-distributive-multiple-add-Ringᵉ :
    (mᵉ nᵉ : ℕᵉ) {xᵉ : type-Ringᵉ Rᵉ} →
    multiple-Ringᵉ Rᵉ (mᵉ +ℕᵉ nᵉ) xᵉ ＝ᵉ
    add-Ringᵉ Rᵉ (multiple-Ringᵉ Rᵉ mᵉ xᵉ) (multiple-Ringᵉ Rᵉ nᵉ xᵉ)
  right-distributive-multiple-add-Ringᵉ =
    right-distributive-multiple-add-Abᵉ (ab-Ringᵉ Rᵉ)
```

### Multiples distribute over the sum of `x` and `y`

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  left-distributive-multiple-add-Ringᵉ :
    (nᵉ : ℕᵉ) {xᵉ yᵉ : type-Ringᵉ Rᵉ} →
    multiple-Ringᵉ Rᵉ nᵉ (add-Ringᵉ Rᵉ xᵉ yᵉ) ＝ᵉ
    add-Ringᵉ Rᵉ (multiple-Ringᵉ Rᵉ nᵉ xᵉ) (multiple-Ringᵉ Rᵉ nᵉ yᵉ)
  left-distributive-multiple-add-Ringᵉ =
    left-distributive-multiple-add-Abᵉ (ab-Ringᵉ Rᵉ)
```

### Multiples by products of natural numbers are iterated multiples

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  multiple-mul-Ringᵉ :
    (mᵉ nᵉ : ℕᵉ) {xᵉ : type-Ringᵉ Rᵉ} →
    multiple-Ringᵉ Rᵉ (mᵉ *ℕᵉ nᵉ) xᵉ ＝ᵉ multiple-Ringᵉ Rᵉ nᵉ (multiple-Ringᵉ Rᵉ mᵉ xᵉ)
  multiple-mul-Ringᵉ = multiple-mul-Abᵉ (ab-Ringᵉ Rᵉ)
```