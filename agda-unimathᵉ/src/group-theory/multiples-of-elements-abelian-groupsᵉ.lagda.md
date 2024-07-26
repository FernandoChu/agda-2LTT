# Multiples of elements in abelian groups

```agda
module group-theory.multiples-of-elements-abelian-groupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbersᵉ
open import elementary-number-theory.multiplication-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ

open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.abelian-groupsᵉ
open import group-theory.powers-of-elements-groupsᵉ
```

</details>

## Idea

Theᵉ multiplicationᵉ operationᵉ onᵉ anᵉ
[abelianᵉ group](group-theory.abelian-groups.mdᵉ) isᵉ theᵉ mapᵉ `nᵉ xᵉ ↦ᵉ nᵉ ·ᵉ x`,ᵉ whichᵉ
isᵉ definedᵉ byᵉ [iteratively](foundation.iterating-functions.mdᵉ) addingᵉ `x`ᵉ with
itselfᵉ `n`ᵉ times.ᵉ Weᵉ defineᵉ thisᵉ operationᵉ where `n`ᵉ rangesᵉ overᵉ theᵉ
[naturalᵉ numbers](elementary-number-theory.natural-numbers.md),ᵉ asᵉ wellᵉ asᵉ where
`n`ᵉ rangesᵉ overᵉ theᵉ [integers](elementary-number-theory.integers.md).ᵉ

## Definition

### Natural number multiples of abelian group elements

```agda
module _
  {lᵉ : Level} (Aᵉ : Abᵉ lᵉ)
  where

  multiple-Abᵉ : ℕᵉ → type-Abᵉ Aᵉ → type-Abᵉ Aᵉ
  multiple-Abᵉ = power-Groupᵉ (group-Abᵉ Aᵉ)
```

### The predicate of being a natural multiple of an element in an abelian group

Weᵉ sayᵉ thatᵉ anᵉ elementᵉ `y`ᵉ **isᵉ aᵉ multiple**ᵉ ofᵉ anᵉ elementᵉ `x`ᵉ ifᵉ thereᵉ
[exists](foundation.existential-quantification.mdᵉ) aᵉ numberᵉ `n`ᵉ suchᵉ thatᵉ
`nxᵉ ＝ᵉ y`.ᵉ

```agda
module _
  {lᵉ : Level} (Aᵉ : Abᵉ lᵉ)
  where

  is-multiple-of-element-prop-Abᵉ :
    (xᵉ yᵉ : type-Abᵉ Aᵉ) → Propᵉ lᵉ
  is-multiple-of-element-prop-Abᵉ =
    is-power-of-element-prop-Groupᵉ (group-Abᵉ Aᵉ)

  is-multiple-of-element-Abᵉ :
    (xᵉ yᵉ : type-Abᵉ Aᵉ) → UUᵉ lᵉ
  is-multiple-of-element-Abᵉ =
    is-power-of-element-Groupᵉ (group-Abᵉ Aᵉ)

  is-prop-is-multiple-of-element-Abᵉ :
    (xᵉ yᵉ : type-Abᵉ Aᵉ) →
    is-propᵉ (is-multiple-of-element-Abᵉ xᵉ yᵉ)
  is-prop-is-multiple-of-element-Abᵉ =
    is-prop-is-power-of-element-Groupᵉ (group-Abᵉ Aᵉ)
```

## Properties

### `n · 0 ＝ 0`

```agda
module _
  {lᵉ : Level} (Aᵉ : Abᵉ lᵉ)
  where

  multiple-zero-Abᵉ :
    (nᵉ : ℕᵉ) → multiple-Abᵉ Aᵉ nᵉ (zero-Abᵉ Aᵉ) ＝ᵉ zero-Abᵉ Aᵉ
  multiple-zero-Abᵉ = power-unit-Groupᵉ (group-Abᵉ Aᵉ)
```

### `(n + 1) · x = n · x + x`

```agda
module _
  {lᵉ : Level} (Aᵉ : Abᵉ lᵉ)
  where

  multiple-succ-Abᵉ :
    (nᵉ : ℕᵉ) (xᵉ : type-Abᵉ Aᵉ) →
    multiple-Abᵉ Aᵉ (succ-ℕᵉ nᵉ) xᵉ ＝ᵉ add-Abᵉ Aᵉ (multiple-Abᵉ Aᵉ nᵉ xᵉ) xᵉ
  multiple-succ-Abᵉ = power-succ-Groupᵉ (group-Abᵉ Aᵉ)
```

### `(n + 1) · x ＝ x + n · x`

```agda
module _
  {lᵉ : Level} (Aᵉ : Abᵉ lᵉ)
  where

  multiple-succ-Ab'ᵉ :
    (nᵉ : ℕᵉ) (xᵉ : type-Abᵉ Aᵉ) →
    multiple-Abᵉ Aᵉ (succ-ℕᵉ nᵉ) xᵉ ＝ᵉ add-Abᵉ Aᵉ xᵉ (multiple-Abᵉ Aᵉ nᵉ xᵉ)
  multiple-succ-Ab'ᵉ = power-succ-Group'ᵉ (group-Abᵉ Aᵉ)
```

### Multiples by sums of natural numbers are products of multiples

```agda
module _
  {lᵉ : Level} (Aᵉ : Abᵉ lᵉ)
  where

  right-distributive-multiple-add-Abᵉ :
    (mᵉ nᵉ : ℕᵉ) {xᵉ : type-Abᵉ Aᵉ} →
    multiple-Abᵉ Aᵉ (mᵉ +ℕᵉ nᵉ) xᵉ ＝ᵉ
    add-Abᵉ Aᵉ (multiple-Abᵉ Aᵉ mᵉ xᵉ) (multiple-Abᵉ Aᵉ nᵉ xᵉ)
  right-distributive-multiple-add-Abᵉ = distributive-power-add-Groupᵉ (group-Abᵉ Aᵉ)
```

### Multiples distribute over the sum of `x` and `y`

```agda
module _
  {lᵉ : Level} (Aᵉ : Abᵉ lᵉ)
  where

  left-distributive-multiple-add-Abᵉ :
    (nᵉ : ℕᵉ) {xᵉ yᵉ : type-Abᵉ Aᵉ} →
    multiple-Abᵉ Aᵉ nᵉ (add-Abᵉ Aᵉ xᵉ yᵉ) ＝ᵉ
    add-Abᵉ Aᵉ (multiple-Abᵉ Aᵉ nᵉ xᵉ) (multiple-Abᵉ Aᵉ nᵉ yᵉ)
  left-distributive-multiple-add-Abᵉ nᵉ =
    distributive-power-mul-Groupᵉ (group-Abᵉ Aᵉ) nᵉ (commutative-add-Abᵉ Aᵉ _ _)
```

### Multiples by products of natural numbers are iterated multiples

```agda
module _
  {lᵉ : Level} (Aᵉ : Abᵉ lᵉ)
  where

  multiple-mul-Abᵉ :
    (mᵉ nᵉ : ℕᵉ) {xᵉ : type-Abᵉ Aᵉ} →
    multiple-Abᵉ Aᵉ (mᵉ *ℕᵉ nᵉ) xᵉ ＝ᵉ multiple-Abᵉ Aᵉ nᵉ (multiple-Abᵉ Aᵉ mᵉ xᵉ)
  multiple-mul-Abᵉ = power-mul-Groupᵉ (group-Abᵉ Aᵉ)
```