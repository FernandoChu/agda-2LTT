# Multiples of elements in commutative rings

```agda
module commutative-algebra.multiples-of-elements-commutative-ringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-ringsᵉ

open import elementary-number-theory.addition-natural-numbersᵉ
open import elementary-number-theory.multiplication-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ

open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ

open import ring-theory.multiples-of-elements-ringsᵉ
```

</details>

## Idea

Forᵉ anyᵉ [commutativeᵉ ring](commutative-algebra.commutative-rings.mdᵉ) `A`ᵉ thereᵉ
isᵉ aᵉ multiplicationᵉ operationᵉ `ℕᵉ → Aᵉ → A`,ᵉ whichᵉ weᵉ writeᵉ informallyᵉ asᵉ
`nᵉ xᵉ ↦ᵉ nᵉ ·ᵉ x`.ᵉ Thisᵉ operationᵉ isᵉ definedᵉ byᵉ
[iteratively](foundation.iterating-functions.mdᵉ) addingᵉ `x`ᵉ with itselfᵉ `n`ᵉ
times.ᵉ

## Definition

### Natural number multiples of elements of commutative rings

```agda
module _
  {lᵉ : Level} (Aᵉ : Commutative-Ringᵉ lᵉ)
  where

  multiple-Commutative-Ringᵉ :
    ℕᵉ → type-Commutative-Ringᵉ Aᵉ → type-Commutative-Ringᵉ Aᵉ
  multiple-Commutative-Ringᵉ =
    multiple-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)
```

## Properties

### `n · 0 ＝ 0`

```agda
module _
  {lᵉ : Level} (Aᵉ : Commutative-Ringᵉ lᵉ)
  where

  multiple-zero-Commutative-Ringᵉ :
    (nᵉ : ℕᵉ) →
    multiple-Commutative-Ringᵉ Aᵉ nᵉ (zero-Commutative-Ringᵉ Aᵉ) ＝ᵉ
    zero-Commutative-Ringᵉ Aᵉ
  multiple-zero-Commutative-Ringᵉ =
    multiple-zero-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)
```

### `(n + 1) · x = n · x + x`

```agda
module _
  {lᵉ : Level} (Aᵉ : Commutative-Ringᵉ lᵉ)
  where

  multiple-succ-Commutative-Ringᵉ :
    (nᵉ : ℕᵉ) (xᵉ : type-Commutative-Ringᵉ Aᵉ) →
    multiple-Commutative-Ringᵉ Aᵉ (succ-ℕᵉ nᵉ) xᵉ ＝ᵉ
    add-Commutative-Ringᵉ Aᵉ (multiple-Commutative-Ringᵉ Aᵉ nᵉ xᵉ) xᵉ
  multiple-succ-Commutative-Ringᵉ =
    multiple-succ-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)
```

### `(n + 1) · x ＝ x + n · x`

```agda
module _
  {lᵉ : Level} (Aᵉ : Commutative-Ringᵉ lᵉ)
  where

  multiple-succ-Commutative-Ring'ᵉ :
    (nᵉ : ℕᵉ) (xᵉ : type-Commutative-Ringᵉ Aᵉ) →
    multiple-Commutative-Ringᵉ Aᵉ (succ-ℕᵉ nᵉ) xᵉ ＝ᵉ
    add-Commutative-Ringᵉ Aᵉ xᵉ (multiple-Commutative-Ringᵉ Aᵉ nᵉ xᵉ)
  multiple-succ-Commutative-Ring'ᵉ =
    multiple-succ-Ring'ᵉ (ring-Commutative-Ringᵉ Aᵉ)
```

### Multiples by sums of natural numbers are products of multiples

```agda
module _
  {lᵉ : Level} (Aᵉ : Commutative-Ringᵉ lᵉ)
  where

  right-distributive-multiple-add-Commutative-Ringᵉ :
    (mᵉ nᵉ : ℕᵉ) {xᵉ : type-Commutative-Ringᵉ Aᵉ} →
    multiple-Commutative-Ringᵉ Aᵉ (mᵉ +ℕᵉ nᵉ) xᵉ ＝ᵉ
    add-Commutative-Ringᵉ Aᵉ
      ( multiple-Commutative-Ringᵉ Aᵉ mᵉ xᵉ)
      ( multiple-Commutative-Ringᵉ Aᵉ nᵉ xᵉ)
  right-distributive-multiple-add-Commutative-Ringᵉ =
    right-distributive-multiple-add-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)
```

### Multiples distribute over the sum of `x` and `y`

```agda
module _
  {lᵉ : Level} (Aᵉ : Commutative-Ringᵉ lᵉ)
  where

  left-distributive-multiple-add-Commutative-Ringᵉ :
    (nᵉ : ℕᵉ) {xᵉ yᵉ : type-Commutative-Ringᵉ Aᵉ} →
    multiple-Commutative-Ringᵉ Aᵉ nᵉ (add-Commutative-Ringᵉ Aᵉ xᵉ yᵉ) ＝ᵉ
    add-Commutative-Ringᵉ Aᵉ
      ( multiple-Commutative-Ringᵉ Aᵉ nᵉ xᵉ)
      ( multiple-Commutative-Ringᵉ Aᵉ nᵉ yᵉ)
  left-distributive-multiple-add-Commutative-Ringᵉ =
    left-distributive-multiple-add-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)
```

### Multiples by products of natural numbers are iterated multiples

```agda
module _
  {lᵉ : Level} (Aᵉ : Commutative-Ringᵉ lᵉ)
  where

  multiple-mul-Commutative-Ringᵉ :
    (mᵉ nᵉ : ℕᵉ) {xᵉ : type-Commutative-Ringᵉ Aᵉ} →
    multiple-Commutative-Ringᵉ Aᵉ (mᵉ *ℕᵉ nᵉ) xᵉ ＝ᵉ
    multiple-Commutative-Ringᵉ Aᵉ nᵉ (multiple-Commutative-Ringᵉ Aᵉ mᵉ xᵉ)
  multiple-mul-Commutative-Ringᵉ =
    multiple-mul-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)
```