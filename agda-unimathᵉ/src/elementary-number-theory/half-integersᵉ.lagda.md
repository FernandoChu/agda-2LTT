# The half-integers

```agda
module elementary-number-theory.half-integersᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integersᵉ
open import elementary-number-theory.integersᵉ

open import foundation.coproduct-typesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Theᵉ **half-integers**ᵉ areᵉ theᵉ numbersᵉ ofᵉ theᵉ formᵉ `xᵉ +ᵉ ½`,ᵉ where `xᵉ : ℤ`.ᵉ

## Definition

### The half-integers

```agda
ℤ+½ᵉ : UUᵉ lzero
ℤ+½ᵉ = ℤᵉ
```

### The disjoint union of the half-integers with the integers

```agda
½ℤᵉ : UUᵉ lzero
½ℤᵉ = ℤ+½ᵉ +ᵉ ℤᵉ
```

### The zero element of `½ℤ`

```agda
zero-½ℤᵉ : ½ℤᵉ
zero-½ℤᵉ = inrᵉ zero-ℤᵉ
```

### Addition on `½ℤ`

```agda
add-½ℤᵉ : ½ℤᵉ → ½ℤᵉ → ½ℤᵉ
add-½ℤᵉ (inlᵉ xᵉ) (inlᵉ yᵉ) = inrᵉ (succ-ℤᵉ (xᵉ +ℤᵉ yᵉ))
add-½ℤᵉ (inlᵉ xᵉ) (inrᵉ yᵉ) = inlᵉ (xᵉ +ℤᵉ yᵉ)
add-½ℤᵉ (inrᵉ xᵉ) (inlᵉ yᵉ) = inlᵉ (xᵉ +ℤᵉ yᵉ)
add-½ℤᵉ (inrᵉ xᵉ) (inrᵉ yᵉ) = inrᵉ (xᵉ +ℤᵉ yᵉ)

infixl 35 _+½ℤᵉ_
_+½ℤᵉ_ = add-½ℤᵉ
```