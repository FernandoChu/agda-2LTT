# The absolute value function on the integers

```agda
module elementary-number-theory.absolute-value-integersᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integersᵉ
open import elementary-number-theory.addition-natural-numbersᵉ
open import elementary-number-theory.inequality-natural-numbersᵉ
open import elementary-number-theory.integersᵉ
open import elementary-number-theory.multiplication-integersᵉ
open import elementary-number-theory.multiplication-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ
open import elementary-number-theory.nonnegative-integersᵉ
open import elementary-number-theory.positive-integersᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.coproduct-typesᵉ
open import foundation.function-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.unit-typeᵉ
```

</details>

## Idea

Theᵉ absoluteᵉ valueᵉ ofᵉ anᵉ integerᵉ isᵉ theᵉ naturalᵉ numberᵉ with theᵉ sameᵉ distanceᵉ
fromᵉ `0`.ᵉ

## Definition

```agda
abs-ℤᵉ : ℤᵉ → ℕᵉ
abs-ℤᵉ (inlᵉ xᵉ) = succ-ℕᵉ xᵉ
abs-ℤᵉ (inrᵉ (inlᵉ starᵉ)) = zero-ℕᵉ
abs-ℤᵉ (inrᵉ (inrᵉ xᵉ)) = succ-ℕᵉ xᵉ

int-abs-ℤᵉ : ℤᵉ → ℤᵉ
int-abs-ℤᵉ = int-ℕᵉ ∘ᵉ abs-ℤᵉ
```

## Properties

### The absolute value of `int-ℕ n` is `n` itself

```agda
abs-int-ℕᵉ : (nᵉ : ℕᵉ) → abs-ℤᵉ (int-ℕᵉ nᵉ) ＝ᵉ nᵉ
abs-int-ℕᵉ zero-ℕᵉ = reflᵉ
abs-int-ℕᵉ (succ-ℕᵉ nᵉ) = reflᵉ
```

### `|-x| ＝ |x|`

```agda
abs-neg-ℤᵉ : (xᵉ : ℤᵉ) → abs-ℤᵉ (neg-ℤᵉ xᵉ) ＝ᵉ abs-ℤᵉ xᵉ
abs-neg-ℤᵉ (inlᵉ xᵉ) = reflᵉ
abs-neg-ℤᵉ (inrᵉ (inlᵉ starᵉ)) = reflᵉ
abs-neg-ℤᵉ (inrᵉ (inrᵉ xᵉ)) = reflᵉ
```

### If `x` is nonnegative, then `int-abs-ℤ x ＝ x`

```agda
int-abs-is-nonnegative-ℤᵉ : (xᵉ : ℤᵉ) → is-nonnegative-ℤᵉ xᵉ → int-abs-ℤᵉ xᵉ ＝ᵉ xᵉ
int-abs-is-nonnegative-ℤᵉ (inrᵉ (inlᵉ starᵉ)) hᵉ = reflᵉ
int-abs-is-nonnegative-ℤᵉ (inrᵉ (inrᵉ xᵉ)) hᵉ = reflᵉ
```

### `|x| ＝ 0` if and only if `x ＝ 0`

```agda
eq-abs-ℤᵉ : (xᵉ : ℤᵉ) → is-zero-ℕᵉ (abs-ℤᵉ xᵉ) → is-zero-ℤᵉ xᵉ
eq-abs-ℤᵉ (inrᵉ (inlᵉ starᵉ)) pᵉ = reflᵉ

abs-eq-ℤᵉ : (xᵉ : ℤᵉ) → is-zero-ℤᵉ xᵉ → is-zero-ℕᵉ (abs-ℤᵉ xᵉ)
abs-eq-ℤᵉ .zero-ℤᵉ reflᵉ = reflᵉ
```

### `|x - 1| ≤ |x| + 1`

```agda
predecessor-law-abs-ℤᵉ :
  (xᵉ : ℤᵉ) → (abs-ℤᵉ (pred-ℤᵉ xᵉ)) ≤-ℕᵉ (succ-ℕᵉ (abs-ℤᵉ xᵉ))
predecessor-law-abs-ℤᵉ (inlᵉ xᵉ) =
  refl-leq-ℕᵉ (succ-ℕᵉ xᵉ)
predecessor-law-abs-ℤᵉ (inrᵉ (inlᵉ starᵉ)) =
  refl-leq-ℕᵉ zero-ℕᵉ
predecessor-law-abs-ℤᵉ (inrᵉ (inrᵉ zero-ℕᵉ)) =
  starᵉ
predecessor-law-abs-ℤᵉ (inrᵉ (inrᵉ (succ-ℕᵉ xᵉ))) =
  preserves-leq-succ-ℕᵉ xᵉ (succ-ℕᵉ xᵉ) (succ-leq-ℕᵉ xᵉ)
```

### `|x + 1| ≤ |x| + 1`

```agda
successor-law-abs-ℤᵉ :
  (xᵉ : ℤᵉ) → (abs-ℤᵉ (succ-ℤᵉ xᵉ)) ≤-ℕᵉ (succ-ℕᵉ (abs-ℤᵉ xᵉ))
successor-law-abs-ℤᵉ (inlᵉ zero-ℕᵉ) =
  starᵉ
successor-law-abs-ℤᵉ (inlᵉ (succ-ℕᵉ xᵉ)) =
  preserves-leq-succ-ℕᵉ xᵉ (succ-ℕᵉ xᵉ) (succ-leq-ℕᵉ xᵉ)
successor-law-abs-ℤᵉ (inrᵉ (inlᵉ starᵉ)) =
  refl-leq-ℕᵉ zero-ℕᵉ
successor-law-abs-ℤᵉ (inrᵉ (inrᵉ xᵉ)) =
  refl-leq-ℕᵉ (succ-ℕᵉ xᵉ)
```

### The absolute value function is subadditive

```agda
subadditive-abs-ℤᵉ :
  (xᵉ yᵉ : ℤᵉ) → (abs-ℤᵉ (xᵉ +ℤᵉ yᵉ)) ≤-ℕᵉ ((abs-ℤᵉ xᵉ) +ℕᵉ (abs-ℤᵉ yᵉ))
subadditive-abs-ℤᵉ xᵉ (inlᵉ zero-ℕᵉ) =
  concatenate-eq-leq-eq-ℕᵉ
    ( apᵉ abs-ℤᵉ (right-add-neg-one-ℤᵉ xᵉ))
    ( predecessor-law-abs-ℤᵉ xᵉ)
    ( reflᵉ)
subadditive-abs-ℤᵉ xᵉ (inlᵉ (succ-ℕᵉ yᵉ)) =
  concatenate-eq-leq-eq-ℕᵉ
    ( apᵉ abs-ℤᵉ (right-predecessor-law-add-ℤᵉ xᵉ (inlᵉ yᵉ)))
    ( transitive-leq-ℕᵉ
      ( abs-ℤᵉ (pred-ℤᵉ (xᵉ +ℤᵉ (inlᵉ yᵉ))))
      ( succ-ℕᵉ (abs-ℤᵉ (xᵉ +ℤᵉ (inlᵉ yᵉ))))
      ( (abs-ℤᵉ xᵉ) +ℕᵉ (succ-ℕᵉ (succ-ℕᵉ yᵉ)))
      ( subadditive-abs-ℤᵉ xᵉ (inlᵉ yᵉ))
      ( predecessor-law-abs-ℤᵉ (xᵉ +ℤᵉ (inlᵉ yᵉ))))
    ( reflᵉ)
subadditive-abs-ℤᵉ xᵉ (inrᵉ (inlᵉ starᵉ)) =
  concatenate-eq-leq-eq-ℕᵉ
    ( apᵉ abs-ℤᵉ (right-unit-law-add-ℤᵉ xᵉ))
    ( refl-leq-ℕᵉ (abs-ℤᵉ xᵉ))
    ( reflᵉ)
subadditive-abs-ℤᵉ xᵉ (inrᵉ (inrᵉ zero-ℕᵉ)) =
  concatenate-eq-leq-eq-ℕᵉ
    ( apᵉ abs-ℤᵉ (right-add-one-ℤᵉ xᵉ))
    ( successor-law-abs-ℤᵉ xᵉ)
    ( reflᵉ)
subadditive-abs-ℤᵉ xᵉ (inrᵉ (inrᵉ (succ-ℕᵉ yᵉ))) =
  concatenate-eq-leq-eq-ℕᵉ
    ( apᵉ abs-ℤᵉ (right-successor-law-add-ℤᵉ xᵉ (inrᵉ (inrᵉ yᵉ))))
    ( transitive-leq-ℕᵉ
      ( abs-ℤᵉ (succ-ℤᵉ (xᵉ +ℤᵉ (inrᵉ (inrᵉ yᵉ)))))
      ( succ-ℕᵉ (abs-ℤᵉ (xᵉ +ℤᵉ (inrᵉ (inrᵉ yᵉ)))))
      ( succ-ℕᵉ ((abs-ℤᵉ xᵉ) +ℕᵉ (succ-ℕᵉ yᵉ)))
      ( subadditive-abs-ℤᵉ xᵉ (inrᵉ (inrᵉ yᵉ)))
      ( successor-law-abs-ℤᵉ (xᵉ +ℤᵉ (inrᵉ (inrᵉ yᵉ)))))
    ( reflᵉ)
```

### `|-x| ＝ |x|`

```agda
negative-law-abs-ℤᵉ :
  (xᵉ : ℤᵉ) → abs-ℤᵉ (neg-ℤᵉ xᵉ) ＝ᵉ abs-ℤᵉ xᵉ
negative-law-abs-ℤᵉ (inlᵉ xᵉ) = reflᵉ
negative-law-abs-ℤᵉ (inrᵉ (inlᵉ starᵉ)) = reflᵉ
negative-law-abs-ℤᵉ (inrᵉ (inrᵉ xᵉ)) = reflᵉ
```

### If `x` is positive then `|x|` is positive

```agda
is-positive-abs-ℤᵉ :
  (xᵉ : ℤᵉ) → is-positive-ℤᵉ xᵉ → is-positive-ℤᵉ (int-abs-ℤᵉ xᵉ)
is-positive-abs-ℤᵉ (inrᵉ (inrᵉ xᵉ)) Hᵉ = starᵉ
```

### If `x` is nonzero then `|x|` is nonzero

```agda
is-nonzero-abs-ℤᵉ :
  (xᵉ : ℤᵉ) → is-positive-ℤᵉ xᵉ → is-nonzero-ℕᵉ (abs-ℤᵉ xᵉ)
is-nonzero-abs-ℤᵉ (inrᵉ (inrᵉ xᵉ)) Hᵉ = is-nonzero-succ-ℕᵉ xᵉ
```

### The absolute value function is multiplicative

```agda
multiplicative-abs-ℤ'ᵉ :
  (xᵉ yᵉ : ℤᵉ) → abs-ℤᵉ (explicit-mul-ℤᵉ xᵉ yᵉ) ＝ᵉ (abs-ℤᵉ xᵉ) *ℕᵉ (abs-ℤᵉ yᵉ)
multiplicative-abs-ℤ'ᵉ (inlᵉ xᵉ) (inlᵉ yᵉ) =
  abs-int-ℕᵉ _
multiplicative-abs-ℤ'ᵉ (inlᵉ xᵉ) (inrᵉ (inlᵉ starᵉ)) =
  invᵉ (right-zero-law-mul-ℕᵉ xᵉ)
multiplicative-abs-ℤ'ᵉ (inlᵉ xᵉ) (inrᵉ (inrᵉ yᵉ)) =
  ( abs-neg-ℤᵉ (inlᵉ ((xᵉ *ℕᵉ (succ-ℕᵉ yᵉ)) +ℕᵉ yᵉ))) ∙ᵉ
  ( abs-int-ℕᵉ ((succ-ℕᵉ xᵉ) *ℕᵉ (succ-ℕᵉ yᵉ)))
multiplicative-abs-ℤ'ᵉ (inrᵉ (inlᵉ starᵉ)) (inlᵉ yᵉ) =
  reflᵉ
multiplicative-abs-ℤ'ᵉ (inrᵉ (inrᵉ xᵉ)) (inlᵉ yᵉ) =
  ( abs-neg-ℤᵉ (inlᵉ ((xᵉ *ℕᵉ (succ-ℕᵉ yᵉ)) +ℕᵉ yᵉ))) ∙ᵉ
  ( abs-int-ℕᵉ (succ-ℕᵉ ((xᵉ *ℕᵉ (succ-ℕᵉ yᵉ)) +ℕᵉ yᵉ)))
multiplicative-abs-ℤ'ᵉ (inrᵉ (inlᵉ starᵉ)) (inrᵉ (inlᵉ starᵉ)) =
  reflᵉ
multiplicative-abs-ℤ'ᵉ (inrᵉ (inlᵉ starᵉ)) (inrᵉ (inrᵉ xᵉ)) =
  reflᵉ
multiplicative-abs-ℤ'ᵉ (inrᵉ (inrᵉ xᵉ)) (inrᵉ (inlᵉ starᵉ)) =
  invᵉ (right-zero-law-mul-ℕᵉ (succ-ℕᵉ xᵉ))
multiplicative-abs-ℤ'ᵉ (inrᵉ (inrᵉ xᵉ)) (inrᵉ (inrᵉ yᵉ)) =
  abs-int-ℕᵉ _

multiplicative-abs-ℤᵉ :
  (xᵉ yᵉ : ℤᵉ) → abs-ℤᵉ (xᵉ *ℤᵉ yᵉ) ＝ᵉ (abs-ℤᵉ xᵉ) *ℕᵉ (abs-ℤᵉ yᵉ)
multiplicative-abs-ℤᵉ xᵉ yᵉ =
  apᵉ abs-ℤᵉ (compute-mul-ℤᵉ xᵉ yᵉ) ∙ᵉ multiplicative-abs-ℤ'ᵉ xᵉ yᵉ
```

### `|(-x)y| ＝ |xy|`

```agda
left-negative-law-mul-abs-ℤᵉ :
  (xᵉ yᵉ : ℤᵉ) → abs-ℤᵉ (xᵉ *ℤᵉ yᵉ) ＝ᵉ abs-ℤᵉ ((neg-ℤᵉ xᵉ) *ℤᵉ yᵉ)
left-negative-law-mul-abs-ℤᵉ xᵉ yᵉ =
  equational-reasoningᵉ
    abs-ℤᵉ (xᵉ *ℤᵉ yᵉ)
    ＝ᵉ abs-ℤᵉ (neg-ℤᵉ (xᵉ *ℤᵉ yᵉ))
      byᵉ (invᵉ (negative-law-abs-ℤᵉ (xᵉ *ℤᵉ yᵉ)))
    ＝ᵉ abs-ℤᵉ ((neg-ℤᵉ xᵉ) *ℤᵉ yᵉ)
      byᵉ (apᵉ abs-ℤᵉ (invᵉ (left-negative-law-mul-ℤᵉ xᵉ yᵉ)))
```

### `|x(-y)| ＝ |xy|`

```agda
right-negative-law-mul-abs-ℤᵉ :
  (xᵉ yᵉ : ℤᵉ) → abs-ℤᵉ (xᵉ *ℤᵉ yᵉ) ＝ᵉ abs-ℤᵉ (xᵉ *ℤᵉ (neg-ℤᵉ yᵉ))
right-negative-law-mul-abs-ℤᵉ xᵉ yᵉ =
  equational-reasoningᵉ
    abs-ℤᵉ (xᵉ *ℤᵉ yᵉ)
    ＝ᵉ abs-ℤᵉ (neg-ℤᵉ (xᵉ *ℤᵉ yᵉ))
      byᵉ (invᵉ (negative-law-abs-ℤᵉ (xᵉ *ℤᵉ yᵉ)))
    ＝ᵉ abs-ℤᵉ (xᵉ *ℤᵉ (neg-ℤᵉ yᵉ))
      byᵉ (apᵉ abs-ℤᵉ (invᵉ (right-negative-law-mul-ℤᵉ xᵉ yᵉ)))
```

### `|(-x)(-y)| ＝ |xy|`

```agda
double-negative-law-mul-abs-ℤᵉ :
  (xᵉ yᵉ : ℤᵉ) → abs-ℤᵉ (xᵉ *ℤᵉ yᵉ) ＝ᵉ abs-ℤᵉ ((neg-ℤᵉ xᵉ) *ℤᵉ (neg-ℤᵉ yᵉ))
double-negative-law-mul-abs-ℤᵉ xᵉ yᵉ =
  (right-negative-law-mul-abs-ℤᵉ xᵉ yᵉ) ∙ᵉ (left-negative-law-mul-abs-ℤᵉ xᵉ (neg-ℤᵉ yᵉ))
```