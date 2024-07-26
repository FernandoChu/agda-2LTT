# Multiplication of positive, negative, nonnegative and nonpositive integers

```agda
module elementary-number-theory.multiplication-positive-and-negative-integersᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-positive-and-negative-integersᵉ
open import elementary-number-theory.inequality-integersᵉ
open import elementary-number-theory.integersᵉ
open import elementary-number-theory.multiplication-integersᵉ
open import elementary-number-theory.natural-numbersᵉ
open import elementary-number-theory.negative-integersᵉ
open import elementary-number-theory.nonnegative-integersᵉ
open import elementary-number-theory.nonpositive-integersᵉ
open import elementary-number-theory.positive-and-negative-integersᵉ
open import elementary-number-theory.positive-integersᵉ
open import elementary-number-theory.strict-inequality-integersᵉ

open import foundation.coproduct-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.empty-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.unit-typeᵉ
```

</details>

## Idea

Whenᵉ weᵉ haveᵉ informationᵉ aboutᵉ theᵉ signᵉ ofᵉ theᵉ factorsᵉ ofᵉ anᵉ
[integerᵉ product](elementary-number-theory.multiplication-integers.md),ᵉ weᵉ canᵉ
deduceᵉ theᵉ signᵉ ofᵉ theirᵉ productᵉ too.ᵉ Theᵉ tableᵉ belowᵉ tabulatesᵉ everyᵉ caseᵉ andᵉ
displaysᵉ theᵉ correspondingᵉ Agdaᵉ definition.ᵉ

|     `p`ᵉ     |     `q`ᵉ     |  `pᵉ *ℤᵉ q`ᵉ   | operationᵉ           |
| :---------ᵉ: | :---------ᵉ: | :---------ᵉ: | -------------------ᵉ |
|  positiveᵉ   |  positiveᵉ   |  positiveᵉ   | `mul-positive-ℤ`ᵉ    |
|  positiveᵉ   | nonnegativeᵉ | nonnegativeᵉ |                     |
|  positiveᵉ   |  negativeᵉ   |  negativeᵉ   |                     |
|  positiveᵉ   | nonpositiveᵉ | nonpositiveᵉ |                     |
| nonnegativeᵉ |  positiveᵉ   | nonnegativeᵉ |                     |
| nonnegativeᵉ | nonnegativeᵉ | nonnegativeᵉ | `mul-nonnegative-ℤ`ᵉ |
| nonnegativeᵉ |  negativeᵉ   | nonpositiveᵉ |                     |
| nonnegativeᵉ | nonpositiveᵉ | nonpositiveᵉ |                     |
|  negativeᵉ   |  positiveᵉ   |  negativeᵉ   |                     |
|  negativeᵉ   | nonnegativeᵉ | nonpositiveᵉ |                     |
|  negativeᵉ   |  negativeᵉ   |  positiveᵉ   | `mul-negative-ℤ`ᵉ    |
|  negativeᵉ   | nonpositiveᵉ | nonnegativeᵉ |                     |
| nonpositiveᵉ |  positiveᵉ   | nonpositiveᵉ |                     |
| nonpositiveᵉ | nonnegativeᵉ | nonpositiveᵉ |                     |
| nonpositiveᵉ |  negativeᵉ   | nonpositiveᵉ |                     |
| nonpositiveᵉ | nonpositiveᵉ | nonnegativeᵉ | `mul-nonpositive-ℤ`ᵉ |

Asᵉ aᵉ consequence,ᵉ multiplicationᵉ byᵉ aᵉ positiveᵉ integerᵉ preservesᵉ andᵉ reflectsᵉ
strictᵉ inequalityᵉ andᵉ multiplicationᵉ byᵉ aᵉ nonpositiveᵉ integerᵉ preservesᵉ
inequality.ᵉ

## Lemmas

### The product of two positive integers is positive

```agda
is-positive-mul-ℤᵉ :
  {xᵉ yᵉ : ℤᵉ} → is-positive-ℤᵉ xᵉ → is-positive-ℤᵉ yᵉ → is-positive-ℤᵉ (xᵉ *ℤᵉ yᵉ)
is-positive-mul-ℤᵉ {inrᵉ (inrᵉ zero-ℕᵉ)} {yᵉ} Hᵉ Kᵉ = Kᵉ
is-positive-mul-ℤᵉ {inrᵉ (inrᵉ (succ-ℕᵉ xᵉ))} {yᵉ} Hᵉ Kᵉ =
  is-positive-add-ℤᵉ Kᵉ (is-positive-mul-ℤᵉ {inrᵉ (inrᵉ xᵉ)} Hᵉ Kᵉ)
```

### The product of a positive and a nonnegative integer is nonnegative

```agda
is-nonnegative-mul-positive-nonnegative-ℤᵉ :
  {xᵉ yᵉ : ℤᵉ} → is-positive-ℤᵉ xᵉ → is-nonnegative-ℤᵉ yᵉ → is-nonnegative-ℤᵉ (xᵉ *ℤᵉ yᵉ)
is-nonnegative-mul-positive-nonnegative-ℤᵉ {inrᵉ (inrᵉ zero-ℕᵉ)} {yᵉ} Hᵉ Kᵉ = Kᵉ
is-nonnegative-mul-positive-nonnegative-ℤᵉ {inrᵉ (inrᵉ (succ-ℕᵉ xᵉ))} {yᵉ} Hᵉ Kᵉ =
  is-nonnegative-add-ℤᵉ Kᵉ
    ( is-nonnegative-mul-positive-nonnegative-ℤᵉ {inrᵉ (inrᵉ xᵉ)} Hᵉ Kᵉ)
```

### The product of a positive and a negative integer is negative

```agda
is-negative-mul-positive-negative-ℤᵉ :
  {xᵉ yᵉ : ℤᵉ} → is-positive-ℤᵉ xᵉ → is-negative-ℤᵉ yᵉ → is-negative-ℤᵉ (xᵉ *ℤᵉ yᵉ)
is-negative-mul-positive-negative-ℤᵉ {xᵉ} {yᵉ} Hᵉ Kᵉ =
  is-negative-eq-ℤᵉ
    ( neg-neg-ℤᵉ (xᵉ *ℤᵉ yᵉ))
    ( is-negative-neg-is-positive-ℤᵉ
      ( is-positive-eq-ℤᵉ
        ( right-negative-law-mul-ℤᵉ xᵉ yᵉ)
        ( is-positive-mul-ℤᵉ Hᵉ (is-positive-neg-is-negative-ℤᵉ Kᵉ))))
```

### The product of a positive and a nonpositive integer is nonpositive

```agda
is-nonpositive-mul-positive-nonpositive-ℤᵉ :
  {xᵉ yᵉ : ℤᵉ} → is-positive-ℤᵉ xᵉ → is-nonpositive-ℤᵉ yᵉ → is-nonpositive-ℤᵉ (xᵉ *ℤᵉ yᵉ)
is-nonpositive-mul-positive-nonpositive-ℤᵉ {xᵉ} {yᵉ} Hᵉ Kᵉ =
  is-nonpositive-eq-ℤᵉ
    ( neg-neg-ℤᵉ (xᵉ *ℤᵉ yᵉ))
    ( is-nonpositive-neg-is-nonnegative-ℤᵉ
      ( is-nonnegative-eq-ℤᵉ
        ( right-negative-law-mul-ℤᵉ xᵉ yᵉ)
        ( is-nonnegative-mul-positive-nonnegative-ℤᵉ Hᵉ
          ( is-nonnegative-neg-is-nonpositive-ℤᵉ Kᵉ))))
```

### The product of a nonnegative integer and a positive integer is nonnegative

```agda
is-nonnegative-mul-nonnegative-positive-ℤᵉ :
  {xᵉ yᵉ : ℤᵉ} → is-nonnegative-ℤᵉ xᵉ → is-positive-ℤᵉ yᵉ → is-nonnegative-ℤᵉ (xᵉ *ℤᵉ yᵉ)
is-nonnegative-mul-nonnegative-positive-ℤᵉ {xᵉ} {yᵉ} Hᵉ Kᵉ =
  is-nonnegative-eq-ℤᵉ
    ( commutative-mul-ℤᵉ yᵉ xᵉ)
    ( is-nonnegative-mul-positive-nonnegative-ℤᵉ Kᵉ Hᵉ)
```

### The product of two nonnegative integers is nonnegative

```agda
is-nonnegative-mul-ℤᵉ :
  {xᵉ yᵉ : ℤᵉ} →
  is-nonnegative-ℤᵉ xᵉ → is-nonnegative-ℤᵉ yᵉ → is-nonnegative-ℤᵉ (xᵉ *ℤᵉ yᵉ)
is-nonnegative-mul-ℤᵉ {inrᵉ (inlᵉ starᵉ)} {yᵉ} Hᵉ Kᵉ = starᵉ
is-nonnegative-mul-ℤᵉ {inrᵉ (inrᵉ xᵉ)} {inrᵉ (inlᵉ starᵉ)} Hᵉ Kᵉ =
  is-nonnegative-eq-ℤᵉ (invᵉ (right-zero-law-mul-ℤᵉ (inrᵉ (inrᵉ xᵉ)))) starᵉ
is-nonnegative-mul-ℤᵉ {inrᵉ (inrᵉ xᵉ)} {inrᵉ (inrᵉ yᵉ)} Hᵉ Kᵉ =
  is-nonnegative-eq-ℤᵉ (invᵉ (compute-mul-ℤᵉ (inrᵉ (inrᵉ xᵉ)) (inrᵉ (inrᵉ yᵉ)))) starᵉ
```

### The product of a nonnegative and a negative integer is nonpositive

```agda
is-nonpositive-mul-nonnegative-negative-ℤᵉ :
  {xᵉ yᵉ : ℤᵉ} → is-nonnegative-ℤᵉ xᵉ → is-negative-ℤᵉ yᵉ → is-nonpositive-ℤᵉ (xᵉ *ℤᵉ yᵉ)
is-nonpositive-mul-nonnegative-negative-ℤᵉ {xᵉ} {yᵉ} Hᵉ Kᵉ =
  is-nonpositive-eq-ℤᵉ
    ( neg-neg-ℤᵉ (xᵉ *ℤᵉ yᵉ))
    ( is-nonpositive-neg-is-nonnegative-ℤᵉ
      ( is-nonnegative-eq-ℤᵉ
        ( right-negative-law-mul-ℤᵉ xᵉ yᵉ)
        ( is-nonnegative-mul-nonnegative-positive-ℤᵉ Hᵉ
          ( is-positive-neg-is-negative-ℤᵉ Kᵉ))))
```

### The product of a nonnegative and a nonpositive integer is nonpositive

```agda
is-nonpositive-mul-nonnegative-nonpositive-ℤᵉ :
  {xᵉ yᵉ : ℤᵉ} →
  is-nonnegative-ℤᵉ xᵉ → is-nonpositive-ℤᵉ yᵉ → is-nonpositive-ℤᵉ (xᵉ *ℤᵉ yᵉ)
is-nonpositive-mul-nonnegative-nonpositive-ℤᵉ {xᵉ} {yᵉ} Hᵉ Kᵉ =
  is-nonpositive-eq-ℤᵉ
    ( neg-neg-ℤᵉ (xᵉ *ℤᵉ yᵉ))
    ( is-nonpositive-neg-is-nonnegative-ℤᵉ
      ( is-nonnegative-eq-ℤᵉ
        ( right-negative-law-mul-ℤᵉ xᵉ yᵉ)
        ( is-nonnegative-mul-ℤᵉ Hᵉ
          ( is-nonnegative-neg-is-nonpositive-ℤᵉ Kᵉ))))
```

### The product of a negative and a positive integer is negative

```agda
is-negative-mul-negative-positive-ℤᵉ :
  {xᵉ yᵉ : ℤᵉ} → is-negative-ℤᵉ xᵉ → is-positive-ℤᵉ yᵉ → is-negative-ℤᵉ (xᵉ *ℤᵉ yᵉ)
is-negative-mul-negative-positive-ℤᵉ {xᵉ} {yᵉ} Hᵉ Kᵉ =
  is-negative-eq-ℤᵉ
    ( commutative-mul-ℤᵉ yᵉ xᵉ)
    ( is-negative-mul-positive-negative-ℤᵉ Kᵉ Hᵉ)
```

### The product of a negative and a nonnegative integer is nonpositive

```agda
is-nonpositive-mul-negative-nonnegative-ℤᵉ :
  {xᵉ yᵉ : ℤᵉ} → is-negative-ℤᵉ xᵉ → is-nonnegative-ℤᵉ yᵉ → is-nonpositive-ℤᵉ (xᵉ *ℤᵉ yᵉ)
is-nonpositive-mul-negative-nonnegative-ℤᵉ {xᵉ} {yᵉ} Hᵉ Kᵉ =
  is-nonpositive-eq-ℤᵉ
    ( commutative-mul-ℤᵉ yᵉ xᵉ)
    ( is-nonpositive-mul-nonnegative-negative-ℤᵉ Kᵉ Hᵉ)
```

### The product of two negative integers is positive

```agda
is-positive-mul-negative-ℤᵉ :
  {xᵉ yᵉ : ℤᵉ} → is-negative-ℤᵉ xᵉ → is-negative-ℤᵉ yᵉ → is-positive-ℤᵉ (xᵉ *ℤᵉ yᵉ)
is-positive-mul-negative-ℤᵉ {xᵉ} {yᵉ} Hᵉ Kᵉ =
  is-positive-eq-ℤᵉ
    ( double-negative-law-mul-ℤᵉ xᵉ yᵉ)
    ( is-positive-mul-ℤᵉ
      ( is-positive-neg-is-negative-ℤᵉ Hᵉ)
      ( is-positive-neg-is-negative-ℤᵉ Kᵉ))
```

### The product of a negative and a nonpositive integer is nonnegative

```agda
is-nonnegative-mul-negative-nonpositive-ℤᵉ :
  {xᵉ yᵉ : ℤᵉ} → is-negative-ℤᵉ xᵉ → is-nonpositive-ℤᵉ yᵉ → is-nonnegative-ℤᵉ (xᵉ *ℤᵉ yᵉ)
is-nonnegative-mul-negative-nonpositive-ℤᵉ {xᵉ} {yᵉ} Hᵉ Kᵉ =
  is-nonnegative-eq-ℤᵉ
    ( double-negative-law-mul-ℤᵉ xᵉ yᵉ)
    ( is-nonnegative-mul-positive-nonnegative-ℤᵉ
      ( is-positive-neg-is-negative-ℤᵉ Hᵉ)
      ( is-nonnegative-neg-is-nonpositive-ℤᵉ Kᵉ))
```

### The product of a nonpositive and a positive integer is nonpositive

```agda
is-nonpositive-mul-nonpositive-positive-ℤᵉ :
  {xᵉ yᵉ : ℤᵉ} → is-nonpositive-ℤᵉ xᵉ → is-positive-ℤᵉ yᵉ → is-nonpositive-ℤᵉ (xᵉ *ℤᵉ yᵉ)
is-nonpositive-mul-nonpositive-positive-ℤᵉ {xᵉ} {yᵉ} Hᵉ Kᵉ =
  is-nonpositive-eq-ℤᵉ
    ( commutative-mul-ℤᵉ yᵉ xᵉ)
    ( is-nonpositive-mul-positive-nonpositive-ℤᵉ Kᵉ Hᵉ)
```

### The product of a nonpositive and a nonnegative integer is nonpositive

```agda
is-nonpositive-mul-nonpositive-nonnegative-ℤᵉ :
  {xᵉ yᵉ : ℤᵉ} →
  is-nonpositive-ℤᵉ xᵉ → is-nonnegative-ℤᵉ yᵉ → is-nonpositive-ℤᵉ (xᵉ *ℤᵉ yᵉ)
is-nonpositive-mul-nonpositive-nonnegative-ℤᵉ {xᵉ} {yᵉ} Hᵉ Kᵉ =
  is-nonpositive-eq-ℤᵉ
    ( commutative-mul-ℤᵉ yᵉ xᵉ)
    ( is-nonpositive-mul-nonnegative-nonpositive-ℤᵉ Kᵉ Hᵉ)
```

### The product of a nonpositive integer and a negative integer is nonnegative

```agda
is-nonnegative-mul-nonpositive-negative-ℤᵉ :
  { xᵉ yᵉ : ℤᵉ} → is-nonpositive-ℤᵉ xᵉ → is-negative-ℤᵉ yᵉ → is-nonnegative-ℤᵉ (xᵉ *ℤᵉ yᵉ)
is-nonnegative-mul-nonpositive-negative-ℤᵉ {xᵉ} {yᵉ} Hᵉ Kᵉ =
  is-nonnegative-eq-ℤᵉ
    ( commutative-mul-ℤᵉ yᵉ xᵉ)
    ( is-nonnegative-mul-negative-nonpositive-ℤᵉ Kᵉ Hᵉ)
```

### The product of two nonpositive integers is nonnegative

```agda
is-nonnegative-mul-nonpositive-ℤᵉ :
  {xᵉ yᵉ : ℤᵉ} →
  is-nonpositive-ℤᵉ xᵉ → is-nonpositive-ℤᵉ yᵉ → is-nonnegative-ℤᵉ (xᵉ *ℤᵉ yᵉ)
is-nonnegative-mul-nonpositive-ℤᵉ {xᵉ} {yᵉ} Hᵉ Kᵉ =
  is-nonnegative-eq-ℤᵉ
    ( double-negative-law-mul-ℤᵉ xᵉ yᵉ)
    ( is-nonnegative-mul-ℤᵉ
      ( is-nonnegative-neg-is-nonpositive-ℤᵉ Hᵉ)
      ( is-nonnegative-neg-is-nonpositive-ℤᵉ Kᵉ))
```

### The left factor of a positive product with a positive right factor is positive

```agda
is-positive-left-factor-mul-ℤᵉ :
  {xᵉ yᵉ : ℤᵉ} → is-positive-ℤᵉ (xᵉ *ℤᵉ yᵉ) → is-positive-ℤᵉ yᵉ → is-positive-ℤᵉ xᵉ
is-positive-left-factor-mul-ℤᵉ {inlᵉ xᵉ} {inrᵉ (inrᵉ yᵉ)} Hᵉ Kᵉ =
  is-positive-eq-ℤᵉ (compute-mul-ℤᵉ (inlᵉ xᵉ) (inrᵉ (inrᵉ yᵉ))) Hᵉ
is-positive-left-factor-mul-ℤᵉ {inrᵉ (inlᵉ starᵉ)} {inrᵉ (inrᵉ yᵉ)} Hᵉ Kᵉ =
  is-positive-eq-ℤᵉ (compute-mul-ℤᵉ zero-ℤᵉ (inrᵉ (inrᵉ yᵉ))) Hᵉ
is-positive-left-factor-mul-ℤᵉ {inrᵉ (inrᵉ xᵉ)} {inrᵉ (inrᵉ yᵉ)} Hᵉ Kᵉ = starᵉ
```

### The right factor of a positive product with a positive left factor is positive

```agda
is-positive-right-factor-mul-ℤᵉ :
  {xᵉ yᵉ : ℤᵉ} → is-positive-ℤᵉ (xᵉ *ℤᵉ yᵉ) → is-positive-ℤᵉ xᵉ → is-positive-ℤᵉ yᵉ
is-positive-right-factor-mul-ℤᵉ {xᵉ} {yᵉ} Hᵉ =
  is-positive-left-factor-mul-ℤᵉ (is-positive-eq-ℤᵉ (commutative-mul-ℤᵉ xᵉ yᵉ) Hᵉ)
```

### The left factor of a nonnegative product with a positive right factor is nonnegative

```agda
is-nonnegative-left-factor-mul-ℤᵉ :
  {xᵉ yᵉ : ℤᵉ} → is-nonnegative-ℤᵉ (xᵉ *ℤᵉ yᵉ) → is-positive-ℤᵉ yᵉ → is-nonnegative-ℤᵉ xᵉ
is-nonnegative-left-factor-mul-ℤᵉ {inlᵉ xᵉ} {inrᵉ (inrᵉ yᵉ)} Hᵉ Kᵉ =
  ex-falsoᵉ (is-nonnegative-eq-ℤᵉ (compute-mul-ℤᵉ (inlᵉ xᵉ) (inrᵉ (inrᵉ yᵉ))) Hᵉ)
is-nonnegative-left-factor-mul-ℤᵉ {inrᵉ xᵉ} {inrᵉ yᵉ} Hᵉ Kᵉ = starᵉ
```

### The right factor of a nonnegative product with a positive left factor is nonnegative

```agda
is-nonnegative-right-factor-mul-ℤᵉ :
  {xᵉ yᵉ : ℤᵉ} → is-nonnegative-ℤᵉ (xᵉ *ℤᵉ yᵉ) → is-positive-ℤᵉ xᵉ → is-nonnegative-ℤᵉ yᵉ
is-nonnegative-right-factor-mul-ℤᵉ {xᵉ} {yᵉ} Hᵉ =
  is-nonnegative-left-factor-mul-ℤᵉ
    ( is-nonnegative-eq-ℤᵉ (commutative-mul-ℤᵉ xᵉ yᵉ) Hᵉ)
```

## Definitions

### Multiplication by a signed integer

```agda
int-mul-positive-ℤᵉ : positive-ℤᵉ → ℤᵉ → ℤᵉ
int-mul-positive-ℤᵉ xᵉ yᵉ = int-positive-ℤᵉ xᵉ *ℤᵉ yᵉ

int-mul-positive-ℤ'ᵉ : positive-ℤᵉ → ℤᵉ → ℤᵉ
int-mul-positive-ℤ'ᵉ xᵉ yᵉ = yᵉ *ℤᵉ int-positive-ℤᵉ xᵉ

int-mul-nonnegative-ℤᵉ : nonnegative-ℤᵉ → ℤᵉ → ℤᵉ
int-mul-nonnegative-ℤᵉ xᵉ yᵉ = int-nonnegative-ℤᵉ xᵉ *ℤᵉ yᵉ

int-mul-nonnegative-ℤ'ᵉ : nonnegative-ℤᵉ → ℤᵉ → ℤᵉ
int-mul-nonnegative-ℤ'ᵉ xᵉ yᵉ = yᵉ *ℤᵉ int-nonnegative-ℤᵉ xᵉ

int-mul-negative-ℤᵉ : negative-ℤᵉ → ℤᵉ → ℤᵉ
int-mul-negative-ℤᵉ xᵉ yᵉ = int-negative-ℤᵉ xᵉ *ℤᵉ yᵉ

int-mul-negative-ℤ'ᵉ : negative-ℤᵉ → ℤᵉ → ℤᵉ
int-mul-negative-ℤ'ᵉ xᵉ yᵉ = yᵉ *ℤᵉ int-negative-ℤᵉ xᵉ

int-mul-nonpositive-ℤᵉ : nonpositive-ℤᵉ → ℤᵉ → ℤᵉ
int-mul-nonpositive-ℤᵉ xᵉ yᵉ = int-nonpositive-ℤᵉ xᵉ *ℤᵉ yᵉ

int-mul-nonpositive-ℤ'ᵉ : nonpositive-ℤᵉ → ℤᵉ → ℤᵉ
int-mul-nonpositive-ℤ'ᵉ xᵉ yᵉ = yᵉ *ℤᵉ int-nonpositive-ℤᵉ xᵉ
```

### Multiplication of positive integers

```agda
mul-positive-ℤᵉ : positive-ℤᵉ → positive-ℤᵉ → positive-ℤᵉ
mul-positive-ℤᵉ (xᵉ ,ᵉ Hᵉ) (yᵉ ,ᵉ Kᵉ) = (mul-ℤᵉ xᵉ yᵉ ,ᵉ is-positive-mul-ℤᵉ Hᵉ Kᵉ)
```

### Multiplication of nonnegative integers

```agda
mul-nonnegative-ℤᵉ : nonnegative-ℤᵉ → nonnegative-ℤᵉ → nonnegative-ℤᵉ
mul-nonnegative-ℤᵉ (xᵉ ,ᵉ Hᵉ) (yᵉ ,ᵉ Kᵉ) = (mul-ℤᵉ xᵉ yᵉ ,ᵉ is-nonnegative-mul-ℤᵉ Hᵉ Kᵉ)
```

### Multiplication of negative integers

```agda
mul-negative-ℤᵉ : negative-ℤᵉ → negative-ℤᵉ → positive-ℤᵉ
mul-negative-ℤᵉ (xᵉ ,ᵉ Hᵉ) (yᵉ ,ᵉ Kᵉ) = (mul-ℤᵉ xᵉ yᵉ ,ᵉ is-positive-mul-negative-ℤᵉ Hᵉ Kᵉ)
```

### Multiplication of nonpositive integers

```agda
mul-nonpositive-ℤᵉ : nonpositive-ℤᵉ → nonpositive-ℤᵉ → nonnegative-ℤᵉ
mul-nonpositive-ℤᵉ (xᵉ ,ᵉ Hᵉ) (yᵉ ,ᵉ Kᵉ) =
  (mul-ℤᵉ xᵉ yᵉ ,ᵉ is-nonnegative-mul-nonpositive-ℤᵉ Hᵉ Kᵉ)
```

## Properties

### Multiplication by a positive integer preserves and reflects the strict ordering

```agda
module _
  (zᵉ : positive-ℤᵉ) (xᵉ yᵉ : ℤᵉ)
  where

  preserves-le-right-mul-positive-ℤᵉ :
    le-ℤᵉ xᵉ yᵉ → le-ℤᵉ (int-mul-positive-ℤᵉ zᵉ xᵉ) (int-mul-positive-ℤᵉ zᵉ yᵉ)
  preserves-le-right-mul-positive-ℤᵉ Kᵉ =
    is-positive-eq-ℤᵉ
      ( left-distributive-mul-diff-ℤᵉ (int-positive-ℤᵉ zᵉ) yᵉ xᵉ)
      ( is-positive-mul-ℤᵉ (is-positive-int-positive-ℤᵉ zᵉ) Kᵉ)

  preserves-le-left-mul-positive-ℤᵉ :
    le-ℤᵉ xᵉ yᵉ → le-ℤᵉ (int-mul-positive-ℤ'ᵉ zᵉ xᵉ) (int-mul-positive-ℤ'ᵉ zᵉ yᵉ)
  preserves-le-left-mul-positive-ℤᵉ Kᵉ =
    is-positive-eq-ℤᵉ
      ( right-distributive-mul-diff-ℤᵉ yᵉ xᵉ (int-positive-ℤᵉ zᵉ))
      ( is-positive-mul-ℤᵉ Kᵉ (is-positive-int-positive-ℤᵉ zᵉ))

  reflects-le-right-mul-positive-ℤᵉ :
    le-ℤᵉ (int-mul-positive-ℤᵉ zᵉ xᵉ) (int-mul-positive-ℤᵉ zᵉ yᵉ) → le-ℤᵉ xᵉ yᵉ
  reflects-le-right-mul-positive-ℤᵉ Kᵉ =
    is-positive-right-factor-mul-ℤᵉ
      ( is-positive-eq-ℤᵉ
        ( invᵉ (left-distributive-mul-diff-ℤᵉ (int-positive-ℤᵉ zᵉ) yᵉ xᵉ))
        ( Kᵉ))
      ( is-positive-int-positive-ℤᵉ zᵉ)

  reflects-le-left-mul-positive-ℤᵉ :
    le-ℤᵉ (int-mul-positive-ℤ'ᵉ zᵉ xᵉ) (int-mul-positive-ℤ'ᵉ zᵉ yᵉ) → le-ℤᵉ xᵉ yᵉ
  reflects-le-left-mul-positive-ℤᵉ Kᵉ =
    is-positive-left-factor-mul-ℤᵉ
      ( is-positive-eq-ℤᵉ
      ( invᵉ (right-distributive-mul-diff-ℤᵉ yᵉ xᵉ (int-positive-ℤᵉ zᵉ)))
        ( Kᵉ))
      ( is-positive-int-positive-ℤᵉ zᵉ)
```

### Multiplication by a nonnegative integer preserves inequality

```agda
module _
  (zᵉ : nonnegative-ℤᵉ) (xᵉ yᵉ : ℤᵉ)
  where

  preserves-leq-right-mul-nonnegative-ℤᵉ :
    leq-ℤᵉ xᵉ yᵉ → leq-ℤᵉ (int-mul-nonnegative-ℤᵉ zᵉ xᵉ) (int-mul-nonnegative-ℤᵉ zᵉ yᵉ)
  preserves-leq-right-mul-nonnegative-ℤᵉ Kᵉ =
    is-nonnegative-eq-ℤᵉ
      ( left-distributive-mul-diff-ℤᵉ (int-nonnegative-ℤᵉ zᵉ) yᵉ xᵉ)
      ( is-nonnegative-mul-ℤᵉ (is-nonnegative-int-nonnegative-ℤᵉ zᵉ) Kᵉ)

  preserves-leq-left-mul-nonnegative-ℤᵉ :
    leq-ℤᵉ xᵉ yᵉ → leq-ℤᵉ (int-mul-nonnegative-ℤ'ᵉ zᵉ xᵉ) (int-mul-nonnegative-ℤ'ᵉ zᵉ yᵉ)
  preserves-leq-left-mul-nonnegative-ℤᵉ Kᵉ =
    is-nonnegative-eq-ℤᵉ
      ( right-distributive-mul-diff-ℤᵉ yᵉ xᵉ (int-nonnegative-ℤᵉ zᵉ))
      ( is-nonnegative-mul-ℤᵉ Kᵉ (is-nonnegative-int-nonnegative-ℤᵉ zᵉ))
```