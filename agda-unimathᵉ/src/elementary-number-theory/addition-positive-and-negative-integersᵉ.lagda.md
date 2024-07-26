# Addition of positive, negative, nonnegative and nonpositive integers

```agda
module elementary-number-theory.addition-positive-and-negative-integersᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integersᵉ
open import elementary-number-theory.integersᵉ
open import elementary-number-theory.natural-numbersᵉ
open import elementary-number-theory.negative-integersᵉ
open import elementary-number-theory.nonnegative-integersᵉ
open import elementary-number-theory.nonpositive-integersᵉ
open import elementary-number-theory.positive-and-negative-integersᵉ
open import elementary-number-theory.positive-integersᵉ

open import foundation.coproduct-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.identity-typesᵉ
open import foundation.injective-mapsᵉ
open import foundation.unit-typeᵉ
```

</details>

## Idea

Whenᵉ weᵉ haveᵉ informationᵉ aboutᵉ theᵉ signᵉ ofᵉ theᵉ summands,ᵉ weᵉ canᵉ in manyᵉ casesᵉ
deduceᵉ theᵉ signᵉ ofᵉ theirᵉ sumᵉ too.ᵉ Theᵉ tableᵉ belowᵉ tabulatesᵉ allᵉ suchᵉ casesᵉ andᵉ
displaysᵉ theᵉ correspondingᵉ Agdaᵉ definition.ᵉ

|     `p`ᵉ     |     `q`ᵉ     |  `pᵉ +ℤᵉ q`ᵉ   | operationᵉ           |
| :---------ᵉ: | :---------ᵉ: | :---------ᵉ: | -------------------ᵉ |
|  positiveᵉ   |  positiveᵉ   |  positiveᵉ   | `add-positive-ℤ`ᵉ    |
|  positiveᵉ   | nonnegativeᵉ |  positiveᵉ   |                     |
|  positiveᵉ   |  negativeᵉ   |             |                     |
|  positiveᵉ   | nonpositiveᵉ |             |                     |
| nonnegativeᵉ |  positiveᵉ   |  positiveᵉ   |                     |
| nonnegativeᵉ | nonnegativeᵉ | nonnegativeᵉ | `add-nonnegative-ℤ`ᵉ |
| nonnegativeᵉ |  negativeᵉ   |             |                     |
| nonnegativeᵉ | nonpositiveᵉ |             |                     |
|  negativeᵉ   |  positiveᵉ   |             |                     |
|  negativeᵉ   | nonnegativeᵉ |             |                     |
|  negativeᵉ   |  negativeᵉ   |  negativeᵉ   | `add-negative-ℤ`ᵉ    |
|  negativeᵉ   | nonpositiveᵉ |  negativeᵉ   |                     |
| nonpositiveᵉ |  positiveᵉ   |             |                     |
| nonpositiveᵉ | nonnegativeᵉ |             |                     |
| nonpositiveᵉ |  negativeᵉ   |  negativeᵉ   |                     |
| nonpositiveᵉ | nonpositiveᵉ | nonpositiveᵉ | `add-nonpositive-ℤ`ᵉ |

## Lemmas

### The sum of two positive integers is positive

```agda
abstract
  is-positive-add-ℤᵉ :
    {xᵉ yᵉ : ℤᵉ} → is-positive-ℤᵉ xᵉ → is-positive-ℤᵉ yᵉ → is-positive-ℤᵉ (xᵉ +ℤᵉ yᵉ)
  is-positive-add-ℤᵉ {inrᵉ (inrᵉ zero-ℕᵉ)} {yᵉ} Hᵉ Kᵉ =
    is-positive-succ-is-positive-ℤᵉ Kᵉ
  is-positive-add-ℤᵉ {inrᵉ (inrᵉ (succ-ℕᵉ xᵉ))} {yᵉ} Hᵉ Kᵉ =
    is-positive-succ-is-positive-ℤᵉ
      ( is-positive-add-ℤᵉ {inrᵉ (inrᵉ xᵉ)} Hᵉ Kᵉ)
```

### The sum of a positive and a nonnegative integer is positive

```agda
abstract
  is-positive-add-positive-nonnegative-ℤᵉ :
    {xᵉ yᵉ : ℤᵉ} → is-positive-ℤᵉ xᵉ → is-nonnegative-ℤᵉ yᵉ → is-positive-ℤᵉ (xᵉ +ℤᵉ yᵉ)
  is-positive-add-positive-nonnegative-ℤᵉ {inrᵉ (inrᵉ zero-ℕᵉ)} {yᵉ} Hᵉ Kᵉ =
    is-positive-succ-is-nonnegative-ℤᵉ Kᵉ
  is-positive-add-positive-nonnegative-ℤᵉ {inrᵉ (inrᵉ (succ-ℕᵉ xᵉ))} {yᵉ} Hᵉ Kᵉ =
    is-positive-succ-is-positive-ℤᵉ
      ( is-positive-add-positive-nonnegative-ℤᵉ {inrᵉ (inrᵉ xᵉ)} Hᵉ Kᵉ)
```

### The sum of a nonnegative and a positive integer is positive

```agda
abstract
  is-positive-add-nonnegative-positive-ℤᵉ :
    {xᵉ yᵉ : ℤᵉ} → is-nonnegative-ℤᵉ xᵉ → is-positive-ℤᵉ yᵉ → is-positive-ℤᵉ (xᵉ +ℤᵉ yᵉ)
  is-positive-add-nonnegative-positive-ℤᵉ {xᵉ} {yᵉ} Hᵉ Kᵉ =
    is-positive-eq-ℤᵉ
      ( commutative-add-ℤᵉ yᵉ xᵉ)
      ( is-positive-add-positive-nonnegative-ℤᵉ Kᵉ Hᵉ)
```

### The sum of two nonnegative integers is nonnegative

```agda
abstract
  is-nonnegative-add-ℤᵉ :
    {xᵉ yᵉ : ℤᵉ} →
    is-nonnegative-ℤᵉ xᵉ → is-nonnegative-ℤᵉ yᵉ → is-nonnegative-ℤᵉ (xᵉ +ℤᵉ yᵉ)
  is-nonnegative-add-ℤᵉ {inrᵉ (inlᵉ xᵉ)} {yᵉ} Hᵉ Kᵉ = Kᵉ
  is-nonnegative-add-ℤᵉ {inrᵉ (inrᵉ zero-ℕᵉ)} {yᵉ} Hᵉ Kᵉ =
    is-nonnegative-succ-is-nonnegative-ℤᵉ Kᵉ
  is-nonnegative-add-ℤᵉ {inrᵉ (inrᵉ (succ-ℕᵉ xᵉ))} {yᵉ} Hᵉ Kᵉ =
    is-nonnegative-succ-is-nonnegative-ℤᵉ
      ( is-nonnegative-add-ℤᵉ {inrᵉ (inrᵉ xᵉ)} starᵉ Kᵉ)
```

### The sum of two negative integers is negative

```agda
abstract
  is-negative-add-ℤᵉ :
    {xᵉ yᵉ : ℤᵉ} → is-negative-ℤᵉ xᵉ → is-negative-ℤᵉ yᵉ → is-negative-ℤᵉ (xᵉ +ℤᵉ yᵉ)
  is-negative-add-ℤᵉ {xᵉ} {yᵉ} Hᵉ Kᵉ =
    is-negative-eq-ℤᵉ
      ( neg-neg-ℤᵉ (xᵉ +ℤᵉ yᵉ))
      ( is-negative-neg-is-positive-ℤᵉ
        ( is-positive-eq-ℤᵉ
          ( invᵉ (distributive-neg-add-ℤᵉ xᵉ yᵉ))
          ( is-positive-add-ℤᵉ
            ( is-positive-neg-is-negative-ℤᵉ Hᵉ)
            ( is-positive-neg-is-negative-ℤᵉ Kᵉ))))
```

### The sum of a negative and a nonpositive integer is negative

```agda
abstract
  is-negative-add-negative-nonnegative-ℤᵉ :
    {xᵉ yᵉ : ℤᵉ} → is-negative-ℤᵉ xᵉ → is-nonpositive-ℤᵉ yᵉ → is-negative-ℤᵉ (xᵉ +ℤᵉ yᵉ)
  is-negative-add-negative-nonnegative-ℤᵉ {xᵉ} {yᵉ} Hᵉ Kᵉ =
    is-negative-eq-ℤᵉ
      ( neg-neg-ℤᵉ (xᵉ +ℤᵉ yᵉ))
      ( is-negative-neg-is-positive-ℤᵉ
        ( is-positive-eq-ℤᵉ
          ( invᵉ (distributive-neg-add-ℤᵉ xᵉ yᵉ))
          ( is-positive-add-positive-nonnegative-ℤᵉ
            ( is-positive-neg-is-negative-ℤᵉ Hᵉ)
            ( is-nonnegative-neg-is-nonpositive-ℤᵉ Kᵉ))))
```

### The sum of a nonpositive and a negative integer is negative

```agda
abstract
  is-negative-add-nonpositive-negative-ℤᵉ :
    {xᵉ yᵉ : ℤᵉ} → is-nonpositive-ℤᵉ xᵉ → is-negative-ℤᵉ yᵉ → is-negative-ℤᵉ (xᵉ +ℤᵉ yᵉ)
  is-negative-add-nonpositive-negative-ℤᵉ {xᵉ} {yᵉ} Hᵉ Kᵉ =
    is-negative-eq-ℤᵉ
      ( commutative-add-ℤᵉ yᵉ xᵉ)
      ( is-negative-add-negative-nonnegative-ℤᵉ Kᵉ Hᵉ)
```

### The sum of two nonpositive integers is nonpositive

```agda
abstract
  is-nonpositive-add-ℤᵉ :
    {xᵉ yᵉ : ℤᵉ} →
    is-nonpositive-ℤᵉ xᵉ → is-nonpositive-ℤᵉ yᵉ → is-nonpositive-ℤᵉ (xᵉ +ℤᵉ yᵉ)
  is-nonpositive-add-ℤᵉ {xᵉ} {yᵉ} Hᵉ Kᵉ =
    is-nonpositive-eq-ℤᵉ
      ( neg-neg-ℤᵉ (xᵉ +ℤᵉ yᵉ))
      ( is-nonpositive-neg-is-nonnegative-ℤᵉ
        ( is-nonnegative-eq-ℤᵉ
          ( invᵉ (distributive-neg-add-ℤᵉ xᵉ yᵉ))
          ( is-nonnegative-add-ℤᵉ
            ( is-nonnegative-neg-is-nonpositive-ℤᵉ Hᵉ)
            ( is-nonnegative-neg-is-nonpositive-ℤᵉ Kᵉ))))
```

## Definitions

### Addition of positive integers

```agda
add-positive-ℤᵉ : positive-ℤᵉ → positive-ℤᵉ → positive-ℤᵉ
add-positive-ℤᵉ (xᵉ ,ᵉ Hᵉ) (yᵉ ,ᵉ Kᵉ) = (add-ℤᵉ xᵉ yᵉ ,ᵉ is-positive-add-ℤᵉ Hᵉ Kᵉ)
```

### Addition of nonnegative integers

```agda
add-nonnegative-ℤᵉ : nonnegative-ℤᵉ → nonnegative-ℤᵉ → nonnegative-ℤᵉ
add-nonnegative-ℤᵉ (xᵉ ,ᵉ Hᵉ) (yᵉ ,ᵉ Kᵉ) = (add-ℤᵉ xᵉ yᵉ ,ᵉ is-nonnegative-add-ℤᵉ Hᵉ Kᵉ)
```

### Addition of negative integers

```agda
add-negative-ℤᵉ : negative-ℤᵉ → negative-ℤᵉ → negative-ℤᵉ
add-negative-ℤᵉ (xᵉ ,ᵉ Hᵉ) (yᵉ ,ᵉ Kᵉ) = (add-ℤᵉ xᵉ yᵉ ,ᵉ is-negative-add-ℤᵉ Hᵉ Kᵉ)
```

### Addition of nonpositive integers

```agda
add-nonpositive-ℤᵉ : nonpositive-ℤᵉ → nonpositive-ℤᵉ → nonpositive-ℤᵉ
add-nonpositive-ℤᵉ (xᵉ ,ᵉ Hᵉ) (yᵉ ,ᵉ Kᵉ) = (add-ℤᵉ xᵉ yᵉ ,ᵉ is-nonpositive-add-ℤᵉ Hᵉ Kᵉ)
```