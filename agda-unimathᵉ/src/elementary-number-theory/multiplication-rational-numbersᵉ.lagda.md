# Multiplication on the rational numbers

```agda
{-# OPTIONSᵉ --lossy-unificationᵉ #-}

module elementary-number-theory.multiplication-rational-numbersᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integer-fractionsᵉ
open import elementary-number-theory.addition-rational-numbersᵉ
open import elementary-number-theory.difference-rational-numbersᵉ
open import elementary-number-theory.greatest-common-divisor-integersᵉ
open import elementary-number-theory.integer-fractionsᵉ
open import elementary-number-theory.integersᵉ
open import elementary-number-theory.multiplication-integer-fractionsᵉ
open import elementary-number-theory.multiplication-integersᵉ
open import elementary-number-theory.rational-numbersᵉ
open import elementary-number-theory.reduced-integer-fractionsᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.coproduct-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.function-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.interchange-lawᵉ
```

</details>

## Idea

**Multiplication**ᵉ onᵉ theᵉ
[rationalᵉ numbers](elementary-number-theory.rational-numbers.mdᵉ) isᵉ definedᵉ byᵉ
extendingᵉ
[multiplication](elementary-number-theory.multiplication-integer-fractions.mdᵉ)
onᵉ [integerᵉ fractions](elementary-number-theory.integer-fractions.mdᵉ) to theᵉ
rationalᵉ numbers.ᵉ

## Definition

```agda
mul-ℚᵉ : ℚᵉ → ℚᵉ → ℚᵉ
mul-ℚᵉ (xᵉ ,ᵉ pᵉ) (yᵉ ,ᵉ qᵉ) = rational-fraction-ℤᵉ (mul-fraction-ℤᵉ xᵉ yᵉ)

mul-ℚ'ᵉ : ℚᵉ → ℚᵉ → ℚᵉ
mul-ℚ'ᵉ xᵉ yᵉ = mul-ℚᵉ yᵉ xᵉ

infixl 40 _*ℚᵉ_
_*ℚᵉ_ = mul-ℚᵉ
```

## Properties

### The multiplication of a rational number by zero is zero

```agda
module _
  (xᵉ : ℚᵉ)
  where

  abstract
    left-zero-law-mul-ℚᵉ : zero-ℚᵉ *ℚᵉ xᵉ ＝ᵉ zero-ℚᵉ
    left-zero-law-mul-ℚᵉ =
      ( eq-ℚ-sim-fraction-ℤᵉ
        ( mul-fraction-ℤᵉ (fraction-ℚᵉ zero-ℚᵉ) (fraction-ℚᵉ xᵉ))
        ( fraction-ℚᵉ zero-ℚᵉ)
        ( eq-is-zero-ℤᵉ
          ( apᵉ (mul-ℤ'ᵉ one-ℤᵉ) (left-zero-law-mul-ℤᵉ (numerator-ℚᵉ xᵉ)))
          ( left-zero-law-mul-ℤᵉ _))) ∙ᵉ
      ( is-retraction-rational-fraction-ℚᵉ zero-ℚᵉ)

    right-zero-law-mul-ℚᵉ : xᵉ *ℚᵉ zero-ℚᵉ ＝ᵉ zero-ℚᵉ
    right-zero-law-mul-ℚᵉ =
      ( eq-ℚ-sim-fraction-ℤᵉ
        ( mul-fraction-ℤᵉ (fraction-ℚᵉ xᵉ) (fraction-ℚᵉ zero-ℚᵉ))
        ( fraction-ℚᵉ zero-ℚᵉ)
        ( eq-is-zero-ℤᵉ
          ( apᵉ (mul-ℤ'ᵉ one-ℤᵉ) (right-zero-law-mul-ℤᵉ (numerator-ℚᵉ xᵉ)))
          ( left-zero-law-mul-ℤᵉ _))) ∙ᵉ
      ( is-retraction-rational-fraction-ℚᵉ zero-ℚᵉ)
```

### If the product of two rational numbers is zero, the left or right factor is zero

```agda
decide-is-zero-factor-is-zero-mul-ℚᵉ :
  (xᵉ yᵉ : ℚᵉ) → is-zero-ℚᵉ (xᵉ *ℚᵉ yᵉ) → (is-zero-ℚᵉ xᵉ) +ᵉ (is-zero-ℚᵉ yᵉ)
decide-is-zero-factor-is-zero-mul-ℚᵉ xᵉ yᵉ Hᵉ =
  rec-coproductᵉ
    ( inlᵉ ∘ᵉ is-zero-is-zero-numerator-ℚᵉ xᵉ)
    ( inrᵉ ∘ᵉ is-zero-is-zero-numerator-ℚᵉ yᵉ)
    ( is-zero-is-zero-mul-ℤᵉ
      ( numerator-ℚᵉ xᵉ)
      ( numerator-ℚᵉ yᵉ)
      ( ( invᵉ
          ( eq-reduce-numerator-fraction-ℤᵉ
            ( mul-fraction-ℤᵉ (fraction-ℚᵉ xᵉ) (fraction-ℚᵉ yᵉ)))) ∙ᵉ
        ( apᵉ
          ( mul-ℤ'ᵉ
            ( gcd-ℤᵉ
              ( numerator-ℚᵉ xᵉ *ℤᵉ numerator-ℚᵉ yᵉ)
              ( denominator-ℚᵉ xᵉ *ℤᵉ denominator-ℚᵉ yᵉ)))
          ( ( is-zero-numerator-is-zero-ℚᵉ (xᵉ *ℚᵉ yᵉ) Hᵉ) ∙ᵉ
            ( left-zero-law-mul-ℤᵉ
              ( gcd-ℤᵉ
                (numerator-ℚᵉ xᵉ *ℤᵉ numerator-ℚᵉ yᵉ)
                (denominator-ℚᵉ xᵉ *ℤᵉ denominator-ℚᵉ yᵉ)))))))
```

### Unit laws for multiplication on rational numbers

```agda
abstract
  left-unit-law-mul-ℚᵉ : (xᵉ : ℚᵉ) → one-ℚᵉ *ℚᵉ xᵉ ＝ᵉ xᵉ
  left-unit-law-mul-ℚᵉ xᵉ =
    ( eq-ℚ-sim-fraction-ℤᵉ
      ( mul-fraction-ℤᵉ one-fraction-ℤᵉ (fraction-ℚᵉ xᵉ))
      ( fraction-ℚᵉ xᵉ)
      ( left-unit-law-mul-fraction-ℤᵉ (fraction-ℚᵉ xᵉ))) ∙ᵉ
    ( is-retraction-rational-fraction-ℚᵉ xᵉ)

  right-unit-law-mul-ℚᵉ : (xᵉ : ℚᵉ) → xᵉ *ℚᵉ one-ℚᵉ ＝ᵉ xᵉ
  right-unit-law-mul-ℚᵉ xᵉ =
    ( eq-ℚ-sim-fraction-ℤᵉ
      ( mul-fraction-ℤᵉ (fraction-ℚᵉ xᵉ) one-fraction-ℤᵉ)
      ( fraction-ℚᵉ xᵉ)
      ( right-unit-law-mul-fraction-ℤᵉ (fraction-ℚᵉ xᵉ))) ∙ᵉ
    ( is-retraction-rational-fraction-ℚᵉ xᵉ)
```

### Multiplication of a rational number by `-1` is equal to the negative

```agda
abstract
  left-neg-unit-law-mul-ℚᵉ : (xᵉ : ℚᵉ) → neg-one-ℚᵉ *ℚᵉ xᵉ ＝ᵉ neg-ℚᵉ xᵉ
  left-neg-unit-law-mul-ℚᵉ xᵉ =
    ( eq-ℚ-sim-fraction-ℤᵉ
      ( mul-fraction-ℤᵉ (fraction-ℚᵉ neg-one-ℚᵉ) (fraction-ℚᵉ xᵉ))
      ( neg-fraction-ℤᵉ (fraction-ℚᵉ xᵉ))
      ( ap-mul-ℤᵉ
        ( left-neg-unit-law-mul-ℤᵉ (numerator-ℚᵉ xᵉ))
        ( invᵉ (left-unit-law-mul-ℤᵉ (denominator-ℚᵉ xᵉ))))) ∙ᵉ
    ( is-retraction-rational-fraction-ℚᵉ (neg-ℚᵉ xᵉ))

  right-neg-unit-law-mul-ℚᵉ : (xᵉ : ℚᵉ) → xᵉ *ℚᵉ neg-one-ℚᵉ ＝ᵉ neg-ℚᵉ xᵉ
  right-neg-unit-law-mul-ℚᵉ xᵉ =
    ( eq-ℚ-sim-fraction-ℤᵉ
      ( mul-fraction-ℤᵉ (fraction-ℚᵉ xᵉ) (fraction-ℚᵉ neg-one-ℚᵉ))
      ( neg-fraction-ℤᵉ (fraction-ℚᵉ xᵉ))
      ( ap-mul-ℤᵉ
        ( right-neg-unit-law-mul-ℤᵉ (numerator-ℚᵉ xᵉ))
        ( invᵉ (right-unit-law-mul-ℤᵉ (denominator-ℚᵉ xᵉ))))) ∙ᵉ
    ( is-retraction-rational-fraction-ℚᵉ (neg-ℚᵉ xᵉ))
```

### Multiplication of rational numbers is associative

```agda
abstract
  associative-mul-ℚᵉ :
    (xᵉ yᵉ zᵉ : ℚᵉ) → (xᵉ *ℚᵉ yᵉ) *ℚᵉ zᵉ ＝ᵉ xᵉ *ℚᵉ (yᵉ *ℚᵉ zᵉ)
  associative-mul-ℚᵉ xᵉ yᵉ zᵉ =
    eq-ℚ-sim-fraction-ℤᵉ
      ( mul-fraction-ℤᵉ (fraction-ℚᵉ (xᵉ *ℚᵉ yᵉ)) (fraction-ℚᵉ zᵉ))
      ( mul-fraction-ℤᵉ (fraction-ℚᵉ xᵉ) (fraction-ℚᵉ (yᵉ *ℚᵉ zᵉ)))
      ( transitive-sim-fraction-ℤᵉ
        ( mul-fraction-ℤᵉ (fraction-ℚᵉ (xᵉ *ℚᵉ yᵉ)) (fraction-ℚᵉ zᵉ))
        ( mul-fraction-ℤᵉ
          ( mul-fraction-ℤᵉ (fraction-ℚᵉ xᵉ) (fraction-ℚᵉ yᵉ))
          ( fraction-ℚᵉ zᵉ))
        ( mul-fraction-ℤᵉ (fraction-ℚᵉ xᵉ) (fraction-ℚᵉ (yᵉ *ℚᵉ zᵉ)))
        ( transitive-sim-fraction-ℤᵉ
          ( mul-fraction-ℤᵉ
            ( mul-fraction-ℤᵉ (fraction-ℚᵉ xᵉ) (fraction-ℚᵉ yᵉ))
            ( fraction-ℚᵉ zᵉ))
          ( mul-fraction-ℤᵉ
            ( fraction-ℚᵉ xᵉ)
            ( mul-fraction-ℤᵉ (fraction-ℚᵉ yᵉ) (fraction-ℚᵉ zᵉ)))
          ( mul-fraction-ℤᵉ (fraction-ℚᵉ xᵉ) (fraction-ℚᵉ (yᵉ *ℚᵉ zᵉ)))
          ( sim-fraction-mul-fraction-ℤᵉ
            ( refl-sim-fraction-ℤᵉ (fraction-ℚᵉ xᵉ))
            ( sim-reduced-fraction-ℤᵉ
              ( mul-fraction-ℤᵉ (fraction-ℚᵉ yᵉ) (fraction-ℚᵉ zᵉ))))
          ( associative-mul-fraction-ℤᵉ
            ( fraction-ℚᵉ xᵉ)
            ( fraction-ℚᵉ yᵉ)
            ( fraction-ℚᵉ zᵉ)))
        ( sim-fraction-mul-fraction-ℤᵉ
          ( invᵉ
            ( sim-reduced-fraction-ℤᵉ
              ( mul-fraction-ℤᵉ (fraction-ℚᵉ xᵉ) (fraction-ℚᵉ yᵉ))))
          ( refl-sim-fraction-ℤᵉ (fraction-ℚᵉ zᵉ))))
```

### Multiplication of rational numbers is commutative

```agda
abstract
  commutative-mul-ℚᵉ : (xᵉ yᵉ : ℚᵉ) → xᵉ *ℚᵉ yᵉ ＝ᵉ yᵉ *ℚᵉ xᵉ
  commutative-mul-ℚᵉ xᵉ yᵉ =
    eq-ℚ-sim-fraction-ℤᵉ
      ( mul-fraction-ℤᵉ (fraction-ℚᵉ xᵉ) (fraction-ℚᵉ yᵉ))
      ( mul-fraction-ℤᵉ (fraction-ℚᵉ yᵉ) (fraction-ℚᵉ xᵉ))
      ( commutative-mul-fraction-ℤᵉ (fraction-ℚᵉ xᵉ) (fraction-ℚᵉ yᵉ))
```

### Interchange law for multiplication on rational numbers with itself

```agda
abstract
  interchange-law-mul-mul-ℚᵉ :
    (xᵉ yᵉ uᵉ vᵉ : ℚᵉ) → (xᵉ *ℚᵉ yᵉ) *ℚᵉ (uᵉ *ℚᵉ vᵉ) ＝ᵉ (xᵉ *ℚᵉ uᵉ) *ℚᵉ (yᵉ *ℚᵉ vᵉ)
  interchange-law-mul-mul-ℚᵉ =
    interchange-law-commutative-and-associativeᵉ
      mul-ℚᵉ
      commutative-mul-ℚᵉ
      associative-mul-ℚᵉ
```

### Negative laws for multiplication on rational numbers

```agda
module _
  (xᵉ yᵉ : ℚᵉ)
  where

  abstract
    left-negative-law-mul-ℚᵉ : (neg-ℚᵉ xᵉ) *ℚᵉ yᵉ ＝ᵉ neg-ℚᵉ (xᵉ *ℚᵉ yᵉ)
    left-negative-law-mul-ℚᵉ =
      ( apᵉ ( _*ℚᵉ yᵉ) (invᵉ (left-neg-unit-law-mul-ℚᵉ xᵉ))) ∙ᵉ
      ( associative-mul-ℚᵉ neg-one-ℚᵉ xᵉ yᵉ) ∙ᵉ
      ( left-neg-unit-law-mul-ℚᵉ (xᵉ *ℚᵉ yᵉ))

    right-negative-law-mul-ℚᵉ : xᵉ *ℚᵉ (neg-ℚᵉ yᵉ) ＝ᵉ neg-ℚᵉ (xᵉ *ℚᵉ yᵉ)
    right-negative-law-mul-ℚᵉ =
      ( apᵉ ( xᵉ *ℚᵉ_) (invᵉ (right-neg-unit-law-mul-ℚᵉ yᵉ))) ∙ᵉ
      ( invᵉ (associative-mul-ℚᵉ xᵉ yᵉ neg-one-ℚᵉ)) ∙ᵉ
      ( right-neg-unit-law-mul-ℚᵉ (xᵉ *ℚᵉ yᵉ))

abstract
  negative-law-mul-ℚᵉ : (xᵉ yᵉ : ℚᵉ) → (neg-ℚᵉ xᵉ) *ℚᵉ (neg-ℚᵉ yᵉ) ＝ᵉ xᵉ *ℚᵉ yᵉ
  negative-law-mul-ℚᵉ xᵉ yᵉ =
    ( left-negative-law-mul-ℚᵉ xᵉ (neg-ℚᵉ yᵉ)) ∙ᵉ
    ( apᵉ neg-ℚᵉ (right-negative-law-mul-ℚᵉ xᵉ yᵉ)) ∙ᵉ
    ( neg-neg-ℚᵉ (xᵉ *ℚᵉ yᵉ))

  swap-neg-mul-ℚᵉ : (xᵉ yᵉ : ℚᵉ) → xᵉ *ℚᵉ (neg-ℚᵉ yᵉ) ＝ᵉ (neg-ℚᵉ xᵉ) *ℚᵉ yᵉ
  swap-neg-mul-ℚᵉ xᵉ yᵉ =
    ( right-negative-law-mul-ℚᵉ xᵉ yᵉ) ∙ᵉ
    ( invᵉ (left-negative-law-mul-ℚᵉ xᵉ yᵉ))
```

### Multiplication on rational numbers distributes over addition

```agda
abstract
  left-distributive-mul-add-ℚᵉ :
    (xᵉ yᵉ zᵉ : ℚᵉ) → xᵉ *ℚᵉ (yᵉ +ℚᵉ zᵉ) ＝ᵉ (xᵉ *ℚᵉ yᵉ) +ℚᵉ (xᵉ *ℚᵉ zᵉ)
  left-distributive-mul-add-ℚᵉ xᵉ yᵉ zᵉ =
    eq-ℚ-sim-fraction-ℤᵉ
      ( mul-fraction-ℤᵉ (fraction-ℚᵉ xᵉ) (fraction-ℚᵉ (yᵉ +ℚᵉ zᵉ)))
      ( add-fraction-ℤᵉ (fraction-ℚᵉ (xᵉ *ℚᵉ yᵉ)) (fraction-ℚᵉ (xᵉ *ℚᵉ zᵉ)))
      ( transitive-sim-fraction-ℤᵉ
        ( mul-fraction-ℤᵉ (fraction-ℚᵉ xᵉ) (fraction-ℚᵉ (yᵉ +ℚᵉ zᵉ)))
        ( mul-fraction-ℤᵉ
          ( fraction-ℚᵉ xᵉ)
          ( add-fraction-ℤᵉ (fraction-ℚᵉ yᵉ) (fraction-ℚᵉ zᵉ)))
        ( add-fraction-ℤᵉ (fraction-ℚᵉ (xᵉ *ℚᵉ yᵉ)) (fraction-ℚᵉ (xᵉ *ℚᵉ zᵉ)))
        ( transitive-sim-fraction-ℤᵉ
          ( mul-fraction-ℤᵉ
            ( fraction-ℚᵉ xᵉ)
            ( add-fraction-ℤᵉ (fraction-ℚᵉ yᵉ) (fraction-ℚᵉ zᵉ)))
          ( add-fraction-ℤᵉ
            ( mul-fraction-ℤᵉ (fraction-ℚᵉ xᵉ) (fraction-ℚᵉ yᵉ))
            ( mul-fraction-ℤᵉ (fraction-ℚᵉ xᵉ) (fraction-ℚᵉ zᵉ)))
          ( add-fraction-ℤᵉ (fraction-ℚᵉ (xᵉ *ℚᵉ yᵉ)) (fraction-ℚᵉ (xᵉ *ℚᵉ zᵉ)))
          ( sim-fraction-add-fraction-ℤᵉ
            ( sim-reduced-fraction-ℤᵉ
              ( mul-fraction-ℤᵉ (fraction-ℚᵉ xᵉ) (fraction-ℚᵉ yᵉ)))
            ( sim-reduced-fraction-ℤᵉ
              ( mul-fraction-ℤᵉ (fraction-ℚᵉ xᵉ) (fraction-ℚᵉ zᵉ))))
          ( left-distributive-mul-add-fraction-ℤᵉ
            ( fraction-ℚᵉ xᵉ)
            ( fraction-ℚᵉ yᵉ)
            ( fraction-ℚᵉ zᵉ)))
        ( sim-fraction-mul-fraction-ℤᵉ
          ( refl-sim-fraction-ℤᵉ (fraction-ℚᵉ xᵉ))
          ( transitive-sim-fraction-ℤᵉ
            ( fraction-ℚᵉ (yᵉ +ℚᵉ zᵉ))
            ( reduce-fraction-ℤᵉ (add-fraction-ℤᵉ (fraction-ℚᵉ yᵉ) (fraction-ℚᵉ zᵉ)))
            ( add-fraction-ℤᵉ (fraction-ℚᵉ yᵉ) (fraction-ℚᵉ zᵉ))
            ( symmetric-sim-fraction-ℤᵉ
              ( add-fraction-ℤᵉ (fraction-ℚᵉ yᵉ) (fraction-ℚᵉ zᵉ))
              ( reduce-fraction-ℤᵉ
                ( add-fraction-ℤᵉ (fraction-ℚᵉ yᵉ) (fraction-ℚᵉ zᵉ)))
              ( sim-reduced-fraction-ℤᵉ
                (add-fraction-ℤᵉ (fraction-ℚᵉ yᵉ) (fraction-ℚᵉ zᵉ))))
            ( refl-sim-fraction-ℤᵉ (fraction-ℚᵉ (yᵉ +ℚᵉ zᵉ))))))

  right-distributive-mul-add-ℚᵉ :
    (xᵉ yᵉ zᵉ : ℚᵉ) → (xᵉ +ℚᵉ yᵉ) *ℚᵉ zᵉ ＝ᵉ (xᵉ *ℚᵉ zᵉ) +ℚᵉ (yᵉ *ℚᵉ zᵉ)
  right-distributive-mul-add-ℚᵉ xᵉ yᵉ zᵉ =
    ( commutative-mul-ℚᵉ (xᵉ +ℚᵉ yᵉ) zᵉ) ∙ᵉ
    ( left-distributive-mul-add-ℚᵉ zᵉ xᵉ yᵉ) ∙ᵉ
    ( ap-add-ℚᵉ (commutative-mul-ℚᵉ zᵉ xᵉ) (commutative-mul-ℚᵉ zᵉ yᵉ))
```

### Multiplication on rational numbers distributes over the difference

```agda
abstract
  left-distributive-mul-diff-ℚᵉ :
    (zᵉ xᵉ yᵉ : ℚᵉ) → zᵉ *ℚᵉ (xᵉ -ℚᵉ yᵉ) ＝ᵉ (zᵉ *ℚᵉ xᵉ) -ℚᵉ (zᵉ *ℚᵉ yᵉ)
  left-distributive-mul-diff-ℚᵉ zᵉ xᵉ yᵉ =
    ( left-distributive-mul-add-ℚᵉ zᵉ xᵉ (neg-ℚᵉ yᵉ)) ∙ᵉ
    ( apᵉ ((zᵉ *ℚᵉ xᵉ) +ℚᵉ_) (right-negative-law-mul-ℚᵉ zᵉ yᵉ))

  right-distributive-mul-diff-ℚᵉ :
    (xᵉ yᵉ zᵉ : ℚᵉ) → (xᵉ -ℚᵉ yᵉ) *ℚᵉ zᵉ ＝ᵉ (xᵉ *ℚᵉ zᵉ) -ℚᵉ (yᵉ *ℚᵉ zᵉ)
  right-distributive-mul-diff-ℚᵉ xᵉ yᵉ zᵉ =
    ( right-distributive-mul-add-ℚᵉ xᵉ (neg-ℚᵉ yᵉ) zᵉ) ∙ᵉ
    ( apᵉ ((xᵉ *ℚᵉ zᵉ) +ℚᵉ_) (left-negative-law-mul-ℚᵉ yᵉ zᵉ))
```

## See also

-ᵉ Theᵉ multiplicativeᵉ monoidᵉ strucutreᵉ onᵉ theᵉ rationalᵉ numbersᵉ isᵉ definedᵉ in
  [`elementary-number-theory.multiplicative-monoid-of-rational-numbers`](elementary-number-theory.multiplicative-monoid-of-rational-numbers.md);ᵉ
-ᵉ Theᵉ multiplicativeᵉ groupᵉ structureᵉ onᵉ theᵉ rationalᵉ numbersᵉ isᵉ definedᵉ in
  [`elementary-number-theory.multiplicative-group-of-rational-numbers`](elementary-number-theory.multiplicative-group-of-rational-numbers.md).ᵉ