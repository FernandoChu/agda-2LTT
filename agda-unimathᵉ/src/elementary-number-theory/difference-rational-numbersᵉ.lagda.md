# The difference between rational numbers

```agda
{-# OPTIONSᵉ --lossy-unificationᵉ #-}

module elementary-number-theory.difference-rational-numbersᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-rational-numbersᵉ
open import elementary-number-theory.rational-numbersᵉ

open import foundation.action-on-identifications-binary-functionsᵉ
open import foundation.action-on-identifications-functionsᵉ
open import foundation.identity-typesᵉ
open import foundation.interchange-lawᵉ
```

</details>

## Idea

Theᵉ {{#conceptᵉ "difference"ᵉ Disambiguation="rationalᵉ numbers"ᵉ Agda=diff-ℚᵉ}} ofᵉ
twoᵉ [rationalᵉ numbers](elementary-number-theory.rational-numbers.mdᵉ) `x`ᵉ andᵉ `y`ᵉ
isᵉ theᵉ additionᵉ ofᵉ `x`ᵉ andᵉ theᵉ negativeᵉ ofᵉ `y`.ᵉ

## Definitions

```agda
diff-ℚᵉ : ℚᵉ → ℚᵉ → ℚᵉ
diff-ℚᵉ xᵉ yᵉ = xᵉ +ℚᵉ (neg-ℚᵉ yᵉ)

infixl 36 _-ℚᵉ_
_-ℚᵉ_ = diff-ℚᵉ

ap-diff-ℚᵉ : {xᵉ x'ᵉ yᵉ y'ᵉ : ℚᵉ} → xᵉ ＝ᵉ x'ᵉ → yᵉ ＝ᵉ y'ᵉ → xᵉ -ℚᵉ yᵉ ＝ᵉ x'ᵉ -ℚᵉ y'ᵉ
ap-diff-ℚᵉ pᵉ qᵉ = ap-binaryᵉ diff-ℚᵉ pᵉ qᵉ
```

## Properties

### Two rational numbers with a difference equal to zero are equal

```agda
abstract
  eq-diff-ℚᵉ : {xᵉ yᵉ : ℚᵉ} → is-zero-ℚᵉ (xᵉ -ℚᵉ yᵉ) → xᵉ ＝ᵉ yᵉ
  eq-diff-ℚᵉ {xᵉ} {yᵉ} Hᵉ =
    ( invᵉ (right-unit-law-add-ℚᵉ xᵉ)) ∙ᵉ
    ( apᵉ (xᵉ +ℚᵉ_) (invᵉ (left-inverse-law-add-ℚᵉ yᵉ))) ∙ᵉ
    ( invᵉ (associative-add-ℚᵉ xᵉ (neg-ℚᵉ yᵉ) yᵉ)) ∙ᵉ
    ( apᵉ (_+ℚᵉ yᵉ) Hᵉ) ∙ᵉ
    ( left-unit-law-add-ℚᵉ yᵉ)
```

### The difference of a rational number with itself is zero

```agda
abstract
  is-zero-diff-ℚ'ᵉ : (xᵉ : ℚᵉ) → is-zero-ℚᵉ (xᵉ -ℚᵉ xᵉ)
  is-zero-diff-ℚ'ᵉ = right-inverse-law-add-ℚᵉ
```

### The difference of two equal rational numbers is zero

```agda
abstract
  is-zero-diff-ℚᵉ : {xᵉ yᵉ : ℚᵉ} → xᵉ ＝ᵉ yᵉ → is-zero-ℚᵉ (xᵉ -ℚᵉ yᵉ)
  is-zero-diff-ℚᵉ {xᵉ} reflᵉ = is-zero-diff-ℚ'ᵉ xᵉ
```

### The difference of a rational number with zero is itself

```agda
abstract
  right-zero-law-diff-ℚᵉ : (xᵉ : ℚᵉ) → xᵉ -ℚᵉ zero-ℚᵉ ＝ᵉ xᵉ
  right-zero-law-diff-ℚᵉ = right-unit-law-add-ℚᵉ
```

### The difference of zero and a rational number is its negative

```agda
abstract
  left-zero-law-diff-ℚᵉ : (xᵉ : ℚᵉ) → zero-ℚᵉ -ℚᵉ xᵉ ＝ᵉ neg-ℚᵉ xᵉ
  left-zero-law-diff-ℚᵉ xᵉ = left-unit-law-add-ℚᵉ (neg-ℚᵉ xᵉ)
```

### Triangular identity for addition and difference of rational numbers

```agda
abstract
  triangle-diff-ℚᵉ :
    (xᵉ yᵉ zᵉ : ℚᵉ) → (xᵉ -ℚᵉ yᵉ) +ℚᵉ (yᵉ -ℚᵉ zᵉ) ＝ᵉ xᵉ -ℚᵉ zᵉ
  triangle-diff-ℚᵉ xᵉ yᵉ zᵉ =
    ( associative-add-ℚᵉ xᵉ (neg-ℚᵉ yᵉ) (yᵉ -ℚᵉ zᵉ)) ∙ᵉ
    ( apᵉ
      ( xᵉ +ℚᵉ_)
      { neg-ℚᵉ yᵉ +ℚᵉ yᵉ -ℚᵉ zᵉ}
      { neg-ℚᵉ zᵉ}
      ( ( invᵉ (associative-add-ℚᵉ (neg-ℚᵉ yᵉ) yᵉ (neg-ℚᵉ zᵉ))) ∙ᵉ
        ( ( apᵉ
            (_+ℚᵉ (neg-ℚᵉ zᵉ))
            { neg-ℚᵉ yᵉ +ℚᵉ yᵉ}
            { zero-ℚᵉ}
            ( left-inverse-law-add-ℚᵉ yᵉ)) ∙ᵉ
          ( left-unit-law-add-ℚᵉ (neg-ℚᵉ zᵉ)))))
```

### The negative of the difference of two rational numbers `x` and `y` is the difference of `y` and `x`

```agda
abstract
  distributive-neg-diff-ℚᵉ :
    (xᵉ yᵉ : ℚᵉ) → neg-ℚᵉ (xᵉ -ℚᵉ yᵉ) ＝ᵉ yᵉ -ℚᵉ xᵉ
  distributive-neg-diff-ℚᵉ xᵉ yᵉ =
    ( distributive-neg-add-ℚᵉ xᵉ (neg-ℚᵉ yᵉ)) ∙ᵉ
    ( apᵉ ((neg-ℚᵉ xᵉ) +ℚᵉ_) (neg-neg-ℚᵉ yᵉ)) ∙ᵉ
    ( commutative-add-ℚᵉ (neg-ℚᵉ xᵉ) yᵉ)
```

### Interchange laws for addition and difference on rational numbers

```agda
abstract
  interchange-law-diff-add-ℚᵉ :
    (xᵉ yᵉ uᵉ vᵉ : ℚᵉ) → (xᵉ +ℚᵉ yᵉ) -ℚᵉ (uᵉ +ℚᵉ vᵉ) ＝ᵉ (xᵉ -ℚᵉ uᵉ) +ℚᵉ (yᵉ -ℚᵉ vᵉ)
  interchange-law-diff-add-ℚᵉ xᵉ yᵉ uᵉ vᵉ =
    ( apᵉ ((xᵉ +ℚᵉ yᵉ) +ℚᵉ_) (distributive-neg-add-ℚᵉ uᵉ vᵉ)) ∙ᵉ
    ( interchange-law-add-add-ℚᵉ xᵉ yᵉ (neg-ℚᵉ uᵉ) (neg-ℚᵉ vᵉ))

  interchange-law-add-diff-ℚᵉ :
    (xᵉ yᵉ uᵉ vᵉ : ℚᵉ) → (xᵉ -ℚᵉ yᵉ) +ℚᵉ (uᵉ -ℚᵉ vᵉ) ＝ᵉ (xᵉ +ℚᵉ uᵉ) -ℚᵉ (yᵉ +ℚᵉ vᵉ)
  interchange-law-add-diff-ℚᵉ xᵉ yᵉ uᵉ vᵉ =
    invᵉ (interchange-law-diff-add-ℚᵉ xᵉ uᵉ yᵉ vᵉ)
```

### The difference of rational numbers is invariant by translation

```agda
abstract
  left-translation-diff-ℚᵉ :
    (xᵉ yᵉ zᵉ : ℚᵉ) → (zᵉ +ℚᵉ xᵉ) -ℚᵉ (zᵉ +ℚᵉ yᵉ) ＝ᵉ xᵉ -ℚᵉ yᵉ
  left-translation-diff-ℚᵉ xᵉ yᵉ zᵉ =
    ( interchange-law-diff-add-ℚᵉ zᵉ xᵉ zᵉ yᵉ) ∙ᵉ
    ( apᵉ (_+ℚᵉ (xᵉ -ℚᵉ yᵉ)) (right-inverse-law-add-ℚᵉ zᵉ)) ∙ᵉ
    ( left-unit-law-add-ℚᵉ (xᵉ -ℚᵉ yᵉ))

  right-translation-diff-ℚᵉ :
    (xᵉ yᵉ zᵉ : ℚᵉ) → (xᵉ +ℚᵉ zᵉ) -ℚᵉ (yᵉ +ℚᵉ zᵉ) ＝ᵉ xᵉ -ℚᵉ yᵉ
  right-translation-diff-ℚᵉ xᵉ yᵉ zᵉ =
    ( ap-diff-ℚᵉ (commutative-add-ℚᵉ xᵉ zᵉ) (commutative-add-ℚᵉ yᵉ zᵉ)) ∙ᵉ
    ( left-translation-diff-ℚᵉ xᵉ yᵉ zᵉ)
```