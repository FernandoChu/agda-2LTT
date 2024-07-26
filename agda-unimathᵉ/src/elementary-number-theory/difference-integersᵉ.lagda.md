# The difference between integers

```agda
module elementary-number-theory.difference-integersᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integersᵉ
open import elementary-number-theory.integersᵉ

open import foundation.action-on-identifications-binary-functionsᵉ
open import foundation.action-on-identifications-functionsᵉ
open import foundation.identity-typesᵉ
open import foundation.interchange-lawᵉ
```

</details>

## Idea

Sinceᵉ integersᵉ ofᵉ theᵉ formᵉ `xᵉ -ᵉ y`ᵉ occurᵉ often,ᵉ weᵉ introduceᵉ themᵉ hereᵉ andᵉ
deriveᵉ theirᵉ basicᵉ propertiesᵉ relativeᵉ to `succ-ℤ`,ᵉ `neg-ℤ`,ᵉ andᵉ `add-ℤ`.ᵉ Theᵉ
fileᵉ `multiplication-integers`ᵉ importsᵉ `difference-integers`ᵉ andᵉ moreᵉ propertiesᵉ
areᵉ derivedᵉ there.ᵉ

## Definition

```agda
diff-ℤᵉ : ℤᵉ → ℤᵉ → ℤᵉ
diff-ℤᵉ xᵉ yᵉ = xᵉ +ℤᵉ (neg-ℤᵉ yᵉ)

infixl 36 _-ℤᵉ_
_-ℤᵉ_ = diff-ℤᵉ

ap-diff-ℤᵉ : {xᵉ x'ᵉ yᵉ y'ᵉ : ℤᵉ} → xᵉ ＝ᵉ x'ᵉ → yᵉ ＝ᵉ y'ᵉ → xᵉ -ℤᵉ yᵉ ＝ᵉ x'ᵉ -ℤᵉ y'ᵉ
ap-diff-ℤᵉ pᵉ qᵉ = ap-binaryᵉ diff-ℤᵉ pᵉ qᵉ
```

## Properties

### Two integers with a difference equal to zero are equal

```agda
abstract
  eq-diff-ℤᵉ : {xᵉ yᵉ : ℤᵉ} → is-zero-ℤᵉ (xᵉ -ℤᵉ yᵉ) → xᵉ ＝ᵉ yᵉ
  eq-diff-ℤᵉ {xᵉ} {yᵉ} Hᵉ =
    ( invᵉ (right-unit-law-add-ℤᵉ xᵉ)) ∙ᵉ
    ( apᵉ (xᵉ +ℤᵉ_) (invᵉ (left-inverse-law-add-ℤᵉ yᵉ))) ∙ᵉ
    ( invᵉ (associative-add-ℤᵉ xᵉ (neg-ℤᵉ yᵉ) yᵉ)) ∙ᵉ
    ( apᵉ (_+ℤᵉ yᵉ) Hᵉ) ∙ᵉ
    ( left-unit-law-add-ℤᵉ yᵉ)
```

### The difference of an integer with itself is zero

```agda
abstract
  is-zero-diff-ℤ'ᵉ : (xᵉ : ℤᵉ) → is-zero-ℤᵉ (xᵉ -ℤᵉ xᵉ)
  is-zero-diff-ℤ'ᵉ = right-inverse-law-add-ℤᵉ
```

### The difference of two equal integers is zero

```agda
abstract
  is-zero-diff-ℤᵉ : {xᵉ yᵉ : ℤᵉ} → xᵉ ＝ᵉ yᵉ → is-zero-ℤᵉ (xᵉ -ℤᵉ yᵉ)
  is-zero-diff-ℤᵉ {xᵉ} {.xᵉ} reflᵉ = is-zero-diff-ℤ'ᵉ xᵉ
```

### The difference of zero and an integer is its negative

```agda
abstract
  left-zero-law-diff-ℤᵉ : (xᵉ : ℤᵉ) → zero-ℤᵉ -ℤᵉ xᵉ ＝ᵉ neg-ℤᵉ xᵉ
  left-zero-law-diff-ℤᵉ xᵉ = left-unit-law-add-ℤᵉ (neg-ℤᵉ xᵉ)
```

### The difference of an integer with zero is itself

```agda
abstract
  right-zero-law-diff-ℤᵉ : (xᵉ : ℤᵉ) → xᵉ -ℤᵉ zero-ℤᵉ ＝ᵉ xᵉ
  right-zero-law-diff-ℤᵉ xᵉ = right-unit-law-add-ℤᵉ xᵉ
```

### Differences with the predecessor or successor of an integer

```agda
abstract
  left-successor-law-diff-ℤᵉ :
    (xᵉ yᵉ : ℤᵉ) → (succ-ℤᵉ xᵉ) -ℤᵉ yᵉ ＝ᵉ succ-ℤᵉ (xᵉ -ℤᵉ yᵉ)
  left-successor-law-diff-ℤᵉ xᵉ yᵉ = left-successor-law-add-ℤᵉ xᵉ (neg-ℤᵉ yᵉ)

  right-successor-law-diff-ℤᵉ :
    (xᵉ yᵉ : ℤᵉ) → xᵉ -ℤᵉ (succ-ℤᵉ yᵉ) ＝ᵉ pred-ℤᵉ (xᵉ -ℤᵉ yᵉ)
  right-successor-law-diff-ℤᵉ xᵉ yᵉ =
    apᵉ (xᵉ +ℤᵉ_) (neg-succ-ℤᵉ yᵉ) ∙ᵉ right-predecessor-law-add-ℤᵉ xᵉ (neg-ℤᵉ yᵉ)

  left-predecessor-law-diff-ℤᵉ :
    (xᵉ yᵉ : ℤᵉ) → (pred-ℤᵉ xᵉ) -ℤᵉ yᵉ ＝ᵉ pred-ℤᵉ (xᵉ -ℤᵉ yᵉ)
  left-predecessor-law-diff-ℤᵉ xᵉ yᵉ = left-predecessor-law-add-ℤᵉ xᵉ (neg-ℤᵉ yᵉ)

  right-predecessor-law-diff-ℤᵉ :
    (xᵉ yᵉ : ℤᵉ) → xᵉ -ℤᵉ (pred-ℤᵉ yᵉ) ＝ᵉ succ-ℤᵉ (xᵉ -ℤᵉ yᵉ)
  right-predecessor-law-diff-ℤᵉ xᵉ yᵉ =
    apᵉ (xᵉ +ℤᵉ_) (neg-pred-ℤᵉ yᵉ) ∙ᵉ right-successor-law-add-ℤᵉ xᵉ (neg-ℤᵉ yᵉ)
```

### Triangular identity for addition and difference of integers

```agda
abstract
  triangle-diff-ℤᵉ :
    (xᵉ yᵉ zᵉ : ℤᵉ) → (xᵉ -ℤᵉ yᵉ) +ℤᵉ (yᵉ -ℤᵉ zᵉ) ＝ᵉ xᵉ -ℤᵉ zᵉ
  triangle-diff-ℤᵉ xᵉ yᵉ zᵉ =
    ( associative-add-ℤᵉ xᵉ (neg-ℤᵉ yᵉ) (yᵉ -ℤᵉ zᵉ)) ∙ᵉ
    ( apᵉ
      ( xᵉ +ℤᵉ_)
      ( ( invᵉ (associative-add-ℤᵉ (neg-ℤᵉ yᵉ) yᵉ (neg-ℤᵉ zᵉ))) ∙ᵉ
        ( ( apᵉ (_+ℤᵉ (neg-ℤᵉ zᵉ)) (left-inverse-law-add-ℤᵉ yᵉ)) ∙ᵉ
          ( left-unit-law-add-ℤᵉ (neg-ℤᵉ zᵉ)))))
```

### The negative of the difference of two integers `x` and `y` is the difference of `y` and `x`

```agda
abstract
  distributive-neg-diff-ℤᵉ :
    (xᵉ yᵉ : ℤᵉ) → neg-ℤᵉ (xᵉ -ℤᵉ yᵉ) ＝ᵉ yᵉ -ℤᵉ xᵉ
  distributive-neg-diff-ℤᵉ xᵉ yᵉ =
    ( distributive-neg-add-ℤᵉ xᵉ (neg-ℤᵉ yᵉ)) ∙ᵉ
    ( apᵉ ((neg-ℤᵉ xᵉ) +ℤᵉ_) (neg-neg-ℤᵉ yᵉ)) ∙ᵉ
    ( commutative-add-ℤᵉ (neg-ℤᵉ xᵉ) yᵉ)
```

### Interchange laws for addition and difference of integers

```agda
abstract
  interchange-law-add-diff-ℤᵉ :
    (xᵉ yᵉ uᵉ vᵉ : ℤᵉ) → (xᵉ -ℤᵉ yᵉ) +ℤᵉ (uᵉ -ℤᵉ vᵉ) ＝ᵉ (xᵉ +ℤᵉ uᵉ) -ℤᵉ (yᵉ +ℤᵉ vᵉ)
  interchange-law-add-diff-ℤᵉ xᵉ yᵉ uᵉ vᵉ =
    ( interchange-law-add-add-ℤᵉ xᵉ (neg-ℤᵉ yᵉ) uᵉ (neg-ℤᵉ vᵉ)) ∙ᵉ
    ( apᵉ ((xᵉ +ℤᵉ uᵉ) +ℤᵉ_) (invᵉ (distributive-neg-add-ℤᵉ yᵉ vᵉ)))

  interchange-law-diff-add-ℤᵉ :
    (xᵉ yᵉ uᵉ vᵉ : ℤᵉ) → (xᵉ +ℤᵉ yᵉ) -ℤᵉ (uᵉ +ℤᵉ vᵉ) ＝ᵉ (xᵉ -ℤᵉ uᵉ) +ℤᵉ (yᵉ -ℤᵉ vᵉ)
  interchange-law-diff-add-ℤᵉ xᵉ yᵉ uᵉ vᵉ = invᵉ (interchange-law-add-diff-ℤᵉ xᵉ uᵉ yᵉ vᵉ)
```

### The difference of integers is invariant by translation

```agda
abstract
  left-translation-diff-ℤᵉ :
    (xᵉ yᵉ zᵉ : ℤᵉ) → (zᵉ +ℤᵉ xᵉ) -ℤᵉ (zᵉ +ℤᵉ yᵉ) ＝ᵉ xᵉ -ℤᵉ yᵉ
  left-translation-diff-ℤᵉ xᵉ yᵉ zᵉ =
    ( interchange-law-diff-add-ℤᵉ zᵉ xᵉ zᵉ yᵉ) ∙ᵉ
    ( ( apᵉ (_+ℤᵉ (xᵉ -ℤᵉ yᵉ)) (right-inverse-law-add-ℤᵉ zᵉ)) ∙ᵉ
      ( left-unit-law-add-ℤᵉ (xᵉ -ℤᵉ yᵉ)))

  right-translation-diff-ℤᵉ :
    (xᵉ yᵉ zᵉ : ℤᵉ) → (xᵉ +ℤᵉ zᵉ) -ℤᵉ (yᵉ +ℤᵉ zᵉ) ＝ᵉ xᵉ -ℤᵉ yᵉ
  right-translation-diff-ℤᵉ xᵉ yᵉ zᵉ =
    ( ap-diff-ℤᵉ (commutative-add-ℤᵉ xᵉ zᵉ) (commutative-add-ℤᵉ yᵉ zᵉ)) ∙ᵉ
    ( left-translation-diff-ℤᵉ xᵉ yᵉ zᵉ)
```

### The difference of the successors of two integers is their difference

```agda
abstract
  diff-succ-ℤᵉ : (xᵉ yᵉ : ℤᵉ) → (succ-ℤᵉ xᵉ) -ℤᵉ (succ-ℤᵉ yᵉ) ＝ᵉ xᵉ -ℤᵉ yᵉ
  diff-succ-ℤᵉ xᵉ yᵉ =
    ( apᵉ ((succ-ℤᵉ xᵉ) +ℤᵉ_) (neg-succ-ℤᵉ yᵉ)) ∙ᵉ
    ( left-successor-law-add-ℤᵉ xᵉ (pred-ℤᵉ (neg-ℤᵉ yᵉ))) ∙ᵉ
    ( apᵉ succ-ℤᵉ (right-predecessor-law-add-ℤᵉ xᵉ (neg-ℤᵉ yᵉ))) ∙ᵉ
    ( is-section-pred-ℤᵉ (xᵉ -ℤᵉ yᵉ))
```