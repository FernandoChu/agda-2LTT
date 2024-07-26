# Addition on the natural numbers

```agda
module elementary-number-theory.addition-natural-numbersᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.equality-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ

open import foundation.action-on-identifications-binary-functionsᵉ
open import foundation.action-on-identifications-functionsᵉ
open import foundation.cartesian-product-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.embeddingsᵉ
open import foundation.empty-typesᵉ
open import foundation.function-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.injective-mapsᵉ
open import foundation.interchange-lawᵉ
open import foundation.negated-equalityᵉ
open import foundation.setsᵉ
```

</details>

## Definition

```agda
add-ℕᵉ : ℕᵉ → ℕᵉ → ℕᵉ
add-ℕᵉ xᵉ 0 = xᵉ
add-ℕᵉ xᵉ (succ-ℕᵉ yᵉ) = succ-ℕᵉ (add-ℕᵉ xᵉ yᵉ)

infixl 35 _+ℕᵉ_
_+ℕᵉ_ = add-ℕᵉ

add-ℕ'ᵉ : ℕᵉ → ℕᵉ → ℕᵉ
add-ℕ'ᵉ mᵉ nᵉ = add-ℕᵉ nᵉ mᵉ

ap-add-ℕᵉ :
  {mᵉ nᵉ m'ᵉ n'ᵉ : ℕᵉ} → mᵉ ＝ᵉ m'ᵉ → nᵉ ＝ᵉ n'ᵉ → mᵉ +ℕᵉ nᵉ ＝ᵉ m'ᵉ +ℕᵉ n'ᵉ
ap-add-ℕᵉ pᵉ qᵉ = ap-binaryᵉ add-ℕᵉ pᵉ qᵉ
```

## Properties

### The left and right unit laws

```agda
right-unit-law-add-ℕᵉ :
  (xᵉ : ℕᵉ) → xᵉ +ℕᵉ zero-ℕᵉ ＝ᵉ xᵉ
right-unit-law-add-ℕᵉ xᵉ = reflᵉ

left-unit-law-add-ℕᵉ :
  (xᵉ : ℕᵉ) → zero-ℕᵉ +ℕᵉ xᵉ ＝ᵉ xᵉ
left-unit-law-add-ℕᵉ zero-ℕᵉ = reflᵉ
left-unit-law-add-ℕᵉ (succ-ℕᵉ xᵉ) = apᵉ succ-ℕᵉ (left-unit-law-add-ℕᵉ xᵉ)
```

### The left and right successor laws

```agda
abstract
  left-successor-law-add-ℕᵉ :
    (xᵉ yᵉ : ℕᵉ) → (succ-ℕᵉ xᵉ) +ℕᵉ yᵉ ＝ᵉ succ-ℕᵉ (xᵉ +ℕᵉ yᵉ)
  left-successor-law-add-ℕᵉ xᵉ zero-ℕᵉ = reflᵉ
  left-successor-law-add-ℕᵉ xᵉ (succ-ℕᵉ yᵉ) =
    apᵉ succ-ℕᵉ (left-successor-law-add-ℕᵉ xᵉ yᵉ)

right-successor-law-add-ℕᵉ :
  (xᵉ yᵉ : ℕᵉ) → xᵉ +ℕᵉ (succ-ℕᵉ yᵉ) ＝ᵉ succ-ℕᵉ (xᵉ +ℕᵉ yᵉ)
right-successor-law-add-ℕᵉ xᵉ yᵉ = reflᵉ
```

### Addition is associative

```agda
abstract
  associative-add-ℕᵉ :
    (xᵉ yᵉ zᵉ : ℕᵉ) → (xᵉ +ℕᵉ yᵉ) +ℕᵉ zᵉ ＝ᵉ xᵉ +ℕᵉ (yᵉ +ℕᵉ zᵉ)
  associative-add-ℕᵉ xᵉ yᵉ zero-ℕᵉ = reflᵉ
  associative-add-ℕᵉ xᵉ yᵉ (succ-ℕᵉ zᵉ) = apᵉ succ-ℕᵉ (associative-add-ℕᵉ xᵉ yᵉ zᵉ)
```

### Addition is commutative

```agda
abstract
  commutative-add-ℕᵉ : (xᵉ yᵉ : ℕᵉ) → xᵉ +ℕᵉ yᵉ ＝ᵉ yᵉ +ℕᵉ xᵉ
  commutative-add-ℕᵉ zero-ℕᵉ yᵉ = left-unit-law-add-ℕᵉ yᵉ
  commutative-add-ℕᵉ (succ-ℕᵉ xᵉ) yᵉ =
    (left-successor-law-add-ℕᵉ xᵉ yᵉ) ∙ᵉ (apᵉ succ-ℕᵉ (commutative-add-ℕᵉ xᵉ yᵉ))
```

### Addition by `1` on the left or on the right is the successor

```agda
abstract
  left-one-law-add-ℕᵉ :
    (xᵉ : ℕᵉ) → 1 +ℕᵉ xᵉ ＝ᵉ succ-ℕᵉ xᵉ
  left-one-law-add-ℕᵉ xᵉ =
    ( left-successor-law-add-ℕᵉ zero-ℕᵉ xᵉ) ∙ᵉ
    ( apᵉ succ-ℕᵉ (left-unit-law-add-ℕᵉ xᵉ))

  right-one-law-add-ℕᵉ :
    (xᵉ : ℕᵉ) → xᵉ +ℕᵉ 1 ＝ᵉ succ-ℕᵉ xᵉ
  right-one-law-add-ℕᵉ xᵉ = reflᵉ
```

### Addition by `1` on the left or on the right is the double successor

```agda
abstract
  left-two-law-add-ℕᵉ :
    (xᵉ : ℕᵉ) → 2 +ℕᵉ xᵉ ＝ᵉ succ-ℕᵉ (succ-ℕᵉ xᵉ)
  left-two-law-add-ℕᵉ xᵉ =
    ( left-successor-law-add-ℕᵉ 1 xᵉ) ∙ᵉ
    ( apᵉ succ-ℕᵉ (left-one-law-add-ℕᵉ xᵉ))

  right-two-law-add-ℕᵉ :
    (xᵉ : ℕᵉ) → xᵉ +ℕᵉ 2 ＝ᵉ succ-ℕᵉ (succ-ℕᵉ xᵉ)
  right-two-law-add-ℕᵉ xᵉ = reflᵉ
```

### Interchange law of addition

```agda
abstract
  interchange-law-add-add-ℕᵉ : interchange-lawᵉ add-ℕᵉ add-ℕᵉ
  interchange-law-add-add-ℕᵉ =
    interchange-law-commutative-and-associativeᵉ
      add-ℕᵉ
      commutative-add-ℕᵉ
      associative-add-ℕᵉ
```

### Addition by a fixed element on either side is injective

```agda
abstract
  is-injective-right-add-ℕᵉ : (kᵉ : ℕᵉ) → is-injectiveᵉ (_+ℕᵉ kᵉ)
  is-injective-right-add-ℕᵉ zero-ℕᵉ = idᵉ
  is-injective-right-add-ℕᵉ (succ-ℕᵉ kᵉ) pᵉ =
    is-injective-right-add-ℕᵉ kᵉ (is-injective-succ-ℕᵉ pᵉ)

  is-injective-left-add-ℕᵉ : (kᵉ : ℕᵉ) → is-injectiveᵉ (kᵉ +ℕᵉ_)
  is-injective-left-add-ℕᵉ kᵉ {xᵉ} {yᵉ} pᵉ =
    is-injective-right-add-ℕᵉ
      ( kᵉ)
      ( commutative-add-ℕᵉ xᵉ kᵉ ∙ᵉ (pᵉ ∙ᵉ commutative-add-ℕᵉ kᵉ yᵉ))
```

### Addition by a fixed element on either side is an embedding

```agda
abstract
  is-emb-left-add-ℕᵉ : (xᵉ : ℕᵉ) → is-embᵉ (xᵉ +ℕᵉ_)
  is-emb-left-add-ℕᵉ xᵉ =
    is-emb-is-injectiveᵉ is-set-ℕᵉ (is-injective-left-add-ℕᵉ xᵉ)

  is-emb-right-add-ℕᵉ : (xᵉ : ℕᵉ) → is-embᵉ (_+ℕᵉ xᵉ)
  is-emb-right-add-ℕᵉ xᵉ =
    is-emb-is-injectiveᵉ is-set-ℕᵉ (is-injective-right-add-ℕᵉ xᵉ)
```

### `x + y ＝ 0` if and only if both `x` and `y` are `0`

```agda
abstract
  is-zero-right-is-zero-add-ℕᵉ :
    (xᵉ yᵉ : ℕᵉ) → is-zero-ℕᵉ (xᵉ +ℕᵉ yᵉ) → is-zero-ℕᵉ yᵉ
  is-zero-right-is-zero-add-ℕᵉ xᵉ zero-ℕᵉ pᵉ = reflᵉ
  is-zero-right-is-zero-add-ℕᵉ xᵉ (succ-ℕᵉ yᵉ) pᵉ =
    ex-falsoᵉ (is-nonzero-succ-ℕᵉ (xᵉ +ℕᵉ yᵉ) pᵉ)

  is-zero-left-is-zero-add-ℕᵉ :
    (xᵉ yᵉ : ℕᵉ) → is-zero-ℕᵉ (xᵉ +ℕᵉ yᵉ) → is-zero-ℕᵉ xᵉ
  is-zero-left-is-zero-add-ℕᵉ xᵉ yᵉ pᵉ =
    is-zero-right-is-zero-add-ℕᵉ yᵉ xᵉ ((commutative-add-ℕᵉ yᵉ xᵉ) ∙ᵉ pᵉ)

  is-zero-summand-is-zero-sum-ℕᵉ :
    (xᵉ yᵉ : ℕᵉ) → is-zero-ℕᵉ (xᵉ +ℕᵉ yᵉ) → (is-zero-ℕᵉ xᵉ) ×ᵉ (is-zero-ℕᵉ yᵉ)
  is-zero-summand-is-zero-sum-ℕᵉ xᵉ yᵉ pᵉ =
    pairᵉ (is-zero-left-is-zero-add-ℕᵉ xᵉ yᵉ pᵉ) (is-zero-right-is-zero-add-ℕᵉ xᵉ yᵉ pᵉ)

  is-zero-sum-is-zero-summand-ℕᵉ :
    (xᵉ yᵉ : ℕᵉ) → (is-zero-ℕᵉ xᵉ) ×ᵉ (is-zero-ℕᵉ yᵉ) → is-zero-ℕᵉ (xᵉ +ℕᵉ yᵉ)
  is-zero-sum-is-zero-summand-ℕᵉ .zero-ℕᵉ .zero-ℕᵉ (pairᵉ reflᵉ reflᵉ) = reflᵉ
```

### `m ≠ m + n + 1`

```agda
abstract
  neq-add-ℕᵉ :
    (mᵉ nᵉ : ℕᵉ) → mᵉ ≠ᵉ mᵉ +ℕᵉ (succ-ℕᵉ nᵉ)
  neq-add-ℕᵉ (succ-ℕᵉ mᵉ) nᵉ pᵉ =
    neq-add-ℕᵉ mᵉ nᵉ
      ( ( is-injective-succ-ℕᵉ pᵉ) ∙ᵉ
        ( left-successor-law-add-ℕᵉ mᵉ nᵉ))
```

## See also

-ᵉ Theᵉ commutativeᵉ monoidᵉ ofᵉ theᵉ naturalᵉ numbersᵉ with additionᵉ isᵉ definedᵉ in
  [`monoid-of-natural-numbers-with-addition`](elementary-number-theory.monoid-of-natural-numbers-with-addition.md).ᵉ