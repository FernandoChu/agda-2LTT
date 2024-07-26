# Addition on the integers

```agda
module elementary-number-theory.addition-integersᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbersᵉ
open import elementary-number-theory.integersᵉ
open import elementary-number-theory.natural-numbersᵉ
open import elementary-number-theory.nonnegative-integersᵉ
open import elementary-number-theory.positive-and-negative-integersᵉ
open import elementary-number-theory.positive-integersᵉ

open import foundation.action-on-identifications-binary-functionsᵉ
open import foundation.action-on-identifications-functionsᵉ
open import foundation.binary-embeddingsᵉ
open import foundation.binary-equivalencesᵉ
open import foundation.coproduct-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.embeddingsᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.injective-mapsᵉ
open import foundation.interchange-lawᵉ
open import foundation.setsᵉ
open import foundation.unit-typeᵉ
```

</details>

## Idea

Weᵉ introduceᵉ {{#conceptᵉ "addition"ᵉ Disambiguation="integers"ᵉ Agda=add-ℤᵉ}} onᵉ theᵉ
[integers](elementary-number-theory.integers.mdᵉ) andᵉ deriveᵉ itsᵉ basicᵉ propertiesᵉ
with respectᵉ to `succ-ℤ`ᵉ andᵉ `neg-ℤ`.ᵉ

## Definition

```agda
add-ℤᵉ : ℤᵉ → ℤᵉ → ℤᵉ
add-ℤᵉ (inlᵉ zero-ℕᵉ) lᵉ = pred-ℤᵉ lᵉ
add-ℤᵉ (inlᵉ (succ-ℕᵉ xᵉ)) lᵉ = pred-ℤᵉ (add-ℤᵉ (inlᵉ xᵉ) lᵉ)
add-ℤᵉ (inrᵉ (inlᵉ starᵉ)) lᵉ = lᵉ
add-ℤᵉ (inrᵉ (inrᵉ zero-ℕᵉ)) lᵉ = succ-ℤᵉ lᵉ
add-ℤᵉ (inrᵉ (inrᵉ (succ-ℕᵉ xᵉ))) lᵉ = succ-ℤᵉ (add-ℤᵉ (inrᵉ (inrᵉ xᵉ)) lᵉ)

add-ℤ'ᵉ : ℤᵉ → ℤᵉ → ℤᵉ
add-ℤ'ᵉ xᵉ yᵉ = add-ℤᵉ yᵉ xᵉ

infixl 35 _+ℤᵉ_
_+ℤᵉ_ = add-ℤᵉ

ap-add-ℤᵉ :
  {xᵉ yᵉ x'ᵉ y'ᵉ : ℤᵉ} → xᵉ ＝ᵉ x'ᵉ → yᵉ ＝ᵉ y'ᵉ → xᵉ +ℤᵉ yᵉ ＝ᵉ x'ᵉ +ℤᵉ y'ᵉ
ap-add-ℤᵉ pᵉ qᵉ = ap-binaryᵉ add-ℤᵉ pᵉ qᵉ
```

## Properties

### Unit laws

```agda
abstract
  left-unit-law-add-ℤᵉ : (kᵉ : ℤᵉ) → zero-ℤᵉ +ℤᵉ kᵉ ＝ᵉ kᵉ
  left-unit-law-add-ℤᵉ kᵉ = reflᵉ

  right-unit-law-add-ℤᵉ : (kᵉ : ℤᵉ) → kᵉ +ℤᵉ zero-ℤᵉ ＝ᵉ kᵉ
  right-unit-law-add-ℤᵉ (inlᵉ zero-ℕᵉ) = reflᵉ
  right-unit-law-add-ℤᵉ (inlᵉ (succ-ℕᵉ xᵉ)) =
    apᵉ pred-ℤᵉ (right-unit-law-add-ℤᵉ (inlᵉ xᵉ))
  right-unit-law-add-ℤᵉ (inrᵉ (inlᵉ starᵉ)) = reflᵉ
  right-unit-law-add-ℤᵉ (inrᵉ (inrᵉ zero-ℕᵉ)) = reflᵉ
  right-unit-law-add-ℤᵉ (inrᵉ (inrᵉ (succ-ℕᵉ xᵉ))) =
    apᵉ succ-ℤᵉ (right-unit-law-add-ℤᵉ (inrᵉ (inrᵉ xᵉ)))
```

### Left and right predecessor laws

```agda
abstract
  left-predecessor-law-add-ℤᵉ :
    (xᵉ yᵉ : ℤᵉ) → pred-ℤᵉ xᵉ +ℤᵉ yᵉ ＝ᵉ pred-ℤᵉ (xᵉ +ℤᵉ yᵉ)
  left-predecessor-law-add-ℤᵉ (inlᵉ nᵉ) yᵉ = reflᵉ
  left-predecessor-law-add-ℤᵉ (inrᵉ (inlᵉ starᵉ)) yᵉ = reflᵉ
  left-predecessor-law-add-ℤᵉ (inrᵉ (inrᵉ zero-ℕᵉ)) yᵉ =
    invᵉ (is-retraction-pred-ℤᵉ yᵉ)
  left-predecessor-law-add-ℤᵉ (inrᵉ (inrᵉ (succ-ℕᵉ xᵉ))) yᵉ =
    invᵉ (is-retraction-pred-ℤᵉ ((inrᵉ (inrᵉ xᵉ)) +ℤᵉ yᵉ))

  right-predecessor-law-add-ℤᵉ :
    (xᵉ yᵉ : ℤᵉ) → xᵉ +ℤᵉ pred-ℤᵉ yᵉ ＝ᵉ pred-ℤᵉ (xᵉ +ℤᵉ yᵉ)
  right-predecessor-law-add-ℤᵉ (inlᵉ zero-ℕᵉ) nᵉ = reflᵉ
  right-predecessor-law-add-ℤᵉ (inlᵉ (succ-ℕᵉ mᵉ)) nᵉ =
    apᵉ pred-ℤᵉ (right-predecessor-law-add-ℤᵉ (inlᵉ mᵉ) nᵉ)
  right-predecessor-law-add-ℤᵉ (inrᵉ (inlᵉ starᵉ)) nᵉ = reflᵉ
  right-predecessor-law-add-ℤᵉ (inrᵉ (inrᵉ zero-ℕᵉ)) nᵉ =
    equational-reasoningᵉ
      succ-ℤᵉ (pred-ℤᵉ nᵉ)
      ＝ᵉ nᵉ
        byᵉ is-section-pred-ℤᵉ nᵉ
      ＝ᵉ pred-ℤᵉ (succ-ℤᵉ nᵉ)
        byᵉ invᵉ (is-retraction-pred-ℤᵉ nᵉ)
  right-predecessor-law-add-ℤᵉ (inrᵉ (inrᵉ (succ-ℕᵉ xᵉ))) nᵉ =
    equational-reasoningᵉ
      succ-ℤᵉ (inrᵉ (inrᵉ xᵉ) +ℤᵉ pred-ℤᵉ nᵉ)
      ＝ᵉ succ-ℤᵉ (pred-ℤᵉ (inrᵉ (inrᵉ xᵉ) +ℤᵉ nᵉ))
        byᵉ apᵉ succ-ℤᵉ (right-predecessor-law-add-ℤᵉ (inrᵉ (inrᵉ xᵉ)) nᵉ)
      ＝ᵉ inrᵉ (inrᵉ xᵉ) +ℤᵉ nᵉ
        byᵉ is-section-pred-ℤᵉ ((inrᵉ (inrᵉ xᵉ)) +ℤᵉ nᵉ)
      ＝ᵉ pred-ℤᵉ (succ-ℤᵉ (inrᵉ (inrᵉ xᵉ) +ℤᵉ nᵉ))
        byᵉ invᵉ (is-retraction-pred-ℤᵉ ((inrᵉ (inrᵉ xᵉ)) +ℤᵉ nᵉ))
```

### Left and right successor laws

```agda
abstract
  left-successor-law-add-ℤᵉ :
    (xᵉ yᵉ : ℤᵉ) → succ-ℤᵉ xᵉ +ℤᵉ yᵉ ＝ᵉ succ-ℤᵉ (xᵉ +ℤᵉ yᵉ)
  left-successor-law-add-ℤᵉ (inlᵉ zero-ℕᵉ) yᵉ =
    invᵉ (is-section-pred-ℤᵉ yᵉ)
  left-successor-law-add-ℤᵉ (inlᵉ (succ-ℕᵉ xᵉ)) yᵉ =
    equational-reasoningᵉ
      inlᵉ xᵉ +ℤᵉ yᵉ
      ＝ᵉ succ-ℤᵉ (pred-ℤᵉ (inlᵉ xᵉ +ℤᵉ yᵉ))
        byᵉ invᵉ (is-section-pred-ℤᵉ ((inlᵉ xᵉ) +ℤᵉ yᵉ))
      ＝ᵉ succ-ℤᵉ (pred-ℤᵉ (inlᵉ xᵉ) +ℤᵉ yᵉ)
        byᵉ apᵉ succ-ℤᵉ (invᵉ (left-predecessor-law-add-ℤᵉ (inlᵉ xᵉ) yᵉ))
  left-successor-law-add-ℤᵉ (inrᵉ (inlᵉ starᵉ)) yᵉ = reflᵉ
  left-successor-law-add-ℤᵉ (inrᵉ (inrᵉ xᵉ)) yᵉ = reflᵉ

  right-successor-law-add-ℤᵉ :
    (xᵉ yᵉ : ℤᵉ) → xᵉ +ℤᵉ succ-ℤᵉ yᵉ ＝ᵉ succ-ℤᵉ (xᵉ +ℤᵉ yᵉ)
  right-successor-law-add-ℤᵉ (inlᵉ zero-ℕᵉ) yᵉ =
    equational-reasoningᵉ
      pred-ℤᵉ (succ-ℤᵉ yᵉ)
      ＝ᵉ yᵉ
        byᵉ is-retraction-pred-ℤᵉ yᵉ
      ＝ᵉ succ-ℤᵉ (pred-ℤᵉ yᵉ)
        byᵉ invᵉ (is-section-pred-ℤᵉ yᵉ)
  right-successor-law-add-ℤᵉ (inlᵉ (succ-ℕᵉ xᵉ)) yᵉ =
    equational-reasoningᵉ
      pred-ℤᵉ (inlᵉ xᵉ +ℤᵉ succ-ℤᵉ yᵉ)
      ＝ᵉ pred-ℤᵉ (succ-ℤᵉ (inlᵉ xᵉ +ℤᵉ yᵉ))
        byᵉ apᵉ pred-ℤᵉ (right-successor-law-add-ℤᵉ (inlᵉ xᵉ) yᵉ)
      ＝ᵉ inlᵉ xᵉ +ℤᵉ yᵉ
        byᵉ is-retraction-pred-ℤᵉ ((inlᵉ xᵉ) +ℤᵉ yᵉ)
      ＝ᵉ succ-ℤᵉ (pred-ℤᵉ (inlᵉ xᵉ +ℤᵉ yᵉ))
        byᵉ invᵉ (is-section-pred-ℤᵉ ((inlᵉ xᵉ) +ℤᵉ yᵉ))
  right-successor-law-add-ℤᵉ (inrᵉ (inlᵉ starᵉ)) yᵉ = reflᵉ
  right-successor-law-add-ℤᵉ (inrᵉ (inrᵉ zero-ℕᵉ)) yᵉ = reflᵉ
  right-successor-law-add-ℤᵉ (inrᵉ (inrᵉ (succ-ℕᵉ xᵉ))) yᵉ =
    apᵉ succ-ℤᵉ (right-successor-law-add-ℤᵉ (inrᵉ (inrᵉ xᵉ)) yᵉ)
```

### The successor of an integer is that integer plus one

```agda
abstract
  is-right-add-one-succ-ℤᵉ : (xᵉ : ℤᵉ) → succ-ℤᵉ xᵉ ＝ᵉ xᵉ +ℤᵉ one-ℤᵉ
  is-right-add-one-succ-ℤᵉ xᵉ =
    equational-reasoningᵉ
      succ-ℤᵉ xᵉ
      ＝ᵉ succ-ℤᵉ (xᵉ +ℤᵉ zero-ℤᵉ)
        byᵉ invᵉ (apᵉ succ-ℤᵉ (right-unit-law-add-ℤᵉ xᵉ))
      ＝ᵉ xᵉ +ℤᵉ one-ℤᵉ
        byᵉ invᵉ (right-successor-law-add-ℤᵉ xᵉ zero-ℤᵉ)

  is-left-add-one-succ-ℤᵉ : (xᵉ : ℤᵉ) → succ-ℤᵉ xᵉ ＝ᵉ one-ℤᵉ +ℤᵉ xᵉ
  is-left-add-one-succ-ℤᵉ xᵉ = invᵉ (left-successor-law-add-ℤᵉ zero-ℤᵉ xᵉ)

  left-add-one-ℤᵉ : (xᵉ : ℤᵉ) → one-ℤᵉ +ℤᵉ xᵉ ＝ᵉ succ-ℤᵉ xᵉ
  left-add-one-ℤᵉ xᵉ = reflᵉ

  right-add-one-ℤᵉ : (xᵉ : ℤᵉ) → xᵉ +ℤᵉ one-ℤᵉ ＝ᵉ succ-ℤᵉ xᵉ
  right-add-one-ℤᵉ xᵉ = invᵉ (is-right-add-one-succ-ℤᵉ xᵉ)
```

### The predecessor of an integer is that integer minus one

```agda
  is-left-add-neg-one-pred-ℤᵉ : (xᵉ : ℤᵉ) → pred-ℤᵉ xᵉ ＝ᵉ neg-one-ℤᵉ +ℤᵉ xᵉ
  is-left-add-neg-one-pred-ℤᵉ xᵉ =
    invᵉ (left-predecessor-law-add-ℤᵉ zero-ℤᵉ xᵉ)

  is-right-add-neg-one-pred-ℤᵉ : (xᵉ : ℤᵉ) → pred-ℤᵉ xᵉ ＝ᵉ xᵉ +ℤᵉ neg-one-ℤᵉ
  is-right-add-neg-one-pred-ℤᵉ xᵉ =
    equational-reasoningᵉ
      pred-ℤᵉ xᵉ
      ＝ᵉ pred-ℤᵉ (xᵉ +ℤᵉ zero-ℤᵉ)
        byᵉ invᵉ (apᵉ pred-ℤᵉ (right-unit-law-add-ℤᵉ xᵉ))
      ＝ᵉ xᵉ +ℤᵉ neg-one-ℤᵉ
        byᵉ invᵉ (right-predecessor-law-add-ℤᵉ xᵉ zero-ℤᵉ)

  left-add-neg-one-ℤᵉ : (xᵉ : ℤᵉ) → neg-one-ℤᵉ +ℤᵉ xᵉ ＝ᵉ pred-ℤᵉ xᵉ
  left-add-neg-one-ℤᵉ xᵉ = reflᵉ

  right-add-neg-one-ℤᵉ : (xᵉ : ℤᵉ) → xᵉ +ℤᵉ neg-one-ℤᵉ ＝ᵉ pred-ℤᵉ xᵉ
  right-add-neg-one-ℤᵉ xᵉ = invᵉ (is-right-add-neg-one-pred-ℤᵉ xᵉ)
```

### Addition is associative

```agda
abstract
  associative-add-ℤᵉ :
    (xᵉ yᵉ zᵉ : ℤᵉ) → ((xᵉ +ℤᵉ yᵉ) +ℤᵉ zᵉ) ＝ᵉ (xᵉ +ℤᵉ (yᵉ +ℤᵉ zᵉ))
  associative-add-ℤᵉ (inlᵉ zero-ℕᵉ) yᵉ zᵉ =
    equational-reasoningᵉ
      (neg-one-ℤᵉ +ℤᵉ yᵉ) +ℤᵉ zᵉ
      ＝ᵉ (pred-ℤᵉ (zero-ℤᵉ +ℤᵉ yᵉ)) +ℤᵉ zᵉ
        byᵉ apᵉ (_+ℤᵉ zᵉ) (left-predecessor-law-add-ℤᵉ zero-ℤᵉ yᵉ)
      ＝ᵉ pred-ℤᵉ (yᵉ +ℤᵉ zᵉ)
        byᵉ left-predecessor-law-add-ℤᵉ yᵉ zᵉ
      ＝ᵉ neg-one-ℤᵉ +ℤᵉ (yᵉ +ℤᵉ zᵉ)
        byᵉ invᵉ (left-predecessor-law-add-ℤᵉ zero-ℤᵉ (yᵉ +ℤᵉ zᵉ))
  associative-add-ℤᵉ (inlᵉ (succ-ℕᵉ xᵉ)) yᵉ zᵉ =
    equational-reasoningᵉ
      (pred-ℤᵉ (inlᵉ xᵉ) +ℤᵉ yᵉ) +ℤᵉ zᵉ
      ＝ᵉ pred-ℤᵉ (inlᵉ xᵉ +ℤᵉ yᵉ) +ℤᵉ zᵉ
        byᵉ apᵉ (_+ℤᵉ zᵉ) (left-predecessor-law-add-ℤᵉ (inlᵉ xᵉ) yᵉ)
      ＝ᵉ pred-ℤᵉ ((inlᵉ xᵉ +ℤᵉ yᵉ) +ℤᵉ zᵉ)
        byᵉ left-predecessor-law-add-ℤᵉ ((inlᵉ xᵉ) +ℤᵉ yᵉ) zᵉ
      ＝ᵉ pred-ℤᵉ (inlᵉ xᵉ +ℤᵉ (yᵉ +ℤᵉ zᵉ))
        byᵉ apᵉ pred-ℤᵉ (associative-add-ℤᵉ (inlᵉ xᵉ) yᵉ zᵉ)
      ＝ᵉ pred-ℤᵉ (inlᵉ xᵉ) +ℤᵉ (yᵉ +ℤᵉ zᵉ)
        byᵉ invᵉ (left-predecessor-law-add-ℤᵉ (inlᵉ xᵉ) (yᵉ +ℤᵉ zᵉ))
  associative-add-ℤᵉ (inrᵉ (inlᵉ starᵉ)) yᵉ zᵉ =
    reflᵉ
  associative-add-ℤᵉ (inrᵉ (inrᵉ zero-ℕᵉ)) yᵉ zᵉ =
    equational-reasoningᵉ
      (one-ℤᵉ +ℤᵉ yᵉ) +ℤᵉ zᵉ
      ＝ᵉ succ-ℤᵉ (zero-ℤᵉ +ℤᵉ yᵉ) +ℤᵉ zᵉ
        byᵉ apᵉ (_+ℤᵉ zᵉ) (left-successor-law-add-ℤᵉ zero-ℤᵉ yᵉ)
      ＝ᵉ succ-ℤᵉ (yᵉ +ℤᵉ zᵉ)
        byᵉ left-successor-law-add-ℤᵉ yᵉ zᵉ
      ＝ᵉ one-ℤᵉ +ℤᵉ (yᵉ +ℤᵉ zᵉ)
        byᵉ invᵉ (left-successor-law-add-ℤᵉ zero-ℤᵉ (yᵉ +ℤᵉ zᵉ))
  associative-add-ℤᵉ (inrᵉ (inrᵉ (succ-ℕᵉ xᵉ))) yᵉ zᵉ =
    equational-reasoningᵉ
      (succ-ℤᵉ (inrᵉ (inrᵉ xᵉ)) +ℤᵉ yᵉ) +ℤᵉ zᵉ
      ＝ᵉ succ-ℤᵉ (inrᵉ (inrᵉ xᵉ) +ℤᵉ yᵉ) +ℤᵉ zᵉ
        byᵉ apᵉ (_+ℤᵉ zᵉ) (left-successor-law-add-ℤᵉ (inrᵉ (inrᵉ xᵉ)) yᵉ)
      ＝ᵉ succ-ℤᵉ ((inrᵉ (inrᵉ xᵉ) +ℤᵉ yᵉ) +ℤᵉ zᵉ)
        byᵉ left-successor-law-add-ℤᵉ ((inrᵉ (inrᵉ xᵉ)) +ℤᵉ yᵉ) zᵉ
      ＝ᵉ succ-ℤᵉ (inrᵉ (inrᵉ xᵉ) +ℤᵉ (yᵉ +ℤᵉ zᵉ))
        byᵉ apᵉ succ-ℤᵉ (associative-add-ℤᵉ (inrᵉ (inrᵉ xᵉ)) yᵉ zᵉ)
      ＝ᵉ succ-ℤᵉ (inrᵉ (inrᵉ xᵉ)) +ℤᵉ (yᵉ +ℤᵉ zᵉ)
        byᵉ invᵉ (left-successor-law-add-ℤᵉ (inrᵉ (inrᵉ xᵉ)) (yᵉ +ℤᵉ zᵉ))
```

### Addition is commutative

```agda
abstract
  commutative-add-ℤᵉ : (xᵉ yᵉ : ℤᵉ) → xᵉ +ℤᵉ yᵉ ＝ᵉ yᵉ +ℤᵉ xᵉ
  commutative-add-ℤᵉ (inlᵉ zero-ℕᵉ) yᵉ =
    equational-reasoningᵉ
      neg-one-ℤᵉ +ℤᵉ yᵉ
      ＝ᵉ pred-ℤᵉ (zero-ℤᵉ +ℤᵉ yᵉ)
        byᵉ left-predecessor-law-add-ℤᵉ zero-ℤᵉ yᵉ
      ＝ᵉ pred-ℤᵉ (yᵉ +ℤᵉ zero-ℤᵉ)
        byᵉ invᵉ (apᵉ pred-ℤᵉ (right-unit-law-add-ℤᵉ yᵉ))
      ＝ᵉ yᵉ +ℤᵉ neg-one-ℤᵉ
        byᵉ invᵉ (right-predecessor-law-add-ℤᵉ yᵉ zero-ℤᵉ)
  commutative-add-ℤᵉ (inlᵉ (succ-ℕᵉ xᵉ)) yᵉ =
    equational-reasoningᵉ
      (inlᵉ (succ-ℕᵉ xᵉ)) +ℤᵉ yᵉ
      ＝ᵉ pred-ℤᵉ (yᵉ +ℤᵉ (inlᵉ xᵉ))
        byᵉ apᵉ pred-ℤᵉ (commutative-add-ℤᵉ (inlᵉ xᵉ) yᵉ)
      ＝ᵉ yᵉ +ℤᵉ (inlᵉ (succ-ℕᵉ xᵉ))
        byᵉ invᵉ (right-predecessor-law-add-ℤᵉ yᵉ (inlᵉ xᵉ))
  commutative-add-ℤᵉ (inrᵉ (inlᵉ starᵉ)) yᵉ =
    invᵉ (right-unit-law-add-ℤᵉ yᵉ)
  commutative-add-ℤᵉ (inrᵉ (inrᵉ zero-ℕᵉ)) yᵉ =
    equational-reasoningᵉ
      succ-ℤᵉ yᵉ
      ＝ᵉ succ-ℤᵉ (yᵉ +ℤᵉ zero-ℤᵉ)
        byᵉ invᵉ (apᵉ succ-ℤᵉ (right-unit-law-add-ℤᵉ yᵉ))
      ＝ᵉ yᵉ +ℤᵉ one-ℤᵉ
        byᵉ invᵉ (right-successor-law-add-ℤᵉ yᵉ zero-ℤᵉ)
  commutative-add-ℤᵉ (inrᵉ (inrᵉ (succ-ℕᵉ xᵉ))) yᵉ =
    equational-reasoningᵉ
      succ-ℤᵉ ((inrᵉ (inrᵉ xᵉ)) +ℤᵉ yᵉ)
      ＝ᵉ succ-ℤᵉ (yᵉ +ℤᵉ (inrᵉ (inrᵉ xᵉ)))
        byᵉ apᵉ succ-ℤᵉ (commutative-add-ℤᵉ (inrᵉ (inrᵉ xᵉ)) yᵉ)
      ＝ᵉ yᵉ +ℤᵉ (succ-ℤᵉ (inrᵉ (inrᵉ xᵉ)))
        byᵉ invᵉ (right-successor-law-add-ℤᵉ yᵉ (inrᵉ (inrᵉ xᵉ)))
```

### The inverse laws for addition and negatives

```agda
abstract
  left-inverse-law-add-ℤᵉ :
    (xᵉ : ℤᵉ) → neg-ℤᵉ xᵉ +ℤᵉ xᵉ ＝ᵉ zero-ℤᵉ
  left-inverse-law-add-ℤᵉ (inlᵉ zero-ℕᵉ) = reflᵉ
  left-inverse-law-add-ℤᵉ (inlᵉ (succ-ℕᵉ xᵉ)) =
    equational-reasoningᵉ
      succ-ℤᵉ (inrᵉ (inrᵉ xᵉ) +ℤᵉ pred-ℤᵉ (inlᵉ xᵉ))
      ＝ᵉ succ-ℤᵉ (pred-ℤᵉ (inrᵉ (inrᵉ xᵉ) +ℤᵉ inlᵉ xᵉ))
        byᵉ apᵉ succ-ℤᵉ (right-predecessor-law-add-ℤᵉ (inrᵉ (inrᵉ xᵉ)) (inlᵉ xᵉ))
      ＝ᵉ inrᵉ (inrᵉ xᵉ) +ℤᵉ inlᵉ xᵉ
        byᵉ is-section-pred-ℤᵉ ((inrᵉ (inrᵉ xᵉ)) +ℤᵉ (inlᵉ xᵉ))
      ＝ᵉ zero-ℤᵉ
        byᵉ left-inverse-law-add-ℤᵉ (inlᵉ xᵉ)
  left-inverse-law-add-ℤᵉ (inrᵉ (inlᵉ starᵉ)) = reflᵉ
  left-inverse-law-add-ℤᵉ (inrᵉ (inrᵉ xᵉ)) =
    equational-reasoningᵉ
      neg-ℤᵉ (inrᵉ (inrᵉ xᵉ)) +ℤᵉ inrᵉ (inrᵉ xᵉ)
      ＝ᵉ inrᵉ (inrᵉ xᵉ) +ℤᵉ inlᵉ xᵉ
        byᵉ commutative-add-ℤᵉ (inlᵉ xᵉ) (inrᵉ (inrᵉ xᵉ))
      ＝ᵉ zero-ℤᵉ
        byᵉ left-inverse-law-add-ℤᵉ (inlᵉ xᵉ)

  right-inverse-law-add-ℤᵉ :
    (xᵉ : ℤᵉ) → xᵉ +ℤᵉ neg-ℤᵉ xᵉ ＝ᵉ zero-ℤᵉ
  right-inverse-law-add-ℤᵉ xᵉ =
    equational-reasoningᵉ
      xᵉ +ℤᵉ neg-ℤᵉ xᵉ
      ＝ᵉ neg-ℤᵉ xᵉ +ℤᵉ xᵉ
        byᵉ commutative-add-ℤᵉ xᵉ (neg-ℤᵉ xᵉ)
      ＝ᵉ zero-ℤᵉ
        byᵉ left-inverse-law-add-ℤᵉ xᵉ
```

### Interchange law for addition with respect to addition

```agda
abstract
  interchange-law-add-add-ℤᵉ :
    (xᵉ yᵉ uᵉ vᵉ : ℤᵉ) → (xᵉ +ℤᵉ yᵉ) +ℤᵉ (uᵉ +ℤᵉ vᵉ) ＝ᵉ (xᵉ +ℤᵉ uᵉ) +ℤᵉ (yᵉ +ℤᵉ vᵉ)
  interchange-law-add-add-ℤᵉ =
    interchange-law-commutative-and-associativeᵉ
      add-ℤᵉ
      commutative-add-ℤᵉ
      associative-add-ℤᵉ
```

### Addition by `x` is a binary equivalence

```agda
abstract
  is-section-left-add-neg-ℤᵉ :
    (xᵉ yᵉ : ℤᵉ) → xᵉ +ℤᵉ (neg-ℤᵉ xᵉ +ℤᵉ yᵉ) ＝ᵉ yᵉ
  is-section-left-add-neg-ℤᵉ xᵉ yᵉ =
    equational-reasoningᵉ
      xᵉ +ℤᵉ (neg-ℤᵉ xᵉ +ℤᵉ yᵉ)
      ＝ᵉ (xᵉ +ℤᵉ neg-ℤᵉ xᵉ) +ℤᵉ yᵉ
        byᵉ invᵉ (associative-add-ℤᵉ xᵉ (neg-ℤᵉ xᵉ) yᵉ)
      ＝ᵉ yᵉ
        byᵉ apᵉ (_+ℤᵉ yᵉ) (right-inverse-law-add-ℤᵉ xᵉ)

  is-retraction-left-add-neg-ℤᵉ :
    (xᵉ yᵉ : ℤᵉ) → (neg-ℤᵉ xᵉ) +ℤᵉ (xᵉ +ℤᵉ yᵉ) ＝ᵉ yᵉ
  is-retraction-left-add-neg-ℤᵉ xᵉ yᵉ =
    equational-reasoningᵉ
      neg-ℤᵉ xᵉ +ℤᵉ (xᵉ +ℤᵉ yᵉ)
      ＝ᵉ (neg-ℤᵉ xᵉ +ℤᵉ xᵉ) +ℤᵉ yᵉ
        byᵉ invᵉ (associative-add-ℤᵉ (neg-ℤᵉ xᵉ) xᵉ yᵉ)
      ＝ᵉ yᵉ
        byᵉ apᵉ (_+ℤᵉ yᵉ) (left-inverse-law-add-ℤᵉ xᵉ)

abstract
  is-equiv-left-add-ℤᵉ : (xᵉ : ℤᵉ) → is-equivᵉ (xᵉ +ℤᵉ_)
  pr1ᵉ (pr1ᵉ (is-equiv-left-add-ℤᵉ xᵉ)) = add-ℤᵉ (neg-ℤᵉ xᵉ)
  pr2ᵉ (pr1ᵉ (is-equiv-left-add-ℤᵉ xᵉ)) = is-section-left-add-neg-ℤᵉ xᵉ
  pr1ᵉ (pr2ᵉ (is-equiv-left-add-ℤᵉ xᵉ)) = add-ℤᵉ (neg-ℤᵉ xᵉ)
  pr2ᵉ (pr2ᵉ (is-equiv-left-add-ℤᵉ xᵉ)) = is-retraction-left-add-neg-ℤᵉ xᵉ

equiv-left-add-ℤᵉ : ℤᵉ → (ℤᵉ ≃ᵉ ℤᵉ)
pr1ᵉ (equiv-left-add-ℤᵉ xᵉ) = add-ℤᵉ xᵉ
pr2ᵉ (equiv-left-add-ℤᵉ xᵉ) = is-equiv-left-add-ℤᵉ xᵉ

abstract
  is-section-right-add-neg-ℤᵉ :
    (xᵉ yᵉ : ℤᵉ) → (yᵉ +ℤᵉ neg-ℤᵉ xᵉ) +ℤᵉ xᵉ ＝ᵉ yᵉ
  is-section-right-add-neg-ℤᵉ xᵉ yᵉ =
    equational-reasoningᵉ
      (yᵉ +ℤᵉ neg-ℤᵉ xᵉ) +ℤᵉ xᵉ
      ＝ᵉ yᵉ +ℤᵉ (neg-ℤᵉ xᵉ +ℤᵉ xᵉ)
        byᵉ associative-add-ℤᵉ yᵉ (neg-ℤᵉ xᵉ) xᵉ
      ＝ᵉ yᵉ +ℤᵉ zero-ℤᵉ
        byᵉ apᵉ (yᵉ +ℤᵉ_) (left-inverse-law-add-ℤᵉ xᵉ)
      ＝ᵉ yᵉ
        byᵉ right-unit-law-add-ℤᵉ yᵉ

  is-retraction-right-add-neg-ℤᵉ :
    (xᵉ yᵉ : ℤᵉ) → (yᵉ +ℤᵉ xᵉ) +ℤᵉ neg-ℤᵉ xᵉ ＝ᵉ yᵉ
  is-retraction-right-add-neg-ℤᵉ xᵉ yᵉ =
    equational-reasoningᵉ
      (yᵉ +ℤᵉ xᵉ) +ℤᵉ neg-ℤᵉ xᵉ
      ＝ᵉ yᵉ +ℤᵉ (xᵉ +ℤᵉ neg-ℤᵉ xᵉ)
        byᵉ associative-add-ℤᵉ yᵉ xᵉ (neg-ℤᵉ xᵉ)
      ＝ᵉ yᵉ +ℤᵉ zero-ℤᵉ
        byᵉ apᵉ (yᵉ +ℤᵉ_) (right-inverse-law-add-ℤᵉ xᵉ)
      ＝ᵉ yᵉ
        byᵉ right-unit-law-add-ℤᵉ yᵉ

abstract
  is-equiv-right-add-ℤᵉ : (yᵉ : ℤᵉ) → is-equivᵉ (_+ℤᵉ yᵉ)
  pr1ᵉ (pr1ᵉ (is-equiv-right-add-ℤᵉ yᵉ)) = _+ℤᵉ (neg-ℤᵉ yᵉ)
  pr2ᵉ (pr1ᵉ (is-equiv-right-add-ℤᵉ yᵉ)) = is-section-right-add-neg-ℤᵉ yᵉ
  pr1ᵉ (pr2ᵉ (is-equiv-right-add-ℤᵉ yᵉ)) = _+ℤᵉ (neg-ℤᵉ yᵉ)
  pr2ᵉ (pr2ᵉ (is-equiv-right-add-ℤᵉ yᵉ)) = is-retraction-right-add-neg-ℤᵉ yᵉ

equiv-right-add-ℤᵉ : ℤᵉ → (ℤᵉ ≃ᵉ ℤᵉ)
pr1ᵉ (equiv-right-add-ℤᵉ yᵉ) = _+ℤᵉ yᵉ
pr2ᵉ (equiv-right-add-ℤᵉ yᵉ) = is-equiv-right-add-ℤᵉ yᵉ

is-binary-equiv-left-add-ℤᵉ : is-binary-equivᵉ add-ℤᵉ
pr1ᵉ is-binary-equiv-left-add-ℤᵉ = is-equiv-right-add-ℤᵉ
pr2ᵉ is-binary-equiv-left-add-ℤᵉ = is-equiv-left-add-ℤᵉ
```

### Addition by an integer is a binary embedding

```agda
abstract
  is-emb-left-add-ℤᵉ :
    (xᵉ : ℤᵉ) → is-embᵉ (xᵉ +ℤᵉ_)
  is-emb-left-add-ℤᵉ xᵉ =
    is-emb-is-equivᵉ (is-equiv-left-add-ℤᵉ xᵉ)

  is-emb-right-add-ℤᵉ :
    (yᵉ : ℤᵉ) → is-embᵉ (_+ℤᵉ yᵉ)
  is-emb-right-add-ℤᵉ yᵉ = is-emb-is-equivᵉ (is-equiv-right-add-ℤᵉ yᵉ)

  is-binary-emb-add-ℤᵉ : is-binary-embᵉ add-ℤᵉ
  is-binary-emb-add-ℤᵉ =
    is-binary-emb-is-binary-equivᵉ is-binary-equiv-left-add-ℤᵉ
```

### Addition by `x` is injective

```agda
abstract
  is-injective-right-add-ℤᵉ : (xᵉ : ℤᵉ) → is-injectiveᵉ (_+ℤᵉ xᵉ)
  is-injective-right-add-ℤᵉ xᵉ = is-injective-is-embᵉ (is-emb-right-add-ℤᵉ xᵉ)

  is-injective-left-add-ℤᵉ : (xᵉ : ℤᵉ) → is-injectiveᵉ (xᵉ +ℤᵉ_)
  is-injective-left-add-ℤᵉ xᵉ = is-injective-is-embᵉ (is-emb-left-add-ℤᵉ xᵉ)
```

### Negative laws for addition

```agda
abstract
  right-negative-law-add-ℤᵉ :
    (kᵉ lᵉ : ℤᵉ) → kᵉ +ℤᵉ neg-ℤᵉ lᵉ ＝ᵉ neg-ℤᵉ (neg-ℤᵉ kᵉ +ℤᵉ lᵉ)
  right-negative-law-add-ℤᵉ (inlᵉ zero-ℕᵉ) lᵉ =
    equational-reasoningᵉ
      neg-one-ℤᵉ +ℤᵉ neg-ℤᵉ lᵉ
      ＝ᵉ pred-ℤᵉ (zero-ℤᵉ +ℤᵉ neg-ℤᵉ lᵉ)
        byᵉ left-predecessor-law-add-ℤᵉ zero-ℤᵉ (neg-ℤᵉ lᵉ)
      ＝ᵉ neg-ℤᵉ (succ-ℤᵉ lᵉ)
        byᵉ pred-neg-ℤᵉ lᵉ
  right-negative-law-add-ℤᵉ (inlᵉ (succ-ℕᵉ xᵉ)) lᵉ =
    equational-reasoningᵉ
      pred-ℤᵉ (inlᵉ xᵉ) +ℤᵉ neg-ℤᵉ lᵉ
      ＝ᵉ pred-ℤᵉ (inlᵉ xᵉ +ℤᵉ neg-ℤᵉ lᵉ)
        byᵉ left-predecessor-law-add-ℤᵉ (inlᵉ xᵉ) (neg-ℤᵉ lᵉ)
      ＝ᵉ pred-ℤᵉ (neg-ℤᵉ (neg-ℤᵉ (inlᵉ xᵉ) +ℤᵉ lᵉ))
        byᵉ apᵉ pred-ℤᵉ (right-negative-law-add-ℤᵉ (inlᵉ xᵉ) lᵉ)
      ＝ᵉ neg-ℤᵉ (succ-ℤᵉ (inrᵉ (inrᵉ xᵉ) +ℤᵉ lᵉ))
        byᵉ pred-neg-ℤᵉ (inrᵉ (inrᵉ xᵉ) +ℤᵉ lᵉ)
  right-negative-law-add-ℤᵉ (inrᵉ (inlᵉ starᵉ)) lᵉ =
    reflᵉ
  right-negative-law-add-ℤᵉ (inrᵉ (inrᵉ zero-ℕᵉ)) lᵉ =
    invᵉ (neg-pred-ℤᵉ lᵉ)
  right-negative-law-add-ℤᵉ (inrᵉ (inrᵉ (succ-ℕᵉ nᵉ))) lᵉ =
    equational-reasoningᵉ
      succ-ℤᵉ (in-pos-ℤᵉ nᵉ) +ℤᵉ neg-ℤᵉ lᵉ
      ＝ᵉ succ-ℤᵉ (in-pos-ℤᵉ nᵉ +ℤᵉ neg-ℤᵉ lᵉ)
        byᵉ left-successor-law-add-ℤᵉ (in-pos-ℤᵉ nᵉ) (neg-ℤᵉ lᵉ)
      ＝ᵉ succ-ℤᵉ (neg-ℤᵉ (neg-ℤᵉ (inrᵉ (inrᵉ nᵉ)) +ℤᵉ lᵉ))
        byᵉ apᵉ succ-ℤᵉ (right-negative-law-add-ℤᵉ (inrᵉ (inrᵉ nᵉ)) lᵉ)
      ＝ᵉ neg-ℤᵉ (pred-ℤᵉ ((inlᵉ nᵉ) +ℤᵉ lᵉ))
        byᵉ invᵉ (neg-pred-ℤᵉ ((inlᵉ nᵉ) +ℤᵉ lᵉ))
```

### Distributivity of negatives over addition

```agda
abstract
  distributive-neg-add-ℤᵉ :
    (kᵉ lᵉ : ℤᵉ) → neg-ℤᵉ (kᵉ +ℤᵉ lᵉ) ＝ᵉ neg-ℤᵉ kᵉ +ℤᵉ neg-ℤᵉ lᵉ
  distributive-neg-add-ℤᵉ (inlᵉ zero-ℕᵉ) lᵉ =
    equational-reasoningᵉ
      neg-ℤᵉ (inlᵉ zero-ℕᵉ +ℤᵉ lᵉ)
      ＝ᵉ neg-ℤᵉ (pred-ℤᵉ (zero-ℤᵉ +ℤᵉ lᵉ))
        byᵉ apᵉ neg-ℤᵉ (left-predecessor-law-add-ℤᵉ zero-ℤᵉ lᵉ)
      ＝ᵉ neg-ℤᵉ (inlᵉ zero-ℕᵉ) +ℤᵉ neg-ℤᵉ lᵉ
        byᵉ neg-pred-ℤᵉ lᵉ
  distributive-neg-add-ℤᵉ (inlᵉ (succ-ℕᵉ nᵉ)) lᵉ =
    equational-reasoningᵉ
      neg-ℤᵉ (pred-ℤᵉ (inlᵉ nᵉ +ℤᵉ lᵉ))
      ＝ᵉ succ-ℤᵉ (neg-ℤᵉ (inlᵉ nᵉ +ℤᵉ lᵉ))
        byᵉ neg-pred-ℤᵉ (inlᵉ nᵉ +ℤᵉ lᵉ)
      ＝ᵉ succ-ℤᵉ (neg-ℤᵉ (inlᵉ nᵉ) +ℤᵉ neg-ℤᵉ lᵉ)
        byᵉ apᵉ succ-ℤᵉ (distributive-neg-add-ℤᵉ (inlᵉ nᵉ) lᵉ)
      ＝ᵉ neg-ℤᵉ (pred-ℤᵉ (inlᵉ nᵉ)) +ℤᵉ neg-ℤᵉ lᵉ
        byᵉ apᵉ (_+ℤᵉ (neg-ℤᵉ lᵉ)) (invᵉ (neg-pred-ℤᵉ (inlᵉ nᵉ)))
  distributive-neg-add-ℤᵉ (inrᵉ (inlᵉ starᵉ)) lᵉ =
    reflᵉ
  distributive-neg-add-ℤᵉ (inrᵉ (inrᵉ zero-ℕᵉ)) lᵉ =
    invᵉ (pred-neg-ℤᵉ lᵉ)
  distributive-neg-add-ℤᵉ (inrᵉ (inrᵉ (succ-ℕᵉ nᵉ))) lᵉ =
    equational-reasoningᵉ
      neg-ℤᵉ (succ-ℤᵉ (in-pos-ℤᵉ nᵉ +ℤᵉ lᵉ))
      ＝ᵉ pred-ℤᵉ (neg-ℤᵉ (in-pos-ℤᵉ nᵉ +ℤᵉ lᵉ))
        byᵉ invᵉ (pred-neg-ℤᵉ (in-pos-ℤᵉ nᵉ +ℤᵉ lᵉ))
      ＝ᵉ pred-ℤᵉ (neg-ℤᵉ (inrᵉ (inrᵉ nᵉ)) +ℤᵉ neg-ℤᵉ lᵉ)
        byᵉ apᵉ pred-ℤᵉ (distributive-neg-add-ℤᵉ (inrᵉ (inrᵉ nᵉ)) lᵉ)
```

### The inclusion of ℕ into ℤ preserves addition

```agda
abstract
  add-int-ℕᵉ : (xᵉ yᵉ : ℕᵉ) → (int-ℕᵉ xᵉ) +ℤᵉ (int-ℕᵉ yᵉ) ＝ᵉ int-ℕᵉ (xᵉ +ℕᵉ yᵉ)
  add-int-ℕᵉ xᵉ zero-ℕᵉ = right-unit-law-add-ℤᵉ (int-ℕᵉ xᵉ)
  add-int-ℕᵉ xᵉ (succ-ℕᵉ yᵉ) =
    equational-reasoningᵉ
      int-ℕᵉ xᵉ +ℤᵉ int-ℕᵉ (succ-ℕᵉ yᵉ)
      ＝ᵉ int-ℕᵉ xᵉ +ℤᵉ succ-ℤᵉ (int-ℕᵉ yᵉ)
        byᵉ apᵉ ((int-ℕᵉ xᵉ) +ℤᵉ_) (invᵉ (succ-int-ℕᵉ yᵉ))
      ＝ᵉ succ-ℤᵉ (int-ℕᵉ xᵉ +ℤᵉ int-ℕᵉ yᵉ)
        byᵉ right-successor-law-add-ℤᵉ (int-ℕᵉ xᵉ) (int-ℕᵉ yᵉ)
      ＝ᵉ succ-ℤᵉ (int-ℕᵉ (xᵉ +ℕᵉ yᵉ))
        byᵉ apᵉ succ-ℤᵉ (add-int-ℕᵉ xᵉ yᵉ)
      ＝ᵉ int-ℕᵉ (succ-ℕᵉ (xᵉ +ℕᵉ yᵉ))
        byᵉ succ-int-ℕᵉ (xᵉ +ℕᵉ yᵉ)
```

### If `x + y = y` then `x = 0`

```agda
abstract
  is-zero-left-add-ℤᵉ :
    (xᵉ yᵉ : ℤᵉ) → xᵉ +ℤᵉ yᵉ ＝ᵉ yᵉ → is-zero-ℤᵉ xᵉ
  is-zero-left-add-ℤᵉ xᵉ yᵉ Hᵉ =
    equational-reasoningᵉ
      xᵉ
      ＝ᵉ xᵉ +ℤᵉ zero-ℤᵉ
        byᵉ invᵉ (right-unit-law-add-ℤᵉ xᵉ)
      ＝ᵉ xᵉ +ℤᵉ (yᵉ +ℤᵉ neg-ℤᵉ yᵉ)
        byᵉ invᵉ (apᵉ (xᵉ +ℤᵉ_) (right-inverse-law-add-ℤᵉ yᵉ))
      ＝ᵉ (xᵉ +ℤᵉ yᵉ) +ℤᵉ neg-ℤᵉ yᵉ
        byᵉ invᵉ (associative-add-ℤᵉ xᵉ yᵉ (neg-ℤᵉ yᵉ))
      ＝ᵉ yᵉ +ℤᵉ neg-ℤᵉ yᵉ
        byᵉ apᵉ (_+ℤᵉ (neg-ℤᵉ yᵉ)) Hᵉ
      ＝ᵉ zero-ℤᵉ
        byᵉ right-inverse-law-add-ℤᵉ yᵉ
```

### If `x + y = x` then `y = 0`

```agda
abstract
  is-zero-right-add-ℤᵉ :
    (xᵉ yᵉ : ℤᵉ) → xᵉ +ℤᵉ yᵉ ＝ᵉ xᵉ → is-zero-ℤᵉ yᵉ
  is-zero-right-add-ℤᵉ xᵉ yᵉ Hᵉ =
    is-zero-left-add-ℤᵉ yᵉ xᵉ (commutative-add-ℤᵉ yᵉ xᵉ ∙ᵉ Hᵉ)
```

## See also

-ᵉ Propertiesᵉ ofᵉ additionᵉ with respectᵉ to positivity,ᵉ nonnegativity,ᵉ negativityᵉ
  andᵉ nonnpositivityᵉ areᵉ derivedᵉ in
  [`addition-positive-and-negative-integers`](elementary-number-theory.addition-positive-and-negative-integers.mdᵉ)
-ᵉ Propertiesᵉ ofᵉ additionᵉ with respectᵉ to theᵉ standardᵉ orderingᵉ onᵉ theᵉ integersᵉ
  areᵉ derivedᵉ in
  [`inequality-integers`](elementary-number-theory.inequality-integers.mdᵉ)
-ᵉ Propertiesᵉ ofᵉ additionᵉ with respectᵉ to theᵉ standardᵉ strictᵉ orderingᵉ onᵉ theᵉ
  integersᵉ areᵉ derivedᵉ in
  [`strict-inequality-integers`](elementary-number-theory.strict-inequality-integers.mdᵉ)