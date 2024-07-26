# Multiplication of integers

```agda
module elementary-number-theory.multiplication-integersᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integersᵉ
open import elementary-number-theory.addition-natural-numbersᵉ
open import elementary-number-theory.addition-positive-and-negative-integersᵉ
open import elementary-number-theory.difference-integersᵉ
open import elementary-number-theory.equality-integersᵉ
open import elementary-number-theory.inequality-integersᵉ
open import elementary-number-theory.integersᵉ
open import elementary-number-theory.multiplication-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ
open import elementary-number-theory.nonnegative-integersᵉ
open import elementary-number-theory.nonzero-integersᵉ
open import elementary-number-theory.positive-integersᵉ

open import foundation.action-on-identifications-binary-functionsᵉ
open import foundation.action-on-identifications-functionsᵉ
open import foundation.coproduct-typesᵉ
open import foundation.embeddingsᵉ
open import foundation.empty-typesᵉ
open import foundation.function-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.injective-mapsᵉ
open import foundation.interchange-lawᵉ
open import foundation.setsᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.type-arithmetic-empty-typeᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Weᵉ introduceᵉ theᵉ
{{#conceptᵉ "multiplication"ᵉ Disambiguation="integers"ᵉ Agda=mul-ℤᵉ}} ofᵉ integersᵉ
andᵉ deriveᵉ itsᵉ basicᵉ propertiesᵉ with respectᵉ to `succ-ℤ`,ᵉ `pred-ℤ`,ᵉ `neg-ℤ`ᵉ andᵉ
`add-ℤ`.ᵉ

## Definitions

### The standard definition of multiplication on ℤ

```agda
mul-ℤᵉ : ℤᵉ → ℤᵉ → ℤᵉ
mul-ℤᵉ (inlᵉ zero-ℕᵉ) lᵉ = neg-ℤᵉ lᵉ
mul-ℤᵉ (inlᵉ (succ-ℕᵉ xᵉ)) lᵉ = (neg-ℤᵉ lᵉ) +ℤᵉ (mul-ℤᵉ (inlᵉ xᵉ) lᵉ)
mul-ℤᵉ (inrᵉ (inlᵉ starᵉ)) lᵉ = zero-ℤᵉ
mul-ℤᵉ (inrᵉ (inrᵉ zero-ℕᵉ)) lᵉ = lᵉ
mul-ℤᵉ (inrᵉ (inrᵉ (succ-ℕᵉ xᵉ))) lᵉ = lᵉ +ℤᵉ (mul-ℤᵉ (inrᵉ (inrᵉ xᵉ)) lᵉ)

infixl 40 _*ℤᵉ_
_*ℤᵉ_ = mul-ℤᵉ

mul-ℤ'ᵉ : ℤᵉ → ℤᵉ → ℤᵉ
mul-ℤ'ᵉ xᵉ yᵉ = mul-ℤᵉ yᵉ xᵉ

ap-mul-ℤᵉ :
  {xᵉ yᵉ x'ᵉ y'ᵉ : ℤᵉ} → xᵉ ＝ᵉ x'ᵉ → yᵉ ＝ᵉ y'ᵉ → xᵉ *ℤᵉ yᵉ ＝ᵉ x'ᵉ *ℤᵉ y'ᵉ
ap-mul-ℤᵉ pᵉ qᵉ = ap-binaryᵉ mul-ℤᵉ pᵉ qᵉ
```

### A definition of multiplication that connects with multiplication on ℕ

```agda
explicit-mul-ℤᵉ : ℤᵉ → ℤᵉ → ℤᵉ
explicit-mul-ℤᵉ (inlᵉ xᵉ) (inlᵉ yᵉ) = int-ℕᵉ ((succ-ℕᵉ xᵉ) *ℕᵉ (succ-ℕᵉ yᵉ))
explicit-mul-ℤᵉ (inlᵉ xᵉ) (inrᵉ (inlᵉ starᵉ)) = zero-ℤᵉ
explicit-mul-ℤᵉ (inlᵉ xᵉ) (inrᵉ (inrᵉ yᵉ)) = neg-ℤᵉ (int-ℕᵉ ((succ-ℕᵉ xᵉ) *ℕᵉ (succ-ℕᵉ yᵉ)))
explicit-mul-ℤᵉ (inrᵉ (inlᵉ starᵉ)) (inlᵉ yᵉ) = zero-ℤᵉ
explicit-mul-ℤᵉ (inrᵉ (inrᵉ xᵉ)) (inlᵉ yᵉ) = neg-ℤᵉ (int-ℕᵉ ((succ-ℕᵉ xᵉ) *ℕᵉ (succ-ℕᵉ yᵉ)))
explicit-mul-ℤᵉ (inrᵉ (inlᵉ starᵉ)) (inrᵉ (inlᵉ starᵉ)) = zero-ℤᵉ
explicit-mul-ℤᵉ (inrᵉ (inlᵉ starᵉ)) (inrᵉ (inrᵉ yᵉ)) = zero-ℤᵉ
explicit-mul-ℤᵉ (inrᵉ (inrᵉ xᵉ)) (inrᵉ (inlᵉ starᵉ)) = zero-ℤᵉ
explicit-mul-ℤᵉ (inrᵉ (inrᵉ xᵉ)) (inrᵉ (inrᵉ yᵉ)) = int-ℕᵉ ((succ-ℕᵉ xᵉ) *ℕᵉ (succ-ℕᵉ yᵉ))

explicit-mul-ℤ'ᵉ : ℤᵉ → ℤᵉ → ℤᵉ
explicit-mul-ℤ'ᵉ xᵉ yᵉ = explicit-mul-ℤᵉ yᵉ xᵉ
```

### A definition of being equal up to sign

```agda
is-plus-or-minus-ℤᵉ : ℤᵉ → ℤᵉ → UUᵉ lzero
is-plus-or-minus-ℤᵉ xᵉ yᵉ = (xᵉ ＝ᵉ yᵉ) +ᵉ (neg-one-ℤᵉ *ℤᵉ xᵉ ＝ᵉ yᵉ)
```

## Properties

### Multiplication by zero is zero

```agda
left-zero-law-mul-ℤᵉ : (kᵉ : ℤᵉ) → zero-ℤᵉ *ℤᵉ kᵉ ＝ᵉ zero-ℤᵉ
left-zero-law-mul-ℤᵉ kᵉ = reflᵉ

right-zero-law-mul-ℤᵉ : (kᵉ : ℤᵉ) → kᵉ *ℤᵉ zero-ℤᵉ ＝ᵉ zero-ℤᵉ
right-zero-law-mul-ℤᵉ (inlᵉ zero-ℕᵉ) = reflᵉ
right-zero-law-mul-ℤᵉ (inlᵉ (succ-ℕᵉ nᵉ)) =
  right-zero-law-mul-ℤᵉ (inlᵉ nᵉ)
right-zero-law-mul-ℤᵉ (inrᵉ (inlᵉ starᵉ)) = reflᵉ
right-zero-law-mul-ℤᵉ (inrᵉ (inrᵉ zero-ℕᵉ)) = reflᵉ
right-zero-law-mul-ℤᵉ (inrᵉ (inrᵉ (succ-ℕᵉ nᵉ))) =
  right-zero-law-mul-ℤᵉ (inrᵉ (inrᵉ nᵉ))
```

### Unit laws

```agda
left-unit-law-mul-ℤᵉ : (kᵉ : ℤᵉ) → one-ℤᵉ *ℤᵉ kᵉ ＝ᵉ kᵉ
left-unit-law-mul-ℤᵉ kᵉ = reflᵉ

right-unit-law-mul-ℤᵉ : (kᵉ : ℤᵉ) → kᵉ *ℤᵉ one-ℤᵉ ＝ᵉ kᵉ
right-unit-law-mul-ℤᵉ (inlᵉ zero-ℕᵉ) = reflᵉ
right-unit-law-mul-ℤᵉ (inlᵉ (succ-ℕᵉ nᵉ)) =
  apᵉ ((neg-one-ℤᵉ) +ℤᵉ_) (right-unit-law-mul-ℤᵉ (inlᵉ nᵉ))
right-unit-law-mul-ℤᵉ (inrᵉ (inlᵉ starᵉ)) = reflᵉ
right-unit-law-mul-ℤᵉ (inrᵉ (inrᵉ zero-ℕᵉ)) = reflᵉ
right-unit-law-mul-ℤᵉ (inrᵉ (inrᵉ (succ-ℕᵉ nᵉ))) =
  apᵉ (one-ℤᵉ +ℤᵉ_) (right-unit-law-mul-ℤᵉ (inrᵉ (inrᵉ nᵉ)))
```

### Multiplication of an integer by `-1` is equal to the negative

```agda
left-neg-unit-law-mul-ℤᵉ : (kᵉ : ℤᵉ) → neg-one-ℤᵉ *ℤᵉ kᵉ ＝ᵉ neg-ℤᵉ kᵉ
left-neg-unit-law-mul-ℤᵉ kᵉ = reflᵉ

right-neg-unit-law-mul-ℤᵉ : (kᵉ : ℤᵉ) → kᵉ *ℤᵉ neg-one-ℤᵉ ＝ᵉ neg-ℤᵉ kᵉ
right-neg-unit-law-mul-ℤᵉ (inlᵉ zero-ℕᵉ) = reflᵉ
right-neg-unit-law-mul-ℤᵉ (inlᵉ (succ-ℕᵉ nᵉ)) =
  apᵉ (one-ℤᵉ +ℤᵉ_) (right-neg-unit-law-mul-ℤᵉ (inlᵉ nᵉ))
right-neg-unit-law-mul-ℤᵉ (inrᵉ (inlᵉ starᵉ)) = reflᵉ
right-neg-unit-law-mul-ℤᵉ (inrᵉ (inrᵉ zero-ℕᵉ)) = reflᵉ
right-neg-unit-law-mul-ℤᵉ (inrᵉ (inrᵉ (succ-ℕᵉ nᵉ))) =
  apᵉ (neg-one-ℤᵉ +ℤᵉ_) (right-neg-unit-law-mul-ℤᵉ (inrᵉ (inrᵉ nᵉ)))
```

### Multiplication by the successor or the predecessor of an integer

```agda
left-successor-law-mul-ℤᵉ :
  (kᵉ lᵉ : ℤᵉ) → (succ-ℤᵉ kᵉ) *ℤᵉ lᵉ ＝ᵉ lᵉ +ℤᵉ (kᵉ *ℤᵉ lᵉ)
left-successor-law-mul-ℤᵉ (inlᵉ zero-ℕᵉ) lᵉ =
  invᵉ (right-inverse-law-add-ℤᵉ lᵉ)
left-successor-law-mul-ℤᵉ (inlᵉ (succ-ℕᵉ nᵉ)) lᵉ =
  ( ( invᵉ (left-unit-law-add-ℤᵉ ((inlᵉ nᵉ) *ℤᵉ lᵉ))) ∙ᵉ
    ( apᵉ
      ( _+ℤᵉ ((inlᵉ nᵉ) *ℤᵉ lᵉ))
      ( invᵉ (right-inverse-law-add-ℤᵉ lᵉ)))) ∙ᵉ
  ( associative-add-ℤᵉ lᵉ (neg-ℤᵉ lᵉ) ((inlᵉ nᵉ) *ℤᵉ lᵉ))
left-successor-law-mul-ℤᵉ (inrᵉ (inlᵉ starᵉ)) lᵉ =
  invᵉ (right-unit-law-add-ℤᵉ lᵉ)
left-successor-law-mul-ℤᵉ (inrᵉ (inrᵉ nᵉ)) lᵉ = reflᵉ

left-predecessor-law-mul-ℤᵉ :
  (kᵉ lᵉ : ℤᵉ) → (pred-ℤᵉ kᵉ) *ℤᵉ lᵉ ＝ᵉ (neg-ℤᵉ lᵉ) +ℤᵉ (kᵉ *ℤᵉ lᵉ)
left-predecessor-law-mul-ℤᵉ (inlᵉ nᵉ) lᵉ = reflᵉ
left-predecessor-law-mul-ℤᵉ (inrᵉ (inlᵉ starᵉ)) lᵉ =
  ( left-neg-unit-law-mul-ℤᵉ lᵉ) ∙ᵉ
  ( invᵉ (right-unit-law-add-ℤᵉ (neg-ℤᵉ lᵉ)))
left-predecessor-law-mul-ℤᵉ (inrᵉ (inrᵉ zero-ℕᵉ)) lᵉ =
  invᵉ (left-inverse-law-add-ℤᵉ lᵉ)
left-predecessor-law-mul-ℤᵉ (inrᵉ (inrᵉ (succ-ℕᵉ xᵉ))) lᵉ =
  ( apᵉ
    ( _+ℤᵉ ((in-pos-ℤᵉ xᵉ) *ℤᵉ lᵉ))
    ( invᵉ (left-inverse-law-add-ℤᵉ lᵉ))) ∙ᵉ
  ( associative-add-ℤᵉ (neg-ℤᵉ lᵉ) lᵉ ((in-pos-ℤᵉ xᵉ) *ℤᵉ lᵉ))

right-successor-law-mul-ℤᵉ :
  (kᵉ lᵉ : ℤᵉ) → kᵉ *ℤᵉ (succ-ℤᵉ lᵉ) ＝ᵉ kᵉ +ℤᵉ (kᵉ *ℤᵉ lᵉ)
right-successor-law-mul-ℤᵉ (inlᵉ zero-ℕᵉ) lᵉ = invᵉ (pred-neg-ℤᵉ lᵉ)
right-successor-law-mul-ℤᵉ (inlᵉ (succ-ℕᵉ nᵉ)) lᵉ =
  ( left-predecessor-law-mul-ℤᵉ (inlᵉ nᵉ) (succ-ℤᵉ lᵉ)) ∙ᵉ
  ( ( apᵉ ((neg-ℤᵉ (succ-ℤᵉ lᵉ)) +ℤᵉ_) (right-successor-law-mul-ℤᵉ (inlᵉ nᵉ) lᵉ)) ∙ᵉ
    ( ( invᵉ (associative-add-ℤᵉ (neg-ℤᵉ (succ-ℤᵉ lᵉ)) (inlᵉ nᵉ) ((inlᵉ nᵉ) *ℤᵉ lᵉ))) ∙ᵉ
      ( ( apᵉ
          ( _+ℤᵉ ((inlᵉ nᵉ) *ℤᵉ lᵉ))
          { xᵉ = (neg-ℤᵉ (succ-ℤᵉ lᵉ)) +ℤᵉ (inlᵉ nᵉ)}
          { yᵉ = (inlᵉ (succ-ℕᵉ nᵉ)) +ℤᵉ (neg-ℤᵉ lᵉ)}
          ( ( right-successor-law-add-ℤᵉ (neg-ℤᵉ (succ-ℤᵉ lᵉ)) (inlᵉ (succ-ℕᵉ nᵉ))) ∙ᵉ
            ( ( apᵉ succ-ℤᵉ
                ( commutative-add-ℤᵉ (neg-ℤᵉ (succ-ℤᵉ lᵉ)) (inlᵉ (succ-ℕᵉ nᵉ)))) ∙ᵉ
              ( ( invᵉ
                  ( right-successor-law-add-ℤᵉ
                    ( inlᵉ (succ-ℕᵉ nᵉ))
                    ( neg-ℤᵉ (succ-ℤᵉ lᵉ)))) ∙ᵉ
                ( apᵉ
                  ( (inlᵉ (succ-ℕᵉ nᵉ)) +ℤᵉ_)
                  ( ( apᵉ succ-ℤᵉ (invᵉ (pred-neg-ℤᵉ lᵉ))) ∙ᵉ
                    ( is-section-pred-ℤᵉ (neg-ℤᵉ lᵉ)))))))) ∙ᵉ
        ( associative-add-ℤᵉ (inlᵉ (succ-ℕᵉ nᵉ)) (neg-ℤᵉ lᵉ) ((inlᵉ nᵉ) *ℤᵉ lᵉ)))))
right-successor-law-mul-ℤᵉ (inrᵉ (inlᵉ starᵉ)) lᵉ = reflᵉ
right-successor-law-mul-ℤᵉ (inrᵉ (inrᵉ zero-ℕᵉ)) lᵉ = reflᵉ
right-successor-law-mul-ℤᵉ (inrᵉ (inrᵉ (succ-ℕᵉ nᵉ))) lᵉ =
  ( left-successor-law-mul-ℤᵉ (in-pos-ℤᵉ nᵉ) (succ-ℤᵉ lᵉ)) ∙ᵉ
  ( ( apᵉ ((succ-ℤᵉ lᵉ) +ℤᵉ_) (right-successor-law-mul-ℤᵉ (inrᵉ (inrᵉ nᵉ)) lᵉ)) ∙ᵉ
    ( ( invᵉ (associative-add-ℤᵉ (succ-ℤᵉ lᵉ) (in-pos-ℤᵉ nᵉ) ((in-pos-ℤᵉ nᵉ) *ℤᵉ lᵉ))) ∙ᵉ
      ( ( apᵉ
          ( _+ℤᵉ ((in-pos-ℤᵉ nᵉ) *ℤᵉ lᵉ))
          { xᵉ = (succ-ℤᵉ lᵉ) +ℤᵉ (in-pos-ℤᵉ nᵉ)}
          { yᵉ = (in-pos-ℤᵉ (succ-ℕᵉ nᵉ)) +ℤᵉ lᵉ}
          ( ( left-successor-law-add-ℤᵉ lᵉ (in-pos-ℤᵉ nᵉ)) ∙ᵉ
            ( ( apᵉ succ-ℤᵉ (commutative-add-ℤᵉ lᵉ (in-pos-ℤᵉ nᵉ))) ∙ᵉ
              ( invᵉ (left-successor-law-add-ℤᵉ (in-pos-ℤᵉ nᵉ) lᵉ))))) ∙ᵉ
        ( associative-add-ℤᵉ (inrᵉ (inrᵉ (succ-ℕᵉ nᵉ))) lᵉ ((inrᵉ (inrᵉ nᵉ)) *ℤᵉ lᵉ)))))

right-predecessor-law-mul-ℤᵉ :
  (kᵉ lᵉ : ℤᵉ) → kᵉ *ℤᵉ (pred-ℤᵉ lᵉ) ＝ᵉ (neg-ℤᵉ kᵉ) +ℤᵉ (kᵉ *ℤᵉ lᵉ)
right-predecessor-law-mul-ℤᵉ (inlᵉ zero-ℕᵉ) lᵉ =
  ( left-neg-unit-law-mul-ℤᵉ (pred-ℤᵉ lᵉ)) ∙ᵉ
  ( neg-pred-ℤᵉ lᵉ)
right-predecessor-law-mul-ℤᵉ (inlᵉ (succ-ℕᵉ nᵉ)) lᵉ =
  ( left-predecessor-law-mul-ℤᵉ (inlᵉ nᵉ) (pred-ℤᵉ lᵉ)) ∙ᵉ
  ( ( apᵉ ((neg-ℤᵉ (pred-ℤᵉ lᵉ)) +ℤᵉ_) (right-predecessor-law-mul-ℤᵉ (inlᵉ nᵉ) lᵉ)) ∙ᵉ
    ( ( invᵉ
        ( associative-add-ℤᵉ (neg-ℤᵉ (pred-ℤᵉ lᵉ)) (in-pos-ℤᵉ nᵉ) ((inlᵉ nᵉ) *ℤᵉ lᵉ))) ∙ᵉ
      ( ( apᵉ
          ( _+ℤᵉ ((inlᵉ nᵉ) *ℤᵉ lᵉ))
          { xᵉ = (neg-ℤᵉ (pred-ℤᵉ lᵉ)) +ℤᵉ (inrᵉ (inrᵉ nᵉ))}
          { yᵉ = (neg-ℤᵉ (inlᵉ (succ-ℕᵉ nᵉ))) +ℤᵉ (neg-ℤᵉ lᵉ)}
          ( ( apᵉ (_+ℤᵉ (in-pos-ℤᵉ nᵉ)) (neg-pred-ℤᵉ lᵉ)) ∙ᵉ
            ( ( left-successor-law-add-ℤᵉ (neg-ℤᵉ lᵉ) (in-pos-ℤᵉ nᵉ)) ∙ᵉ
              ( ( apᵉ succ-ℤᵉ (commutative-add-ℤᵉ (neg-ℤᵉ lᵉ) (in-pos-ℤᵉ nᵉ))) ∙ᵉ
                ( invᵉ (left-successor-law-add-ℤᵉ (in-pos-ℤᵉ nᵉ) (neg-ℤᵉ lᵉ))))))) ∙ᵉ
        ( associative-add-ℤᵉ (in-pos-ℤᵉ (succ-ℕᵉ nᵉ)) (neg-ℤᵉ lᵉ) ((inlᵉ nᵉ) *ℤᵉ lᵉ)))))
right-predecessor-law-mul-ℤᵉ (inrᵉ (inlᵉ starᵉ)) lᵉ = reflᵉ
right-predecessor-law-mul-ℤᵉ (inrᵉ (inrᵉ zero-ℕᵉ)) lᵉ = reflᵉ
right-predecessor-law-mul-ℤᵉ (inrᵉ (inrᵉ (succ-ℕᵉ nᵉ))) lᵉ =
  ( left-successor-law-mul-ℤᵉ (in-pos-ℤᵉ nᵉ) (pred-ℤᵉ lᵉ)) ∙ᵉ
  ( ( apᵉ ((pred-ℤᵉ lᵉ) +ℤᵉ_) (right-predecessor-law-mul-ℤᵉ (inrᵉ (inrᵉ nᵉ)) lᵉ)) ∙ᵉ
    ( ( invᵉ (associative-add-ℤᵉ (pred-ℤᵉ lᵉ) (inlᵉ nᵉ) ((inrᵉ (inrᵉ nᵉ)) *ℤᵉ lᵉ))) ∙ᵉ
      ( ( apᵉ
          ( _+ℤᵉ ((in-pos-ℤᵉ nᵉ) *ℤᵉ lᵉ))
          { xᵉ = (pred-ℤᵉ lᵉ) +ℤᵉ (inlᵉ nᵉ)}
          { yᵉ = (neg-ℤᵉ (in-pos-ℤᵉ (succ-ℕᵉ nᵉ))) +ℤᵉ lᵉ}
          ( ( left-predecessor-law-add-ℤᵉ lᵉ (inlᵉ nᵉ)) ∙ᵉ
            ( ( apᵉ pred-ℤᵉ (commutative-add-ℤᵉ lᵉ (inlᵉ nᵉ))) ∙ᵉ
              ( invᵉ (left-predecessor-law-add-ℤᵉ (inlᵉ nᵉ) lᵉ))))) ∙ᵉ
        ( associative-add-ℤᵉ (inlᵉ (succ-ℕᵉ nᵉ)) lᵉ ((inrᵉ (inrᵉ nᵉ)) *ℤᵉ lᵉ)))))
```

### Multiplication on the integers distributes on the right over addition

```agda
right-distributive-mul-add-ℤᵉ :
  (kᵉ lᵉ mᵉ : ℤᵉ) → (kᵉ +ℤᵉ lᵉ) *ℤᵉ mᵉ ＝ᵉ (kᵉ *ℤᵉ mᵉ) +ℤᵉ (lᵉ *ℤᵉ mᵉ)
right-distributive-mul-add-ℤᵉ (inlᵉ zero-ℕᵉ) lᵉ mᵉ =
  ( left-predecessor-law-mul-ℤᵉ lᵉ mᵉ) ∙ᵉ
  ( apᵉ
    ( _+ℤᵉ (lᵉ *ℤᵉ mᵉ))
    ( invᵉ
      ( ( left-predecessor-law-mul-ℤᵉ zero-ℤᵉ mᵉ) ∙ᵉ
        ( right-unit-law-add-ℤᵉ (neg-ℤᵉ mᵉ)))))
right-distributive-mul-add-ℤᵉ (inlᵉ (succ-ℕᵉ xᵉ)) lᵉ mᵉ =
  ( left-predecessor-law-mul-ℤᵉ ((inlᵉ xᵉ) +ℤᵉ lᵉ) mᵉ) ∙ᵉ
  ( ( apᵉ ((neg-ℤᵉ mᵉ) +ℤᵉ_) (right-distributive-mul-add-ℤᵉ (inlᵉ xᵉ) lᵉ mᵉ)) ∙ᵉ
    ( invᵉ (associative-add-ℤᵉ (neg-ℤᵉ mᵉ) ((inlᵉ xᵉ) *ℤᵉ mᵉ) (lᵉ *ℤᵉ mᵉ))))
right-distributive-mul-add-ℤᵉ (inrᵉ (inlᵉ starᵉ)) lᵉ mᵉ = reflᵉ
right-distributive-mul-add-ℤᵉ (inrᵉ (inrᵉ zero-ℕᵉ)) lᵉ mᵉ =
  left-successor-law-mul-ℤᵉ lᵉ mᵉ
right-distributive-mul-add-ℤᵉ (inrᵉ (inrᵉ (succ-ℕᵉ nᵉ))) lᵉ mᵉ =
  ( left-successor-law-mul-ℤᵉ ((in-pos-ℤᵉ nᵉ) +ℤᵉ lᵉ) mᵉ) ∙ᵉ
  ( ( apᵉ (mᵉ +ℤᵉ_) (right-distributive-mul-add-ℤᵉ (inrᵉ (inrᵉ nᵉ)) lᵉ mᵉ)) ∙ᵉ
    ( invᵉ (associative-add-ℤᵉ mᵉ ((in-pos-ℤᵉ nᵉ) *ℤᵉ mᵉ) (lᵉ *ℤᵉ mᵉ))))
```

### Left multiplication by the negative of an integer is the negative of the multiplication

```agda
left-negative-law-mul-ℤᵉ :
  (kᵉ lᵉ : ℤᵉ) → (neg-ℤᵉ kᵉ) *ℤᵉ lᵉ ＝ᵉ neg-ℤᵉ (kᵉ *ℤᵉ lᵉ)
left-negative-law-mul-ℤᵉ (inlᵉ zero-ℕᵉ) lᵉ =
  ( left-unit-law-mul-ℤᵉ lᵉ) ∙ᵉ
  ( invᵉ (neg-neg-ℤᵉ lᵉ))
left-negative-law-mul-ℤᵉ (inlᵉ (succ-ℕᵉ nᵉ)) lᵉ =
  ( apᵉ (_*ℤᵉ lᵉ) (neg-pred-ℤᵉ (inlᵉ nᵉ))) ∙ᵉ
  ( ( left-successor-law-mul-ℤᵉ (neg-ℤᵉ (inlᵉ nᵉ)) lᵉ) ∙ᵉ
    ( ( apᵉ (lᵉ +ℤᵉ_) (left-negative-law-mul-ℤᵉ (inlᵉ nᵉ) lᵉ)) ∙ᵉ
      ( right-negative-law-add-ℤᵉ lᵉ ((inlᵉ nᵉ) *ℤᵉ lᵉ))))
left-negative-law-mul-ℤᵉ (inrᵉ (inlᵉ starᵉ)) lᵉ = reflᵉ
left-negative-law-mul-ℤᵉ (inrᵉ (inrᵉ zero-ℕᵉ)) lᵉ = reflᵉ
left-negative-law-mul-ℤᵉ (inrᵉ (inrᵉ (succ-ℕᵉ nᵉ))) lᵉ =
  ( left-predecessor-law-mul-ℤᵉ (inlᵉ nᵉ) lᵉ) ∙ᵉ
  ( ( apᵉ ((neg-ℤᵉ lᵉ) +ℤᵉ_) (left-negative-law-mul-ℤᵉ (inrᵉ (inrᵉ nᵉ)) lᵉ)) ∙ᵉ
    ( invᵉ (distributive-neg-add-ℤᵉ lᵉ ((in-pos-ℤᵉ nᵉ) *ℤᵉ lᵉ))))
```

### Multiplication on the integers is associative

```agda
associative-mul-ℤᵉ :
  (kᵉ lᵉ mᵉ : ℤᵉ) → (kᵉ *ℤᵉ lᵉ) *ℤᵉ mᵉ ＝ᵉ kᵉ *ℤᵉ (lᵉ *ℤᵉ mᵉ)
associative-mul-ℤᵉ (inlᵉ zero-ℕᵉ) lᵉ mᵉ =
  left-negative-law-mul-ℤᵉ lᵉ mᵉ
associative-mul-ℤᵉ (inlᵉ (succ-ℕᵉ nᵉ)) lᵉ mᵉ =
  ( right-distributive-mul-add-ℤᵉ (neg-ℤᵉ lᵉ) ((inlᵉ nᵉ) *ℤᵉ lᵉ) mᵉ) ∙ᵉ
  ( ( apᵉ (((neg-ℤᵉ lᵉ) *ℤᵉ mᵉ) +ℤᵉ_) (associative-mul-ℤᵉ (inlᵉ nᵉ) lᵉ mᵉ)) ∙ᵉ
    ( apᵉ
      ( _+ℤᵉ ((inlᵉ nᵉ) *ℤᵉ (lᵉ *ℤᵉ mᵉ)))
      ( left-negative-law-mul-ℤᵉ lᵉ mᵉ)))
associative-mul-ℤᵉ (inrᵉ (inlᵉ starᵉ)) lᵉ mᵉ = reflᵉ
associative-mul-ℤᵉ (inrᵉ (inrᵉ zero-ℕᵉ)) lᵉ mᵉ = reflᵉ
associative-mul-ℤᵉ (inrᵉ (inrᵉ (succ-ℕᵉ nᵉ))) lᵉ mᵉ =
  ( right-distributive-mul-add-ℤᵉ lᵉ ((in-pos-ℤᵉ nᵉ) *ℤᵉ lᵉ) mᵉ) ∙ᵉ
  ( apᵉ ((lᵉ *ℤᵉ mᵉ) +ℤᵉ_) (associative-mul-ℤᵉ (inrᵉ (inrᵉ nᵉ)) lᵉ mᵉ))
```

### Multiplication on the integers is commutative

```agda
commutative-mul-ℤᵉ :
  (kᵉ lᵉ : ℤᵉ) → kᵉ *ℤᵉ lᵉ ＝ᵉ lᵉ *ℤᵉ kᵉ
commutative-mul-ℤᵉ (inlᵉ zero-ℕᵉ) lᵉ = invᵉ (right-neg-unit-law-mul-ℤᵉ lᵉ)
commutative-mul-ℤᵉ (inlᵉ (succ-ℕᵉ nᵉ)) lᵉ =
  ( apᵉ ((neg-ℤᵉ lᵉ) +ℤᵉ_) (commutative-mul-ℤᵉ (inlᵉ nᵉ) lᵉ)) ∙ᵉ
  ( invᵉ (right-predecessor-law-mul-ℤᵉ lᵉ (inlᵉ nᵉ)))
commutative-mul-ℤᵉ (inrᵉ (inlᵉ starᵉ)) lᵉ = invᵉ (right-zero-law-mul-ℤᵉ lᵉ)
commutative-mul-ℤᵉ (inrᵉ (inrᵉ zero-ℕᵉ)) lᵉ = invᵉ (right-unit-law-mul-ℤᵉ lᵉ)
commutative-mul-ℤᵉ (inrᵉ (inrᵉ (succ-ℕᵉ nᵉ))) lᵉ =
  ( apᵉ (lᵉ +ℤᵉ_) (commutative-mul-ℤᵉ (inrᵉ (inrᵉ nᵉ)) lᵉ)) ∙ᵉ
  ( invᵉ (right-successor-law-mul-ℤᵉ lᵉ (in-pos-ℤᵉ nᵉ)))
```

### Multiplication on the integers distributes on the left over addition

```agda
left-distributive-mul-add-ℤᵉ :
  (mᵉ kᵉ lᵉ : ℤᵉ) → mᵉ *ℤᵉ (kᵉ +ℤᵉ lᵉ) ＝ᵉ (mᵉ *ℤᵉ kᵉ) +ℤᵉ (mᵉ *ℤᵉ lᵉ)
left-distributive-mul-add-ℤᵉ mᵉ kᵉ lᵉ =
  commutative-mul-ℤᵉ mᵉ (kᵉ +ℤᵉ lᵉ) ∙ᵉ
    ( ( right-distributive-mul-add-ℤᵉ kᵉ lᵉ mᵉ) ∙ᵉ
      ( ap-add-ℤᵉ (commutative-mul-ℤᵉ kᵉ mᵉ) (commutative-mul-ℤᵉ lᵉ mᵉ)))
```

### Right multiplication by the negative of an integer is the negative of the multiplication

```agda
right-negative-law-mul-ℤᵉ :
  (kᵉ lᵉ : ℤᵉ) → kᵉ *ℤᵉ (neg-ℤᵉ lᵉ) ＝ᵉ neg-ℤᵉ (kᵉ *ℤᵉ lᵉ)
right-negative-law-mul-ℤᵉ kᵉ lᵉ =
  ( ( commutative-mul-ℤᵉ kᵉ (neg-ℤᵉ lᵉ)) ∙ᵉ
    ( left-negative-law-mul-ℤᵉ lᵉ kᵉ)) ∙ᵉ
  ( apᵉ neg-ℤᵉ (commutative-mul-ℤᵉ lᵉ kᵉ))
```

### The multiplication of the negatives of two integers is equal to their multiplication

```agda
double-negative-law-mul-ℤᵉ : (kᵉ lᵉ : ℤᵉ) → (neg-ℤᵉ kᵉ) *ℤᵉ (neg-ℤᵉ lᵉ) ＝ᵉ kᵉ *ℤᵉ lᵉ
double-negative-law-mul-ℤᵉ kᵉ lᵉ =
  equational-reasoningᵉ
    (neg-ℤᵉ kᵉ) *ℤᵉ (neg-ℤᵉ lᵉ)
    ＝ᵉ neg-ℤᵉ (kᵉ *ℤᵉ (neg-ℤᵉ lᵉ))
      byᵉ left-negative-law-mul-ℤᵉ kᵉ (neg-ℤᵉ lᵉ)
    ＝ᵉ neg-ℤᵉ (neg-ℤᵉ (kᵉ *ℤᵉ lᵉ))
      byᵉ apᵉ neg-ℤᵉ (right-negative-law-mul-ℤᵉ kᵉ lᵉ)
    ＝ᵉ kᵉ *ℤᵉ lᵉ
      byᵉ neg-neg-ℤᵉ (kᵉ *ℤᵉ lᵉ)
```

### Interchange law

```agda
interchange-law-mul-mul-ℤᵉ :
  (xᵉ yᵉ uᵉ vᵉ : ℤᵉ) → (xᵉ *ℤᵉ yᵉ) *ℤᵉ (uᵉ *ℤᵉ vᵉ) ＝ᵉ (xᵉ *ℤᵉ uᵉ) *ℤᵉ (yᵉ *ℤᵉ vᵉ)
interchange-law-mul-mul-ℤᵉ =
  interchange-law-commutative-and-associativeᵉ
    mul-ℤᵉ
    commutative-mul-ℤᵉ
    associative-mul-ℤᵉ
```

### Computing multiplication of integers that come from natural numbers

```agda
mul-int-ℕᵉ : (xᵉ yᵉ : ℕᵉ) → (int-ℕᵉ xᵉ) *ℤᵉ (int-ℕᵉ yᵉ) ＝ᵉ int-ℕᵉ (xᵉ *ℕᵉ yᵉ)
mul-int-ℕᵉ zero-ℕᵉ yᵉ = reflᵉ
mul-int-ℕᵉ (succ-ℕᵉ xᵉ) yᵉ =
  ( apᵉ (_*ℤᵉ (int-ℕᵉ yᵉ)) (invᵉ (succ-int-ℕᵉ xᵉ))) ∙ᵉ
  ( ( left-successor-law-mul-ℤᵉ (int-ℕᵉ xᵉ) (int-ℕᵉ yᵉ)) ∙ᵉ
    ( ( ( apᵉ ((int-ℕᵉ yᵉ) +ℤᵉ_) (mul-int-ℕᵉ xᵉ yᵉ)) ∙ᵉ
        ( add-int-ℕᵉ yᵉ (xᵉ *ℕᵉ yᵉ))) ∙ᵉ
      ( apᵉ int-ℕᵉ (commutative-add-ℕᵉ yᵉ (xᵉ *ℕᵉ yᵉ)))))

compute-mul-ℤᵉ : (xᵉ yᵉ : ℤᵉ) → xᵉ *ℤᵉ yᵉ ＝ᵉ explicit-mul-ℤᵉ xᵉ yᵉ
compute-mul-ℤᵉ (inlᵉ zero-ℕᵉ) (inlᵉ yᵉ) =
  invᵉ (apᵉ int-ℕᵉ (left-unit-law-mul-ℕᵉ (succ-ℕᵉ yᵉ)))
compute-mul-ℤᵉ (inlᵉ (succ-ℕᵉ xᵉ)) (inlᵉ yᵉ) =
  ( ( apᵉ ((int-ℕᵉ (succ-ℕᵉ yᵉ)) +ℤᵉ_) (compute-mul-ℤᵉ (inlᵉ xᵉ) (inlᵉ yᵉ))) ∙ᵉ
    ( commutative-add-ℤᵉ
      ( int-ℕᵉ (succ-ℕᵉ yᵉ))
      ( int-ℕᵉ ((succ-ℕᵉ xᵉ) *ℕᵉ (succ-ℕᵉ yᵉ))))) ∙ᵉ
  ( add-int-ℕᵉ ((succ-ℕᵉ xᵉ) *ℕᵉ (succ-ℕᵉ yᵉ)) (succ-ℕᵉ yᵉ))
compute-mul-ℤᵉ (inlᵉ zero-ℕᵉ) (inrᵉ (inlᵉ starᵉ)) = reflᵉ
compute-mul-ℤᵉ (inlᵉ zero-ℕᵉ) (inrᵉ (inrᵉ xᵉ)) = apᵉ inlᵉ (invᵉ (left-unit-law-add-ℕᵉ xᵉ))
compute-mul-ℤᵉ (inlᵉ (succ-ℕᵉ xᵉ)) (inrᵉ (inlᵉ starᵉ)) = right-zero-law-mul-ℤᵉ (inlᵉ xᵉ)
compute-mul-ℤᵉ (inlᵉ (succ-ℕᵉ xᵉ)) (inrᵉ (inrᵉ yᵉ)) =
  ( ( ( apᵉ ((inlᵉ yᵉ) +ℤᵉ_) (compute-mul-ℤᵉ (inlᵉ xᵉ) (inrᵉ (inrᵉ yᵉ)))) ∙ᵉ
      ( invᵉ
        ( distributive-neg-add-ℤᵉ
          ( inrᵉ (inrᵉ yᵉ))
          ( int-ℕᵉ ((succ-ℕᵉ xᵉ) *ℕᵉ (succ-ℕᵉ yᵉ)))))) ∙ᵉ
    ( apᵉ
      ( neg-ℤᵉ)
      ( commutative-add-ℤᵉ
        ( int-ℕᵉ (succ-ℕᵉ yᵉ))
        ( int-ℕᵉ ((succ-ℕᵉ xᵉ) *ℕᵉ (succ-ℕᵉ yᵉ)))))) ∙ᵉ
  ( apᵉ neg-ℤᵉ (add-int-ℕᵉ ((succ-ℕᵉ xᵉ) *ℕᵉ (succ-ℕᵉ yᵉ)) (succ-ℕᵉ yᵉ)))
compute-mul-ℤᵉ (inrᵉ (inlᵉ starᵉ)) (inlᵉ yᵉ) = reflᵉ
compute-mul-ℤᵉ (inrᵉ (inrᵉ zero-ℕᵉ)) (inlᵉ yᵉ) = apᵉ inlᵉ (invᵉ (left-unit-law-add-ℕᵉ yᵉ))
compute-mul-ℤᵉ (inrᵉ (inrᵉ (succ-ℕᵉ xᵉ))) (inlᵉ yᵉ) =
  ( apᵉ ((inlᵉ yᵉ) +ℤᵉ_) (compute-mul-ℤᵉ (inrᵉ (inrᵉ xᵉ)) (inlᵉ yᵉ))) ∙ᵉ
  ( ( ( invᵉ
        ( distributive-neg-add-ℤᵉ
          ( inrᵉ (inrᵉ yᵉ))
          ( inrᵉ (inrᵉ ((xᵉ *ℕᵉ (succ-ℕᵉ yᵉ)) +ℕᵉ yᵉ))))) ∙ᵉ
      ( apᵉ
        ( neg-ℤᵉ)
        ( ( add-int-ℕᵉ (succ-ℕᵉ yᵉ) ((succ-ℕᵉ xᵉ) *ℕᵉ (succ-ℕᵉ yᵉ))) ∙ᵉ
          ( apᵉ
            ( inrᵉ ∘ᵉ inrᵉ)
            ( left-successor-law-add-ℕᵉ yᵉ ((xᵉ *ℕᵉ (succ-ℕᵉ yᵉ)) +ℕᵉ yᵉ)))))) ∙ᵉ
    ( apᵉ inlᵉ (commutative-add-ℕᵉ yᵉ ((succ-ℕᵉ xᵉ) *ℕᵉ (succ-ℕᵉ yᵉ)))))
compute-mul-ℤᵉ (inrᵉ (inlᵉ starᵉ)) (inrᵉ (inlᵉ starᵉ)) = reflᵉ
compute-mul-ℤᵉ (inrᵉ (inlᵉ starᵉ)) (inrᵉ (inrᵉ yᵉ)) = reflᵉ
compute-mul-ℤᵉ (inrᵉ (inrᵉ zero-ℕᵉ)) (inrᵉ (inlᵉ starᵉ)) = reflᵉ
compute-mul-ℤᵉ (inrᵉ (inrᵉ (succ-ℕᵉ xᵉ))) (inrᵉ (inlᵉ starᵉ)) =
  right-zero-law-mul-ℤᵉ (inrᵉ (inrᵉ (succ-ℕᵉ xᵉ)))
compute-mul-ℤᵉ (inrᵉ (inrᵉ zero-ℕᵉ)) (inrᵉ (inrᵉ yᵉ)) =
  apᵉ
    ( inrᵉ ∘ᵉ inrᵉ)
    ( invᵉ
      ( ( apᵉ (_+ℕᵉ yᵉ) (left-zero-law-mul-ℕᵉ (succ-ℕᵉ yᵉ))) ∙ᵉ
        ( left-unit-law-add-ℕᵉ yᵉ)))
compute-mul-ℤᵉ (inrᵉ (inrᵉ (succ-ℕᵉ xᵉ))) (inrᵉ (inrᵉ yᵉ)) =
  ( apᵉ ((inrᵉ (inrᵉ yᵉ)) +ℤᵉ_) (compute-mul-ℤᵉ (inrᵉ (inrᵉ xᵉ)) (inrᵉ (inrᵉ yᵉ)))) ∙ᵉ
  ( ( add-int-ℕᵉ (succ-ℕᵉ yᵉ) ((succ-ℕᵉ xᵉ) *ℕᵉ (succ-ℕᵉ yᵉ))) ∙ᵉ
    ( apᵉ int-ℕᵉ (commutative-add-ℕᵉ (succ-ℕᵉ yᵉ) ((succ-ℕᵉ xᵉ) *ℕᵉ (succ-ℕᵉ yᵉ)))))
```

### Multiplication on integers distributes over the difference

```agda
left-distributive-mul-diff-ℤᵉ :
  (zᵉ xᵉ yᵉ : ℤᵉ) → zᵉ *ℤᵉ (xᵉ -ℤᵉ yᵉ) ＝ᵉ (zᵉ *ℤᵉ xᵉ) -ℤᵉ (zᵉ *ℤᵉ yᵉ)
left-distributive-mul-diff-ℤᵉ zᵉ xᵉ yᵉ =
  ( left-distributive-mul-add-ℤᵉ zᵉ xᵉ (neg-ℤᵉ yᵉ)) ∙ᵉ
  ( apᵉ ((zᵉ *ℤᵉ xᵉ) +ℤᵉ_) (right-negative-law-mul-ℤᵉ zᵉ yᵉ))

right-distributive-mul-diff-ℤᵉ :
  (xᵉ yᵉ zᵉ : ℤᵉ) → (xᵉ -ℤᵉ yᵉ) *ℤᵉ zᵉ ＝ᵉ (xᵉ *ℤᵉ zᵉ) -ℤᵉ (yᵉ *ℤᵉ zᵉ)
right-distributive-mul-diff-ℤᵉ xᵉ yᵉ zᵉ =
  ( right-distributive-mul-add-ℤᵉ xᵉ (neg-ℤᵉ yᵉ) zᵉ) ∙ᵉ
  ( apᵉ ((xᵉ *ℤᵉ zᵉ) +ℤᵉ_) (left-negative-law-mul-ℤᵉ yᵉ zᵉ))
```

### If the product of two integers is zero, one of the factors is zero

```agda
is-zero-is-zero-mul-ℤᵉ :
  (xᵉ yᵉ : ℤᵉ) → is-zero-ℤᵉ (xᵉ *ℤᵉ yᵉ) → (is-zero-ℤᵉ xᵉ) +ᵉ (is-zero-ℤᵉ yᵉ)
is-zero-is-zero-mul-ℤᵉ (inlᵉ xᵉ) (inlᵉ yᵉ) Hᵉ =
  ex-falsoᵉ (Eq-eq-ℤᵉ (invᵉ (compute-mul-ℤᵉ (inlᵉ xᵉ) (inlᵉ yᵉ)) ∙ᵉ Hᵉ))
is-zero-is-zero-mul-ℤᵉ (inlᵉ xᵉ) (inrᵉ (inlᵉ starᵉ)) Hᵉ = inrᵉ reflᵉ
is-zero-is-zero-mul-ℤᵉ (inlᵉ xᵉ) (inrᵉ (inrᵉ yᵉ)) Hᵉ =
  ex-falsoᵉ (Eq-eq-ℤᵉ (invᵉ (compute-mul-ℤᵉ (inlᵉ xᵉ) (inrᵉ (inrᵉ yᵉ))) ∙ᵉ Hᵉ))
is-zero-is-zero-mul-ℤᵉ (inrᵉ (inlᵉ starᵉ)) yᵉ Hᵉ = inlᵉ reflᵉ
is-zero-is-zero-mul-ℤᵉ (inrᵉ (inrᵉ xᵉ)) (inlᵉ yᵉ) Hᵉ =
  ex-falsoᵉ (Eq-eq-ℤᵉ (invᵉ (compute-mul-ℤᵉ (inrᵉ (inrᵉ xᵉ)) (inlᵉ yᵉ)) ∙ᵉ Hᵉ))
is-zero-is-zero-mul-ℤᵉ (inrᵉ (inrᵉ xᵉ)) (inrᵉ (inlᵉ starᵉ)) Hᵉ = inrᵉ reflᵉ
is-zero-is-zero-mul-ℤᵉ (inrᵉ (inrᵉ xᵉ)) (inrᵉ (inrᵉ yᵉ)) Hᵉ =
  ex-falsoᵉ (Eq-eq-ℤᵉ (invᵉ (compute-mul-ℤᵉ (inrᵉ (inrᵉ xᵉ)) (inrᵉ (inrᵉ yᵉ))) ∙ᵉ Hᵉ))
```

### Injectivity of multiplication by a nonzero integer

```agda
is-injective-left-mul-ℤᵉ :
  (xᵉ : ℤᵉ) → is-nonzero-ℤᵉ xᵉ → is-injectiveᵉ (xᵉ *ℤᵉ_)
is-injective-left-mul-ℤᵉ xᵉ fᵉ {yᵉ} {zᵉ} pᵉ =
  eq-diff-ℤᵉ
    ( map-left-unit-law-coproduct-is-emptyᵉ
      ( is-zero-ℤᵉ xᵉ)
      ( is-zero-ℤᵉ (yᵉ -ℤᵉ zᵉ))
      ( fᵉ)
      ( is-zero-is-zero-mul-ℤᵉ xᵉ
        ( yᵉ -ℤᵉ zᵉ)
        ( left-distributive-mul-diff-ℤᵉ xᵉ yᵉ zᵉ ∙ᵉ is-zero-diff-ℤᵉ pᵉ)))

is-injective-right-mul-ℤᵉ :
  (xᵉ : ℤᵉ) → is-nonzero-ℤᵉ xᵉ → is-injectiveᵉ (_*ℤᵉ xᵉ)
is-injective-right-mul-ℤᵉ xᵉ fᵉ {yᵉ} {zᵉ} pᵉ =
  is-injective-left-mul-ℤᵉ
    ( xᵉ)
    ( fᵉ)
    ( commutative-mul-ℤᵉ xᵉ yᵉ ∙ᵉ (pᵉ ∙ᵉ commutative-mul-ℤᵉ zᵉ xᵉ))
```

### Multiplication by a nonzero integer is an embedding

```agda
is-emb-left-mul-ℤᵉ : (xᵉ : ℤᵉ) → is-nonzero-ℤᵉ xᵉ → is-embᵉ (xᵉ *ℤᵉ_)
is-emb-left-mul-ℤᵉ xᵉ fᵉ =
  is-emb-is-injectiveᵉ is-set-ℤᵉ (is-injective-left-mul-ℤᵉ xᵉ fᵉ)

is-emb-right-mul-ℤᵉ : (xᵉ : ℤᵉ) → is-nonzero-ℤᵉ xᵉ → is-embᵉ (_*ℤᵉ xᵉ)
is-emb-right-mul-ℤᵉ xᵉ fᵉ =
  is-emb-is-injectiveᵉ is-set-ℤᵉ (is-injective-right-mul-ℤᵉ xᵉ fᵉ)
```

## See also

-ᵉ Propertiesᵉ ofᵉ multiplicationᵉ with respectᵉ to inequalityᵉ andᵉ positivity,ᵉ
  nonnegativity,ᵉ negativityᵉ andᵉ nonnpositivityᵉ ofᵉ integersᵉ areᵉ derivedᵉ in
  [`multiplication-positive-and-negative-integers`](elementary-number-theory.multiplication-positive-and-negative-integers.mdᵉ)