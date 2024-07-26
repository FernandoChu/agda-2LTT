# The distance between integers

```agda
module elementary-number-theory.distance-integersᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.absolute-value-integersᵉ
open import elementary-number-theory.difference-integersᵉ
open import elementary-number-theory.distance-natural-numbersᵉ
open import elementary-number-theory.integersᵉ
open import elementary-number-theory.natural-numbersᵉ
open import elementary-number-theory.nonnegative-integersᵉ
open import elementary-number-theory.positive-and-negative-integersᵉ
open import elementary-number-theory.positive-integersᵉ

open import foundation.action-on-identifications-binary-functionsᵉ
open import foundation.action-on-identifications-functionsᵉ
open import foundation.coproduct-typesᵉ
open import foundation.identity-typesᵉ
```

</details>

## Idea

Theᵉ distanceᵉ functionᵉ betweenᵉ integersᵉ measuresᵉ howᵉ farᵉ twoᵉ integersᵉ areᵉ apart.ᵉ

## Definition

```agda
dist-ℤᵉ : ℤᵉ → ℤᵉ → ℕᵉ
dist-ℤᵉ xᵉ yᵉ = abs-ℤᵉ (xᵉ -ℤᵉ yᵉ)

ap-dist-ℤᵉ :
  {xᵉ x'ᵉ yᵉ y'ᵉ : ℤᵉ} → xᵉ ＝ᵉ x'ᵉ → yᵉ ＝ᵉ y'ᵉ → dist-ℤᵉ xᵉ yᵉ ＝ᵉ dist-ℤᵉ x'ᵉ y'ᵉ
ap-dist-ℤᵉ pᵉ qᵉ = ap-binaryᵉ dist-ℤᵉ pᵉ qᵉ

left-zero-law-dist-ℤᵉ : (xᵉ : ℤᵉ) → dist-ℤᵉ zero-ℤᵉ xᵉ ＝ᵉ abs-ℤᵉ xᵉ
left-zero-law-dist-ℤᵉ xᵉ = apᵉ abs-ℤᵉ (left-zero-law-diff-ℤᵉ xᵉ) ∙ᵉ abs-neg-ℤᵉ xᵉ

right-zero-law-dist-ℤᵉ : (xᵉ : ℤᵉ) → dist-ℤᵉ xᵉ zero-ℤᵉ ＝ᵉ abs-ℤᵉ xᵉ
right-zero-law-dist-ℤᵉ xᵉ = apᵉ abs-ℤᵉ (right-zero-law-diff-ℤᵉ xᵉ)

dist-int-ℕᵉ :
  (xᵉ yᵉ : ℕᵉ) → dist-ℤᵉ (int-ℕᵉ xᵉ) (int-ℕᵉ yᵉ) ＝ᵉ dist-ℕᵉ xᵉ yᵉ
dist-int-ℕᵉ zero-ℕᵉ zero-ℕᵉ = reflᵉ
dist-int-ℕᵉ zero-ℕᵉ (succ-ℕᵉ yᵉ) = left-zero-law-dist-ℤᵉ (int-ℕᵉ (succ-ℕᵉ yᵉ))
dist-int-ℕᵉ (succ-ℕᵉ xᵉ) zero-ℕᵉ = right-zero-law-dist-ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ))
dist-int-ℕᵉ (succ-ℕᵉ xᵉ) (succ-ℕᵉ yᵉ) =
  ( ( ap-dist-ℤᵉ (invᵉ (succ-int-ℕᵉ xᵉ)) (invᵉ (succ-int-ℕᵉ yᵉ))) ∙ᵉ
    ( apᵉ abs-ℤᵉ (diff-succ-ℤᵉ (int-ℕᵉ xᵉ) (int-ℕᵉ yᵉ)))) ∙ᵉ
  ( dist-int-ℕᵉ xᵉ yᵉ)

dist-abs-ℤᵉ :
  (xᵉ yᵉ : ℤᵉ) → (Hᵉ : is-nonnegative-ℤᵉ xᵉ) → (Kᵉ : is-nonnegative-ℤᵉ yᵉ) →
  dist-ℕᵉ (abs-ℤᵉ xᵉ) (abs-ℤᵉ yᵉ) ＝ᵉ dist-ℤᵉ xᵉ yᵉ
dist-abs-ℤᵉ (inrᵉ (inlᵉ _)) yᵉ Hᵉ Kᵉ =
  equational-reasoningᵉ
    dist-ℕᵉ 0 (abs-ℤᵉ yᵉ)
    ＝ᵉ abs-ℤᵉ yᵉ
      byᵉ left-unit-law-dist-ℕᵉ (abs-ℤᵉ yᵉ)
    ＝ᵉ dist-ℤᵉ (zero-ℤᵉ) yᵉ
      byᵉ invᵉ (left-zero-law-dist-ℤᵉ yᵉ)
dist-abs-ℤᵉ (inrᵉ (inrᵉ xᵉ)) (inrᵉ (inlᵉ _)) Hᵉ Kᵉ =
  equational-reasoningᵉ
    dist-ℕᵉ (abs-ℤᵉ (inrᵉ (inrᵉ xᵉ))) 0
    ＝ᵉ succ-ℕᵉ xᵉ
      byᵉ right-unit-law-dist-ℕᵉ (abs-ℤᵉ (inrᵉ (inrᵉ xᵉ)))
    ＝ᵉ dist-ℤᵉ (inrᵉ (inrᵉ xᵉ)) zero-ℤᵉ
      byᵉ invᵉ (right-zero-law-dist-ℤᵉ (inrᵉ (inrᵉ xᵉ)))
dist-abs-ℤᵉ (inrᵉ (inrᵉ xᵉ)) (inrᵉ (inrᵉ yᵉ)) Hᵉ Kᵉ =
  equational-reasoningᵉ
    dist-ℕᵉ (succ-ℕᵉ xᵉ) (succ-ℕᵉ yᵉ)
    ＝ᵉ dist-ℤᵉ (int-ℕᵉ (succ-ℕᵉ xᵉ)) (int-ℕᵉ (succ-ℕᵉ yᵉ))
      byᵉ invᵉ (dist-int-ℕᵉ (succ-ℕᵉ xᵉ) (succ-ℕᵉ yᵉ))
```