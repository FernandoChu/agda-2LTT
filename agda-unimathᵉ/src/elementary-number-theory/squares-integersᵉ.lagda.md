# Squares in the integers

```agda
module elementary-number-theory.squares-integersᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.absolute-value-integersᵉ
open import elementary-number-theory.integersᵉ
open import elementary-number-theory.multiplication-integersᵉ
open import elementary-number-theory.multiplication-positive-and-negative-integersᵉ
open import elementary-number-theory.natural-numbersᵉ
open import elementary-number-theory.nonnegative-integersᵉ
open import elementary-number-theory.positive-and-negative-integersᵉ
open import elementary-number-theory.positive-integersᵉ
open import elementary-number-theory.squares-natural-numbersᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.coproduct-typesᵉ
open import foundation.decidable-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.negationᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.cartesian-product-typesᵉ
open import foundation-core.transport-along-identificationsᵉ
```

</details>

## Definition

```agda
square-ℤᵉ : ℤᵉ → ℤᵉ
square-ℤᵉ aᵉ = mul-ℤᵉ aᵉ aᵉ

cube-ℤᵉ : ℤᵉ → ℤᵉ
cube-ℤᵉ aᵉ = mul-ℤᵉ (square-ℤᵉ aᵉ) aᵉ

is-square-ℤᵉ : ℤᵉ → UUᵉ lzero
is-square-ℤᵉ aᵉ = Σᵉ ℤᵉ (λ xᵉ → aᵉ ＝ᵉ square-ℤᵉ xᵉ)

square-root-ℤᵉ : (aᵉ : ℤᵉ) → is-square-ℤᵉ aᵉ → ℤᵉ
square-root-ℤᵉ _ (rootᵉ ,ᵉ _) = rootᵉ
```

## Properties

### Squares in ℤ are nonnegative

```agda
is-nonnegative-square-ℤᵉ : (aᵉ : ℤᵉ) → is-nonnegative-ℤᵉ (square-ℤᵉ aᵉ)
is-nonnegative-square-ℤᵉ aᵉ =
  rec-coproductᵉ
    ( λ Hᵉ → is-nonnegative-is-positive-ℤᵉ (is-positive-mul-negative-ℤᵉ Hᵉ Hᵉ))
    ( λ Hᵉ → is-nonnegative-mul-ℤᵉ Hᵉ Hᵉ)
    ( decide-is-negative-is-nonnegative-ℤᵉ {aᵉ})
```

### The squares in ℤ are exactly the squares in ℕ

```agda
is-square-int-is-square-natᵉ : {nᵉ : ℕᵉ} → is-square-ℕᵉ nᵉ → is-square-ℤᵉ (int-ℕᵉ nᵉ)
is-square-int-is-square-natᵉ (rootᵉ ,ᵉ pf-squareᵉ) =
  ( ( int-ℕᵉ rootᵉ) ,ᵉ
    ( ( apᵉ int-ℕᵉ pf-squareᵉ) ∙ᵉ
      ( invᵉ (mul-int-ℕᵉ rootᵉ rootᵉ))))

is-square-nat-is-square-intᵉ : {aᵉ : ℤᵉ} → is-square-ℤᵉ aᵉ → is-square-ℕᵉ (abs-ℤᵉ aᵉ)
is-square-nat-is-square-intᵉ (rootᵉ ,ᵉ pf-squareᵉ) =
  ( ( abs-ℤᵉ rootᵉ) ,ᵉ
    ( ( apᵉ abs-ℤᵉ pf-squareᵉ) ∙ᵉ
      ( multiplicative-abs-ℤᵉ rootᵉ rootᵉ)))

iff-is-square-int-is-square-natᵉ :
  (nᵉ : ℕᵉ) → is-square-ℕᵉ nᵉ ↔ᵉ is-square-ℤᵉ (int-ℕᵉ nᵉ)
pr1ᵉ (iff-is-square-int-is-square-natᵉ nᵉ) = is-square-int-is-square-natᵉ
pr2ᵉ (iff-is-square-int-is-square-natᵉ nᵉ) Hᵉ =
  trᵉ is-square-ℕᵉ (abs-int-ℕᵉ nᵉ) (is-square-nat-is-square-intᵉ Hᵉ)

iff-is-nonneg-square-nat-is-square-intᵉ :
  (aᵉ : ℤᵉ) → is-square-ℤᵉ aᵉ ↔ᵉ is-nonnegative-ℤᵉ aᵉ ×ᵉ is-square-ℕᵉ (abs-ℤᵉ aᵉ)
pr1ᵉ (iff-is-nonneg-square-nat-is-square-intᵉ aᵉ) (rootᵉ ,ᵉ pf-squareᵉ) =
  ( ( trᵉ is-nonnegative-ℤᵉ (invᵉ pf-squareᵉ) (is-nonnegative-square-ℤᵉ rootᵉ)) ,ᵉ
    ( is-square-nat-is-square-intᵉ (rootᵉ ,ᵉ pf-squareᵉ)))
pr2ᵉ
  ( iff-is-nonneg-square-nat-is-square-intᵉ aᵉ) (pf-nonnegᵉ ,ᵉ (rootᵉ ,ᵉ pf-squareᵉ)) =
  ( ( int-ℕᵉ rootᵉ) ,ᵉ
    ( ( invᵉ (int-abs-is-nonnegative-ℤᵉ aᵉ pf-nonnegᵉ)) ∙ᵉ
      ( pr2ᵉ (is-square-int-is-square-natᵉ (rootᵉ ,ᵉ pf-squareᵉ)))))
```

### Squareness in ℤ is decidable

```agda
is-decidable-is-square-ℤᵉ : (aᵉ : ℤᵉ) → is-decidableᵉ (is-square-ℤᵉ aᵉ)
is-decidable-is-square-ℤᵉ (inlᵉ nᵉ) =
  inrᵉ (map-negᵉ (pr1ᵉ (iff-is-nonneg-square-nat-is-square-intᵉ (inlᵉ nᵉ))) pr1ᵉ)
is-decidable-is-square-ℤᵉ (inrᵉ (inlᵉ nᵉ)) = inlᵉ (zero-ℤᵉ ,ᵉ reflᵉ)
is-decidable-is-square-ℤᵉ (inrᵉ (inrᵉ nᵉ)) =
  is-decidable-iffᵉ
    ( is-square-int-is-square-natᵉ)
    ( is-square-nat-is-square-intᵉ)
    ( is-decidable-is-square-ℕᵉ (succ-ℕᵉ nᵉ))
```