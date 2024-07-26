# The distance between natural numbers

```agda
module elementary-number-theory.distance-natural-numbersᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbersᵉ
open import elementary-number-theory.inequality-natural-numbersᵉ
open import elementary-number-theory.multiplication-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ
open import elementary-number-theory.strict-inequality-natural-numbersᵉ

open import foundation.action-on-identifications-binary-functionsᵉ
open import foundation.action-on-identifications-functionsᵉ
open import foundation.coproduct-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.function-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Theᵉ distanceᵉ functionᵉ betweenᵉ naturalᵉ numbersᵉ measuresᵉ howᵉ farᵉ twoᵉ naturalᵉ
numbersᵉ areᵉ apart.ᵉ Inᵉ theᵉ agda-unimathᵉ libraryᵉ weᵉ oftenᵉ preferᵉ to workᵉ with
`dist-ℕ`ᵉ overᵉ theᵉ partiallyᵉ definedᵉ subtractionᵉ operation.ᵉ

## Definition

```agda
dist-ℕᵉ : ℕᵉ → ℕᵉ → ℕᵉ
dist-ℕᵉ zero-ℕᵉ nᵉ = nᵉ
dist-ℕᵉ (succ-ℕᵉ mᵉ) zero-ℕᵉ = succ-ℕᵉ mᵉ
dist-ℕᵉ (succ-ℕᵉ mᵉ) (succ-ℕᵉ nᵉ) = dist-ℕᵉ mᵉ nᵉ

dist-ℕ'ᵉ : ℕᵉ → ℕᵉ → ℕᵉ
dist-ℕ'ᵉ mᵉ nᵉ = dist-ℕᵉ nᵉ mᵉ

ap-dist-ℕᵉ :
  {mᵉ nᵉ m'ᵉ n'ᵉ : ℕᵉ} → mᵉ ＝ᵉ m'ᵉ → nᵉ ＝ᵉ n'ᵉ → dist-ℕᵉ mᵉ nᵉ ＝ᵉ dist-ℕᵉ m'ᵉ n'ᵉ
ap-dist-ℕᵉ pᵉ qᵉ = ap-binaryᵉ dist-ℕᵉ pᵉ qᵉ
```

## Properties

### Two natural numbers are equal if and only if their distance is zero

```agda
eq-dist-ℕᵉ : (mᵉ nᵉ : ℕᵉ) → is-zero-ℕᵉ (dist-ℕᵉ mᵉ nᵉ) → mᵉ ＝ᵉ nᵉ
eq-dist-ℕᵉ zero-ℕᵉ zero-ℕᵉ pᵉ = reflᵉ
eq-dist-ℕᵉ (succ-ℕᵉ mᵉ) (succ-ℕᵉ nᵉ) pᵉ = apᵉ succ-ℕᵉ (eq-dist-ℕᵉ mᵉ nᵉ pᵉ)

dist-eq-ℕ'ᵉ : (nᵉ : ℕᵉ) → is-zero-ℕᵉ (dist-ℕᵉ nᵉ nᵉ)
dist-eq-ℕ'ᵉ zero-ℕᵉ = reflᵉ
dist-eq-ℕ'ᵉ (succ-ℕᵉ nᵉ) = dist-eq-ℕ'ᵉ nᵉ

dist-eq-ℕᵉ : (mᵉ nᵉ : ℕᵉ) → mᵉ ＝ᵉ nᵉ → is-zero-ℕᵉ (dist-ℕᵉ mᵉ nᵉ)
dist-eq-ℕᵉ mᵉ .mᵉ reflᵉ = dist-eq-ℕ'ᵉ mᵉ

is-one-dist-succ-ℕᵉ : (xᵉ : ℕᵉ) → is-one-ℕᵉ (dist-ℕᵉ xᵉ (succ-ℕᵉ xᵉ))
is-one-dist-succ-ℕᵉ zero-ℕᵉ = reflᵉ
is-one-dist-succ-ℕᵉ (succ-ℕᵉ xᵉ) = is-one-dist-succ-ℕᵉ xᵉ

is-one-dist-succ-ℕ'ᵉ : (xᵉ : ℕᵉ) → is-one-ℕᵉ (dist-ℕᵉ (succ-ℕᵉ xᵉ) xᵉ)
is-one-dist-succ-ℕ'ᵉ zero-ℕᵉ = reflᵉ
is-one-dist-succ-ℕ'ᵉ (succ-ℕᵉ xᵉ) = is-one-dist-succ-ℕ'ᵉ xᵉ
```

### The distance function is symmetric

```agda
symmetric-dist-ℕᵉ :
  (mᵉ nᵉ : ℕᵉ) → dist-ℕᵉ mᵉ nᵉ ＝ᵉ dist-ℕᵉ nᵉ mᵉ
symmetric-dist-ℕᵉ zero-ℕᵉ zero-ℕᵉ = reflᵉ
symmetric-dist-ℕᵉ zero-ℕᵉ (succ-ℕᵉ nᵉ) = reflᵉ
symmetric-dist-ℕᵉ (succ-ℕᵉ mᵉ) zero-ℕᵉ = reflᵉ
symmetric-dist-ℕᵉ (succ-ℕᵉ mᵉ) (succ-ℕᵉ nᵉ) = symmetric-dist-ℕᵉ mᵉ nᵉ
```

### The distance from zero

```agda
left-unit-law-dist-ℕᵉ :
  (nᵉ : ℕᵉ) → dist-ℕᵉ zero-ℕᵉ nᵉ ＝ᵉ nᵉ
left-unit-law-dist-ℕᵉ zero-ℕᵉ = reflᵉ
left-unit-law-dist-ℕᵉ (succ-ℕᵉ nᵉ) = reflᵉ

right-unit-law-dist-ℕᵉ :
  (nᵉ : ℕᵉ) → dist-ℕᵉ nᵉ zero-ℕᵉ ＝ᵉ nᵉ
right-unit-law-dist-ℕᵉ zero-ℕᵉ = reflᵉ
right-unit-law-dist-ℕᵉ (succ-ℕᵉ nᵉ) = reflᵉ
```

## The triangle inequality

```agda
triangle-inequality-dist-ℕᵉ :
  (mᵉ nᵉ kᵉ : ℕᵉ) → (dist-ℕᵉ mᵉ nᵉ) ≤-ℕᵉ ((dist-ℕᵉ mᵉ kᵉ) +ℕᵉ (dist-ℕᵉ kᵉ nᵉ))
triangle-inequality-dist-ℕᵉ zero-ℕᵉ zero-ℕᵉ zero-ℕᵉ = starᵉ
triangle-inequality-dist-ℕᵉ zero-ℕᵉ zero-ℕᵉ (succ-ℕᵉ kᵉ) = starᵉ
triangle-inequality-dist-ℕᵉ zero-ℕᵉ (succ-ℕᵉ nᵉ) zero-ℕᵉ =
  trᵉ
    ( leq-ℕᵉ (succ-ℕᵉ nᵉ))
    ( invᵉ (left-unit-law-add-ℕᵉ (succ-ℕᵉ nᵉ)))
    ( refl-leq-ℕᵉ (succ-ℕᵉ nᵉ))
triangle-inequality-dist-ℕᵉ zero-ℕᵉ (succ-ℕᵉ nᵉ) (succ-ℕᵉ kᵉ) =
  concatenate-eq-leq-eq-ℕᵉ
    ( invᵉ (apᵉ succ-ℕᵉ (left-unit-law-dist-ℕᵉ nᵉ)))
    ( triangle-inequality-dist-ℕᵉ zero-ℕᵉ nᵉ kᵉ)
    ( ( apᵉ (succ-ℕᵉ ∘ᵉ (_+ℕᵉ (dist-ℕᵉ kᵉ nᵉ))) (left-unit-law-dist-ℕᵉ kᵉ)) ∙ᵉ
      ( invᵉ (left-successor-law-add-ℕᵉ kᵉ (dist-ℕᵉ kᵉ nᵉ))))
triangle-inequality-dist-ℕᵉ (succ-ℕᵉ mᵉ) zero-ℕᵉ zero-ℕᵉ = refl-leq-ℕᵉ (succ-ℕᵉ mᵉ)
triangle-inequality-dist-ℕᵉ (succ-ℕᵉ mᵉ) zero-ℕᵉ (succ-ℕᵉ kᵉ) =
  concatenate-eq-leq-eq-ℕᵉ
    ( invᵉ (apᵉ succ-ℕᵉ (right-unit-law-dist-ℕᵉ mᵉ)))
    ( triangle-inequality-dist-ℕᵉ mᵉ zero-ℕᵉ kᵉ)
    ( apᵉ (succ-ℕᵉ ∘ᵉ ((dist-ℕᵉ mᵉ kᵉ) +ℕᵉ_)) (right-unit-law-dist-ℕᵉ kᵉ))
triangle-inequality-dist-ℕᵉ (succ-ℕᵉ mᵉ) (succ-ℕᵉ nᵉ) zero-ℕᵉ =
  concatenate-leq-eq-ℕᵉ
    ( dist-ℕᵉ mᵉ nᵉ)
    ( transitive-leq-ℕᵉ
      ( dist-ℕᵉ mᵉ nᵉ)
      ( succ-ℕᵉ ((dist-ℕᵉ mᵉ zero-ℕᵉ) +ℕᵉ (dist-ℕᵉ zero-ℕᵉ nᵉ)))
      ( succ-ℕᵉ (succ-ℕᵉ ((dist-ℕᵉ mᵉ zero-ℕᵉ) +ℕᵉ (dist-ℕᵉ zero-ℕᵉ nᵉ))))
      ( succ-leq-ℕᵉ (succ-ℕᵉ ((dist-ℕᵉ mᵉ zero-ℕᵉ) +ℕᵉ (dist-ℕᵉ zero-ℕᵉ nᵉ))))
      ( transitive-leq-ℕᵉ
        ( dist-ℕᵉ mᵉ nᵉ)
        ( (dist-ℕᵉ mᵉ zero-ℕᵉ) +ℕᵉ (dist-ℕᵉ zero-ℕᵉ nᵉ))
        ( succ-ℕᵉ ((dist-ℕᵉ mᵉ zero-ℕᵉ) +ℕᵉ (dist-ℕᵉ zero-ℕᵉ nᵉ)))
        ( succ-leq-ℕᵉ ((dist-ℕᵉ mᵉ zero-ℕᵉ) +ℕᵉ (dist-ℕᵉ zero-ℕᵉ nᵉ)))
        ( triangle-inequality-dist-ℕᵉ mᵉ nᵉ zero-ℕᵉ)))
    ( ( apᵉ
        ( succ-ℕᵉ ∘ᵉ succ-ℕᵉ)
        ( ap-add-ℕᵉ (right-unit-law-dist-ℕᵉ mᵉ) (left-unit-law-dist-ℕᵉ nᵉ))) ∙ᵉ
      ( invᵉ (left-successor-law-add-ℕᵉ mᵉ (succ-ℕᵉ nᵉ))))
triangle-inequality-dist-ℕᵉ (succ-ℕᵉ mᵉ) (succ-ℕᵉ nᵉ) (succ-ℕᵉ kᵉ) =
  triangle-inequality-dist-ℕᵉ mᵉ nᵉ kᵉ
```

### `dist-ℕ x y` is a solution in `z` to `x + z ＝ y`

```agda
is-additive-right-inverse-dist-ℕᵉ :
  (xᵉ yᵉ : ℕᵉ) → xᵉ ≤-ℕᵉ yᵉ → xᵉ +ℕᵉ (dist-ℕᵉ xᵉ yᵉ) ＝ᵉ yᵉ
is-additive-right-inverse-dist-ℕᵉ zero-ℕᵉ zero-ℕᵉ Hᵉ = reflᵉ
is-additive-right-inverse-dist-ℕᵉ zero-ℕᵉ (succ-ℕᵉ yᵉ) starᵉ =
  left-unit-law-add-ℕᵉ (succ-ℕᵉ yᵉ)
is-additive-right-inverse-dist-ℕᵉ (succ-ℕᵉ xᵉ) (succ-ℕᵉ yᵉ) Hᵉ =
  ( left-successor-law-add-ℕᵉ xᵉ (dist-ℕᵉ xᵉ yᵉ)) ∙ᵉ
  ( apᵉ succ-ℕᵉ (is-additive-right-inverse-dist-ℕᵉ xᵉ yᵉ Hᵉ))

rewrite-left-add-dist-ℕᵉ :
  (xᵉ yᵉ zᵉ : ℕᵉ) → xᵉ +ℕᵉ yᵉ ＝ᵉ zᵉ → xᵉ ＝ᵉ dist-ℕᵉ yᵉ zᵉ
rewrite-left-add-dist-ℕᵉ zero-ℕᵉ zero-ℕᵉ .zero-ℕᵉ reflᵉ = reflᵉ
rewrite-left-add-dist-ℕᵉ zero-ℕᵉ (succ-ℕᵉ yᵉ) .(succ-ℕᵉ (zero-ℕᵉ +ℕᵉ yᵉ)) reflᵉ =
  ( invᵉ (dist-eq-ℕ'ᵉ yᵉ)) ∙ᵉ
  ( invᵉ (apᵉ (dist-ℕᵉ (succ-ℕᵉ yᵉ)) (left-unit-law-add-ℕᵉ (succ-ℕᵉ yᵉ))))
rewrite-left-add-dist-ℕᵉ (succ-ℕᵉ xᵉ) zero-ℕᵉ .(succ-ℕᵉ xᵉ) reflᵉ = reflᵉ
rewrite-left-add-dist-ℕᵉ (succ-ℕᵉ xᵉ) (succ-ℕᵉ yᵉ) ._ reflᵉ =
  rewrite-left-add-dist-ℕᵉ (succ-ℕᵉ xᵉ) yᵉ ((succ-ℕᵉ xᵉ) +ℕᵉ yᵉ) reflᵉ

rewrite-left-dist-add-ℕᵉ :
  (xᵉ yᵉ zᵉ : ℕᵉ) → yᵉ ≤-ℕᵉ zᵉ → xᵉ ＝ᵉ dist-ℕᵉ yᵉ zᵉ → xᵉ +ℕᵉ yᵉ ＝ᵉ zᵉ
rewrite-left-dist-add-ℕᵉ .(dist-ℕᵉ yᵉ zᵉ) yᵉ zᵉ Hᵉ reflᵉ =
  ( commutative-add-ℕᵉ (dist-ℕᵉ yᵉ zᵉ) yᵉ) ∙ᵉ
  ( is-additive-right-inverse-dist-ℕᵉ yᵉ zᵉ Hᵉ)

rewrite-right-add-dist-ℕᵉ :
  (xᵉ yᵉ zᵉ : ℕᵉ) → xᵉ +ℕᵉ yᵉ ＝ᵉ zᵉ → yᵉ ＝ᵉ dist-ℕᵉ xᵉ zᵉ
rewrite-right-add-dist-ℕᵉ xᵉ yᵉ zᵉ pᵉ =
  rewrite-left-add-dist-ℕᵉ yᵉ xᵉ zᵉ (commutative-add-ℕᵉ yᵉ xᵉ ∙ᵉ pᵉ)

rewrite-right-dist-add-ℕᵉ :
  (xᵉ yᵉ zᵉ : ℕᵉ) → xᵉ ≤-ℕᵉ zᵉ → yᵉ ＝ᵉ dist-ℕᵉ xᵉ zᵉ → xᵉ +ℕᵉ yᵉ ＝ᵉ zᵉ
rewrite-right-dist-add-ℕᵉ xᵉ .(dist-ℕᵉ xᵉ zᵉ) zᵉ Hᵉ reflᵉ =
  is-additive-right-inverse-dist-ℕᵉ xᵉ zᵉ Hᵉ

is-difference-dist-ℕᵉ :
  (xᵉ yᵉ : ℕᵉ) → xᵉ ≤-ℕᵉ yᵉ → xᵉ +ℕᵉ (dist-ℕᵉ xᵉ yᵉ) ＝ᵉ yᵉ
is-difference-dist-ℕᵉ zero-ℕᵉ zero-ℕᵉ Hᵉ = reflᵉ
is-difference-dist-ℕᵉ zero-ℕᵉ (succ-ℕᵉ yᵉ) Hᵉ = left-unit-law-add-ℕᵉ (succ-ℕᵉ yᵉ)
is-difference-dist-ℕᵉ (succ-ℕᵉ xᵉ) (succ-ℕᵉ yᵉ) Hᵉ =
  ( left-successor-law-add-ℕᵉ xᵉ (dist-ℕᵉ xᵉ yᵉ)) ∙ᵉ
  ( apᵉ succ-ℕᵉ (is-difference-dist-ℕᵉ xᵉ yᵉ Hᵉ))

is-difference-dist-ℕ'ᵉ :
  (xᵉ yᵉ : ℕᵉ) → xᵉ ≤-ℕᵉ yᵉ → (dist-ℕᵉ xᵉ yᵉ) +ℕᵉ xᵉ ＝ᵉ yᵉ
is-difference-dist-ℕ'ᵉ xᵉ yᵉ Hᵉ =
  ( commutative-add-ℕᵉ (dist-ℕᵉ xᵉ yᵉ) xᵉ) ∙ᵉ
  ( is-difference-dist-ℕᵉ xᵉ yᵉ Hᵉ)
```

### The distance from `n` to `n + m` is `m`

```agda
dist-add-ℕᵉ : (xᵉ yᵉ : ℕᵉ) → dist-ℕᵉ xᵉ (xᵉ +ℕᵉ yᵉ) ＝ᵉ yᵉ
dist-add-ℕᵉ xᵉ yᵉ = invᵉ (rewrite-right-add-dist-ℕᵉ xᵉ yᵉ (xᵉ +ℕᵉ yᵉ) reflᵉ)

dist-add-ℕ'ᵉ : (xᵉ yᵉ : ℕᵉ) → dist-ℕᵉ (xᵉ +ℕᵉ yᵉ) xᵉ ＝ᵉ yᵉ
dist-add-ℕ'ᵉ xᵉ yᵉ = symmetric-dist-ℕᵉ (xᵉ +ℕᵉ yᵉ) xᵉ ∙ᵉ dist-add-ℕᵉ xᵉ yᵉ
```

### If three elements are ordered linearly, then their distances add up

```agda
triangle-equality-dist-ℕᵉ :
  (xᵉ yᵉ zᵉ : ℕᵉ) → (xᵉ ≤-ℕᵉ yᵉ) → (yᵉ ≤-ℕᵉ zᵉ) →
  (dist-ℕᵉ xᵉ yᵉ) +ℕᵉ (dist-ℕᵉ yᵉ zᵉ) ＝ᵉ dist-ℕᵉ xᵉ zᵉ
triangle-equality-dist-ℕᵉ zero-ℕᵉ zero-ℕᵉ zero-ℕᵉ H1ᵉ H2ᵉ = reflᵉ
triangle-equality-dist-ℕᵉ zero-ℕᵉ zero-ℕᵉ (succ-ℕᵉ zᵉ) starᵉ starᵉ =
  apᵉ succ-ℕᵉ (left-unit-law-add-ℕᵉ zᵉ)
triangle-equality-dist-ℕᵉ zero-ℕᵉ (succ-ℕᵉ yᵉ) (succ-ℕᵉ zᵉ) starᵉ H2ᵉ =
  left-successor-law-add-ℕᵉ yᵉ (dist-ℕᵉ yᵉ zᵉ) ∙ᵉ
  apᵉ succ-ℕᵉ (is-additive-right-inverse-dist-ℕᵉ yᵉ zᵉ H2ᵉ)
triangle-equality-dist-ℕᵉ (succ-ℕᵉ xᵉ) (succ-ℕᵉ yᵉ) (succ-ℕᵉ zᵉ) H1ᵉ H2ᵉ =
  triangle-equality-dist-ℕᵉ xᵉ yᵉ zᵉ H1ᵉ H2ᵉ

cases-dist-ℕᵉ :
  (xᵉ yᵉ zᵉ : ℕᵉ) → UUᵉ lzero
cases-dist-ℕᵉ xᵉ yᵉ zᵉ =
  ( (dist-ℕᵉ xᵉ yᵉ) +ℕᵉ (dist-ℕᵉ yᵉ zᵉ) ＝ᵉ dist-ℕᵉ xᵉ zᵉ) +ᵉ
  ( ( (dist-ℕᵉ yᵉ zᵉ) +ℕᵉ (dist-ℕᵉ xᵉ zᵉ) ＝ᵉ dist-ℕᵉ xᵉ yᵉ) +ᵉ
    ( (dist-ℕᵉ xᵉ zᵉ) +ℕᵉ (dist-ℕᵉ xᵉ yᵉ) ＝ᵉ dist-ℕᵉ yᵉ zᵉ))

is-total-dist-ℕᵉ :
  (xᵉ yᵉ zᵉ : ℕᵉ) → cases-dist-ℕᵉ xᵉ yᵉ zᵉ
is-total-dist-ℕᵉ xᵉ yᵉ zᵉ with order-three-elements-ℕᵉ xᵉ yᵉ zᵉ
is-total-dist-ℕᵉ xᵉ yᵉ zᵉ | inlᵉ (inlᵉ (pairᵉ H1ᵉ H2ᵉ)) =
  inlᵉ (triangle-equality-dist-ℕᵉ xᵉ yᵉ zᵉ H1ᵉ H2ᵉ)
is-total-dist-ℕᵉ xᵉ yᵉ zᵉ | inlᵉ (inrᵉ (pairᵉ H1ᵉ H2ᵉ)) =
  inrᵉ
    ( inlᵉ
      ( ( commutative-add-ℕᵉ (dist-ℕᵉ yᵉ zᵉ) (dist-ℕᵉ xᵉ zᵉ)) ∙ᵉ
        ( ( apᵉ ((dist-ℕᵉ xᵉ zᵉ) +ℕᵉ_) (symmetric-dist-ℕᵉ yᵉ zᵉ)) ∙ᵉ
          ( triangle-equality-dist-ℕᵉ xᵉ zᵉ yᵉ H1ᵉ H2ᵉ))))
is-total-dist-ℕᵉ xᵉ yᵉ zᵉ | inrᵉ (inlᵉ (inlᵉ (pairᵉ H1ᵉ H2ᵉ))) =
  inrᵉ
    ( inlᵉ
      ( ( apᵉ ((dist-ℕᵉ yᵉ zᵉ) +ℕᵉ_) (symmetric-dist-ℕᵉ xᵉ zᵉ)) ∙ᵉ
        ( ( triangle-equality-dist-ℕᵉ yᵉ zᵉ xᵉ H1ᵉ H2ᵉ) ∙ᵉ
          ( symmetric-dist-ℕᵉ yᵉ xᵉ))))
is-total-dist-ℕᵉ xᵉ yᵉ zᵉ | inrᵉ (inlᵉ (inrᵉ (pairᵉ H1ᵉ H2ᵉ))) =
  inrᵉ
    ( inrᵉ
      ( ( apᵉ ((dist-ℕᵉ xᵉ zᵉ) +ℕᵉ_) (symmetric-dist-ℕᵉ xᵉ yᵉ)) ∙ᵉ
        ( ( commutative-add-ℕᵉ (dist-ℕᵉ xᵉ zᵉ) (dist-ℕᵉ yᵉ xᵉ)) ∙ᵉ
          ( triangle-equality-dist-ℕᵉ yᵉ xᵉ zᵉ H1ᵉ H2ᵉ))))
is-total-dist-ℕᵉ xᵉ yᵉ zᵉ | inrᵉ (inrᵉ (inlᵉ (pairᵉ H1ᵉ H2ᵉ))) =
  inrᵉ
    ( inrᵉ
      ( ( apᵉ (_+ℕᵉ (dist-ℕᵉ xᵉ yᵉ)) (symmetric-dist-ℕᵉ xᵉ zᵉ)) ∙ᵉ
        ( ( triangle-equality-dist-ℕᵉ zᵉ xᵉ yᵉ H1ᵉ H2ᵉ) ∙ᵉ
          ( symmetric-dist-ℕᵉ zᵉ yᵉ))))
is-total-dist-ℕᵉ xᵉ yᵉ zᵉ | inrᵉ (inrᵉ (inrᵉ (pairᵉ H1ᵉ H2ᵉ))) =
  inlᵉ
    ( ( ap-add-ℕᵉ (symmetric-dist-ℕᵉ xᵉ yᵉ) (symmetric-dist-ℕᵉ yᵉ zᵉ)) ∙ᵉ
      ( ( commutative-add-ℕᵉ (dist-ℕᵉ yᵉ xᵉ) (dist-ℕᵉ zᵉ yᵉ)) ∙ᵉ
        ( ( triangle-equality-dist-ℕᵉ zᵉ yᵉ xᵉ H1ᵉ H2ᵉ) ∙ᵉ
          ( symmetric-dist-ℕᵉ zᵉ xᵉ))))
```

### If `x ≤ y` then the distance between `x` and `y` is less than `y`

```agda
leq-dist-ℕᵉ :
  (xᵉ yᵉ : ℕᵉ) → xᵉ ≤-ℕᵉ yᵉ → dist-ℕᵉ xᵉ yᵉ ≤-ℕᵉ yᵉ
leq-dist-ℕᵉ zero-ℕᵉ zero-ℕᵉ Hᵉ = refl-leq-ℕᵉ zero-ℕᵉ
leq-dist-ℕᵉ zero-ℕᵉ (succ-ℕᵉ yᵉ) Hᵉ = refl-leq-ℕᵉ yᵉ
leq-dist-ℕᵉ (succ-ℕᵉ xᵉ) (succ-ℕᵉ yᵉ) Hᵉ =
  transitive-leq-ℕᵉ (dist-ℕᵉ xᵉ yᵉ) yᵉ (succ-ℕᵉ yᵉ) (succ-leq-ℕᵉ yᵉ) (leq-dist-ℕᵉ xᵉ yᵉ Hᵉ)
```

### If `x < b` and `y < b`, then `dist-ℕ x y < b`

```agda
strict-upper-bound-dist-ℕᵉ :
  (bᵉ xᵉ yᵉ : ℕᵉ) → le-ℕᵉ xᵉ bᵉ → le-ℕᵉ yᵉ bᵉ → le-ℕᵉ (dist-ℕᵉ xᵉ yᵉ) bᵉ
strict-upper-bound-dist-ℕᵉ (succ-ℕᵉ bᵉ) zero-ℕᵉ yᵉ Hᵉ Kᵉ = Kᵉ
strict-upper-bound-dist-ℕᵉ (succ-ℕᵉ bᵉ) (succ-ℕᵉ xᵉ) zero-ℕᵉ Hᵉ Kᵉ = Hᵉ
strict-upper-bound-dist-ℕᵉ (succ-ℕᵉ bᵉ) (succ-ℕᵉ xᵉ) (succ-ℕᵉ yᵉ) Hᵉ Kᵉ =
  preserves-le-succ-ℕᵉ (dist-ℕᵉ xᵉ yᵉ) bᵉ (strict-upper-bound-dist-ℕᵉ bᵉ xᵉ yᵉ Hᵉ Kᵉ)
```

### If `x < y` then `dist-ℕ x (succ-ℕ y) = succ-ℕ (dist-ℕ x y)`

```agda
right-successor-law-dist-ℕᵉ :
  (xᵉ yᵉ : ℕᵉ) → leq-ℕᵉ xᵉ yᵉ → dist-ℕᵉ xᵉ (succ-ℕᵉ yᵉ) ＝ᵉ succ-ℕᵉ (dist-ℕᵉ xᵉ yᵉ)
right-successor-law-dist-ℕᵉ zero-ℕᵉ zero-ℕᵉ starᵉ = reflᵉ
right-successor-law-dist-ℕᵉ zero-ℕᵉ (succ-ℕᵉ yᵉ) starᵉ = reflᵉ
right-successor-law-dist-ℕᵉ (succ-ℕᵉ xᵉ) (succ-ℕᵉ yᵉ) Hᵉ =
  right-successor-law-dist-ℕᵉ xᵉ yᵉ Hᵉ

left-successor-law-dist-ℕᵉ :
  (xᵉ yᵉ : ℕᵉ) → leq-ℕᵉ yᵉ xᵉ → dist-ℕᵉ (succ-ℕᵉ xᵉ) yᵉ ＝ᵉ succ-ℕᵉ (dist-ℕᵉ xᵉ yᵉ)
left-successor-law-dist-ℕᵉ zero-ℕᵉ zero-ℕᵉ starᵉ = reflᵉ
left-successor-law-dist-ℕᵉ (succ-ℕᵉ xᵉ) zero-ℕᵉ starᵉ = reflᵉ
left-successor-law-dist-ℕᵉ (succ-ℕᵉ xᵉ) (succ-ℕᵉ yᵉ) Hᵉ =
  left-successor-law-dist-ℕᵉ xᵉ yᵉ Hᵉ
```

### `dist-ℕ` is translation invariant

```agda
translation-invariant-dist-ℕᵉ :
  (kᵉ mᵉ nᵉ : ℕᵉ) → dist-ℕᵉ (kᵉ +ℕᵉ mᵉ) (kᵉ +ℕᵉ nᵉ) ＝ᵉ dist-ℕᵉ mᵉ nᵉ
translation-invariant-dist-ℕᵉ zero-ℕᵉ mᵉ nᵉ =
  ap-dist-ℕᵉ (left-unit-law-add-ℕᵉ mᵉ) (left-unit-law-add-ℕᵉ nᵉ)
translation-invariant-dist-ℕᵉ (succ-ℕᵉ kᵉ) mᵉ nᵉ =
  ( ap-dist-ℕᵉ (left-successor-law-add-ℕᵉ kᵉ mᵉ) (left-successor-law-add-ℕᵉ kᵉ nᵉ)) ∙ᵉ
  ( translation-invariant-dist-ℕᵉ kᵉ mᵉ nᵉ)

translation-invariant-dist-ℕ'ᵉ :
  (kᵉ mᵉ nᵉ : ℕᵉ) → dist-ℕᵉ (mᵉ +ℕᵉ kᵉ) (nᵉ +ℕᵉ kᵉ) ＝ᵉ dist-ℕᵉ mᵉ nᵉ
translation-invariant-dist-ℕ'ᵉ kᵉ mᵉ nᵉ =
  ( ap-dist-ℕᵉ (commutative-add-ℕᵉ mᵉ kᵉ) (commutative-add-ℕᵉ nᵉ kᵉ)) ∙ᵉ
  ( translation-invariant-dist-ℕᵉ kᵉ mᵉ nᵉ)
```

### `dist-ℕ` is linear with respect to scalar multiplication

```agda
left-distributive-mul-dist-ℕᵉ :
  (mᵉ nᵉ kᵉ : ℕᵉ) → kᵉ *ℕᵉ (dist-ℕᵉ mᵉ nᵉ) ＝ᵉ dist-ℕᵉ (kᵉ *ℕᵉ mᵉ) (kᵉ *ℕᵉ nᵉ)
left-distributive-mul-dist-ℕᵉ zero-ℕᵉ zero-ℕᵉ zero-ℕᵉ = reflᵉ
left-distributive-mul-dist-ℕᵉ zero-ℕᵉ zero-ℕᵉ (succ-ℕᵉ kᵉ) =
  left-distributive-mul-dist-ℕᵉ zero-ℕᵉ zero-ℕᵉ kᵉ
left-distributive-mul-dist-ℕᵉ zero-ℕᵉ (succ-ℕᵉ nᵉ) zero-ℕᵉ = reflᵉ
left-distributive-mul-dist-ℕᵉ zero-ℕᵉ (succ-ℕᵉ nᵉ) (succ-ℕᵉ kᵉ) =
  apᵉ
    ( dist-ℕ'ᵉ ((succ-ℕᵉ kᵉ) *ℕᵉ (succ-ℕᵉ nᵉ)))
    ( invᵉ (right-zero-law-mul-ℕᵉ (succ-ℕᵉ kᵉ)))
left-distributive-mul-dist-ℕᵉ (succ-ℕᵉ mᵉ) zero-ℕᵉ zero-ℕᵉ = reflᵉ
left-distributive-mul-dist-ℕᵉ (succ-ℕᵉ mᵉ) zero-ℕᵉ (succ-ℕᵉ kᵉ) =
  apᵉ
    ( dist-ℕᵉ ((succ-ℕᵉ kᵉ) *ℕᵉ (succ-ℕᵉ mᵉ)))
    ( invᵉ (right-zero-law-mul-ℕᵉ (succ-ℕᵉ kᵉ)))
left-distributive-mul-dist-ℕᵉ (succ-ℕᵉ mᵉ) (succ-ℕᵉ nᵉ) zero-ℕᵉ = reflᵉ
left-distributive-mul-dist-ℕᵉ (succ-ℕᵉ mᵉ) (succ-ℕᵉ nᵉ) (succ-ℕᵉ kᵉ) =
  invᵉ
    ( ( ap-dist-ℕᵉ
        ( right-successor-law-mul-ℕᵉ (succ-ℕᵉ kᵉ) mᵉ)
        ( right-successor-law-mul-ℕᵉ (succ-ℕᵉ kᵉ) nᵉ)) ∙ᵉ
      ( ( translation-invariant-dist-ℕᵉ
          ( succ-ℕᵉ kᵉ)
          ( (succ-ℕᵉ kᵉ) *ℕᵉ mᵉ)
          ( (succ-ℕᵉ kᵉ) *ℕᵉ nᵉ)) ∙ᵉ
        ( invᵉ (left-distributive-mul-dist-ℕᵉ mᵉ nᵉ (succ-ℕᵉ kᵉ)))))

right-distributive-mul-dist-ℕᵉ :
  (xᵉ yᵉ kᵉ : ℕᵉ) → (dist-ℕᵉ xᵉ yᵉ) *ℕᵉ kᵉ ＝ᵉ dist-ℕᵉ (xᵉ *ℕᵉ kᵉ) (yᵉ *ℕᵉ kᵉ)
right-distributive-mul-dist-ℕᵉ xᵉ yᵉ kᵉ =
  ( commutative-mul-ℕᵉ (dist-ℕᵉ xᵉ yᵉ) kᵉ) ∙ᵉ
  ( ( left-distributive-mul-dist-ℕᵉ xᵉ yᵉ kᵉ) ∙ᵉ
    ( ap-dist-ℕᵉ (commutative-mul-ℕᵉ kᵉ xᵉ) (commutative-mul-ℕᵉ kᵉ yᵉ)))
```