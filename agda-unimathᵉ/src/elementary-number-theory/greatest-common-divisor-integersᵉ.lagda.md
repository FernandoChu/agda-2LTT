# The greatest common divisor of integers

```agda
module elementary-number-theory.greatest-common-divisor-integersᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.absolute-value-integersᵉ
open import elementary-number-theory.addition-natural-numbersᵉ
open import elementary-number-theory.divisibility-integersᵉ
open import elementary-number-theory.equality-integersᵉ
open import elementary-number-theory.greatest-common-divisor-natural-numbersᵉ
open import elementary-number-theory.integersᵉ
open import elementary-number-theory.natural-numbersᵉ
open import elementary-number-theory.nonnegative-integersᵉ
open import elementary-number-theory.positive-and-negative-integersᵉ
open import elementary-number-theory.positive-integersᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.cartesian-product-typesᵉ
open import foundation.coproduct-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.empty-typesᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-cartesian-product-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Definition

### The predicate of being a greatest common divisor

```agda
is-common-divisor-ℤᵉ : ℤᵉ → ℤᵉ → ℤᵉ → UUᵉ lzero
is-common-divisor-ℤᵉ xᵉ yᵉ dᵉ = (div-ℤᵉ dᵉ xᵉ) ×ᵉ (div-ℤᵉ dᵉ yᵉ)

is-gcd-ℤᵉ : ℤᵉ → ℤᵉ → ℤᵉ → UUᵉ lzero
is-gcd-ℤᵉ xᵉ yᵉ dᵉ =
  is-nonnegative-ℤᵉ dᵉ ×ᵉ ((kᵉ : ℤᵉ) → is-common-divisor-ℤᵉ xᵉ yᵉ kᵉ ↔ᵉ div-ℤᵉ kᵉ dᵉ)
```

### The greatest common divisor of two integers

```agda
nat-gcd-ℤᵉ : ℤᵉ → ℤᵉ → ℕᵉ
nat-gcd-ℤᵉ xᵉ yᵉ = gcd-ℕᵉ (abs-ℤᵉ xᵉ) (abs-ℤᵉ yᵉ)

gcd-ℤᵉ : ℤᵉ → ℤᵉ → ℤᵉ
gcd-ℤᵉ xᵉ yᵉ = int-ℕᵉ (nat-gcd-ℤᵉ xᵉ yᵉ)
```

## Properties

### The greatest common divisor is invariant under negatives

```agda
module _
  (xᵉ yᵉ : ℤᵉ)
  where

  preserves-gcd-left-neg-ℤᵉ : gcd-ℤᵉ (neg-ℤᵉ xᵉ) yᵉ ＝ᵉ gcd-ℤᵉ xᵉ yᵉ
  preserves-gcd-left-neg-ℤᵉ =
    apᵉ (int-ℕᵉ ∘ᵉ (λ zᵉ → gcd-ℕᵉ zᵉ (abs-ℤᵉ yᵉ))) (abs-neg-ℤᵉ xᵉ)

  preserves-gcd-right-neg-ℤᵉ : gcd-ℤᵉ xᵉ (neg-ℤᵉ yᵉ) ＝ᵉ gcd-ℤᵉ xᵉ yᵉ
  preserves-gcd-right-neg-ℤᵉ =
    apᵉ (int-ℕᵉ ∘ᵉ (gcd-ℕᵉ (abs-ℤᵉ xᵉ))) (abs-neg-ℤᵉ yᵉ)
```

### A natural number `d` is a common divisor of two natural numbers `x` and `y` if and only if `int-ℕ d` is a common divisor of `int-ℕ x` and `ind-ℕ y`

```agda
is-common-divisor-int-is-common-divisor-ℕᵉ :
  {xᵉ yᵉ dᵉ : ℕᵉ} →
  is-common-divisor-ℕᵉ xᵉ yᵉ dᵉ → is-common-divisor-ℤᵉ (int-ℕᵉ xᵉ) (int-ℕᵉ yᵉ) (int-ℕᵉ dᵉ)
is-common-divisor-int-is-common-divisor-ℕᵉ =
  map-productᵉ div-int-div-ℕᵉ div-int-div-ℕᵉ

is-common-divisor-is-common-divisor-int-ℕᵉ :
  {xᵉ yᵉ dᵉ : ℕᵉ} →
  is-common-divisor-ℤᵉ (int-ℕᵉ xᵉ) (int-ℕᵉ yᵉ) (int-ℕᵉ dᵉ) → is-common-divisor-ℕᵉ xᵉ yᵉ dᵉ
is-common-divisor-is-common-divisor-int-ℕᵉ {xᵉ} {yᵉ} {dᵉ} =
  map-productᵉ div-div-int-ℕᵉ div-div-int-ℕᵉ
```

### If `ux ＝ x'` and `vy ＝ y'` for two units `u` and `v`, then `d` is a common divisor of `x` and `y` if and only if `d` is a common divisor of `x'` and `y'`

```agda
is-common-divisor-sim-unit-ℤᵉ :
  {xᵉ x'ᵉ yᵉ y'ᵉ dᵉ d'ᵉ : ℤᵉ} → sim-unit-ℤᵉ xᵉ x'ᵉ → sim-unit-ℤᵉ yᵉ y'ᵉ → sim-unit-ℤᵉ dᵉ d'ᵉ →
  is-common-divisor-ℤᵉ xᵉ yᵉ dᵉ → is-common-divisor-ℤᵉ x'ᵉ y'ᵉ d'ᵉ
is-common-divisor-sim-unit-ℤᵉ Hᵉ Kᵉ Lᵉ =
  map-productᵉ (div-sim-unit-ℤᵉ Lᵉ Hᵉ) (div-sim-unit-ℤᵉ Lᵉ Kᵉ)
```

### If `ux ＝ x'` and `vy ＝ y'` for two units `u` and `v`, then `d` is a greatest common divisor of `x` and `y` if and only if `c` is a greatest common divisor of `x'` and `y'`

```agda
is-gcd-sim-unit-ℤᵉ :
  {xᵉ x'ᵉ yᵉ y'ᵉ dᵉ : ℤᵉ} →
  sim-unit-ℤᵉ xᵉ x'ᵉ → sim-unit-ℤᵉ yᵉ y'ᵉ →
  is-gcd-ℤᵉ xᵉ yᵉ dᵉ → is-gcd-ℤᵉ x'ᵉ y'ᵉ dᵉ
pr1ᵉ (is-gcd-sim-unit-ℤᵉ Hᵉ Kᵉ (pairᵉ xᵉ _)) = xᵉ
pr1ᵉ (pr2ᵉ (is-gcd-sim-unit-ℤᵉ Hᵉ Kᵉ (pairᵉ _ Gᵉ)) kᵉ) =
  ( pr1ᵉ (Gᵉ kᵉ)) ∘ᵉ
  ( is-common-divisor-sim-unit-ℤᵉ
    ( symmetric-sim-unit-ℤᵉ _ _ Hᵉ)
    ( symmetric-sim-unit-ℤᵉ _ _ Kᵉ)
    ( refl-sim-unit-ℤᵉ kᵉ))
pr2ᵉ (pr2ᵉ (is-gcd-sim-unit-ℤᵉ Hᵉ Kᵉ (pairᵉ _ Gᵉ)) kᵉ) =
  ( is-common-divisor-sim-unit-ℤᵉ Hᵉ Kᵉ (refl-sim-unit-ℤᵉ kᵉ)) ∘ᵉ
  ( pr2ᵉ (Gᵉ kᵉ))
```

### An integer `d` is a common divisor of `x` and `y` if and only if `|d|` is a common divisor of `x` and `y`

```agda
is-common-divisor-int-abs-is-common-divisor-ℤᵉ :
  {xᵉ yᵉ dᵉ : ℤᵉ} →
  is-common-divisor-ℤᵉ xᵉ yᵉ dᵉ → is-common-divisor-ℤᵉ xᵉ yᵉ (int-abs-ℤᵉ dᵉ)
is-common-divisor-int-abs-is-common-divisor-ℤᵉ =
  map-productᵉ div-int-abs-div-ℤᵉ div-int-abs-div-ℤᵉ

is-common-divisor-is-common-divisor-int-abs-ℤᵉ :
  {xᵉ yᵉ dᵉ : ℤᵉ} →
  is-common-divisor-ℤᵉ xᵉ yᵉ (int-abs-ℤᵉ dᵉ) → is-common-divisor-ℤᵉ xᵉ yᵉ dᵉ
is-common-divisor-is-common-divisor-int-abs-ℤᵉ =
  map-productᵉ div-div-int-abs-ℤᵉ div-div-int-abs-ℤᵉ

is-common-divisor-is-gcd-ℤᵉ :
  (aᵉ bᵉ dᵉ : ℤᵉ) → is-gcd-ℤᵉ aᵉ bᵉ dᵉ → is-common-divisor-ℤᵉ aᵉ bᵉ dᵉ
is-common-divisor-is-gcd-ℤᵉ aᵉ bᵉ dᵉ Hᵉ = pr2ᵉ (pr2ᵉ Hᵉ dᵉ) (refl-div-ℤᵉ dᵉ)
```

### A natural number `d` is a greatest common divisor of two natural numbers `x` and `y` if and only if `int-ℕ d` is a greatest common divisor of `int-ℕ x` and `int-ℕ y`

```agda
is-gcd-int-is-gcd-ℕᵉ :
  {xᵉ yᵉ dᵉ : ℕᵉ} → is-gcd-ℕᵉ xᵉ yᵉ dᵉ → is-gcd-ℤᵉ (int-ℕᵉ xᵉ) (int-ℕᵉ yᵉ) (int-ℕᵉ dᵉ)
pr1ᵉ (is-gcd-int-is-gcd-ℕᵉ {xᵉ} {yᵉ} {dᵉ} Hᵉ) = is-nonnegative-int-ℕᵉ dᵉ
pr1ᵉ (pr2ᵉ (is-gcd-int-is-gcd-ℕᵉ {xᵉ} {yᵉ} {dᵉ} Hᵉ) kᵉ) =
  ( ( ( ( div-div-int-abs-ℤᵉ) ∘ᵉ
        ( div-int-div-ℕᵉ)) ∘ᵉ
      ( pr1ᵉ (Hᵉ (abs-ℤᵉ kᵉ)))) ∘ᵉ
    ( is-common-divisor-is-common-divisor-int-ℕᵉ)) ∘ᵉ
  ( is-common-divisor-int-abs-is-common-divisor-ℤᵉ)
pr2ᵉ (pr2ᵉ (is-gcd-int-is-gcd-ℕᵉ {xᵉ} {yᵉ} {dᵉ} Hᵉ) kᵉ) =
  ( ( ( ( is-common-divisor-is-common-divisor-int-abs-ℤᵉ) ∘ᵉ
        ( is-common-divisor-int-is-common-divisor-ℕᵉ)) ∘ᵉ
      ( pr2ᵉ (Hᵉ (abs-ℤᵉ kᵉ)))) ∘ᵉ
    ( div-div-int-ℕᵉ)) ∘ᵉ
  ( div-int-abs-div-ℤᵉ)

is-gcd-is-gcd-int-ℕᵉ :
  {xᵉ yᵉ dᵉ : ℕᵉ} → is-gcd-ℤᵉ (int-ℕᵉ xᵉ) (int-ℕᵉ yᵉ) (int-ℕᵉ dᵉ) → is-gcd-ℕᵉ xᵉ yᵉ dᵉ
pr1ᵉ (is-gcd-is-gcd-int-ℕᵉ {xᵉ} {yᵉ} {dᵉ} Hᵉ kᵉ) =
  ( ( div-div-int-ℕᵉ) ∘ᵉ
    ( pr1ᵉ (pr2ᵉ Hᵉ (int-ℕᵉ kᵉ)))) ∘ᵉ
  ( is-common-divisor-int-is-common-divisor-ℕᵉ)
pr2ᵉ (is-gcd-is-gcd-int-ℕᵉ {xᵉ} {yᵉ} {dᵉ} Hᵉ kᵉ) =
  ( ( is-common-divisor-is-common-divisor-int-ℕᵉ) ∘ᵉ
    ( pr2ᵉ (pr2ᵉ Hᵉ (int-ℕᵉ kᵉ)))) ∘ᵉ
  ( div-int-div-ℕᵉ)
```

### `gcd-ℤ x y` is a greatest common divisor of `x` and `y`

```agda
is-nonnegative-gcd-ℤᵉ : (xᵉ yᵉ : ℤᵉ) → is-nonnegative-ℤᵉ (gcd-ℤᵉ xᵉ yᵉ)
is-nonnegative-gcd-ℤᵉ xᵉ yᵉ = is-nonnegative-int-ℕᵉ (nat-gcd-ℤᵉ xᵉ yᵉ)

gcd-nonnegative-ℤᵉ : ℤᵉ → ℤᵉ → nonnegative-ℤᵉ
pr1ᵉ (gcd-nonnegative-ℤᵉ xᵉ yᵉ) = gcd-ℤᵉ xᵉ yᵉ
pr2ᵉ (gcd-nonnegative-ℤᵉ xᵉ yᵉ) = is-nonnegative-gcd-ℤᵉ xᵉ yᵉ

is-gcd-gcd-ℤᵉ : (xᵉ yᵉ : ℤᵉ) → is-gcd-ℤᵉ xᵉ yᵉ (gcd-ℤᵉ xᵉ yᵉ)
pr1ᵉ (is-gcd-gcd-ℤᵉ xᵉ yᵉ) = is-nonnegative-gcd-ℤᵉ xᵉ yᵉ
pr1ᵉ (pr2ᵉ (is-gcd-gcd-ℤᵉ xᵉ yᵉ) kᵉ) =
  ( ( ( ( ( div-sim-unit-ℤᵉ
            ( sim-unit-abs-ℤᵉ kᵉ)
            ( refl-sim-unit-ℤᵉ (gcd-ℤᵉ xᵉ yᵉ))) ∘ᵉ
          ( div-int-div-ℕᵉ)) ∘ᵉ
        ( pr1ᵉ (is-gcd-gcd-ℕᵉ (abs-ℤᵉ xᵉ) (abs-ℤᵉ yᵉ) (abs-ℤᵉ kᵉ)))) ∘ᵉ
      ( is-common-divisor-is-common-divisor-int-ℕᵉ)) ∘ᵉ
    ( is-common-divisor-int-abs-is-common-divisor-ℤᵉ)) ∘ᵉ
  ( is-common-divisor-sim-unit-ℤᵉ
    ( symmetric-sim-unit-ℤᵉ (int-abs-ℤᵉ xᵉ) xᵉ (sim-unit-abs-ℤᵉ xᵉ))
    ( symmetric-sim-unit-ℤᵉ (int-abs-ℤᵉ yᵉ) yᵉ (sim-unit-abs-ℤᵉ yᵉ))
    ( refl-sim-unit-ℤᵉ kᵉ))
pr2ᵉ (pr2ᵉ (is-gcd-gcd-ℤᵉ xᵉ yᵉ) kᵉ) =
  ( ( ( ( ( is-common-divisor-sim-unit-ℤᵉ
            ( sim-unit-abs-ℤᵉ xᵉ)
            ( sim-unit-abs-ℤᵉ yᵉ)
            ( refl-sim-unit-ℤᵉ kᵉ)) ∘ᵉ
          ( is-common-divisor-is-common-divisor-int-abs-ℤᵉ)) ∘ᵉ
        ( is-common-divisor-int-is-common-divisor-ℕᵉ)) ∘ᵉ
      ( pr2ᵉ (is-gcd-gcd-ℕᵉ (abs-ℤᵉ xᵉ) (abs-ℤᵉ yᵉ) (abs-ℤᵉ kᵉ)))) ∘ᵉ
    ( div-div-int-ℕᵉ)) ∘ᵉ
  ( div-sim-unit-ℤᵉ
    ( symmetric-sim-unit-ℤᵉ (int-abs-ℤᵉ kᵉ) kᵉ (sim-unit-abs-ℤᵉ kᵉ))
    ( refl-sim-unit-ℤᵉ (gcd-ℤᵉ xᵉ yᵉ)))
```

### The gcd in `ℕ` of `x` and `y` is equal to the gcd in `ℤ` of `int-ℕ x` and `int-ℕ y`

```agda
eq-gcd-gcd-int-ℕᵉ :
  (xᵉ yᵉ : ℕᵉ) → gcd-ℤᵉ (int-ℕᵉ xᵉ) (int-ℕᵉ yᵉ) ＝ᵉ int-ℕᵉ (gcd-ℕᵉ xᵉ yᵉ)
eq-gcd-gcd-int-ℕᵉ xᵉ yᵉ =
  ( ( apᵉ
      ( λ xᵉ → int-ℕᵉ (gcd-ℕᵉ xᵉ (abs-ℤᵉ (int-ℕᵉ yᵉ))))
      ( abs-int-ℕᵉ xᵉ)) ∙ᵉ
    ( apᵉ
      ( λ yᵉ → int-ℕᵉ (gcd-ℕᵉ xᵉ yᵉ))
      ( abs-int-ℕᵉ yᵉ)))
```

### The gcd of `x` and `y` divides both `x` and `y`

```agda
is-common-divisor-gcd-ℤᵉ :
  (xᵉ yᵉ : ℤᵉ) → is-common-divisor-ℤᵉ xᵉ yᵉ (gcd-ℤᵉ xᵉ yᵉ)
is-common-divisor-gcd-ℤᵉ xᵉ yᵉ =
  pr2ᵉ (pr2ᵉ (is-gcd-gcd-ℤᵉ xᵉ yᵉ) (gcd-ℤᵉ xᵉ yᵉ)) (refl-div-ℤᵉ (gcd-ℤᵉ xᵉ yᵉ))

div-left-gcd-ℤᵉ : (xᵉ yᵉ : ℤᵉ) → div-ℤᵉ (gcd-ℤᵉ xᵉ yᵉ) xᵉ
div-left-gcd-ℤᵉ xᵉ yᵉ = pr1ᵉ (is-common-divisor-gcd-ℤᵉ xᵉ yᵉ)

div-right-gcd-ℤᵉ : (xᵉ yᵉ : ℤᵉ) → div-ℤᵉ (gcd-ℤᵉ xᵉ yᵉ) yᵉ
div-right-gcd-ℤᵉ xᵉ yᵉ = pr2ᵉ (is-common-divisor-gcd-ℤᵉ xᵉ yᵉ)
```

### Any common divisor of `x` and `y` divides the greatest common divisor

```agda
div-gcd-is-common-divisor-ℤᵉ :
  (xᵉ yᵉ kᵉ : ℤᵉ) → is-common-divisor-ℤᵉ xᵉ yᵉ kᵉ → div-ℤᵉ kᵉ (gcd-ℤᵉ xᵉ yᵉ)
div-gcd-is-common-divisor-ℤᵉ xᵉ yᵉ kᵉ Hᵉ =
  pr1ᵉ (pr2ᵉ (is-gcd-gcd-ℤᵉ xᵉ yᵉ) kᵉ) Hᵉ
```

### If either `x` or `y` is a positive integer, then `gcd-ℤ x y` is positive

```agda
is-positive-gcd-is-positive-left-ℤᵉ :
  (xᵉ yᵉ : ℤᵉ) → is-positive-ℤᵉ xᵉ → is-positive-ℤᵉ (gcd-ℤᵉ xᵉ yᵉ)
is-positive-gcd-is-positive-left-ℤᵉ xᵉ yᵉ Hᵉ =
  is-positive-int-is-nonzero-ℕᵉ
    ( gcd-ℕᵉ (abs-ℤᵉ xᵉ) (abs-ℤᵉ yᵉ))
    ( is-nonzero-gcd-ℕᵉ
      ( abs-ℤᵉ xᵉ)
      ( abs-ℤᵉ yᵉ)
      ( λ pᵉ → is-nonzero-abs-ℤᵉ xᵉ Hᵉ (fᵉ pᵉ)))
  where
  fᵉ : is-zero-ℕᵉ ((abs-ℤᵉ xᵉ) +ℕᵉ (abs-ℤᵉ yᵉ)) → is-zero-ℕᵉ (abs-ℤᵉ xᵉ)
  fᵉ = is-zero-left-is-zero-add-ℕᵉ (abs-ℤᵉ xᵉ) (abs-ℤᵉ yᵉ)

is-positive-gcd-is-positive-right-ℤᵉ :
  (xᵉ yᵉ : ℤᵉ) → is-positive-ℤᵉ yᵉ → is-positive-ℤᵉ (gcd-ℤᵉ xᵉ yᵉ)
is-positive-gcd-is-positive-right-ℤᵉ xᵉ yᵉ Hᵉ =
  is-positive-int-is-nonzero-ℕᵉ
    ( gcd-ℕᵉ (abs-ℤᵉ xᵉ) (abs-ℤᵉ yᵉ))
    ( is-nonzero-gcd-ℕᵉ
      ( abs-ℤᵉ xᵉ)
      ( abs-ℤᵉ yᵉ)
      ( λ pᵉ → is-nonzero-abs-ℤᵉ yᵉ Hᵉ (fᵉ pᵉ)))
  where
  fᵉ : is-zero-ℕᵉ ((abs-ℤᵉ xᵉ) +ℕᵉ (abs-ℤᵉ yᵉ)) → is-zero-ℕᵉ (abs-ℤᵉ yᵉ)
  fᵉ = is-zero-right-is-zero-add-ℕᵉ (abs-ℤᵉ xᵉ) (abs-ℤᵉ yᵉ)

is-positive-gcd-ℤᵉ :
  (xᵉ yᵉ : ℤᵉ) → (is-positive-ℤᵉ xᵉ) +ᵉ (is-positive-ℤᵉ yᵉ) →
  is-positive-ℤᵉ (gcd-ℤᵉ xᵉ yᵉ)
is-positive-gcd-ℤᵉ xᵉ yᵉ (inlᵉ Hᵉ) = is-positive-gcd-is-positive-left-ℤᵉ xᵉ yᵉ Hᵉ
is-positive-gcd-ℤᵉ xᵉ yᵉ (inrᵉ Hᵉ) = is-positive-gcd-is-positive-right-ℤᵉ xᵉ yᵉ Hᵉ
```

### `gcd-ℤ a b` is zero if and only if both `a` and `b` are zero

```agda
is-zero-gcd-ℤᵉ :
  (aᵉ bᵉ : ℤᵉ) → is-zero-ℤᵉ aᵉ → is-zero-ℤᵉ bᵉ → is-zero-ℤᵉ (gcd-ℤᵉ aᵉ bᵉ)
is-zero-gcd-ℤᵉ zero-ℤᵉ zero-ℤᵉ reflᵉ reflᵉ =
  apᵉ int-ℕᵉ is-zero-gcd-zero-zero-ℕᵉ

is-zero-left-is-zero-gcd-ℤᵉ :
  (aᵉ bᵉ : ℤᵉ) → is-zero-ℤᵉ (gcd-ℤᵉ aᵉ bᵉ) → is-zero-ℤᵉ aᵉ
is-zero-left-is-zero-gcd-ℤᵉ aᵉ bᵉ =
  is-zero-is-zero-div-ℤᵉ aᵉ (gcd-ℤᵉ aᵉ bᵉ) (div-left-gcd-ℤᵉ aᵉ bᵉ)

is-zero-right-is-zero-gcd-ℤᵉ :
  (aᵉ bᵉ : ℤᵉ) → is-zero-ℤᵉ (gcd-ℤᵉ aᵉ bᵉ) → is-zero-ℤᵉ bᵉ
is-zero-right-is-zero-gcd-ℤᵉ aᵉ bᵉ =
  is-zero-is-zero-div-ℤᵉ bᵉ (gcd-ℤᵉ aᵉ bᵉ) (div-right-gcd-ℤᵉ aᵉ bᵉ)
```

### `gcd-ℤ` is commutative

```agda
is-commutative-gcd-ℤᵉ : (xᵉ yᵉ : ℤᵉ) → gcd-ℤᵉ xᵉ yᵉ ＝ᵉ gcd-ℤᵉ yᵉ xᵉ
is-commutative-gcd-ℤᵉ xᵉ yᵉ =
  apᵉ int-ℕᵉ (is-commutative-gcd-ℕᵉ (abs-ℤᵉ xᵉ) (abs-ℤᵉ yᵉ))
```

### `gcd-ℕ 1 b ＝ 1`

```agda
is-one-is-gcd-one-ℤᵉ : {bᵉ xᵉ : ℤᵉ} → is-gcd-ℤᵉ one-ℤᵉ bᵉ xᵉ → is-one-ℤᵉ xᵉ
is-one-is-gcd-one-ℤᵉ {bᵉ} {xᵉ} Hᵉ with
  ( is-one-or-neg-one-is-unit-ℤᵉ xᵉ
    ( pr1ᵉ (is-common-divisor-is-gcd-ℤᵉ one-ℤᵉ bᵉ xᵉ Hᵉ)))
... | inlᵉ pᵉ = pᵉ
... | inrᵉ pᵉ = ex-falsoᵉ (trᵉ is-nonnegative-ℤᵉ pᵉ (pr1ᵉ Hᵉ))

is-one-gcd-one-ℤᵉ : (bᵉ : ℤᵉ) → is-one-ℤᵉ (gcd-ℤᵉ one-ℤᵉ bᵉ)
is-one-gcd-one-ℤᵉ bᵉ = is-one-is-gcd-one-ℤᵉ (is-gcd-gcd-ℤᵉ one-ℤᵉ bᵉ)
```

### `gcd-ℤ a 1 ＝ 1`

```agda
is-one-is-gcd-one-ℤ'ᵉ : {aᵉ xᵉ : ℤᵉ} → is-gcd-ℤᵉ aᵉ one-ℤᵉ xᵉ → is-one-ℤᵉ xᵉ
is-one-is-gcd-one-ℤ'ᵉ {aᵉ} {xᵉ} Hᵉ with
  ( is-one-or-neg-one-is-unit-ℤᵉ xᵉ
    ( pr2ᵉ (is-common-divisor-is-gcd-ℤᵉ aᵉ one-ℤᵉ xᵉ Hᵉ)))
... | inlᵉ pᵉ = pᵉ
... | inrᵉ pᵉ = ex-falsoᵉ (trᵉ is-nonnegative-ℤᵉ pᵉ (pr1ᵉ Hᵉ))

is-one-gcd-one-ℤ'ᵉ : (aᵉ : ℤᵉ) → is-one-ℤᵉ (gcd-ℤᵉ aᵉ one-ℤᵉ)
is-one-gcd-one-ℤ'ᵉ aᵉ = is-one-is-gcd-one-ℤ'ᵉ (is-gcd-gcd-ℤᵉ aᵉ one-ℤᵉ)
```

### `gcd-ℤ 0 b ＝ abs-ℤ b`

```agda
is-sim-id-is-gcd-zero-ℤᵉ : {bᵉ xᵉ : ℤᵉ} → gcd-ℤᵉ zero-ℤᵉ bᵉ ＝ᵉ xᵉ → sim-unit-ℤᵉ xᵉ bᵉ
is-sim-id-is-gcd-zero-ℤᵉ {bᵉ} {xᵉ} Hᵉ = antisymmetric-div-ℤᵉ xᵉ bᵉ
  (pr2ᵉ (is-common-divisor-is-gcd-ℤᵉ zero-ℤᵉ bᵉ xᵉ
    (trᵉ (λ tᵉ → is-gcd-ℤᵉ zero-ℤᵉ bᵉ tᵉ) Hᵉ (
      is-gcd-gcd-ℤᵉ zero-ℤᵉ bᵉ))))
  (trᵉ (λ tᵉ → div-ℤᵉ bᵉ tᵉ) Hᵉ
    (div-gcd-is-common-divisor-ℤᵉ zero-ℤᵉ bᵉ bᵉ
      (pair'ᵉ (div-zero-ℤᵉ bᵉ) (refl-div-ℤᵉ bᵉ))))

is-id-is-gcd-zero-ℤᵉ : {bᵉ xᵉ : ℤᵉ} → gcd-ℤᵉ zero-ℤᵉ bᵉ ＝ᵉ xᵉ → xᵉ ＝ᵉ int-ℕᵉ (abs-ℤᵉ bᵉ)
is-id-is-gcd-zero-ℤᵉ {inlᵉ bᵉ} {xᵉ} Hᵉ
  with (is-plus-or-minus-sim-unit-ℤᵉ (is-sim-id-is-gcd-zero-ℤᵉ {inlᵉ bᵉ} {xᵉ} Hᵉ))
... | inlᵉ pᵉ =
  ex-falsoᵉ
    ( Eq-eq-ℤᵉ
      ( invᵉ (pr2ᵉ (lemᵉ (gcd-ℤᵉ zero-ℤᵉ (inlᵉ bᵉ)) gcd-is-nonnegᵉ)) ∙ᵉ (Hᵉ ∙ᵉ pᵉ)))
  where
  gcd-is-nonnegᵉ : is-nonnegative-ℤᵉ (gcd-ℤᵉ zero-ℤᵉ (inlᵉ bᵉ))
  gcd-is-nonnegᵉ = is-nonnegative-int-ℕᵉ (gcd-ℕᵉ 0 (succ-ℕᵉ bᵉ))
  lemᵉ : (yᵉ : ℤᵉ) → is-nonnegative-ℤᵉ yᵉ → Σᵉ (unitᵉ +ᵉ ℕᵉ) (λ zᵉ → yᵉ ＝ᵉ inrᵉ zᵉ)
  lemᵉ (inrᵉ zᵉ) Hᵉ = pairᵉ zᵉ reflᵉ
... | inrᵉ pᵉ = invᵉ (neg-neg-ℤᵉ xᵉ) ∙ᵉ apᵉ neg-ℤᵉ pᵉ
is-id-is-gcd-zero-ℤᵉ {inrᵉ (inlᵉ starᵉ)} {xᵉ} Hᵉ =
  invᵉ Hᵉ ∙ᵉ is-zero-gcd-ℤᵉ zero-ℤᵉ zero-ℤᵉ reflᵉ reflᵉ
is-id-is-gcd-zero-ℤᵉ {inrᵉ (inrᵉ bᵉ)} {xᵉ} Hᵉ
  with
  is-plus-or-minus-sim-unit-ℤᵉ (is-sim-id-is-gcd-zero-ℤᵉ {inrᵉ (inrᵉ bᵉ)} {xᵉ} Hᵉ)
... | inlᵉ pᵉ = pᵉ
... | inrᵉ pᵉ =
  ex-falsoᵉ
    ( Eq-eq-ℤᵉ
      ( ( invᵉ (pr2ᵉ (lemᵉ (gcd-ℤᵉ zero-ℤᵉ (inlᵉ bᵉ)) gcd-is-nonnegᵉ))) ∙ᵉ
        ( Hᵉ ∙ᵉ (invᵉ (neg-neg-ℤᵉ xᵉ) ∙ᵉ apᵉ neg-ℤᵉ pᵉ))))
  where
  gcd-is-nonnegᵉ : is-nonnegative-ℤᵉ (gcd-ℤᵉ zero-ℤᵉ (inlᵉ bᵉ))
  gcd-is-nonnegᵉ = is-nonnegative-int-ℕᵉ (gcd-ℕᵉ 0 (succ-ℕᵉ bᵉ))
  lemᵉ : (yᵉ : ℤᵉ) → is-nonnegative-ℤᵉ yᵉ → Σᵉ (unitᵉ +ᵉ ℕᵉ) (λ zᵉ → yᵉ ＝ᵉ inrᵉ zᵉ)
  lemᵉ (inrᵉ zᵉ) Hᵉ = pairᵉ zᵉ reflᵉ
```

### `gcd-ℤ a 0 ＝ abs-ℤ a`

```agda
is-sim-id-is-gcd-zero-ℤ'ᵉ : {aᵉ xᵉ : ℤᵉ} → gcd-ℤᵉ aᵉ zero-ℤᵉ ＝ᵉ xᵉ → sim-unit-ℤᵉ xᵉ aᵉ
is-sim-id-is-gcd-zero-ℤ'ᵉ {aᵉ} {xᵉ} Hᵉ = is-sim-id-is-gcd-zero-ℤᵉ {aᵉ} {xᵉ}
  ((is-commutative-gcd-ℤᵉ zero-ℤᵉ aᵉ) ∙ᵉ Hᵉ)

is-id-is-gcd-zero-ℤ'ᵉ : {aᵉ xᵉ : ℤᵉ} → gcd-ℤᵉ aᵉ zero-ℤᵉ ＝ᵉ xᵉ → xᵉ ＝ᵉ int-ℕᵉ (abs-ℤᵉ aᵉ)
is-id-is-gcd-zero-ℤ'ᵉ {aᵉ} {xᵉ} Hᵉ =
  is-id-is-gcd-zero-ℤᵉ {aᵉ} {xᵉ} (is-commutative-gcd-ℤᵉ zero-ℤᵉ aᵉ ∙ᵉ Hᵉ)
```