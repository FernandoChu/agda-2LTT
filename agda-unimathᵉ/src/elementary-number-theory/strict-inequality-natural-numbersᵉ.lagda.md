# Strict inequality on the natural numbers

```agda
module elementary-number-theory.strict-inequality-natural-numbersᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbersᵉ
open import elementary-number-theory.inequality-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.cartesian-product-typesᵉ
open import foundation.coproduct-typesᵉ
open import foundation.decidable-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.empty-typesᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-coproduct-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.negated-equalityᵉ
open import foundation.negationᵉ
open import foundation.propositionsᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Definition

### The standard strict inequality on the natural numbers

```agda
le-ℕ-Propᵉ : ℕᵉ → ℕᵉ → Propᵉ lzero
le-ℕ-Propᵉ mᵉ zero-ℕᵉ = empty-Propᵉ
le-ℕ-Propᵉ zero-ℕᵉ (succ-ℕᵉ mᵉ) = unit-Propᵉ
le-ℕ-Propᵉ (succ-ℕᵉ nᵉ) (succ-ℕᵉ mᵉ) = le-ℕ-Propᵉ nᵉ mᵉ

le-ℕᵉ : ℕᵉ → ℕᵉ → UUᵉ lzero
le-ℕᵉ nᵉ mᵉ = type-Propᵉ (le-ℕ-Propᵉ nᵉ mᵉ)

is-prop-le-ℕᵉ : (nᵉ : ℕᵉ) → (mᵉ : ℕᵉ) → is-propᵉ (le-ℕᵉ nᵉ mᵉ)
is-prop-le-ℕᵉ nᵉ mᵉ = is-prop-type-Propᵉ (le-ℕ-Propᵉ nᵉ mᵉ)

infix 30 _<-ℕᵉ_
_<-ℕᵉ_ = le-ℕᵉ
```

## Properties

### Concatenating strict inequalities and equalities

```agda
concatenate-eq-le-eq-ℕᵉ :
  {xᵉ yᵉ zᵉ wᵉ : ℕᵉ} → xᵉ ＝ᵉ yᵉ → le-ℕᵉ yᵉ zᵉ → zᵉ ＝ᵉ wᵉ → le-ℕᵉ xᵉ wᵉ
concatenate-eq-le-eq-ℕᵉ reflᵉ pᵉ reflᵉ = pᵉ

concatenate-eq-le-ℕᵉ :
  {xᵉ yᵉ zᵉ : ℕᵉ} → xᵉ ＝ᵉ yᵉ → le-ℕᵉ yᵉ zᵉ → le-ℕᵉ xᵉ zᵉ
concatenate-eq-le-ℕᵉ reflᵉ pᵉ = pᵉ

concatenate-le-eq-ℕᵉ :
  {xᵉ yᵉ zᵉ : ℕᵉ} → le-ℕᵉ xᵉ yᵉ → yᵉ ＝ᵉ zᵉ → le-ℕᵉ xᵉ zᵉ
concatenate-le-eq-ℕᵉ pᵉ reflᵉ = pᵉ
```

### Strict inequality on the natural numbers is decidable

```agda
is-decidable-le-ℕᵉ :
  (mᵉ nᵉ : ℕᵉ) → is-decidableᵉ (le-ℕᵉ mᵉ nᵉ)
is-decidable-le-ℕᵉ zero-ℕᵉ zero-ℕᵉ = inrᵉ idᵉ
is-decidable-le-ℕᵉ zero-ℕᵉ (succ-ℕᵉ nᵉ) = inlᵉ starᵉ
is-decidable-le-ℕᵉ (succ-ℕᵉ mᵉ) zero-ℕᵉ = inrᵉ idᵉ
is-decidable-le-ℕᵉ (succ-ℕᵉ mᵉ) (succ-ℕᵉ nᵉ) = is-decidable-le-ℕᵉ mᵉ nᵉ
```

### If `m < n` then `n` must be nonzero

```agda
is-nonzero-le-ℕᵉ : (mᵉ nᵉ : ℕᵉ) → le-ℕᵉ mᵉ nᵉ → is-nonzero-ℕᵉ nᵉ
is-nonzero-le-ℕᵉ mᵉ .zero-ℕᵉ () reflᵉ
```

### Any nonzero natural number is strictly greater than `0`

```agda
le-is-nonzero-ℕᵉ : (nᵉ : ℕᵉ) → is-nonzero-ℕᵉ nᵉ → le-ℕᵉ zero-ℕᵉ nᵉ
le-is-nonzero-ℕᵉ zero-ℕᵉ Hᵉ = Hᵉ reflᵉ
le-is-nonzero-ℕᵉ (succ-ℕᵉ nᵉ) Hᵉ = starᵉ
```

### No natural number is strictly less than zero

```agda
contradiction-le-zero-ℕᵉ :
  (mᵉ : ℕᵉ) → (le-ℕᵉ mᵉ zero-ℕᵉ) → emptyᵉ
contradiction-le-zero-ℕᵉ zero-ℕᵉ ()
contradiction-le-zero-ℕᵉ (succ-ℕᵉ mᵉ) ()
```

### No successor is strictly less than one

```agda
contradiction-le-one-ℕᵉ :
  (nᵉ : ℕᵉ) → le-ℕᵉ (succ-ℕᵉ nᵉ) 1 → emptyᵉ
contradiction-le-one-ℕᵉ zero-ℕᵉ ()
contradiction-le-one-ℕᵉ (succ-ℕᵉ nᵉ) ()
```

### The strict inequality on the natural numbers is anti-reflexive

```agda
anti-reflexive-le-ℕᵉ : (nᵉ : ℕᵉ) → ¬ᵉ (nᵉ <-ℕᵉ nᵉ)
anti-reflexive-le-ℕᵉ zero-ℕᵉ ()
anti-reflexive-le-ℕᵉ (succ-ℕᵉ nᵉ) = anti-reflexive-le-ℕᵉ nᵉ
```

### If `x < y` then `x ≠ y`

```agda
neq-le-ℕᵉ : {xᵉ yᵉ : ℕᵉ} → le-ℕᵉ xᵉ yᵉ → xᵉ ≠ᵉ yᵉ
neq-le-ℕᵉ {zero-ℕᵉ} {succ-ℕᵉ yᵉ} Hᵉ = is-nonzero-succ-ℕᵉ yᵉ ∘ᵉ invᵉ
neq-le-ℕᵉ {succ-ℕᵉ xᵉ} {succ-ℕᵉ yᵉ} Hᵉ pᵉ = neq-le-ℕᵉ Hᵉ (is-injective-succ-ℕᵉ pᵉ)
```

### The strict inequality on the natural numbers is antisymmetric

```agda
antisymmetric-le-ℕᵉ : (mᵉ nᵉ : ℕᵉ) → le-ℕᵉ mᵉ nᵉ → le-ℕᵉ nᵉ mᵉ → mᵉ ＝ᵉ nᵉ
antisymmetric-le-ℕᵉ (succ-ℕᵉ mᵉ) (succ-ℕᵉ nᵉ) pᵉ qᵉ =
  apᵉ succ-ℕᵉ (antisymmetric-le-ℕᵉ mᵉ nᵉ pᵉ qᵉ)
```

### The strict inequality on the natural numbers is transitive

```agda
transitive-le-ℕᵉ : (nᵉ mᵉ lᵉ : ℕᵉ) → (le-ℕᵉ nᵉ mᵉ) → (le-ℕᵉ mᵉ lᵉ) → (le-ℕᵉ nᵉ lᵉ)
transitive-le-ℕᵉ zero-ℕᵉ (succ-ℕᵉ mᵉ) (succ-ℕᵉ lᵉ) pᵉ qᵉ = starᵉ
transitive-le-ℕᵉ (succ-ℕᵉ nᵉ) (succ-ℕᵉ mᵉ) (succ-ℕᵉ lᵉ) pᵉ qᵉ =
  transitive-le-ℕᵉ nᵉ mᵉ lᵉ pᵉ qᵉ
```

### A sharper variant of transitivity

```agda
transitive-le-ℕ'ᵉ :
  (kᵉ lᵉ mᵉ : ℕᵉ) → (le-ℕᵉ kᵉ lᵉ) → (le-ℕᵉ lᵉ (succ-ℕᵉ mᵉ)) → le-ℕᵉ kᵉ mᵉ
transitive-le-ℕ'ᵉ zero-ℕᵉ zero-ℕᵉ mᵉ () sᵉ
transitive-le-ℕ'ᵉ (succ-ℕᵉ kᵉ) zero-ℕᵉ mᵉ () sᵉ
transitive-le-ℕ'ᵉ zero-ℕᵉ (succ-ℕᵉ lᵉ) zero-ℕᵉ starᵉ sᵉ =
  ex-falsoᵉ (contradiction-le-one-ℕᵉ lᵉ sᵉ)
transitive-le-ℕ'ᵉ (succ-ℕᵉ kᵉ) (succ-ℕᵉ lᵉ) zero-ℕᵉ tᵉ sᵉ =
  ex-falsoᵉ (contradiction-le-one-ℕᵉ lᵉ sᵉ)
transitive-le-ℕ'ᵉ zero-ℕᵉ (succ-ℕᵉ lᵉ) (succ-ℕᵉ mᵉ) starᵉ sᵉ = starᵉ
transitive-le-ℕ'ᵉ (succ-ℕᵉ kᵉ) (succ-ℕᵉ lᵉ) (succ-ℕᵉ mᵉ) tᵉ sᵉ =
  transitive-le-ℕ'ᵉ kᵉ lᵉ mᵉ tᵉ sᵉ
```

### The strict inequality on the natural numbers is linear

```agda
linear-le-ℕᵉ : (xᵉ yᵉ : ℕᵉ) → (le-ℕᵉ xᵉ yᵉ) +ᵉ ((xᵉ ＝ᵉ yᵉ) +ᵉ (le-ℕᵉ yᵉ xᵉ))
linear-le-ℕᵉ zero-ℕᵉ zero-ℕᵉ = inrᵉ (inlᵉ reflᵉ)
linear-le-ℕᵉ zero-ℕᵉ (succ-ℕᵉ yᵉ) = inlᵉ starᵉ
linear-le-ℕᵉ (succ-ℕᵉ xᵉ) zero-ℕᵉ = inrᵉ (inrᵉ starᵉ)
linear-le-ℕᵉ (succ-ℕᵉ xᵉ) (succ-ℕᵉ yᵉ) =
  map-coproductᵉ idᵉ (map-coproductᵉ (apᵉ succ-ℕᵉ) idᵉ) (linear-le-ℕᵉ xᵉ yᵉ)
```

### `n < m` if and only if there exists a nonzero natural number `l` such that `n + l = m`

```agda
subtraction-le-ℕᵉ :
  (nᵉ mᵉ : ℕᵉ) → le-ℕᵉ nᵉ mᵉ → Σᵉ ℕᵉ (λ lᵉ → (is-nonzero-ℕᵉ lᵉ) ×ᵉ (lᵉ +ℕᵉ nᵉ ＝ᵉ mᵉ))
subtraction-le-ℕᵉ zero-ℕᵉ mᵉ pᵉ = pairᵉ mᵉ (pairᵉ (is-nonzero-le-ℕᵉ zero-ℕᵉ mᵉ pᵉ) reflᵉ)
subtraction-le-ℕᵉ (succ-ℕᵉ nᵉ) (succ-ℕᵉ mᵉ) pᵉ =
  pairᵉ (pr1ᵉ Pᵉ) (pairᵉ (pr1ᵉ (pr2ᵉ Pᵉ)) (apᵉ succ-ℕᵉ (pr2ᵉ (pr2ᵉ Pᵉ))))
  where
  Pᵉ : Σᵉ ℕᵉ (λ l'ᵉ → (is-nonzero-ℕᵉ l'ᵉ) ×ᵉ (l'ᵉ +ℕᵉ nᵉ ＝ᵉ mᵉ))
  Pᵉ = subtraction-le-ℕᵉ nᵉ mᵉ pᵉ

le-subtraction-ℕᵉ : (nᵉ mᵉ lᵉ : ℕᵉ) → is-nonzero-ℕᵉ lᵉ → lᵉ +ℕᵉ nᵉ ＝ᵉ mᵉ → le-ℕᵉ nᵉ mᵉ
le-subtraction-ℕᵉ zero-ℕᵉ mᵉ lᵉ qᵉ pᵉ =
  trᵉ (λ xᵉ → le-ℕᵉ zero-ℕᵉ xᵉ) pᵉ (le-is-nonzero-ℕᵉ lᵉ qᵉ)
le-subtraction-ℕᵉ (succ-ℕᵉ nᵉ) (succ-ℕᵉ mᵉ) lᵉ qᵉ pᵉ =
  le-subtraction-ℕᵉ nᵉ mᵉ lᵉ qᵉ (is-injective-succ-ℕᵉ pᵉ)
```

### Any natural number is strictly less than its successor

```agda
succ-le-ℕᵉ : (nᵉ : ℕᵉ) → le-ℕᵉ nᵉ (succ-ℕᵉ nᵉ)
succ-le-ℕᵉ zero-ℕᵉ = starᵉ
succ-le-ℕᵉ (succ-ℕᵉ nᵉ) = succ-le-ℕᵉ nᵉ
```

### The successor function preserves strict inequality on the right

```agda
preserves-le-succ-ℕᵉ :
  (mᵉ nᵉ : ℕᵉ) → le-ℕᵉ mᵉ nᵉ → le-ℕᵉ mᵉ (succ-ℕᵉ nᵉ)
preserves-le-succ-ℕᵉ mᵉ nᵉ Hᵉ =
  transitive-le-ℕᵉ mᵉ nᵉ (succ-ℕᵉ nᵉ) Hᵉ (succ-le-ℕᵉ nᵉ)
```

### Concatenating strict and nonstrict inequalities

```agda
concatenate-leq-le-ℕᵉ :
  {xᵉ yᵉ zᵉ : ℕᵉ} → xᵉ ≤-ℕᵉ yᵉ → le-ℕᵉ yᵉ zᵉ → le-ℕᵉ xᵉ zᵉ
concatenate-leq-le-ℕᵉ {zero-ℕᵉ} {zero-ℕᵉ} {succ-ℕᵉ zᵉ} Hᵉ Kᵉ = starᵉ
concatenate-leq-le-ℕᵉ {zero-ℕᵉ} {succ-ℕᵉ yᵉ} {succ-ℕᵉ zᵉ} Hᵉ Kᵉ = starᵉ
concatenate-leq-le-ℕᵉ {succ-ℕᵉ xᵉ} {succ-ℕᵉ yᵉ} {succ-ℕᵉ zᵉ} Hᵉ Kᵉ =
  concatenate-leq-le-ℕᵉ {xᵉ} {yᵉ} {zᵉ} Hᵉ Kᵉ

concatenate-le-leq-ℕᵉ :
  {xᵉ yᵉ zᵉ : ℕᵉ} → le-ℕᵉ xᵉ yᵉ → yᵉ ≤-ℕᵉ zᵉ → le-ℕᵉ xᵉ zᵉ
concatenate-le-leq-ℕᵉ {zero-ℕᵉ} {succ-ℕᵉ yᵉ} {succ-ℕᵉ zᵉ} Hᵉ Kᵉ = starᵉ
concatenate-le-leq-ℕᵉ {succ-ℕᵉ xᵉ} {succ-ℕᵉ yᵉ} {succ-ℕᵉ zᵉ} Hᵉ Kᵉ =
  concatenate-le-leq-ℕᵉ {xᵉ} {yᵉ} {zᵉ} Hᵉ Kᵉ
```

### If `m < n` then `n ≰ m`

```agda
contradiction-le-ℕᵉ : (mᵉ nᵉ : ℕᵉ) → le-ℕᵉ mᵉ nᵉ → ¬ᵉ (nᵉ ≤-ℕᵉ mᵉ)
contradiction-le-ℕᵉ zero-ℕᵉ (succ-ℕᵉ nᵉ) Hᵉ Kᵉ = Kᵉ
contradiction-le-ℕᵉ (succ-ℕᵉ mᵉ) (succ-ℕᵉ nᵉ) Hᵉ = contradiction-le-ℕᵉ mᵉ nᵉ Hᵉ
```

### If `n ≤ m` then `m ≮ n`

```agda
contradiction-le-ℕ'ᵉ : (mᵉ nᵉ : ℕᵉ) → nᵉ ≤-ℕᵉ mᵉ → ¬ᵉ (le-ℕᵉ mᵉ nᵉ)
contradiction-le-ℕ'ᵉ mᵉ nᵉ Kᵉ Hᵉ = contradiction-le-ℕᵉ mᵉ nᵉ Hᵉ Kᵉ
```

### If `m ≮ n` then `n ≤ m`

```agda
leq-not-le-ℕᵉ : (mᵉ nᵉ : ℕᵉ) → ¬ᵉ (le-ℕᵉ mᵉ nᵉ) → nᵉ ≤-ℕᵉ mᵉ
leq-not-le-ℕᵉ zero-ℕᵉ zero-ℕᵉ Hᵉ = starᵉ
leq-not-le-ℕᵉ zero-ℕᵉ (succ-ℕᵉ nᵉ) Hᵉ = ex-falsoᵉ (Hᵉ starᵉ)
leq-not-le-ℕᵉ (succ-ℕᵉ mᵉ) zero-ℕᵉ Hᵉ = starᵉ
leq-not-le-ℕᵉ (succ-ℕᵉ mᵉ) (succ-ℕᵉ nᵉ) Hᵉ = leq-not-le-ℕᵉ mᵉ nᵉ Hᵉ
```

### If `x < y` then `x ≤ y`

```agda
leq-le-ℕᵉ :
  (xᵉ yᵉ : ℕᵉ) → le-ℕᵉ xᵉ yᵉ → xᵉ ≤-ℕᵉ yᵉ
leq-le-ℕᵉ zero-ℕᵉ (succ-ℕᵉ yᵉ) Hᵉ = starᵉ
leq-le-ℕᵉ (succ-ℕᵉ xᵉ) (succ-ℕᵉ yᵉ) Hᵉ = leq-le-ℕᵉ xᵉ yᵉ Hᵉ
```

### If `x < y + 1` then `x ≤ y`

```agda
leq-le-succ-ℕᵉ :
  (xᵉ yᵉ : ℕᵉ) → le-ℕᵉ xᵉ (succ-ℕᵉ yᵉ) → xᵉ ≤-ℕᵉ yᵉ
leq-le-succ-ℕᵉ zero-ℕᵉ yᵉ Hᵉ = starᵉ
leq-le-succ-ℕᵉ (succ-ℕᵉ xᵉ) (succ-ℕᵉ yᵉ) Hᵉ = leq-le-succ-ℕᵉ xᵉ yᵉ Hᵉ
```

### If `x < y` then `x + 1 ≤ y`

```agda
leq-succ-le-ℕᵉ :
  (xᵉ yᵉ : ℕᵉ) → le-ℕᵉ xᵉ yᵉ → leq-ℕᵉ (succ-ℕᵉ xᵉ) yᵉ
leq-succ-le-ℕᵉ zero-ℕᵉ (succ-ℕᵉ yᵉ) Hᵉ = starᵉ
leq-succ-le-ℕᵉ (succ-ℕᵉ xᵉ) (succ-ℕᵉ yᵉ) Hᵉ = leq-succ-le-ℕᵉ xᵉ yᵉ Hᵉ
```

### If `x ≤ y` then `x < y + 1`

```agda
le-succ-leq-ℕᵉ :
  (xᵉ yᵉ : ℕᵉ) → leq-ℕᵉ xᵉ yᵉ → le-ℕᵉ xᵉ (succ-ℕᵉ yᵉ)
le-succ-leq-ℕᵉ zero-ℕᵉ zero-ℕᵉ Hᵉ = starᵉ
le-succ-leq-ℕᵉ zero-ℕᵉ (succ-ℕᵉ yᵉ) Hᵉ = starᵉ
le-succ-leq-ℕᵉ (succ-ℕᵉ xᵉ) (succ-ℕᵉ yᵉ) Hᵉ = le-succ-leq-ℕᵉ xᵉ yᵉ Hᵉ
```

### `x ≤ y` if and only if `(x ＝ y) + (x < y)`

```agda
eq-or-le-leq-ℕᵉ :
  (xᵉ yᵉ : ℕᵉ) → leq-ℕᵉ xᵉ yᵉ → ((xᵉ ＝ᵉ yᵉ) +ᵉ (le-ℕᵉ xᵉ yᵉ))
eq-or-le-leq-ℕᵉ zero-ℕᵉ zero-ℕᵉ Hᵉ = inlᵉ reflᵉ
eq-or-le-leq-ℕᵉ zero-ℕᵉ (succ-ℕᵉ yᵉ) Hᵉ = inrᵉ starᵉ
eq-or-le-leq-ℕᵉ (succ-ℕᵉ xᵉ) (succ-ℕᵉ yᵉ) Hᵉ =
  map-coproductᵉ (apᵉ succ-ℕᵉ) idᵉ (eq-or-le-leq-ℕᵉ xᵉ yᵉ Hᵉ)

eq-or-le-leq-ℕ'ᵉ :
  (xᵉ yᵉ : ℕᵉ) → leq-ℕᵉ xᵉ yᵉ → ((yᵉ ＝ᵉ xᵉ) +ᵉ (le-ℕᵉ xᵉ yᵉ))
eq-or-le-leq-ℕ'ᵉ xᵉ yᵉ Hᵉ = map-coproductᵉ invᵉ idᵉ (eq-or-le-leq-ℕᵉ xᵉ yᵉ Hᵉ)

leq-eq-or-le-ℕᵉ :
  (xᵉ yᵉ : ℕᵉ) → ((xᵉ ＝ᵉ yᵉ) +ᵉ (le-ℕᵉ xᵉ yᵉ)) → leq-ℕᵉ xᵉ yᵉ
leq-eq-or-le-ℕᵉ xᵉ .xᵉ (inlᵉ reflᵉ) = refl-leq-ℕᵉ xᵉ
leq-eq-or-le-ℕᵉ xᵉ yᵉ (inrᵉ lᵉ) = leq-le-ℕᵉ xᵉ yᵉ lᵉ
```

### If `x ≤ y` and `x ≠ y` then `x < y`

```agda
le-leq-neq-ℕᵉ : {xᵉ yᵉ : ℕᵉ} → xᵉ ≤-ℕᵉ yᵉ → xᵉ ≠ᵉ yᵉ → le-ℕᵉ xᵉ yᵉ
le-leq-neq-ℕᵉ {zero-ℕᵉ} {zero-ℕᵉ} lᵉ fᵉ = ex-falsoᵉ (fᵉ reflᵉ)
le-leq-neq-ℕᵉ {zero-ℕᵉ} {succ-ℕᵉ yᵉ} lᵉ fᵉ = starᵉ
le-leq-neq-ℕᵉ {succ-ℕᵉ xᵉ} {succ-ℕᵉ yᵉ} lᵉ fᵉ =
  le-leq-neq-ℕᵉ {xᵉ} {yᵉ} lᵉ (λ pᵉ → fᵉ (apᵉ succ-ℕᵉ pᵉ))
```