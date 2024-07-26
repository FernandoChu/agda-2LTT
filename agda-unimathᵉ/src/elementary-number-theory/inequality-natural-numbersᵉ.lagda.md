# Inequality of natural numbers

```agda
module elementary-number-theory.inequality-natural-numbersᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbersᵉ
open import elementary-number-theory.multiplication-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.binary-relationsᵉ
open import foundation.cartesian-product-typesᵉ
open import foundation.coproduct-typesᵉ
open import foundation.decidable-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.empty-typesᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-coproduct-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.negationᵉ
open import foundation.propositionsᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import order-theory.posetsᵉ
open import order-theory.preordersᵉ
```

</details>

## Idea

Theᵉ relationᵉ `≤`ᵉ onᵉ theᵉ naturalᵉ numbersᵉ isᵉ theᵉ uniqueᵉ relationᵉ suchᵉ thatᵉ `0`ᵉ isᵉ
lessᵉ thanᵉ anyᵉ naturalᵉ number,ᵉ andᵉ suchᵉ thatᵉ `m+1ᵉ ≤ᵉ n+1`ᵉ isᵉ equivalentᵉ to
`mᵉ ≤ᵉ n`.ᵉ

## Definitions

### Inequality on the natural numbers

```agda
leq-ℕᵉ : ℕᵉ → ℕᵉ → UUᵉ lzero
leq-ℕᵉ zero-ℕᵉ mᵉ = unitᵉ
leq-ℕᵉ (succ-ℕᵉ nᵉ) zero-ℕᵉ = emptyᵉ
leq-ℕᵉ (succ-ℕᵉ nᵉ) (succ-ℕᵉ mᵉ) = leq-ℕᵉ nᵉ mᵉ

infix 30 _≤-ℕᵉ_
_≤-ℕᵉ_ = leq-ℕᵉ
```

### Alternative definition of the inequality on the natural numbers

```agda
data leq-ℕ'ᵉ : ℕᵉ → ℕᵉ → UUᵉ lzero where
  refl-leq-ℕ'ᵉ : (nᵉ : ℕᵉ) → leq-ℕ'ᵉ nᵉ nᵉ
  propagate-leq-ℕ'ᵉ : {xᵉ yᵉ zᵉ : ℕᵉ} → succ-ℕᵉ yᵉ ＝ᵉ zᵉ → (leq-ℕ'ᵉ xᵉ yᵉ) → (leq-ℕ'ᵉ xᵉ zᵉ)
```

## Properties

### Inequality on the natural numbers is a proposition

```agda
is-prop-leq-ℕᵉ :
  (mᵉ nᵉ : ℕᵉ) → is-propᵉ (leq-ℕᵉ mᵉ nᵉ)
is-prop-leq-ℕᵉ zero-ℕᵉ zero-ℕᵉ = is-prop-unitᵉ
is-prop-leq-ℕᵉ zero-ℕᵉ (succ-ℕᵉ nᵉ) = is-prop-unitᵉ
is-prop-leq-ℕᵉ (succ-ℕᵉ mᵉ) zero-ℕᵉ = is-prop-emptyᵉ
is-prop-leq-ℕᵉ (succ-ℕᵉ mᵉ) (succ-ℕᵉ nᵉ) = is-prop-leq-ℕᵉ mᵉ nᵉ

leq-ℕ-Propᵉ : ℕᵉ → ℕᵉ → Propᵉ lzero
pr1ᵉ (leq-ℕ-Propᵉ mᵉ nᵉ) = leq-ℕᵉ mᵉ nᵉ
pr2ᵉ (leq-ℕ-Propᵉ mᵉ nᵉ) = is-prop-leq-ℕᵉ mᵉ nᵉ
```

### Inequality on the natural numbers is decidable

```agda
is-decidable-leq-ℕᵉ :
  (mᵉ nᵉ : ℕᵉ) → is-decidableᵉ (leq-ℕᵉ mᵉ nᵉ)
is-decidable-leq-ℕᵉ zero-ℕᵉ zero-ℕᵉ = inlᵉ starᵉ
is-decidable-leq-ℕᵉ zero-ℕᵉ (succ-ℕᵉ nᵉ) = inlᵉ starᵉ
is-decidable-leq-ℕᵉ (succ-ℕᵉ mᵉ) zero-ℕᵉ = inrᵉ idᵉ
is-decidable-leq-ℕᵉ (succ-ℕᵉ mᵉ) (succ-ℕᵉ nᵉ) = is-decidable-leq-ℕᵉ mᵉ nᵉ
```

### Inequality on the natural numbers is a congruence

```agda
concatenate-eq-leq-eq-ℕᵉ :
  {x'ᵉ xᵉ yᵉ y'ᵉ : ℕᵉ} → x'ᵉ ＝ᵉ xᵉ → xᵉ ≤-ℕᵉ yᵉ → yᵉ ＝ᵉ y'ᵉ → x'ᵉ ≤-ℕᵉ y'ᵉ
concatenate-eq-leq-eq-ℕᵉ reflᵉ Hᵉ reflᵉ = Hᵉ

concatenate-leq-eq-ℕᵉ :
  (mᵉ : ℕᵉ) {nᵉ n'ᵉ : ℕᵉ} → mᵉ ≤-ℕᵉ nᵉ → nᵉ ＝ᵉ n'ᵉ → mᵉ ≤-ℕᵉ n'ᵉ
concatenate-leq-eq-ℕᵉ mᵉ Hᵉ reflᵉ = Hᵉ

concatenate-eq-leq-ℕᵉ :
  {mᵉ m'ᵉ : ℕᵉ} (nᵉ : ℕᵉ) → m'ᵉ ＝ᵉ mᵉ → mᵉ ≤-ℕᵉ nᵉ → m'ᵉ ≤-ℕᵉ nᵉ
concatenate-eq-leq-ℕᵉ nᵉ reflᵉ Hᵉ = Hᵉ
```

### Inequality on the natural numbers is reflexive

```agda
refl-leq-ℕᵉ : (nᵉ : ℕᵉ) → nᵉ ≤-ℕᵉ nᵉ
refl-leq-ℕᵉ zero-ℕᵉ = starᵉ
refl-leq-ℕᵉ (succ-ℕᵉ nᵉ) = refl-leq-ℕᵉ nᵉ

leq-eq-ℕᵉ : (mᵉ nᵉ : ℕᵉ) → mᵉ ＝ᵉ nᵉ → mᵉ ≤-ℕᵉ nᵉ
leq-eq-ℕᵉ mᵉ .mᵉ reflᵉ = refl-leq-ℕᵉ mᵉ
```

### Inequality on the natural numbers is transitive

```agda
transitive-leq-ℕᵉ : is-transitiveᵉ leq-ℕᵉ
transitive-leq-ℕᵉ zero-ℕᵉ mᵉ lᵉ pᵉ qᵉ = starᵉ
transitive-leq-ℕᵉ (succ-ℕᵉ nᵉ) (succ-ℕᵉ mᵉ) (succ-ℕᵉ lᵉ) pᵉ qᵉ =
  transitive-leq-ℕᵉ nᵉ mᵉ lᵉ pᵉ qᵉ
```

### Inequality on the natural numbers is antisymmetric

```agda
antisymmetric-leq-ℕᵉ : (mᵉ nᵉ : ℕᵉ) → mᵉ ≤-ℕᵉ nᵉ → nᵉ ≤-ℕᵉ mᵉ → mᵉ ＝ᵉ nᵉ
antisymmetric-leq-ℕᵉ zero-ℕᵉ zero-ℕᵉ pᵉ qᵉ = reflᵉ
antisymmetric-leq-ℕᵉ (succ-ℕᵉ mᵉ) (succ-ℕᵉ nᵉ) pᵉ qᵉ =
  apᵉ succ-ℕᵉ (antisymmetric-leq-ℕᵉ mᵉ nᵉ pᵉ qᵉ)
```

### The partially ordered set of natural numbers ordered by inequality

```agda
ℕ-Preorderᵉ : Preorderᵉ lzero lzero
pr1ᵉ ℕ-Preorderᵉ = ℕᵉ
pr1ᵉ (pr2ᵉ ℕ-Preorderᵉ) = leq-ℕ-Propᵉ
pr1ᵉ (pr2ᵉ (pr2ᵉ ℕ-Preorderᵉ)) = refl-leq-ℕᵉ
pr2ᵉ (pr2ᵉ (pr2ᵉ ℕ-Preorderᵉ)) = transitive-leq-ℕᵉ

ℕ-Posetᵉ : Posetᵉ lzero lzero
pr1ᵉ ℕ-Posetᵉ = ℕ-Preorderᵉ
pr2ᵉ ℕ-Posetᵉ = antisymmetric-leq-ℕᵉ
```

### For any two natural numbers we can decide which one is less than the other

```agda
linear-leq-ℕᵉ :
  (mᵉ nᵉ : ℕᵉ) → (mᵉ ≤-ℕᵉ nᵉ) +ᵉ (nᵉ ≤-ℕᵉ mᵉ)
linear-leq-ℕᵉ zero-ℕᵉ zero-ℕᵉ = inlᵉ starᵉ
linear-leq-ℕᵉ zero-ℕᵉ (succ-ℕᵉ nᵉ) = inlᵉ starᵉ
linear-leq-ℕᵉ (succ-ℕᵉ mᵉ) zero-ℕᵉ = inrᵉ starᵉ
linear-leq-ℕᵉ (succ-ℕᵉ mᵉ) (succ-ℕᵉ nᵉ) = linear-leq-ℕᵉ mᵉ nᵉ
```

### For any three natural numbers, there are three cases in how they can be ordered

```agda
cases-order-three-elements-ℕᵉ :
  (xᵉ yᵉ zᵉ : ℕᵉ) → UUᵉ lzero
cases-order-three-elements-ℕᵉ xᵉ yᵉ zᵉ =
  ( ( leq-ℕᵉ xᵉ yᵉ ×ᵉ leq-ℕᵉ yᵉ zᵉ) +ᵉ
    ( leq-ℕᵉ xᵉ zᵉ ×ᵉ leq-ℕᵉ zᵉ yᵉ)) +ᵉ
  ( ( ( leq-ℕᵉ yᵉ zᵉ ×ᵉ leq-ℕᵉ zᵉ xᵉ) +ᵉ
      ( leq-ℕᵉ yᵉ xᵉ ×ᵉ leq-ℕᵉ xᵉ zᵉ)) +ᵉ
    ( ( leq-ℕᵉ zᵉ xᵉ ×ᵉ leq-ℕᵉ xᵉ yᵉ) +ᵉ
      ( leq-ℕᵉ zᵉ yᵉ ×ᵉ leq-ℕᵉ yᵉ xᵉ)))

order-three-elements-ℕᵉ :
  (xᵉ yᵉ zᵉ : ℕᵉ) → cases-order-three-elements-ℕᵉ xᵉ yᵉ zᵉ
order-three-elements-ℕᵉ zero-ℕᵉ zero-ℕᵉ zero-ℕᵉ = inlᵉ (inlᵉ (pairᵉ starᵉ starᵉ))
order-three-elements-ℕᵉ zero-ℕᵉ zero-ℕᵉ (succ-ℕᵉ zᵉ) = inlᵉ (inlᵉ (pairᵉ starᵉ starᵉ))
order-three-elements-ℕᵉ zero-ℕᵉ (succ-ℕᵉ yᵉ) zero-ℕᵉ = inlᵉ (inrᵉ (pairᵉ starᵉ starᵉ))
order-three-elements-ℕᵉ zero-ℕᵉ (succ-ℕᵉ yᵉ) (succ-ℕᵉ zᵉ) =
  inlᵉ (map-coproductᵉ (pairᵉ starᵉ) (pairᵉ starᵉ) (linear-leq-ℕᵉ yᵉ zᵉ))
order-three-elements-ℕᵉ (succ-ℕᵉ xᵉ) zero-ℕᵉ zero-ℕᵉ =
  inrᵉ (inlᵉ (inlᵉ (pairᵉ starᵉ starᵉ)))
order-three-elements-ℕᵉ (succ-ℕᵉ xᵉ) zero-ℕᵉ (succ-ℕᵉ zᵉ) =
  inrᵉ (inlᵉ (map-coproductᵉ (pairᵉ starᵉ) (pairᵉ starᵉ) (linear-leq-ℕᵉ zᵉ xᵉ)))
order-three-elements-ℕᵉ (succ-ℕᵉ xᵉ) (succ-ℕᵉ yᵉ) zero-ℕᵉ =
  inrᵉ (inrᵉ (map-coproductᵉ (pairᵉ starᵉ) (pairᵉ starᵉ) (linear-leq-ℕᵉ xᵉ yᵉ)))
order-three-elements-ℕᵉ (succ-ℕᵉ xᵉ) (succ-ℕᵉ yᵉ) (succ-ℕᵉ zᵉ) =
  order-three-elements-ℕᵉ xᵉ yᵉ zᵉ
```

### Zero is less than or equal to any natural number

```agda
leq-zero-ℕᵉ :
  (nᵉ : ℕᵉ) → zero-ℕᵉ ≤-ℕᵉ nᵉ
leq-zero-ℕᵉ nᵉ = starᵉ
```

### Any natural number less than zero is zero

```agda
is-zero-leq-zero-ℕᵉ :
  (xᵉ : ℕᵉ) → xᵉ ≤-ℕᵉ zero-ℕᵉ → is-zero-ℕᵉ xᵉ
is-zero-leq-zero-ℕᵉ zero-ℕᵉ starᵉ = reflᵉ

is-zero-leq-zero-ℕ'ᵉ :
  (xᵉ : ℕᵉ) → xᵉ ≤-ℕᵉ zero-ℕᵉ → is-zero-ℕ'ᵉ xᵉ
is-zero-leq-zero-ℕ'ᵉ zero-ℕᵉ starᵉ = reflᵉ
```

### Any number is nonzero natural number if it is at least `1`

```agda
leq-one-is-nonzero-ℕᵉ :
  (xᵉ : ℕᵉ) → is-nonzero-ℕᵉ xᵉ → leq-ℕᵉ 1 xᵉ
leq-one-is-nonzero-ℕᵉ zero-ℕᵉ Hᵉ = ex-falsoᵉ (Hᵉ reflᵉ)
leq-one-is-nonzero-ℕᵉ (succ-ℕᵉ xᵉ) Hᵉ = starᵉ

is-nonzero-leq-one-ℕᵉ :
  (xᵉ : ℕᵉ) → leq-ℕᵉ 1 xᵉ → is-nonzero-ℕᵉ xᵉ
is-nonzero-leq-one-ℕᵉ .zero-ℕᵉ () reflᵉ
```

### Any natural number is less than or equal to its own successor

```agda
succ-leq-ℕᵉ : (nᵉ : ℕᵉ) → nᵉ ≤-ℕᵉ (succ-ℕᵉ nᵉ)
succ-leq-ℕᵉ zero-ℕᵉ = starᵉ
succ-leq-ℕᵉ (succ-ℕᵉ nᵉ) = succ-leq-ℕᵉ nᵉ
```

### Any natural number less than or equal to `n+1` is either less than or equal to `n` or it is `n+1`

```agda
decide-leq-succ-ℕᵉ :
  (mᵉ nᵉ : ℕᵉ) → mᵉ ≤-ℕᵉ (succ-ℕᵉ nᵉ) → (mᵉ ≤-ℕᵉ nᵉ) +ᵉ (mᵉ ＝ᵉ succ-ℕᵉ nᵉ)
decide-leq-succ-ℕᵉ zero-ℕᵉ zero-ℕᵉ lᵉ = inlᵉ starᵉ
decide-leq-succ-ℕᵉ zero-ℕᵉ (succ-ℕᵉ nᵉ) lᵉ = inlᵉ starᵉ
decide-leq-succ-ℕᵉ (succ-ℕᵉ mᵉ) zero-ℕᵉ lᵉ =
  inrᵉ (apᵉ succ-ℕᵉ (is-zero-leq-zero-ℕᵉ mᵉ lᵉ))
decide-leq-succ-ℕᵉ (succ-ℕᵉ mᵉ) (succ-ℕᵉ nᵉ) lᵉ =
  map-coproductᵉ idᵉ (apᵉ succ-ℕᵉ) (decide-leq-succ-ℕᵉ mᵉ nᵉ lᵉ)
```

### If `m` is less than `n`, then it is less than `n+1`

```agda
preserves-leq-succ-ℕᵉ :
  (mᵉ nᵉ : ℕᵉ) → mᵉ ≤-ℕᵉ nᵉ → mᵉ ≤-ℕᵉ (succ-ℕᵉ nᵉ)
preserves-leq-succ-ℕᵉ mᵉ nᵉ pᵉ = transitive-leq-ℕᵉ mᵉ nᵉ (succ-ℕᵉ nᵉ) (succ-leq-ℕᵉ nᵉ) pᵉ
```

### The successor of `n` is not less than or equal to `n`

```agda
neg-succ-leq-ℕᵉ :
  (nᵉ : ℕᵉ) → ¬ᵉ (leq-ℕᵉ (succ-ℕᵉ nᵉ) nᵉ)
neg-succ-leq-ℕᵉ zero-ℕᵉ = idᵉ
neg-succ-leq-ℕᵉ (succ-ℕᵉ nᵉ) = neg-succ-leq-ℕᵉ nᵉ
```

### If `m ≤ n + 1` then either `m ≤ n` or `m = n + 1`

```agda
cases-leq-succ-ℕᵉ :
  {mᵉ nᵉ : ℕᵉ} → leq-ℕᵉ mᵉ (succ-ℕᵉ nᵉ) → (leq-ℕᵉ mᵉ nᵉ) +ᵉ (mᵉ ＝ᵉ succ-ℕᵉ nᵉ)
cases-leq-succ-ℕᵉ {zero-ℕᵉ} {nᵉ} starᵉ = inlᵉ starᵉ
cases-leq-succ-ℕᵉ {succ-ℕᵉ mᵉ} {zero-ℕᵉ} pᵉ =
  inrᵉ (apᵉ succ-ℕᵉ (antisymmetric-leq-ℕᵉ mᵉ zero-ℕᵉ pᵉ starᵉ))
cases-leq-succ-ℕᵉ {succ-ℕᵉ mᵉ} {succ-ℕᵉ nᵉ} pᵉ =
  map-coproductᵉ idᵉ (apᵉ succ-ℕᵉ) (cases-leq-succ-ℕᵉ pᵉ)

cases-leq-succ-reflexive-leq-ℕᵉ :
  {nᵉ : ℕᵉ} → cases-leq-succ-ℕᵉ {succ-ℕᵉ nᵉ} {nᵉ} (refl-leq-ℕᵉ nᵉ) ＝ᵉ inrᵉ reflᵉ
cases-leq-succ-reflexive-leq-ℕᵉ {zero-ℕᵉ} = reflᵉ
cases-leq-succ-reflexive-leq-ℕᵉ {succ-ℕᵉ nᵉ} =
  apᵉ (map-coproductᵉ idᵉ (apᵉ succ-ℕᵉ)) cases-leq-succ-reflexive-leq-ℕᵉ
```

### `m ≤ n` if and only if `n + 1 ≰ m`

```agda
contradiction-leq-ℕᵉ : (mᵉ nᵉ : ℕᵉ) → mᵉ ≤-ℕᵉ nᵉ → ¬ᵉ ((succ-ℕᵉ nᵉ) ≤-ℕᵉ mᵉ)
contradiction-leq-ℕᵉ (succ-ℕᵉ mᵉ) (succ-ℕᵉ nᵉ) Hᵉ Kᵉ = contradiction-leq-ℕᵉ mᵉ nᵉ Hᵉ Kᵉ

contradiction-leq-ℕ'ᵉ : (mᵉ nᵉ : ℕᵉ) → (succ-ℕᵉ nᵉ) ≤-ℕᵉ mᵉ → ¬ᵉ (mᵉ ≤-ℕᵉ nᵉ)
contradiction-leq-ℕ'ᵉ mᵉ nᵉ Kᵉ Hᵉ = contradiction-leq-ℕᵉ mᵉ nᵉ Hᵉ Kᵉ
```

### Addition preserves inequality of natural numbers

```agda
preserves-leq-left-add-ℕᵉ :
  (kᵉ mᵉ nᵉ : ℕᵉ) → mᵉ ≤-ℕᵉ nᵉ → (mᵉ +ℕᵉ kᵉ) ≤-ℕᵉ (nᵉ +ℕᵉ kᵉ)
preserves-leq-left-add-ℕᵉ zero-ℕᵉ mᵉ nᵉ = idᵉ
preserves-leq-left-add-ℕᵉ (succ-ℕᵉ kᵉ) mᵉ nᵉ Hᵉ = preserves-leq-left-add-ℕᵉ kᵉ mᵉ nᵉ Hᵉ

preserves-leq-right-add-ℕᵉ : (kᵉ mᵉ nᵉ : ℕᵉ) → mᵉ ≤-ℕᵉ nᵉ → (kᵉ +ℕᵉ mᵉ) ≤-ℕᵉ (kᵉ +ℕᵉ nᵉ)
preserves-leq-right-add-ℕᵉ kᵉ mᵉ nᵉ Hᵉ =
  concatenate-eq-leq-eq-ℕᵉ
    ( commutative-add-ℕᵉ kᵉ mᵉ)
    ( preserves-leq-left-add-ℕᵉ kᵉ mᵉ nᵉ Hᵉ)
    ( commutative-add-ℕᵉ nᵉ kᵉ)

preserves-leq-add-ℕᵉ :
  {mᵉ m'ᵉ nᵉ n'ᵉ : ℕᵉ} → mᵉ ≤-ℕᵉ m'ᵉ → nᵉ ≤-ℕᵉ n'ᵉ → (mᵉ +ℕᵉ nᵉ) ≤-ℕᵉ (m'ᵉ +ℕᵉ n'ᵉ)
preserves-leq-add-ℕᵉ {mᵉ} {m'ᵉ} {nᵉ} {n'ᵉ} Hᵉ Kᵉ =
  transitive-leq-ℕᵉ
    ( mᵉ +ℕᵉ nᵉ)
    ( m'ᵉ +ℕᵉ nᵉ)
    ( m'ᵉ +ℕᵉ n'ᵉ)
    ( preserves-leq-right-add-ℕᵉ m'ᵉ nᵉ n'ᵉ Kᵉ)
    ( preserves-leq-left-add-ℕᵉ nᵉ mᵉ m'ᵉ Hᵉ)
```

### Addition reflects inequality of natural numbers

```agda
reflects-leq-left-add-ℕᵉ :
  (kᵉ mᵉ nᵉ : ℕᵉ) → (mᵉ +ℕᵉ kᵉ) ≤-ℕᵉ (nᵉ +ℕᵉ kᵉ) → mᵉ ≤-ℕᵉ nᵉ
reflects-leq-left-add-ℕᵉ zero-ℕᵉ mᵉ nᵉ = idᵉ
reflects-leq-left-add-ℕᵉ (succ-ℕᵉ kᵉ) mᵉ nᵉ = reflects-leq-left-add-ℕᵉ kᵉ mᵉ nᵉ

reflects-leq-right-add-ℕᵉ :
  (kᵉ mᵉ nᵉ : ℕᵉ) → (kᵉ +ℕᵉ mᵉ) ≤-ℕᵉ (kᵉ +ℕᵉ nᵉ) → mᵉ ≤-ℕᵉ nᵉ
reflects-leq-right-add-ℕᵉ kᵉ mᵉ nᵉ Hᵉ =
  reflects-leq-left-add-ℕᵉ kᵉ mᵉ nᵉ
    ( concatenate-eq-leq-eq-ℕᵉ
      ( commutative-add-ℕᵉ mᵉ kᵉ)
      ( Hᵉ)
      ( commutative-add-ℕᵉ kᵉ nᵉ))
```

### `m ≤ m + n` for any two natural numbers `m` and `n`

```agda
leq-add-ℕᵉ : (mᵉ nᵉ : ℕᵉ) → mᵉ ≤-ℕᵉ (mᵉ +ℕᵉ nᵉ)
leq-add-ℕᵉ mᵉ zero-ℕᵉ = refl-leq-ℕᵉ mᵉ
leq-add-ℕᵉ mᵉ (succ-ℕᵉ nᵉ) =
  transitive-leq-ℕᵉ
    ( mᵉ)
    ( mᵉ +ℕᵉ nᵉ)
    ( succ-ℕᵉ (mᵉ +ℕᵉ nᵉ))
    ( succ-leq-ℕᵉ (mᵉ +ℕᵉ nᵉ))
    ( leq-add-ℕᵉ mᵉ nᵉ)

leq-add-ℕ'ᵉ : (mᵉ nᵉ : ℕᵉ) → mᵉ ≤-ℕᵉ (nᵉ +ℕᵉ mᵉ)
leq-add-ℕ'ᵉ mᵉ nᵉ =
  concatenate-leq-eq-ℕᵉ mᵉ (leq-add-ℕᵉ mᵉ nᵉ) (commutative-add-ℕᵉ mᵉ nᵉ)
```

### We have `n ≤ m` if and only if there is a number `l` such that `l+n=m`

```agda
subtraction-leq-ℕᵉ : (nᵉ mᵉ : ℕᵉ) → nᵉ ≤-ℕᵉ mᵉ → Σᵉ ℕᵉ (λ lᵉ → lᵉ +ℕᵉ nᵉ ＝ᵉ mᵉ)
subtraction-leq-ℕᵉ zero-ℕᵉ mᵉ pᵉ = pairᵉ mᵉ reflᵉ
subtraction-leq-ℕᵉ (succ-ℕᵉ nᵉ) (succ-ℕᵉ mᵉ) pᵉ = pairᵉ (pr1ᵉ Pᵉ) (apᵉ succ-ℕᵉ (pr2ᵉ Pᵉ))
  where
  Pᵉ : Σᵉ ℕᵉ (λ l'ᵉ → l'ᵉ +ℕᵉ nᵉ ＝ᵉ mᵉ)
  Pᵉ = subtraction-leq-ℕᵉ nᵉ mᵉ pᵉ

leq-subtraction-ℕᵉ : (nᵉ mᵉ lᵉ : ℕᵉ) → lᵉ +ℕᵉ nᵉ ＝ᵉ mᵉ → nᵉ ≤-ℕᵉ mᵉ
leq-subtraction-ℕᵉ zero-ℕᵉ mᵉ lᵉ pᵉ = leq-zero-ℕᵉ mᵉ
leq-subtraction-ℕᵉ (succ-ℕᵉ nᵉ) (succ-ℕᵉ mᵉ) lᵉ pᵉ =
  leq-subtraction-ℕᵉ nᵉ mᵉ lᵉ (is-injective-succ-ℕᵉ pᵉ)
```

### Multiplication preserves inequality of natural numbers

```agda
preserves-leq-left-mul-ℕᵉ :
  (kᵉ mᵉ nᵉ : ℕᵉ) → mᵉ ≤-ℕᵉ nᵉ → (mᵉ *ℕᵉ kᵉ) ≤-ℕᵉ (nᵉ *ℕᵉ kᵉ)
preserves-leq-left-mul-ℕᵉ kᵉ zero-ℕᵉ nᵉ pᵉ = starᵉ
preserves-leq-left-mul-ℕᵉ kᵉ (succ-ℕᵉ mᵉ) (succ-ℕᵉ nᵉ) pᵉ =
  preserves-leq-left-add-ℕᵉ kᵉ
    ( mᵉ *ℕᵉ kᵉ)
    ( nᵉ *ℕᵉ kᵉ)
    ( preserves-leq-left-mul-ℕᵉ kᵉ mᵉ nᵉ pᵉ)

preserves-leq-right-mul-ℕᵉ :
  (kᵉ mᵉ nᵉ : ℕᵉ) → mᵉ ≤-ℕᵉ nᵉ → (kᵉ *ℕᵉ mᵉ) ≤-ℕᵉ (kᵉ *ℕᵉ nᵉ)
preserves-leq-right-mul-ℕᵉ kᵉ mᵉ nᵉ Hᵉ =
  concatenate-eq-leq-eq-ℕᵉ
    ( commutative-mul-ℕᵉ kᵉ mᵉ)
    ( preserves-leq-left-mul-ℕᵉ kᵉ mᵉ nᵉ Hᵉ)
    ( commutative-mul-ℕᵉ nᵉ kᵉ)

preserves-leq-mul-ℕᵉ :
  (mᵉ m'ᵉ nᵉ n'ᵉ : ℕᵉ) → mᵉ ≤-ℕᵉ m'ᵉ → nᵉ ≤-ℕᵉ n'ᵉ → (mᵉ *ℕᵉ nᵉ) ≤-ℕᵉ (m'ᵉ *ℕᵉ n'ᵉ)
preserves-leq-mul-ℕᵉ mᵉ m'ᵉ nᵉ n'ᵉ Hᵉ Kᵉ =
  transitive-leq-ℕᵉ
    ( mᵉ *ℕᵉ nᵉ)
    ( m'ᵉ *ℕᵉ nᵉ)
    ( m'ᵉ *ℕᵉ n'ᵉ)
    ( preserves-leq-right-mul-ℕᵉ m'ᵉ nᵉ n'ᵉ Kᵉ)
    ( preserves-leq-left-mul-ℕᵉ nᵉ mᵉ m'ᵉ Hᵉ)
```

### Multiplication by a nonzero natural number reflects inequality of natural numbers

```agda
reflects-order-mul-ℕᵉ :
  (kᵉ mᵉ nᵉ : ℕᵉ) → (mᵉ *ℕᵉ (succ-ℕᵉ kᵉ)) ≤-ℕᵉ (nᵉ *ℕᵉ (succ-ℕᵉ kᵉ)) → mᵉ ≤-ℕᵉ nᵉ
reflects-order-mul-ℕᵉ kᵉ zero-ℕᵉ nᵉ pᵉ = starᵉ
reflects-order-mul-ℕᵉ kᵉ (succ-ℕᵉ mᵉ) (succ-ℕᵉ nᵉ) pᵉ =
  reflects-order-mul-ℕᵉ kᵉ mᵉ nᵉ
    ( reflects-leq-left-add-ℕᵉ
      ( succ-ℕᵉ kᵉ)
      ( mᵉ *ℕᵉ (succ-ℕᵉ kᵉ))
      ( nᵉ *ℕᵉ (succ-ℕᵉ kᵉ))
      ( pᵉ))

reflects-order-mul-ℕ'ᵉ :
  (kᵉ mᵉ nᵉ : ℕᵉ) → ((succ-ℕᵉ kᵉ) *ℕᵉ mᵉ) ≤-ℕᵉ ((succ-ℕᵉ kᵉ) *ℕᵉ nᵉ) → mᵉ ≤-ℕᵉ nᵉ
reflects-order-mul-ℕ'ᵉ kᵉ mᵉ nᵉ Hᵉ =
  reflects-order-mul-ℕᵉ kᵉ mᵉ nᵉ
    ( concatenate-eq-leq-eq-ℕᵉ
      ( commutative-mul-ℕᵉ mᵉ (succ-ℕᵉ kᵉ))
      ( Hᵉ)
      ( commutative-mul-ℕᵉ (succ-ℕᵉ kᵉ) nᵉ))
```

### Any number `x` is less than a nonzero multiple of itself

```agda
leq-mul-ℕᵉ :
  (kᵉ xᵉ : ℕᵉ) → xᵉ ≤-ℕᵉ (xᵉ *ℕᵉ (succ-ℕᵉ kᵉ))
leq-mul-ℕᵉ kᵉ xᵉ =
  concatenate-eq-leq-ℕᵉ
    ( xᵉ *ℕᵉ (succ-ℕᵉ kᵉ))
    ( invᵉ (right-unit-law-mul-ℕᵉ xᵉ))
    ( preserves-leq-right-mul-ℕᵉ xᵉ 1 (succ-ℕᵉ kᵉ) (leq-zero-ℕᵉ kᵉ))

leq-mul-ℕ'ᵉ :
  (kᵉ xᵉ : ℕᵉ) → xᵉ ≤-ℕᵉ ((succ-ℕᵉ kᵉ) *ℕᵉ xᵉ)
leq-mul-ℕ'ᵉ kᵉ xᵉ =
  concatenate-leq-eq-ℕᵉ xᵉ
    ( leq-mul-ℕᵉ kᵉ xᵉ)
    ( commutative-mul-ℕᵉ xᵉ (succ-ℕᵉ kᵉ))

leq-mul-is-nonzero-ℕᵉ :
  (kᵉ xᵉ : ℕᵉ) → is-nonzero-ℕᵉ kᵉ → xᵉ ≤-ℕᵉ (xᵉ *ℕᵉ kᵉ)
leq-mul-is-nonzero-ℕᵉ kᵉ xᵉ Hᵉ with is-successor-is-nonzero-ℕᵉ Hᵉ
... | pairᵉ lᵉ reflᵉ = leq-mul-ℕᵉ lᵉ xᵉ

leq-mul-is-nonzero-ℕ'ᵉ :
  (kᵉ xᵉ : ℕᵉ) → is-nonzero-ℕᵉ kᵉ → xᵉ ≤-ℕᵉ (kᵉ *ℕᵉ xᵉ)
leq-mul-is-nonzero-ℕ'ᵉ kᵉ xᵉ Hᵉ with is-successor-is-nonzero-ℕᵉ Hᵉ
... | pairᵉ lᵉ reflᵉ = leq-mul-ℕ'ᵉ lᵉ xᵉ
```

## See also

-ᵉ Strictᵉ inequalityᵉ ofᵉ theᵉ naturalᵉ numbersᵉ isᵉ definedᵉ in
  [`strict-inequality-natural-numbers`](elementary-number-theory.strict-inequality-natural-numbers.mdᵉ)