# Decidable types in elementary number theory

```agda
module elementary-number-theory.decidable-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ
open import elementary-number-theory.strict-inequality-natural-numbersᵉ
open import elementary-number-theory.upper-bounds-natural-numbersᵉ

open import foundation.cartesian-product-typesᵉ
open import foundation.coproduct-typesᵉ
open import foundation.decidable-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.empty-typesᵉ
open import foundation.function-typesᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Weᵉ describeᵉ conditionsᵉ underᵉ whichᵉ dependentᵉ sumsᵉ andᵉ dependentᵉ productsᵉ areᵉ
decidable.ᵉ

## Properties

### Given a family of decidable types and a number `m` such that `Σ (m ≤ x), P x` is decidable, then `Σ ℕ P` is decidable

```agda
is-decidable-Σ-ℕᵉ :
  {lᵉ : Level} (mᵉ : ℕᵉ) (Pᵉ : ℕᵉ → UUᵉ lᵉ) (dᵉ : is-decidable-famᵉ Pᵉ) →
  is-decidableᵉ (Σᵉ ℕᵉ (λ xᵉ → (leq-ℕᵉ mᵉ xᵉ) ×ᵉ (Pᵉ xᵉ))) → is-decidableᵉ (Σᵉ ℕᵉ Pᵉ)
is-decidable-Σ-ℕᵉ mᵉ Pᵉ dᵉ (inlᵉ (pairᵉ xᵉ (pairᵉ lᵉ pᵉ))) = inlᵉ (pairᵉ xᵉ pᵉ)
is-decidable-Σ-ℕᵉ zero-ℕᵉ Pᵉ dᵉ (inrᵉ fᵉ) =
  inrᵉ (λ pᵉ → fᵉ (pairᵉ (pr1ᵉ pᵉ) (pairᵉ starᵉ (pr2ᵉ pᵉ))))
is-decidable-Σ-ℕᵉ (succ-ℕᵉ mᵉ) Pᵉ dᵉ (inrᵉ fᵉ) with dᵉ zero-ℕᵉ
... | inlᵉ pᵉ = inlᵉ (pairᵉ zero-ℕᵉ pᵉ)
... | inrᵉ gᵉ with
  is-decidable-Σ-ℕᵉ mᵉ
    ( Pᵉ ∘ᵉ succ-ℕᵉ)
    ( λ xᵉ → dᵉ (succ-ℕᵉ xᵉ))
    ( inrᵉ (λ pᵉ → fᵉ (pairᵉ (succ-ℕᵉ (pr1ᵉ pᵉ)) (pr2ᵉ pᵉ))))
... | inlᵉ pᵉ = inlᵉ (pairᵉ (succ-ℕᵉ (pr1ᵉ pᵉ)) (pr2ᵉ pᵉ))
... | inrᵉ hᵉ = inrᵉ αᵉ
  where
  αᵉ : Σᵉ ℕᵉ Pᵉ → emptyᵉ
  αᵉ (pairᵉ zero-ℕᵉ pᵉ) = gᵉ pᵉ
  αᵉ (pairᵉ (succ-ℕᵉ xᵉ) pᵉ) = hᵉ (pairᵉ xᵉ pᵉ)
```

### Bounded sums of decidable families over ℕ are decidable

```agda
is-decidable-bounded-Σ-ℕᵉ :
  {l1ᵉ l2ᵉ : Level} (mᵉ : ℕᵉ) (Pᵉ : ℕᵉ → UUᵉ l1ᵉ) (Qᵉ : ℕᵉ → UUᵉ l2ᵉ)
  (dPᵉ : is-decidable-famᵉ Pᵉ) (dQᵉ : is-decidable-famᵉ Qᵉ)
  (Hᵉ : is-upper-bound-ℕᵉ Pᵉ mᵉ) → is-decidableᵉ (Σᵉ ℕᵉ (λ xᵉ → (Pᵉ xᵉ) ×ᵉ (Qᵉ xᵉ)))
is-decidable-bounded-Σ-ℕᵉ mᵉ Pᵉ Qᵉ dPᵉ dQᵉ Hᵉ =
  is-decidable-Σ-ℕᵉ
    ( succ-ℕᵉ mᵉ)
    ( λ xᵉ → (Pᵉ xᵉ) ×ᵉ (Qᵉ xᵉ))
    ( λ xᵉ → is-decidable-productᵉ (dPᵉ xᵉ) (dQᵉ xᵉ))
    ( inrᵉ
      ( λ pᵉ →
        contradiction-leq-ℕᵉ
          ( pr1ᵉ pᵉ)
          ( mᵉ)
          ( Hᵉ (pr1ᵉ pᵉ) (pr1ᵉ (pr2ᵉ (pr2ᵉ pᵉ))))
          ( pr1ᵉ (pr2ᵉ pᵉ))))

is-decidable-bounded-Σ-ℕ'ᵉ :
  {lᵉ : Level} (mᵉ : ℕᵉ) (Pᵉ : ℕᵉ → UUᵉ lᵉ) (dᵉ : is-decidable-famᵉ Pᵉ) →
  is-decidableᵉ (Σᵉ ℕᵉ (λ xᵉ → (leq-ℕᵉ xᵉ mᵉ) ×ᵉ (Pᵉ xᵉ)))
is-decidable-bounded-Σ-ℕ'ᵉ mᵉ Pᵉ dᵉ =
  is-decidable-bounded-Σ-ℕᵉ mᵉ
    ( λ xᵉ → leq-ℕᵉ xᵉ mᵉ)
    ( Pᵉ)
    ( λ xᵉ → is-decidable-leq-ℕᵉ xᵉ mᵉ)
    ( dᵉ)
    ( λ xᵉ → idᵉ)
```

### Strictly bounded sums of decidable families over ℕ are decidable

```agda
is-decidable-strictly-bounded-Σ-ℕᵉ :
  {l1ᵉ l2ᵉ : Level} (mᵉ : ℕᵉ) (Pᵉ : ℕᵉ → UUᵉ l1ᵉ) (Qᵉ : ℕᵉ → UUᵉ l2ᵉ)
  (dPᵉ : is-decidable-famᵉ Pᵉ) (dQᵉ : is-decidable-famᵉ Qᵉ)
  (Hᵉ : is-strict-upper-bound-ℕᵉ Pᵉ mᵉ) →
  is-decidableᵉ (Σᵉ ℕᵉ (λ xᵉ → (Pᵉ xᵉ) ×ᵉ (Qᵉ xᵉ)))
is-decidable-strictly-bounded-Σ-ℕᵉ mᵉ Pᵉ Qᵉ dPᵉ dQᵉ Hᵉ =
  is-decidable-bounded-Σ-ℕᵉ mᵉ Pᵉ Qᵉ dPᵉ dQᵉ
    ( is-upper-bound-is-strict-upper-bound-ℕᵉ Pᵉ mᵉ Hᵉ)

is-decidable-strictly-bounded-Σ-ℕ'ᵉ :
  {lᵉ : Level} (mᵉ : ℕᵉ) (Pᵉ : ℕᵉ → UUᵉ lᵉ) (dᵉ : is-decidable-famᵉ Pᵉ) →
  is-decidableᵉ (Σᵉ ℕᵉ (λ xᵉ → (le-ℕᵉ xᵉ mᵉ) ×ᵉ (Pᵉ xᵉ)))
is-decidable-strictly-bounded-Σ-ℕ'ᵉ mᵉ Pᵉ dᵉ =
  is-decidable-strictly-bounded-Σ-ℕᵉ mᵉ
    ( λ xᵉ → le-ℕᵉ xᵉ mᵉ)
    ( Pᵉ)
    ( λ xᵉ → is-decidable-le-ℕᵉ xᵉ mᵉ)
    ( dᵉ)
    ( λ xᵉ → idᵉ)
```

### Given a family `P `of decidable types over ℕ and a number `m` such that `Π (m ≤ x), P x`, the type `Π ℕ P` is decidable

```agda
is-decidable-Π-ℕᵉ :
  {lᵉ : Level} (Pᵉ : ℕᵉ → UUᵉ lᵉ) (dᵉ : is-decidable-famᵉ Pᵉ) (mᵉ : ℕᵉ) →
  is-decidableᵉ ((xᵉ : ℕᵉ) → (leq-ℕᵉ mᵉ xᵉ) → Pᵉ xᵉ) → is-decidableᵉ ((xᵉ : ℕᵉ) → Pᵉ xᵉ)
is-decidable-Π-ℕᵉ Pᵉ dᵉ zero-ℕᵉ (inrᵉ nHᵉ) = inrᵉ (λ fᵉ → nHᵉ (λ xᵉ yᵉ → fᵉ xᵉ))
is-decidable-Π-ℕᵉ Pᵉ dᵉ zero-ℕᵉ (inlᵉ Hᵉ) = inlᵉ (λ xᵉ → Hᵉ xᵉ (leq-zero-ℕᵉ xᵉ))
is-decidable-Π-ℕᵉ Pᵉ dᵉ (succ-ℕᵉ mᵉ) (inrᵉ nHᵉ) = inrᵉ (λ fᵉ → nHᵉ (λ xᵉ yᵉ → fᵉ xᵉ))
is-decidable-Π-ℕᵉ Pᵉ dᵉ (succ-ℕᵉ mᵉ) (inlᵉ Hᵉ) with dᵉ zero-ℕᵉ
... | inrᵉ npᵉ = inrᵉ (λ fᵉ → npᵉ (fᵉ zero-ℕᵉ))
... | inlᵉ pᵉ with
  is-decidable-Π-ℕᵉ
    ( λ xᵉ → Pᵉ (succ-ℕᵉ xᵉ))
    ( λ xᵉ → dᵉ (succ-ℕᵉ xᵉ))
    ( mᵉ)
    ( inlᵉ (λ xᵉ → Hᵉ (succ-ℕᵉ xᵉ)))
... | inlᵉ gᵉ = inlᵉ (ind-ℕᵉ pᵉ (λ xᵉ yᵉ → gᵉ xᵉ))
... | inrᵉ ngᵉ = inrᵉ (λ fᵉ → ngᵉ (λ xᵉ → fᵉ (succ-ℕᵉ xᵉ)))
```

### Bounded dependent products of decidable types are decidable

```agda
is-decidable-bounded-Π-ℕᵉ :
  {l1ᵉ l2ᵉ : Level} (Pᵉ : ℕᵉ → UUᵉ l1ᵉ) (Qᵉ : ℕᵉ → UUᵉ l2ᵉ) (dPᵉ : is-decidable-famᵉ Pᵉ) →
  (dQᵉ : is-decidable-famᵉ Qᵉ) (mᵉ : ℕᵉ) (Hᵉ : is-upper-bound-ℕᵉ Pᵉ mᵉ) →
  is-decidableᵉ ((xᵉ : ℕᵉ) → Pᵉ xᵉ → Qᵉ xᵉ)
is-decidable-bounded-Π-ℕᵉ Pᵉ Qᵉ dPᵉ dQᵉ mᵉ Hᵉ =
  is-decidable-Π-ℕᵉ
    ( λ xᵉ → Pᵉ xᵉ → Qᵉ xᵉ)
    ( λ xᵉ → is-decidable-function-typeᵉ (dPᵉ xᵉ) (dQᵉ xᵉ))
    ( succ-ℕᵉ mᵉ)
    ( inlᵉ (λ xᵉ lᵉ pᵉ → ex-falsoᵉ (contradiction-leq-ℕᵉ xᵉ mᵉ (Hᵉ xᵉ pᵉ) lᵉ)))

is-decidable-bounded-Π-ℕ'ᵉ :
  {lᵉ : Level} (Pᵉ : ℕᵉ → UUᵉ lᵉ) (dᵉ : is-decidable-famᵉ Pᵉ) (mᵉ : ℕᵉ) →
  is-decidableᵉ ((xᵉ : ℕᵉ) → (leq-ℕᵉ xᵉ mᵉ) → Pᵉ xᵉ)
is-decidable-bounded-Π-ℕ'ᵉ Pᵉ dᵉ mᵉ =
  is-decidable-bounded-Π-ℕᵉ
    ( λ xᵉ → leq-ℕᵉ xᵉ mᵉ)
    ( Pᵉ)
    ( λ xᵉ → is-decidable-leq-ℕᵉ xᵉ mᵉ)
    ( dᵉ)
    ( mᵉ)
    ( λ xᵉ → idᵉ)
```

### Strictly bounded dependent products of decidable types are decidable

```agda
is-decidable-strictly-bounded-Π-ℕᵉ :
  {l1ᵉ l2ᵉ : Level} (Pᵉ : ℕᵉ → UUᵉ l1ᵉ) (Qᵉ : ℕᵉ → UUᵉ l2ᵉ) (dPᵉ : is-decidable-famᵉ Pᵉ) →
  (dQᵉ : is-decidable-famᵉ Qᵉ) (mᵉ : ℕᵉ) (Hᵉ : is-strict-upper-bound-ℕᵉ Pᵉ mᵉ) →
  is-decidableᵉ ((xᵉ : ℕᵉ) → Pᵉ xᵉ → Qᵉ xᵉ)
is-decidable-strictly-bounded-Π-ℕᵉ Pᵉ Qᵉ dPᵉ dQᵉ mᵉ Hᵉ =
  is-decidable-bounded-Π-ℕᵉ Pᵉ Qᵉ dPᵉ dQᵉ mᵉ (λ xᵉ pᵉ → leq-le-ℕᵉ xᵉ mᵉ (Hᵉ xᵉ pᵉ))

is-decidable-strictly-bounded-Π-ℕ'ᵉ :
  {lᵉ : Level} (Pᵉ : ℕᵉ → UUᵉ lᵉ) (dᵉ : is-decidable-famᵉ Pᵉ) (mᵉ : ℕᵉ) →
  is-decidableᵉ ((xᵉ : ℕᵉ) → le-ℕᵉ xᵉ mᵉ → Pᵉ xᵉ)
is-decidable-strictly-bounded-Π-ℕ'ᵉ Pᵉ dᵉ mᵉ =
  is-decidable-strictly-bounded-Π-ℕᵉ
    ( λ xᵉ → le-ℕᵉ xᵉ mᵉ)
    ( Pᵉ)
    ( λ xᵉ → is-decidable-le-ℕᵉ xᵉ mᵉ)
    ( dᵉ)
    ( mᵉ)
    ( λ xᵉ → idᵉ)
```