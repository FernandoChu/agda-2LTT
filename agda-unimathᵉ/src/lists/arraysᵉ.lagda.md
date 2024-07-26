# Arrays

```agda
module lists.arraysᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.coproduct-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.empty-typesᵉ
open import foundation.equality-dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import linear-algebra.vectorsᵉ

open import lists.listsᵉ

open import univalent-combinatorics.involution-standard-finite-typesᵉ
open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Anᵉ arrayᵉ isᵉ aᵉ pairᵉ ofᵉ aᵉ naturalᵉ numberᵉ `n`,ᵉ andᵉ aᵉ functionᵉ fromᵉ `Finᵉ n`ᵉ to `A`.ᵉ
Weᵉ showᵉ thatᵉ arraysᵉ andᵉ listsᵉ areᵉ equivalent.ᵉ

```agda
arrayᵉ : {lᵉ : Level} → UUᵉ lᵉ → UUᵉ lᵉ
arrayᵉ Aᵉ = Σᵉ ℕᵉ (λ nᵉ → functional-vecᵉ Aᵉ nᵉ)

module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  length-arrayᵉ : arrayᵉ Aᵉ → ℕᵉ
  length-arrayᵉ = pr1ᵉ

  functional-vec-arrayᵉ : (tᵉ : arrayᵉ Aᵉ) → Finᵉ (length-arrayᵉ tᵉ) → Aᵉ
  functional-vec-arrayᵉ = pr2ᵉ

  empty-arrayᵉ : arrayᵉ Aᵉ
  pr1ᵉ (empty-arrayᵉ) = zero-ℕᵉ
  pr2ᵉ (empty-arrayᵉ) ()

  is-empty-array-Propᵉ : arrayᵉ Aᵉ → Propᵉ lzero
  is-empty-array-Propᵉ (zero-ℕᵉ ,ᵉ tᵉ) = unit-Propᵉ
  is-empty-array-Propᵉ (succ-ℕᵉ nᵉ ,ᵉ tᵉ) = empty-Propᵉ

  is-empty-arrayᵉ : arrayᵉ Aᵉ → UUᵉ lzero
  is-empty-arrayᵉ = type-Propᵉ ∘ᵉ is-empty-array-Propᵉ

  is-nonempty-array-Propᵉ : arrayᵉ Aᵉ → Propᵉ lzero
  is-nonempty-array-Propᵉ (zero-ℕᵉ ,ᵉ tᵉ) = empty-Propᵉ
  is-nonempty-array-Propᵉ (succ-ℕᵉ nᵉ ,ᵉ tᵉ) = unit-Propᵉ

  is-nonempty-arrayᵉ : arrayᵉ Aᵉ → UUᵉ lzero
  is-nonempty-arrayᵉ = type-Propᵉ ∘ᵉ is-nonempty-array-Propᵉ

  head-arrayᵉ : (tᵉ : arrayᵉ Aᵉ) → is-nonempty-arrayᵉ tᵉ → Aᵉ
  head-arrayᵉ (succ-ℕᵉ nᵉ ,ᵉ fᵉ) _ = fᵉ (inrᵉ starᵉ)

  tail-arrayᵉ : (tᵉ : arrayᵉ Aᵉ) → is-nonempty-arrayᵉ tᵉ → arrayᵉ Aᵉ
  tail-arrayᵉ (succ-ℕᵉ nᵉ ,ᵉ fᵉ) _ = nᵉ ,ᵉ fᵉ ∘ᵉ inlᵉ

  cons-arrayᵉ : Aᵉ → arrayᵉ Aᵉ → arrayᵉ Aᵉ
  cons-arrayᵉ aᵉ tᵉ =
    ( succ-ℕᵉ (length-arrayᵉ tᵉ) ,ᵉ
      rec-coproductᵉ (functional-vec-arrayᵉ tᵉ) (λ _ → aᵉ))

  revert-arrayᵉ : arrayᵉ Aᵉ → arrayᵉ Aᵉ
  revert-arrayᵉ (nᵉ ,ᵉ tᵉ) = (nᵉ ,ᵉ λ kᵉ → tᵉ (opposite-Finᵉ nᵉ kᵉ))
```

### The definition of `fold-vec`

```agda
fold-vecᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (bᵉ : Bᵉ) (μᵉ : Aᵉ → (Bᵉ → Bᵉ)) →
  {nᵉ : ℕᵉ} → vecᵉ Aᵉ nᵉ → Bᵉ
fold-vecᵉ bᵉ μᵉ {0ᵉ} _ = bᵉ
fold-vecᵉ bᵉ μᵉ (aᵉ ∷ᵉ lᵉ) = μᵉ aᵉ (fold-vecᵉ bᵉ μᵉ lᵉ)
```

## Properties

### The types of lists and arrays are equivalent

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  list-vecᵉ : (nᵉ : ℕᵉ) → (vecᵉ Aᵉ nᵉ) → listᵉ Aᵉ
  list-vecᵉ zero-ℕᵉ _ = nilᵉ
  list-vecᵉ (succ-ℕᵉ nᵉ) (xᵉ ∷ᵉ lᵉ) = consᵉ xᵉ (list-vecᵉ nᵉ lᵉ)

  vec-listᵉ : (lᵉ : listᵉ Aᵉ) → vecᵉ Aᵉ (length-listᵉ lᵉ)
  vec-listᵉ nilᵉ = empty-vecᵉ
  vec-listᵉ (consᵉ xᵉ lᵉ) = xᵉ ∷ᵉ vec-listᵉ lᵉ

  is-section-vec-listᵉ : (λ lᵉ → list-vecᵉ (length-listᵉ lᵉ) (vec-listᵉ lᵉ)) ~ᵉ idᵉ
  is-section-vec-listᵉ nilᵉ = reflᵉ
  is-section-vec-listᵉ (consᵉ xᵉ lᵉ) = apᵉ (consᵉ xᵉ) (is-section-vec-listᵉ lᵉ)

  is-retraction-vec-listᵉ :
    ( λ (xᵉ : Σᵉ ℕᵉ (λ nᵉ → vecᵉ Aᵉ nᵉ)) →
      ( length-listᵉ (list-vecᵉ (pr1ᵉ xᵉ) (pr2ᵉ xᵉ)) ,ᵉ
        vec-listᵉ (list-vecᵉ (pr1ᵉ xᵉ) (pr2ᵉ xᵉ)))) ~ᵉ
    idᵉ
  is-retraction-vec-listᵉ (zero-ℕᵉ ,ᵉ empty-vecᵉ) = reflᵉ
  is-retraction-vec-listᵉ (succ-ℕᵉ nᵉ ,ᵉ (xᵉ ∷ᵉ vᵉ)) =
    apᵉ
      ( λ vᵉ → succ-ℕᵉ (pr1ᵉ vᵉ) ,ᵉ (xᵉ ∷ᵉ (pr2ᵉ vᵉ)))
      ( is-retraction-vec-listᵉ (nᵉ ,ᵉ vᵉ))

  list-arrayᵉ : arrayᵉ Aᵉ → listᵉ Aᵉ
  list-arrayᵉ (nᵉ ,ᵉ tᵉ) = list-vecᵉ nᵉ (listed-vec-functional-vecᵉ nᵉ tᵉ)

  array-listᵉ : listᵉ Aᵉ → arrayᵉ Aᵉ
  array-listᵉ lᵉ =
    ( length-listᵉ lᵉ ,ᵉ functional-vec-vecᵉ (length-listᵉ lᵉ) (vec-listᵉ lᵉ))

  is-section-array-listᵉ : (list-arrayᵉ ∘ᵉ array-listᵉ) ~ᵉ idᵉ
  is-section-array-listᵉ nilᵉ = reflᵉ
  is-section-array-listᵉ (consᵉ xᵉ lᵉ) = apᵉ (consᵉ xᵉ) (is-section-array-listᵉ lᵉ)

  is-retraction-array-listᵉ : (array-listᵉ ∘ᵉ list-arrayᵉ) ~ᵉ idᵉ
  is-retraction-array-listᵉ (nᵉ ,ᵉ tᵉ) =
    apᵉ
      ( λ (nᵉ ,ᵉ vᵉ) → (nᵉ ,ᵉ functional-vec-vecᵉ nᵉ vᵉ))
      ( is-retraction-vec-listᵉ (nᵉ ,ᵉ listed-vec-functional-vecᵉ nᵉ tᵉ)) ∙ᵉ
    eq-pair-eq-fiberᵉ (is-retraction-functional-vec-vecᵉ nᵉ tᵉ)

  equiv-list-arrayᵉ : arrayᵉ Aᵉ ≃ᵉ listᵉ Aᵉ
  pr1ᵉ equiv-list-arrayᵉ = list-arrayᵉ
  pr2ᵉ equiv-list-arrayᵉ =
    is-equiv-is-invertibleᵉ
      array-listᵉ
      is-section-array-listᵉ
      is-retraction-array-listᵉ

  equiv-array-listᵉ : listᵉ Aᵉ ≃ᵉ arrayᵉ Aᵉ
  pr1ᵉ equiv-array-listᵉ = array-listᵉ
  pr2ᵉ equiv-array-listᵉ =
    is-equiv-is-invertibleᵉ
      list-arrayᵉ
      is-retraction-array-listᵉ
      is-section-array-listᵉ
```

### Computational rules of the equivalence between arrays and lists

```agda
  compute-length-list-list-vecᵉ :
    (nᵉ : ℕᵉ) (vᵉ : vecᵉ Aᵉ nᵉ) →
    length-listᵉ (list-vecᵉ nᵉ vᵉ) ＝ᵉ nᵉ
  compute-length-list-list-vecᵉ zero-ℕᵉ vᵉ = reflᵉ
  compute-length-list-list-vecᵉ (succ-ℕᵉ nᵉ) (xᵉ ∷ᵉ vᵉ) =
    apᵉ succ-ℕᵉ (compute-length-list-list-vecᵉ nᵉ vᵉ)

  compute-length-list-list-arrayᵉ :
    (tᵉ : arrayᵉ Aᵉ) → length-listᵉ (list-arrayᵉ tᵉ) ＝ᵉ length-arrayᵉ tᵉ
  compute-length-list-list-arrayᵉ tᵉ =
    compute-length-list-list-vecᵉ
      ( length-arrayᵉ tᵉ)
      ( listed-vec-functional-vecᵉ (length-arrayᵉ tᵉ) (functional-vec-arrayᵉ tᵉ))
```

### An element `x` is in a vector `v` iff it is in `list-vec n v`

```agda
  is-in-list-is-in-vec-listᵉ :
    (lᵉ : listᵉ Aᵉ) (xᵉ : Aᵉ) →
    xᵉ ∈-vecᵉ (vec-listᵉ lᵉ) → xᵉ ∈-listᵉ lᵉ
  is-in-list-is-in-vec-listᵉ (consᵉ yᵉ lᵉ) .yᵉ (is-headᵉ .yᵉ .(vec-listᵉ lᵉ)) =
    is-headᵉ yᵉ lᵉ
  is-in-list-is-in-vec-listᵉ (consᵉ yᵉ lᵉ) xᵉ (is-in-tailᵉ .xᵉ .yᵉ .(vec-listᵉ lᵉ) Iᵉ) =
    is-in-tailᵉ xᵉ yᵉ lᵉ (is-in-list-is-in-vec-listᵉ lᵉ xᵉ Iᵉ)

  is-in-vec-list-is-in-listᵉ :
    (lᵉ : listᵉ Aᵉ) (xᵉ : Aᵉ) →
    xᵉ ∈-listᵉ lᵉ → xᵉ ∈-vecᵉ (vec-listᵉ lᵉ)
  is-in-vec-list-is-in-listᵉ (consᵉ xᵉ lᵉ) xᵉ (is-headᵉ .xᵉ lᵉ) =
    is-headᵉ xᵉ (vec-listᵉ lᵉ)
  is-in-vec-list-is-in-listᵉ (consᵉ yᵉ lᵉ) xᵉ (is-in-tailᵉ .xᵉ .yᵉ lᵉ Iᵉ) =
    is-in-tailᵉ xᵉ yᵉ (vec-listᵉ lᵉ) (is-in-vec-list-is-in-listᵉ lᵉ xᵉ Iᵉ)
```

### Link between `fold-list` and `fold-vec`

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  (bᵉ : Bᵉ)
  (μᵉ : Aᵉ → (Bᵉ → Bᵉ))
  where
  htpy-fold-list-fold-vecᵉ :
    (lᵉ : listᵉ Aᵉ) →
    fold-vecᵉ bᵉ μᵉ (vec-listᵉ lᵉ) ＝ᵉ fold-listᵉ bᵉ μᵉ lᵉ
  htpy-fold-list-fold-vecᵉ nilᵉ = reflᵉ
  htpy-fold-list-fold-vecᵉ (consᵉ xᵉ lᵉ) =
    apᵉ (μᵉ xᵉ) (htpy-fold-list-fold-vecᵉ lᵉ)
```