# Diagonal maps of types

```agda
module foundation.diagonal-maps-of-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equality-cartesian-product-typesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.morphisms-arrowsᵉ
open import foundation.postcomposition-functionsᵉ
open import foundation.retracts-of-typesᵉ
open import foundation.transposition-identifications-along-equivalencesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.cartesian-product-typesᵉ
open import foundation-core.constant-mapsᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.fibers-of-mapsᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.injective-mapsᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.retractionsᵉ
open import foundation-core.sectionsᵉ
```

</details>

## Idea

Theᵉ
{{#conceptᵉ "diagonalᵉ map"ᵉ Disambiguation="ofᵉ aᵉ typeᵉ intoᵉ exponentials"ᵉ Agda=diagonal-exponentialᵉ}}
ofᵉ aᵉ typeᵉ `A`ᵉ isᵉ theᵉ mapᵉ thatᵉ includesᵉ theᵉ pointsᵉ ofᵉ `A`ᵉ intoᵉ theᵉ exponentialᵉ
`Xᵉ → A`.ᵉ

## Definitions

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Xᵉ : UUᵉ l2ᵉ)
  where

  diagonal-exponentialᵉ : Aᵉ → Xᵉ → Aᵉ
  diagonal-exponentialᵉ = constᵉ Xᵉ
```

## Properties

### The action on identifications of a diagonal map is another diagonal map

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (xᵉ yᵉ : Aᵉ) (Bᵉ : UUᵉ l2ᵉ)
  where

  htpy-diagonal-exponential-Id-ap-diagonal-exponential-htpy-eqᵉ :
    htpy-eqᵉ ∘ᵉ apᵉ (diagonal-exponentialᵉ Aᵉ Bᵉ) ~ᵉ diagonal-exponentialᵉ (xᵉ ＝ᵉ yᵉ) Bᵉ
  htpy-diagonal-exponential-Id-ap-diagonal-exponential-htpy-eqᵉ reflᵉ = reflᵉ

  htpy-ap-diagonal-exponential-htpy-eq-diagonal-exponential-Idᵉ :
    diagonal-exponentialᵉ (xᵉ ＝ᵉ yᵉ) Bᵉ ~ᵉ htpy-eqᵉ ∘ᵉ apᵉ (diagonal-exponentialᵉ Aᵉ Bᵉ)
  htpy-ap-diagonal-exponential-htpy-eq-diagonal-exponential-Idᵉ =
    inv-htpyᵉ htpy-diagonal-exponential-Id-ap-diagonal-exponential-htpy-eqᵉ
```

### Given an element of the exponent the diagonal map is injective

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : UUᵉ l2ᵉ) (bᵉ : Bᵉ)
  where

  is-injective-diagonal-exponentialᵉ :
    is-injectiveᵉ (diagonal-exponentialᵉ Aᵉ Bᵉ)
  is-injective-diagonal-exponentialᵉ pᵉ = htpy-eqᵉ pᵉ bᵉ

  diagonal-exponential-injectionᵉ : injectionᵉ Aᵉ (Bᵉ → Aᵉ)
  pr1ᵉ diagonal-exponential-injectionᵉ = diagonal-exponentialᵉ Aᵉ Bᵉ
  pr2ᵉ diagonal-exponential-injectionᵉ = is-injective-diagonal-exponentialᵉ
```

### The action on identifications of an (exponential) diagonal is a diagonal

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) {Bᵉ : UUᵉ l2ᵉ} (xᵉ yᵉ : Bᵉ)
  where

  compute-htpy-eq-ap-diagonal-exponentialᵉ :
    htpy-eqᵉ ∘ᵉ apᵉ (diagonal-exponentialᵉ Bᵉ Aᵉ) ~ᵉ diagonal-exponentialᵉ (xᵉ ＝ᵉ yᵉ) Aᵉ
  compute-htpy-eq-ap-diagonal-exponentialᵉ reflᵉ = reflᵉ

  inv-compute-htpy-eq-ap-diagonal-exponentialᵉ :
    diagonal-exponentialᵉ (xᵉ ＝ᵉ yᵉ) Aᵉ ~ᵉ htpy-eqᵉ ∘ᵉ apᵉ (diagonal-exponentialᵉ Bᵉ Aᵉ)
  inv-compute-htpy-eq-ap-diagonal-exponentialᵉ =
    inv-htpyᵉ compute-htpy-eq-ap-diagonal-exponentialᵉ

  compute-eq-htpy-ap-diagonal-exponentialᵉ :
    apᵉ (diagonal-exponentialᵉ Bᵉ Aᵉ) ~ᵉ eq-htpyᵉ ∘ᵉ diagonal-exponentialᵉ (xᵉ ＝ᵉ yᵉ) Aᵉ
  compute-eq-htpy-ap-diagonal-exponentialᵉ pᵉ =
    map-eq-transpose-equivᵉ
      ( equiv-funextᵉ)
      ( compute-htpy-eq-ap-diagonal-exponentialᵉ pᵉ)
```

### Computing the fibers of diagonal maps

```agda
compute-fiber-diagonal-exponentialᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) →
  fiberᵉ (diagonal-exponentialᵉ Bᵉ Aᵉ) fᵉ ≃ᵉ Σᵉ Bᵉ (λ bᵉ → (xᵉ : Aᵉ) → bᵉ ＝ᵉ fᵉ xᵉ)
compute-fiber-diagonal-exponentialᵉ fᵉ = equiv-totᵉ (λ _ → equiv-funextᵉ)
```