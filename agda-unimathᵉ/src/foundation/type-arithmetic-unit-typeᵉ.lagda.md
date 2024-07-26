# Type arithmetic with the unit type

```agda
module foundation.type-arithmetic-unit-typeᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.cartesian-product-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.retractionsᵉ
open import foundation-core.sectionsᵉ
```

</details>

## Idea

Weᵉ proveᵉ arithmeticalᵉ lawsᵉ involvingᵉ theᵉ unitᵉ typeᵉ

## Laws

### Left unit law for dependent pair types

```agda
module _
  {lᵉ : Level} (Aᵉ : unitᵉ → UUᵉ lᵉ)
  where

  map-left-unit-law-Σᵉ : Σᵉ unitᵉ Aᵉ → Aᵉ starᵉ
  map-left-unit-law-Σᵉ (ᵉ_ ,ᵉ aᵉ) = aᵉ

  map-inv-left-unit-law-Σᵉ : Aᵉ starᵉ → Σᵉ unitᵉ Aᵉ
  pr1ᵉ (map-inv-left-unit-law-Σᵉ aᵉ) = starᵉ
  pr2ᵉ (map-inv-left-unit-law-Σᵉ aᵉ) = aᵉ

  is-section-map-inv-left-unit-law-Σᵉ :
    ( map-left-unit-law-Σᵉ ∘ᵉ map-inv-left-unit-law-Σᵉ) ~ᵉ idᵉ
  is-section-map-inv-left-unit-law-Σᵉ = refl-htpyᵉ

  is-retraction-map-inv-left-unit-law-Σᵉ :
    ( map-inv-left-unit-law-Σᵉ ∘ᵉ map-left-unit-law-Σᵉ) ~ᵉ idᵉ
  is-retraction-map-inv-left-unit-law-Σᵉ = refl-htpyᵉ

  is-equiv-map-left-unit-law-Σᵉ : is-equivᵉ map-left-unit-law-Σᵉ
  is-equiv-map-left-unit-law-Σᵉ =
    is-equiv-is-invertibleᵉ
      map-inv-left-unit-law-Σᵉ
      is-section-map-inv-left-unit-law-Σᵉ
      is-retraction-map-inv-left-unit-law-Σᵉ

  left-unit-law-Σᵉ : Σᵉ unitᵉ Aᵉ ≃ᵉ Aᵉ starᵉ
  pr1ᵉ left-unit-law-Σᵉ = map-left-unit-law-Σᵉ
  pr2ᵉ left-unit-law-Σᵉ = is-equiv-map-left-unit-law-Σᵉ

  is-equiv-map-inv-left-unit-law-Σᵉ : is-equivᵉ map-inv-left-unit-law-Σᵉ
  is-equiv-map-inv-left-unit-law-Σᵉ =
    is-equiv-is-invertibleᵉ
      map-left-unit-law-Σᵉ
      is-retraction-map-inv-left-unit-law-Σᵉ
      is-section-map-inv-left-unit-law-Σᵉ

  inv-left-unit-law-Σᵉ : Aᵉ starᵉ ≃ᵉ Σᵉ unitᵉ Aᵉ
  pr1ᵉ inv-left-unit-law-Σᵉ = map-inv-left-unit-law-Σᵉ
  pr2ᵉ inv-left-unit-law-Σᵉ = is-equiv-map-inv-left-unit-law-Σᵉ
```

### Left unit law for cartesian products

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  map-left-unit-law-productᵉ : unitᵉ ×ᵉ Aᵉ → Aᵉ
  map-left-unit-law-productᵉ = pr2ᵉ

  map-inv-left-unit-law-productᵉ : Aᵉ → unitᵉ ×ᵉ Aᵉ
  map-inv-left-unit-law-productᵉ = map-inv-left-unit-law-Σᵉ (λ _ → Aᵉ)

  is-section-map-inv-left-unit-law-productᵉ :
    is-sectionᵉ map-left-unit-law-productᵉ map-inv-left-unit-law-productᵉ
  is-section-map-inv-left-unit-law-productᵉ =
    is-section-map-inv-left-unit-law-Σᵉ (λ _ → Aᵉ)

  is-retraction-map-inv-left-unit-law-productᵉ :
    is-retractionᵉ map-left-unit-law-productᵉ map-inv-left-unit-law-productᵉ
  is-retraction-map-inv-left-unit-law-productᵉ = refl-htpyᵉ

  is-equiv-map-left-unit-law-productᵉ : is-equivᵉ map-left-unit-law-productᵉ
  is-equiv-map-left-unit-law-productᵉ =
    is-equiv-is-invertibleᵉ
      map-inv-left-unit-law-productᵉ
      is-section-map-inv-left-unit-law-productᵉ
      is-retraction-map-inv-left-unit-law-productᵉ

  left-unit-law-productᵉ : (unitᵉ ×ᵉ Aᵉ) ≃ᵉ Aᵉ
  pr1ᵉ left-unit-law-productᵉ = map-left-unit-law-productᵉ
  pr2ᵉ left-unit-law-productᵉ = is-equiv-map-left-unit-law-productᵉ

  is-equiv-map-inv-left-unit-law-productᵉ :
    is-equivᵉ map-inv-left-unit-law-productᵉ
  is-equiv-map-inv-left-unit-law-productᵉ =
    is-equiv-is-invertibleᵉ
      map-left-unit-law-productᵉ
      is-retraction-map-inv-left-unit-law-productᵉ
      is-section-map-inv-left-unit-law-productᵉ

  inv-left-unit-law-productᵉ : Aᵉ ≃ᵉ (unitᵉ ×ᵉ Aᵉ)
  pr1ᵉ inv-left-unit-law-productᵉ = map-inv-left-unit-law-productᵉ
  pr2ᵉ inv-left-unit-law-productᵉ = is-equiv-map-inv-left-unit-law-productᵉ
```

### Right unit law for cartesian products

```agda
  map-right-unit-law-productᵉ : Aᵉ ×ᵉ unitᵉ → Aᵉ
  map-right-unit-law-productᵉ = pr1ᵉ

  map-inv-right-unit-law-productᵉ : Aᵉ → Aᵉ ×ᵉ unitᵉ
  pr1ᵉ (map-inv-right-unit-law-productᵉ aᵉ) = aᵉ
  pr2ᵉ (map-inv-right-unit-law-productᵉ aᵉ) = starᵉ

  is-section-map-inv-right-unit-law-productᵉ :
    is-sectionᵉ map-right-unit-law-productᵉ map-inv-right-unit-law-productᵉ
  is-section-map-inv-right-unit-law-productᵉ = refl-htpyᵉ

  is-retraction-map-inv-right-unit-law-productᵉ :
    is-retractionᵉ map-right-unit-law-productᵉ map-inv-right-unit-law-productᵉ
  is-retraction-map-inv-right-unit-law-productᵉ = refl-htpyᵉ

  is-equiv-map-right-unit-law-productᵉ : is-equivᵉ map-right-unit-law-productᵉ
  is-equiv-map-right-unit-law-productᵉ =
    is-equiv-is-invertibleᵉ
      map-inv-right-unit-law-productᵉ
      is-section-map-inv-right-unit-law-productᵉ
      is-retraction-map-inv-right-unit-law-productᵉ

  right-unit-law-productᵉ : (Aᵉ ×ᵉ unitᵉ) ≃ᵉ Aᵉ
  pr1ᵉ right-unit-law-productᵉ = map-right-unit-law-productᵉ
  pr2ᵉ right-unit-law-productᵉ = is-equiv-map-right-unit-law-productᵉ
```

### Left unit law for dependent function types

```agda
module _
  {lᵉ : Level} (Aᵉ : unitᵉ → UUᵉ lᵉ)
  where

  map-left-unit-law-Πᵉ : ((tᵉ : unitᵉ) → Aᵉ tᵉ) → Aᵉ starᵉ
  map-left-unit-law-Πᵉ fᵉ = fᵉ starᵉ

  map-inv-left-unit-law-Πᵉ : Aᵉ starᵉ → ((tᵉ : unitᵉ) → Aᵉ tᵉ)
  map-inv-left-unit-law-Πᵉ aᵉ _ = aᵉ

  is-section-map-inv-left-unit-law-Πᵉ :
    is-sectionᵉ map-left-unit-law-Πᵉ map-inv-left-unit-law-Πᵉ
  is-section-map-inv-left-unit-law-Πᵉ = refl-htpyᵉ

  is-retraction-map-inv-left-unit-law-Πᵉ :
    is-retractionᵉ map-left-unit-law-Πᵉ map-inv-left-unit-law-Πᵉ
  is-retraction-map-inv-left-unit-law-Πᵉ = refl-htpyᵉ

  is-equiv-map-left-unit-law-Πᵉ : is-equivᵉ map-left-unit-law-Πᵉ
  is-equiv-map-left-unit-law-Πᵉ =
    is-equiv-is-invertibleᵉ
      map-inv-left-unit-law-Πᵉ
      is-section-map-inv-left-unit-law-Πᵉ
      is-retraction-map-inv-left-unit-law-Πᵉ

  left-unit-law-Πᵉ : ((tᵉ : unitᵉ) → Aᵉ tᵉ) ≃ᵉ Aᵉ starᵉ
  pr1ᵉ left-unit-law-Πᵉ = map-left-unit-law-Πᵉ
  pr2ᵉ left-unit-law-Πᵉ = is-equiv-map-left-unit-law-Πᵉ

  is-equiv-map-inv-left-unit-law-Πᵉ : is-equivᵉ map-inv-left-unit-law-Πᵉ
  is-equiv-map-inv-left-unit-law-Πᵉ =
    is-equiv-is-invertibleᵉ
      map-left-unit-law-Πᵉ
      is-retraction-map-inv-left-unit-law-Πᵉ
      is-section-map-inv-left-unit-law-Πᵉ

  inv-left-unit-law-Πᵉ : Aᵉ starᵉ ≃ᵉ ((tᵉ : unitᵉ) → Aᵉ tᵉ)
  pr1ᵉ inv-left-unit-law-Πᵉ = map-inv-left-unit-law-Πᵉ
  pr2ᵉ inv-left-unit-law-Πᵉ = is-equiv-map-inv-left-unit-law-Πᵉ
```

### Left unit law for nondependent function types

```agda
module _
  {lᵉ : Level} (Aᵉ : UUᵉ lᵉ)
  where

  map-left-unit-law-function-typeᵉ : (unitᵉ → Aᵉ) → Aᵉ
  map-left-unit-law-function-typeᵉ = map-left-unit-law-Πᵉ (λ _ → Aᵉ)

  map-inv-left-unit-law-function-typeᵉ : Aᵉ → (unitᵉ → Aᵉ)
  map-inv-left-unit-law-function-typeᵉ = map-inv-left-unit-law-Πᵉ (λ _ → Aᵉ)

  is-equiv-map-left-unit-law-function-typeᵉ :
    is-equivᵉ map-left-unit-law-function-typeᵉ
  is-equiv-map-left-unit-law-function-typeᵉ =
    is-equiv-map-left-unit-law-Πᵉ (λ _ → Aᵉ)

  is-equiv-map-inv-left-unit-law-function-typeᵉ :
    is-equivᵉ map-inv-left-unit-law-function-typeᵉ
  is-equiv-map-inv-left-unit-law-function-typeᵉ =
    is-equiv-map-inv-left-unit-law-Πᵉ (λ _ → Aᵉ)

  left-unit-law-function-typeᵉ : (unitᵉ → Aᵉ) ≃ᵉ Aᵉ
  left-unit-law-function-typeᵉ = left-unit-law-Πᵉ (λ _ → Aᵉ)

  inv-left-unit-law-function-typeᵉ : Aᵉ ≃ᵉ (unitᵉ → Aᵉ)
  inv-left-unit-law-function-typeᵉ = inv-left-unit-law-Πᵉ (λ _ → Aᵉ)
```

## See also

-ᵉ Thatᵉ `unit`ᵉ isᵉ theᵉ terminalᵉ typeᵉ isᵉ aᵉ corollaryᵉ ofᵉ `is-contr-Π`,ᵉ whichᵉ mayᵉ beᵉ
  foundᵉ in
  [`foundation-core.contractible-types`](foundation-core.contractible-types.md).ᵉ
  Thisᵉ canᵉ beᵉ consideredᵉ aᵉ _rightᵉ zeroᵉ lawᵉ forᵉ functionᵉ typesᵉ_
  (`(Aᵉ → unitᵉ) ≃ᵉ unit`).ᵉ