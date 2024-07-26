# The universal property of truncations

```agda
module foundation-core.universal-property-truncationᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.universal-property-equivalencesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.contractible-mapsᵉ
open import foundation-core.contractible-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.functoriality-dependent-pair-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.precomposition-functionsᵉ
open import foundation-core.sectionsᵉ
open import foundation-core.truncated-typesᵉ
open import foundation-core.truncation-levelsᵉ
open import foundation-core.type-theoretic-principle-of-choiceᵉ
```

</details>

## Idea

Weᵉ sayᵉ thatᵉ aᵉ mapᵉ `fᵉ : Aᵉ → B`ᵉ intoᵉ aᵉ `k`-truncatedᵉ typeᵉ `B`ᵉ isᵉ aᵉ
**`k`-truncation**ᵉ ofᵉ `A`ᵉ --ᵉ orᵉ thatᵉ itᵉ **satisfiesᵉ theᵉ universalᵉ propertyᵉ ofᵉ
theᵉ `k`-truncation**ᵉ ofᵉ `A`ᵉ --ᵉ ifᵉ anyᵉ mapᵉ `gᵉ : Aᵉ → C`ᵉ intoᵉ aᵉ `k`-truncatedᵉ typeᵉ
`C`ᵉ extendsᵉ uniquelyᵉ alongᵉ `f`ᵉ to aᵉ mapᵉ `Bᵉ → C`.ᵉ

## Definition

### The condition on a map to be a truncation

```agda
precomp-Truncᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {kᵉ : 𝕋ᵉ} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ)
  (Cᵉ : Truncated-Typeᵉ l3ᵉ kᵉ) →
  (Bᵉ → type-Truncated-Typeᵉ Cᵉ) → (Aᵉ → type-Truncated-Typeᵉ Cᵉ)
precomp-Truncᵉ fᵉ Cᵉ = precompᵉ fᵉ (type-Truncated-Typeᵉ Cᵉ)

module _
  {l1ᵉ l2ᵉ : Level} {kᵉ : 𝕋ᵉ} {Aᵉ : UUᵉ l1ᵉ}
  (Bᵉ : Truncated-Typeᵉ l2ᵉ kᵉ) (fᵉ : Aᵉ → type-Truncated-Typeᵉ Bᵉ)
  where

  is-truncationᵉ : UUωᵉ
  is-truncationᵉ =
    {lᵉ : Level} (Cᵉ : Truncated-Typeᵉ lᵉ kᵉ) → is-equivᵉ (precomp-Truncᵉ fᵉ Cᵉ)

  equiv-is-truncationᵉ :
    {l3ᵉ : Level} (Hᵉ : is-truncationᵉ) (Cᵉ : Truncated-Typeᵉ l3ᵉ kᵉ) →
    ( type-Truncated-Typeᵉ Bᵉ → type-Truncated-Typeᵉ Cᵉ) ≃ᵉ
    ( Aᵉ → type-Truncated-Typeᵉ Cᵉ)
  pr1ᵉ (equiv-is-truncationᵉ Hᵉ Cᵉ) = precomp-Truncᵉ fᵉ Cᵉ
  pr2ᵉ (equiv-is-truncationᵉ Hᵉ Cᵉ) = Hᵉ Cᵉ
```

### The universal property of truncations

```agda
module _
  {l1ᵉ l2ᵉ : Level} {kᵉ : 𝕋ᵉ} {Aᵉ : UUᵉ l1ᵉ}
  (Bᵉ : Truncated-Typeᵉ l2ᵉ kᵉ) (fᵉ : Aᵉ → type-Truncated-Typeᵉ Bᵉ)
  where

  universal-property-truncationᵉ : UUωᵉ
  universal-property-truncationᵉ =
    {lᵉ : Level} (Cᵉ : Truncated-Typeᵉ lᵉ kᵉ) (gᵉ : Aᵉ → type-Truncated-Typeᵉ Cᵉ) →
    is-contrᵉ (Σᵉ (type-hom-Truncated-Typeᵉ kᵉ Bᵉ Cᵉ) (λ hᵉ → hᵉ ∘ᵉ fᵉ ~ᵉ gᵉ))
```

### The dependent universal property of truncations

```agda
precomp-Π-Truncated-Typeᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {kᵉ : 𝕋ᵉ} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ)
  (Cᵉ : Bᵉ → Truncated-Typeᵉ l3ᵉ kᵉ) →
  ((bᵉ : Bᵉ) → type-Truncated-Typeᵉ (Cᵉ bᵉ)) →
  ((aᵉ : Aᵉ) → type-Truncated-Typeᵉ (Cᵉ (fᵉ aᵉ)))
precomp-Π-Truncated-Typeᵉ fᵉ Cᵉ hᵉ aᵉ = hᵉ (fᵉ aᵉ)

module _
  {l1ᵉ l2ᵉ : Level} {kᵉ : 𝕋ᵉ} {Aᵉ : UUᵉ l1ᵉ}
  (Bᵉ : Truncated-Typeᵉ l2ᵉ kᵉ) (fᵉ : Aᵉ → type-Truncated-Typeᵉ Bᵉ)
  where

  dependent-universal-property-truncationᵉ : UUωᵉ
  dependent-universal-property-truncationᵉ =
    {lᵉ : Level} (Xᵉ : type-Truncated-Typeᵉ Bᵉ → Truncated-Typeᵉ lᵉ kᵉ) →
    is-equivᵉ (precomp-Π-Truncated-Typeᵉ fᵉ Xᵉ)
```

## Properties

### Equivalences into `k`-truncated types are truncations

```agda
abstract
  is-truncation-idᵉ :
    {l1ᵉ : Level} {kᵉ : 𝕋ᵉ} {Aᵉ : UUᵉ l1ᵉ} (Hᵉ : is-truncᵉ kᵉ Aᵉ) →
    is-truncationᵉ (Aᵉ ,ᵉ Hᵉ) idᵉ
  is-truncation-idᵉ Hᵉ Bᵉ =
    is-equiv-precomp-is-equivᵉ idᵉ is-equiv-idᵉ (type-Truncated-Typeᵉ Bᵉ)

abstract
  is-truncation-equivᵉ :
    {l1ᵉ l2ᵉ : Level} {kᵉ : 𝕋ᵉ} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : Truncated-Typeᵉ l2ᵉ kᵉ)
    (eᵉ : Aᵉ ≃ᵉ type-Truncated-Typeᵉ Bᵉ) →
    is-truncationᵉ Bᵉ (map-equivᵉ eᵉ)
  is-truncation-equivᵉ Bᵉ eᵉ Cᵉ =
    is-equiv-precomp-is-equivᵉ
      ( map-equivᵉ eᵉ)
      ( is-equiv-map-equivᵉ eᵉ)
      ( type-Truncated-Typeᵉ Cᵉ)
```

### A map into a truncated type is a truncation if and only if it satisfies the universal property of the truncation

```agda
module _
  {l1ᵉ l2ᵉ : Level} {kᵉ : 𝕋ᵉ} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : Truncated-Typeᵉ l2ᵉ kᵉ)
  (fᵉ : Aᵉ → type-Truncated-Typeᵉ Bᵉ)
  where

  abstract
    is-truncation-universal-property-truncationᵉ :
      universal-property-truncationᵉ Bᵉ fᵉ → is-truncationᵉ Bᵉ fᵉ
    is-truncation-universal-property-truncationᵉ Hᵉ Cᵉ =
      is-equiv-is-contr-mapᵉ
        ( λ gᵉ →
          is-contr-equivᵉ
            ( Σᵉ (type-hom-Truncated-Typeᵉ kᵉ Bᵉ Cᵉ) (λ hᵉ → (hᵉ ∘ᵉ fᵉ) ~ᵉ gᵉ))
            ( equiv-totᵉ (λ hᵉ → equiv-funextᵉ))
            ( Hᵉ Cᵉ gᵉ))

  abstract
    universal-property-truncation-is-truncationᵉ :
      is-truncationᵉ Bᵉ fᵉ → universal-property-truncationᵉ Bᵉ fᵉ
    universal-property-truncation-is-truncationᵉ Hᵉ Cᵉ gᵉ =
      is-contr-equiv'ᵉ
        ( Σᵉ (type-hom-Truncated-Typeᵉ kᵉ Bᵉ Cᵉ) (λ hᵉ → (hᵉ ∘ᵉ fᵉ) ＝ᵉ gᵉ))
        ( equiv-totᵉ (λ hᵉ → equiv-funextᵉ))
        ( is-contr-map-is-equivᵉ (Hᵉ Cᵉ) gᵉ)

  map-is-truncationᵉ :
    is-truncationᵉ Bᵉ fᵉ →
    {lᵉ : Level} (Cᵉ : Truncated-Typeᵉ lᵉ kᵉ) (gᵉ : Aᵉ → type-Truncated-Typeᵉ Cᵉ) →
    type-hom-Truncated-Typeᵉ kᵉ Bᵉ Cᵉ
  map-is-truncationᵉ Hᵉ Cᵉ gᵉ =
    pr1ᵉ (centerᵉ (universal-property-truncation-is-truncationᵉ Hᵉ Cᵉ gᵉ))

  triangle-is-truncationᵉ :
    (Hᵉ : is-truncationᵉ Bᵉ fᵉ) →
    {lᵉ : Level} (Cᵉ : Truncated-Typeᵉ lᵉ kᵉ) (gᵉ : Aᵉ → type-Truncated-Typeᵉ Cᵉ) →
    map-is-truncationᵉ Hᵉ Cᵉ gᵉ ∘ᵉ fᵉ ~ᵉ gᵉ
  triangle-is-truncationᵉ Hᵉ Cᵉ gᵉ =
    pr2ᵉ (centerᵉ (universal-property-truncation-is-truncationᵉ Hᵉ Cᵉ gᵉ))
```

### A map into a truncated type is a truncation if and only if it satisfies the dependent universal property of the truncation

```agda
module _
  {l1ᵉ l2ᵉ : Level} {kᵉ : 𝕋ᵉ} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : Truncated-Typeᵉ l2ᵉ kᵉ)
  (fᵉ : Aᵉ → type-Truncated-Typeᵉ Bᵉ)
  where

  abstract
    dependent-universal-property-truncation-is-truncationᵉ :
      is-truncationᵉ Bᵉ fᵉ →
      dependent-universal-property-truncationᵉ Bᵉ fᵉ
    dependent-universal-property-truncation-is-truncationᵉ Hᵉ Xᵉ =
      is-fiberwise-equiv-is-equiv-map-Σᵉ
        ( λ (hᵉ : Aᵉ → type-Truncated-Typeᵉ Bᵉ) →
          (aᵉ : Aᵉ) → type-Truncated-Typeᵉ (Xᵉ (hᵉ aᵉ)))
        ( λ (gᵉ : type-Truncated-Typeᵉ Bᵉ → type-Truncated-Typeᵉ Bᵉ) → gᵉ ∘ᵉ fᵉ)
        ( λ gᵉ (sᵉ : (bᵉ : type-Truncated-Typeᵉ Bᵉ) →
          type-Truncated-Typeᵉ (Xᵉ (gᵉ bᵉ))) (aᵉ : Aᵉ) → sᵉ (fᵉ aᵉ))
        ( Hᵉ Bᵉ)
        ( is-equiv-equivᵉ
          ( inv-distributive-Π-Σᵉ)
          ( inv-distributive-Π-Σᵉ)
          ( ind-Σᵉ (λ gᵉ sᵉ → reflᵉ))
          ( Hᵉ (Σ-Truncated-Typeᵉ Bᵉ Xᵉ)))
        ( idᵉ)

  abstract
    is-truncation-dependent-universal-property-truncationᵉ :
      dependent-universal-property-truncationᵉ Bᵉ fᵉ → is-truncationᵉ Bᵉ fᵉ
    is-truncation-dependent-universal-property-truncationᵉ Hᵉ Xᵉ = Hᵉ (λ _ → Xᵉ)

  section-is-truncationᵉ :
    is-truncationᵉ Bᵉ fᵉ →
    {l3ᵉ : Level} (Cᵉ : Truncated-Typeᵉ l3ᵉ kᵉ)
    (hᵉ : Aᵉ → type-Truncated-Typeᵉ Cᵉ) (gᵉ : type-hom-Truncated-Typeᵉ kᵉ Cᵉ Bᵉ) →
    fᵉ ~ᵉ gᵉ ∘ᵉ hᵉ → sectionᵉ gᵉ
  section-is-truncationᵉ Hᵉ Cᵉ hᵉ gᵉ Kᵉ =
    map-distributive-Π-Σᵉ
      ( map-inv-is-equivᵉ
        ( dependent-universal-property-truncation-is-truncationᵉ Hᵉ
          ( fiber-Truncated-Typeᵉ Cᵉ Bᵉ gᵉ))
        ( λ aᵉ → (hᵉ aᵉ ,ᵉ invᵉ (Kᵉ aᵉ))))
```