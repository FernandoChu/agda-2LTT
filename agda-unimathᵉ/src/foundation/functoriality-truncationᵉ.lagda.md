# Functoriality of truncations

```agda
module foundation.functoriality-truncationᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.truncationsᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ

open import foundation-core.commuting-squares-of-mapsᵉ
open import foundation-core.contractible-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.retractionsᵉ
open import foundation-core.retracts-of-typesᵉ
open import foundation-core.sectionsᵉ
open import foundation-core.truncation-levelsᵉ
```

</details>

## Idea

Theᵉ
[universalᵉ propertyᵉ ofᵉ truncations](foundation.universal-property-truncation.mdᵉ)
canᵉ beᵉ usedᵉ to defineᵉ theᵉ functorialᵉ actionᵉ ofᵉ
[truncations](foundation.truncations.md).ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} (kᵉ : 𝕋ᵉ) {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ)
  where

  unique-map-truncᵉ :
    is-contrᵉ
      ( Σᵉ ( type-truncᵉ kᵉ Aᵉ → type-truncᵉ kᵉ Bᵉ)
          ( coherence-square-mapsᵉ fᵉ unit-truncᵉ unit-truncᵉ))
  unique-map-truncᵉ =
    universal-property-truncᵉ kᵉ Aᵉ (truncᵉ kᵉ Bᵉ) (unit-truncᵉ ∘ᵉ fᵉ)

  map-truncᵉ : type-truncᵉ kᵉ Aᵉ → type-truncᵉ kᵉ Bᵉ
  map-truncᵉ = pr1ᵉ (centerᵉ unique-map-truncᵉ)

  coherence-square-map-truncᵉ :
    coherence-square-mapsᵉ fᵉ unit-truncᵉ unit-truncᵉ map-truncᵉ
  coherence-square-map-truncᵉ = pr2ᵉ (centerᵉ unique-map-truncᵉ)
```

## Properties

### Truncations of homotopic maps are homotopic

```agda
naturality-unit-truncᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (kᵉ : 𝕋ᵉ) (fᵉ : Aᵉ → Bᵉ) →
  map-truncᵉ kᵉ fᵉ ∘ᵉ unit-truncᵉ ~ᵉ unit-truncᵉ ∘ᵉ fᵉ
naturality-unit-truncᵉ kᵉ fᵉ = pr2ᵉ (centerᵉ (unique-map-truncᵉ kᵉ fᵉ))

htpy-uniqueness-map-truncᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (kᵉ : 𝕋ᵉ) (fᵉ : Aᵉ → Bᵉ) →
  (hᵉ : type-truncᵉ kᵉ Aᵉ → type-truncᵉ kᵉ Bᵉ) →
  hᵉ ∘ᵉ unit-truncᵉ ~ᵉ unit-truncᵉ ∘ᵉ fᵉ → map-truncᵉ kᵉ fᵉ ~ᵉ hᵉ
htpy-uniqueness-map-truncᵉ kᵉ fᵉ hᵉ Hᵉ =
  htpy-eqᵉ (apᵉ pr1ᵉ (contractionᵉ (unique-map-truncᵉ kᵉ fᵉ) (hᵉ ,ᵉ Hᵉ)))

htpy-truncᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {kᵉ : 𝕋ᵉ} {fᵉ gᵉ : Aᵉ → Bᵉ} →
  fᵉ ~ᵉ gᵉ → map-truncᵉ kᵉ fᵉ ~ᵉ map-truncᵉ kᵉ gᵉ
htpy-truncᵉ {kᵉ = kᵉ} {fᵉ} {gᵉ} Hᵉ =
  htpy-uniqueness-map-truncᵉ
    ( kᵉ)
    ( fᵉ)
    ( map-truncᵉ kᵉ gᵉ)
    ( naturality-unit-truncᵉ kᵉ gᵉ ∙hᵉ inv-htpyᵉ (unit-truncᵉ ·lᵉ Hᵉ))
```

### The truncation of the identity map is the identity map

```agda
id-map-truncᵉ : {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (kᵉ : 𝕋ᵉ) → map-truncᵉ kᵉ (idᵉ {Aᵉ = Aᵉ}) ~ᵉ idᵉ
id-map-truncᵉ kᵉ = htpy-uniqueness-map-truncᵉ kᵉ idᵉ idᵉ refl-htpyᵉ
```

### The truncation of a composite is the composite of the truncations

```agda
preserves-comp-map-truncᵉ :
  { l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} (kᵉ : 𝕋ᵉ)
  ( gᵉ : Bᵉ → Cᵉ) (fᵉ : Aᵉ → Bᵉ) →
  ( map-truncᵉ kᵉ (gᵉ ∘ᵉ fᵉ)) ~ᵉ
  ( (map-truncᵉ kᵉ gᵉ) ∘ᵉ (map-truncᵉ kᵉ fᵉ))
preserves-comp-map-truncᵉ kᵉ gᵉ fᵉ =
  htpy-uniqueness-map-truncᵉ kᵉ
    ( gᵉ ∘ᵉ fᵉ)
    ( map-truncᵉ kᵉ gᵉ ∘ᵉ map-truncᵉ kᵉ fᵉ)
    ( ( map-truncᵉ kᵉ gᵉ ·lᵉ naturality-unit-truncᵉ kᵉ fᵉ) ∙hᵉ
      ( naturality-unit-truncᵉ kᵉ gᵉ ·rᵉ fᵉ))
```

### The functorial action of truncations preserves equivalences

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (kᵉ : 𝕋ᵉ) (eᵉ : Aᵉ ≃ᵉ Bᵉ)
  where

  map-equiv-truncᵉ : type-truncᵉ kᵉ Aᵉ → type-truncᵉ kᵉ Bᵉ
  map-equiv-truncᵉ = map-truncᵉ kᵉ (map-equivᵉ eᵉ)

  map-inv-equiv-truncᵉ : type-truncᵉ kᵉ Bᵉ → type-truncᵉ kᵉ Aᵉ
  map-inv-equiv-truncᵉ = map-truncᵉ kᵉ (map-inv-equivᵉ eᵉ)

  is-equiv-map-equiv-truncᵉ : is-equivᵉ map-equiv-truncᵉ
  is-equiv-map-equiv-truncᵉ =
    is-equiv-is-invertibleᵉ
      ( map-inv-equiv-truncᵉ)
      ( inv-htpyᵉ
        ( preserves-comp-map-truncᵉ kᵉ (map-equivᵉ eᵉ) (map-inv-equivᵉ eᵉ)) ∙hᵉ
        ( htpy-truncᵉ (is-section-map-inv-equivᵉ eᵉ) ∙hᵉ id-map-truncᵉ kᵉ))
      ( inv-htpyᵉ
        ( preserves-comp-map-truncᵉ kᵉ (map-inv-equivᵉ eᵉ) (map-equivᵉ eᵉ)) ∙hᵉ
        ( htpy-truncᵉ (is-retraction-map-inv-equivᵉ eᵉ) ∙hᵉ id-map-truncᵉ kᵉ))

  equiv-truncᵉ : (type-truncᵉ kᵉ Aᵉ ≃ᵉ type-truncᵉ kᵉ Bᵉ)
  pr1ᵉ equiv-truncᵉ = map-equiv-truncᵉ
  pr2ᵉ equiv-truncᵉ = is-equiv-map-equiv-truncᵉ
```

### Truncations preserve retracts

```agda
module _
  {l1ᵉ l2ᵉ : Level} {kᵉ : 𝕋ᵉ} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  section-map-trunc-sectionᵉ :
    (fᵉ : Aᵉ → Bᵉ) → sectionᵉ fᵉ → sectionᵉ (map-truncᵉ kᵉ fᵉ)
  pr1ᵉ (section-map-trunc-sectionᵉ fᵉ Sᵉ) =
    map-truncᵉ kᵉ (map-sectionᵉ fᵉ Sᵉ)
  pr2ᵉ (section-map-trunc-sectionᵉ fᵉ (sᵉ ,ᵉ hᵉ)) =
    homotopy-reasoningᵉ
      map-truncᵉ kᵉ fᵉ ∘ᵉ map-truncᵉ kᵉ sᵉ
      ~ᵉ map-truncᵉ kᵉ (fᵉ ∘ᵉ sᵉ)
        byᵉ inv-htpyᵉ (preserves-comp-map-truncᵉ kᵉ fᵉ sᵉ)
      ~ᵉ map-truncᵉ kᵉ idᵉ
        byᵉ htpy-eqᵉ (apᵉ (map-truncᵉ kᵉ) (eq-htpyᵉ hᵉ))
      ~ᵉ idᵉ
        byᵉ id-map-truncᵉ kᵉ

  retraction-map-trunc-retractionᵉ :
    (fᵉ : Aᵉ → Bᵉ) → retractionᵉ fᵉ → retractionᵉ (map-truncᵉ kᵉ fᵉ)
  pr1ᵉ (retraction-map-trunc-retractionᵉ fᵉ Sᵉ) =
    map-truncᵉ kᵉ (map-retractionᵉ fᵉ Sᵉ)
  pr2ᵉ (retraction-map-trunc-retractionᵉ fᵉ (rᵉ ,ᵉ hᵉ)) =
    homotopy-reasoningᵉ
      map-truncᵉ kᵉ rᵉ ∘ᵉ map-truncᵉ kᵉ fᵉ
      ~ᵉ map-truncᵉ kᵉ (rᵉ ∘ᵉ fᵉ)
        byᵉ inv-htpyᵉ (preserves-comp-map-truncᵉ kᵉ rᵉ fᵉ)
      ~ᵉ map-truncᵉ kᵉ idᵉ
        byᵉ htpy-eqᵉ (apᵉ (map-truncᵉ kᵉ) (eq-htpyᵉ hᵉ))
      ~ᵉ idᵉ
        byᵉ id-map-truncᵉ kᵉ

  retract-of-trunc-retract-ofᵉ :
    Aᵉ retract-ofᵉ Bᵉ → (type-truncᵉ kᵉ Aᵉ) retract-ofᵉ (type-truncᵉ kᵉ Bᵉ)
  pr1ᵉ (retract-of-trunc-retract-ofᵉ Rᵉ) =
    map-truncᵉ kᵉ (inclusion-retractᵉ Rᵉ)
  pr2ᵉ (retract-of-trunc-retract-ofᵉ Rᵉ) =
    retraction-map-trunc-retractionᵉ
      ( inclusion-retractᵉ Rᵉ)
      ( retraction-retractᵉ Rᵉ)
```