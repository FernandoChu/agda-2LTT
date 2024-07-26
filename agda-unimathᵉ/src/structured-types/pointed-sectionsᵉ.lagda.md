# Pointed sections of pointed maps

```agda
module structured-types.pointed-sectionsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.sectionsᵉ
open import foundation.universe-levelsᵉ

open import structured-types.pointed-homotopiesᵉ
open import structured-types.pointed-mapsᵉ
open import structured-types.pointed-typesᵉ
```

</details>

## Idea

Aᵉ
{{#conceptᵉ "pointedᵉ section"ᵉ Disambiguation="pointedᵉ map"ᵉ Agda=pointed-sectionᵉ}}
ofᵉ aᵉ [pointedᵉ map](structured-types.pointed-maps.mdᵉ) `fᵉ : Aᵉ →∗ᵉ B`ᵉ consistsᵉ ofᵉ aᵉ
pointedᵉ mapᵉ `gᵉ : Bᵉ →∗ᵉ A`ᵉ equippedᵉ with aᵉ
[pointedᵉ homotopy](structured-types.pointed-homotopies.mdᵉ) `Hᵉ : fᵉ ∘∗ᵉ gᵉ ~∗ᵉ id`.ᵉ

## Definitions

### The predicate of being a pointed section of a pointed map

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : Pointed-Typeᵉ l1ᵉ} {Bᵉ : Pointed-Typeᵉ l2ᵉ} (fᵉ : Aᵉ →∗ᵉ Bᵉ)
  where

  is-pointed-sectionᵉ : (Bᵉ →∗ᵉ Aᵉ) → UUᵉ l2ᵉ
  is-pointed-sectionᵉ gᵉ = fᵉ ∘∗ᵉ gᵉ ~∗ᵉ id-pointed-mapᵉ
```

### The type of pointed sections of a pointed map

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : Pointed-Typeᵉ l1ᵉ} {Bᵉ : Pointed-Typeᵉ l2ᵉ} (fᵉ : Aᵉ →∗ᵉ Bᵉ)
  where

  pointed-sectionᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  pointed-sectionᵉ =
    Σᵉ (Bᵉ →∗ᵉ Aᵉ) (is-pointed-sectionᵉ fᵉ)

  module _
    (sᵉ : pointed-sectionᵉ)
    where

    pointed-map-pointed-sectionᵉ : Bᵉ →∗ᵉ Aᵉ
    pointed-map-pointed-sectionᵉ = pr1ᵉ sᵉ

    is-pointed-section-pointed-sectionᵉ :
      is-pointed-sectionᵉ fᵉ pointed-map-pointed-sectionᵉ
    is-pointed-section-pointed-sectionᵉ = pr2ᵉ sᵉ

    map-pointed-sectionᵉ : type-Pointed-Typeᵉ Bᵉ → type-Pointed-Typeᵉ Aᵉ
    map-pointed-sectionᵉ = map-pointed-mapᵉ pointed-map-pointed-sectionᵉ

    preserves-point-pointed-map-pointed-sectionᵉ :
      map-pointed-sectionᵉ (point-Pointed-Typeᵉ Bᵉ) ＝ᵉ point-Pointed-Typeᵉ Aᵉ
    preserves-point-pointed-map-pointed-sectionᵉ =
      preserves-point-pointed-mapᵉ pointed-map-pointed-sectionᵉ

    is-section-pointed-sectionᵉ :
      is-sectionᵉ (map-pointed-mapᵉ fᵉ) map-pointed-sectionᵉ
    is-section-pointed-sectionᵉ =
      htpy-pointed-htpyᵉ is-pointed-section-pointed-sectionᵉ

    section-pointed-sectionᵉ : sectionᵉ (map-pointed-mapᵉ fᵉ)
    pr1ᵉ section-pointed-sectionᵉ = map-pointed-sectionᵉ
    pr2ᵉ section-pointed-sectionᵉ = is-section-pointed-sectionᵉ

    coherence-point-is-section-pointed-sectionᵉ :
      coherence-point-unpointed-htpy-pointed-Πᵉ
        ( fᵉ ∘∗ᵉ pointed-map-pointed-sectionᵉ)
        ( id-pointed-mapᵉ)
        ( is-section-pointed-sectionᵉ)
    coherence-point-is-section-pointed-sectionᵉ =
      coherence-point-pointed-htpyᵉ is-pointed-section-pointed-sectionᵉ
```