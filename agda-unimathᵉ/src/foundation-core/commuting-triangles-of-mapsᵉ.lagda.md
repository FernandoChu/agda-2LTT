# Commuting triangles of maps

```agda
module foundation-core.commuting-triangles-of-mapsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ

open import foundation-core.function-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.retractionsᵉ
open import foundation-core.sectionsᵉ
```

</details>

## Idea

Aᵉ triangleᵉ ofᵉ mapsᵉ

```text
        topᵉ
     Aᵉ ---->ᵉ Bᵉ
      \ᵉ     /ᵉ
  leftᵉ \ᵉ   /ᵉ rightᵉ
        ∨ᵉ ∨ᵉ
         Xᵉ
```

isᵉ saidᵉ to **commute**ᵉ ifᵉ thereᵉ isᵉ aᵉ [homotopy](foundation-core.homotopies.mdᵉ)
betweenᵉ theᵉ mapᵉ onᵉ theᵉ leftᵉ andᵉ theᵉ compositeᵉ ofᵉ theᵉ topᵉ andᵉ rightᵉ mapsᵉ:

```text
  leftᵉ ~ᵉ rightᵉ ∘ᵉ top.ᵉ
```

## Definitions

### Commuting triangles of maps

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ}
  where

  coherence-triangle-mapsᵉ :
    (leftᵉ : Aᵉ → Xᵉ) (rightᵉ : Bᵉ → Xᵉ) (topᵉ : Aᵉ → Bᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  coherence-triangle-mapsᵉ leftᵉ rightᵉ topᵉ = leftᵉ ~ᵉ rightᵉ ∘ᵉ topᵉ

  coherence-triangle-maps'ᵉ :
    (leftᵉ : Aᵉ → Xᵉ) (rightᵉ : Bᵉ → Xᵉ) (topᵉ : Aᵉ → Bᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  coherence-triangle-maps'ᵉ leftᵉ rightᵉ topᵉ = rightᵉ ∘ᵉ topᵉ ~ᵉ leftᵉ
```

### Concatenation of commuting triangles of maps

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ} {Cᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ) (hᵉ : Cᵉ → Xᵉ) (iᵉ : Aᵉ → Bᵉ) (jᵉ : Bᵉ → Cᵉ)
  where

  concat-coherence-triangle-mapsᵉ :
    coherence-triangle-mapsᵉ fᵉ gᵉ iᵉ →
    coherence-triangle-mapsᵉ gᵉ hᵉ jᵉ →
    coherence-triangle-mapsᵉ fᵉ hᵉ (jᵉ ∘ᵉ iᵉ)
  concat-coherence-triangle-mapsᵉ Hᵉ Kᵉ =
    Hᵉ ∙hᵉ (Kᵉ ·rᵉ iᵉ)
```

## Properties

### If the top map has a section, then the reversed triangle with the section on top commutes

Ifᵉ `tᵉ : Bᵉ → A`ᵉ isᵉ aᵉ [section](foundation-core.sections.mdᵉ) ofᵉ theᵉ topᵉ mapᵉ `h`,ᵉ
thenᵉ theᵉ triangleᵉ

```text
       tᵉ
  Bᵉ ------>ᵉ Aᵉ
   \ᵉ       /ᵉ
   g\ᵉ     /fᵉ
     \ᵉ   /ᵉ
      ∨ᵉ ∨ᵉ
       Xᵉ
```

commutes.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ}
  (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ) (hᵉ : Aᵉ → Bᵉ) (Hᵉ : coherence-triangle-mapsᵉ fᵉ gᵉ hᵉ)
  (tᵉ : sectionᵉ hᵉ)
  where

  inv-triangle-sectionᵉ : coherence-triangle-maps'ᵉ gᵉ fᵉ (map-sectionᵉ hᵉ tᵉ)
  inv-triangle-sectionᵉ =
    (Hᵉ ·rᵉ map-sectionᵉ hᵉ tᵉ) ∙hᵉ (gᵉ ·lᵉ is-section-map-sectionᵉ hᵉ tᵉ)

  triangle-sectionᵉ : coherence-triangle-mapsᵉ gᵉ fᵉ (map-sectionᵉ hᵉ tᵉ)
  triangle-sectionᵉ = inv-htpyᵉ inv-triangle-sectionᵉ
```

### If the right map has a retraction, then the reversed triangle with the retraction on the right commutes

Ifᵉ `rᵉ : Xᵉ → B`ᵉ isᵉ aᵉ retractionᵉ ofᵉ theᵉ rightᵉ mapᵉ `g`ᵉ in aᵉ triangleᵉ `fᵉ ~ᵉ gᵉ ∘ᵉ h`,ᵉ
thenᵉ theᵉ triangleᵉ

```text
       fᵉ
  Aᵉ ------>ᵉ Xᵉ
   \ᵉ       /ᵉ
   h\ᵉ     /rᵉ
     \ᵉ   /ᵉ
      ∨ᵉ ∨ᵉ
       Bᵉ
```

commutes.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ}
  (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ) (hᵉ : Aᵉ → Bᵉ) (Hᵉ : coherence-triangle-mapsᵉ fᵉ gᵉ hᵉ)
  (rᵉ : retractionᵉ gᵉ)
  where

  inv-triangle-retractionᵉ : coherence-triangle-maps'ᵉ hᵉ (map-retractionᵉ gᵉ rᵉ) fᵉ
  inv-triangle-retractionᵉ =
    (map-retractionᵉ gᵉ rᵉ ·lᵉ Hᵉ) ∙hᵉ (is-retraction-map-retractionᵉ gᵉ rᵉ ·rᵉ hᵉ)

  triangle-retractionᵉ : coherence-triangle-mapsᵉ hᵉ (map-retractionᵉ gᵉ rᵉ) fᵉ
  triangle-retractionᵉ = inv-htpyᵉ inv-triangle-retractionᵉ
```