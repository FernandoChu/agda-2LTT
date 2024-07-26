# Cones over inverse sequential diagrams

```agda
module foundation.cones-over-inverse-sequential-diagramsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.binary-homotopiesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equality-dependent-function-typesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.homotopy-inductionᵉ
open import foundation.inverse-sequential-diagramsᵉ
open import foundation.structure-identity-principleᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ

open import foundation-core.commuting-triangles-of-mapsᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.torsorial-type-familiesᵉ
```

</details>

## Idea

Aᵉ **coneᵉ overᵉ anᵉ
[inverseᵉ sequentialᵉ diagram](foundation.inverse-sequential-diagrams.mdᵉ) `A`ᵉ with
domainᵉ `X`**ᵉ isᵉ aᵉ [sequence](foundation.dependent-sequences.mdᵉ) ofᵉ functionsᵉ
fromᵉ `X`ᵉ intoᵉ theᵉ sequenceᵉ ofᵉ typesᵉ ofᵉ `A`ᵉ suchᵉ thatᵉ theᵉ trianglesᵉ

```text
     Xᵉ
    /ᵉ \ᵉ
   /ᵉ   \ᵉ
  ∨ᵉ     ∨ᵉ
 Aₙ₊₁ᵉ ->ᵉ Aₙᵉ
```

[commute](foundation-core.commuting-triangles-of-maps.mdᵉ) forᵉ allᵉ `nᵉ : ℕ`.ᵉ

## Definitions

### Cones over inverse sequential diagrams

```agda
module _
  {l1ᵉ : Level} (Aᵉ : inverse-sequential-diagramᵉ l1ᵉ)
  where

  cone-inverse-sequential-diagramᵉ : {l2ᵉ : Level} → UUᵉ l2ᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  cone-inverse-sequential-diagramᵉ Xᵉ =
    Σᵉ ( (nᵉ : ℕᵉ) → Xᵉ → family-inverse-sequential-diagramᵉ Aᵉ nᵉ)
      ( λ fᵉ →
        (nᵉ : ℕᵉ) →
        coherence-triangle-mapsᵉ
          ( fᵉ nᵉ)
          ( map-inverse-sequential-diagramᵉ Aᵉ nᵉ)
          ( fᵉ (succ-ℕᵉ nᵉ)))

  map-cone-inverse-sequential-diagramᵉ :
    {l2ᵉ : Level} {Xᵉ : UUᵉ l2ᵉ} → cone-inverse-sequential-diagramᵉ Xᵉ →
    (nᵉ : ℕᵉ) → Xᵉ → family-inverse-sequential-diagramᵉ Aᵉ nᵉ
  map-cone-inverse-sequential-diagramᵉ = pr1ᵉ

  coherence-cone-inverse-sequential-diagramᵉ :
    {l2ᵉ : Level} {Xᵉ : UUᵉ l2ᵉ} (cᵉ : cone-inverse-sequential-diagramᵉ Xᵉ) (nᵉ : ℕᵉ) →
    coherence-triangle-mapsᵉ
      ( map-cone-inverse-sequential-diagramᵉ cᵉ nᵉ)
      ( map-inverse-sequential-diagramᵉ Aᵉ nᵉ)
      ( map-cone-inverse-sequential-diagramᵉ cᵉ (succ-ℕᵉ nᵉ))
  coherence-cone-inverse-sequential-diagramᵉ = pr2ᵉ
```

### Identifications of cones over inverse sequential diagrams of types

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : inverse-sequential-diagramᵉ l1ᵉ) {Xᵉ : UUᵉ l2ᵉ}
  where

  coherence-htpy-cone-inverse-sequential-diagramᵉ :
    (cᵉ c'ᵉ : cone-inverse-sequential-diagramᵉ Aᵉ Xᵉ) →
    ( (nᵉ : ℕᵉ) →
      map-cone-inverse-sequential-diagramᵉ Aᵉ cᵉ nᵉ ~ᵉ
      map-cone-inverse-sequential-diagramᵉ Aᵉ c'ᵉ nᵉ) →
    UUᵉ (l1ᵉ ⊔ l2ᵉ)
  coherence-htpy-cone-inverse-sequential-diagramᵉ cᵉ c'ᵉ Hᵉ =
    (nᵉ : ℕᵉ) →
    ( coherence-cone-inverse-sequential-diagramᵉ Aᵉ cᵉ nᵉ ∙hᵉ
      map-inverse-sequential-diagramᵉ Aᵉ nᵉ ·lᵉ Hᵉ (succ-ℕᵉ nᵉ)) ~ᵉ
    ( Hᵉ nᵉ ∙hᵉ coherence-cone-inverse-sequential-diagramᵉ Aᵉ c'ᵉ nᵉ)

  htpy-cone-inverse-sequential-diagramᵉ :
    cone-inverse-sequential-diagramᵉ Aᵉ Xᵉ →
    cone-inverse-sequential-diagramᵉ Aᵉ Xᵉ →
    UUᵉ (l1ᵉ ⊔ l2ᵉ)
  htpy-cone-inverse-sequential-diagramᵉ cᵉ c'ᵉ =
    Σᵉ ( (nᵉ : ℕᵉ) →
        map-cone-inverse-sequential-diagramᵉ Aᵉ cᵉ nᵉ ~ᵉ
        map-cone-inverse-sequential-diagramᵉ Aᵉ c'ᵉ nᵉ)
      ( coherence-htpy-cone-inverse-sequential-diagramᵉ cᵉ c'ᵉ)

  refl-htpy-cone-inverse-sequential-diagramᵉ :
    (cᵉ : cone-inverse-sequential-diagramᵉ Aᵉ Xᵉ) →
    htpy-cone-inverse-sequential-diagramᵉ cᵉ cᵉ
  pr1ᵉ (refl-htpy-cone-inverse-sequential-diagramᵉ cᵉ) nᵉ = refl-htpyᵉ
  pr2ᵉ (refl-htpy-cone-inverse-sequential-diagramᵉ cᵉ) nᵉ = right-unit-htpyᵉ

  htpy-eq-cone-inverse-sequential-diagramᵉ :
    (cᵉ c'ᵉ : cone-inverse-sequential-diagramᵉ Aᵉ Xᵉ) →
    cᵉ ＝ᵉ c'ᵉ → htpy-cone-inverse-sequential-diagramᵉ cᵉ c'ᵉ
  htpy-eq-cone-inverse-sequential-diagramᵉ cᵉ .cᵉ reflᵉ =
    refl-htpy-cone-inverse-sequential-diagramᵉ cᵉ

  is-torsorial-htpy-cone-inverse-sequential-diagramᵉ :
    (cᵉ : cone-inverse-sequential-diagramᵉ Aᵉ Xᵉ) →
    is-torsorialᵉ (htpy-cone-inverse-sequential-diagramᵉ cᵉ)
  is-torsorial-htpy-cone-inverse-sequential-diagramᵉ cᵉ =
    is-torsorial-Eq-structureᵉ
      ( is-torsorial-binary-htpyᵉ (map-cone-inverse-sequential-diagramᵉ Aᵉ cᵉ))
      ( map-cone-inverse-sequential-diagramᵉ Aᵉ cᵉ ,ᵉ (λ nᵉ → refl-htpyᵉ))
      ( is-torsorial-Eq-Πᵉ
        ( λ nᵉ →
          is-torsorial-htpyᵉ
            ( coherence-cone-inverse-sequential-diagramᵉ Aᵉ cᵉ nᵉ ∙hᵉ refl-htpyᵉ)))

  is-equiv-htpy-eq-cone-inverse-sequential-diagramᵉ :
    (cᵉ c'ᵉ : cone-inverse-sequential-diagramᵉ Aᵉ Xᵉ) →
    is-equivᵉ (htpy-eq-cone-inverse-sequential-diagramᵉ cᵉ c'ᵉ)
  is-equiv-htpy-eq-cone-inverse-sequential-diagramᵉ cᵉ =
    fundamental-theorem-idᵉ
      ( is-torsorial-htpy-cone-inverse-sequential-diagramᵉ cᵉ)
      ( htpy-eq-cone-inverse-sequential-diagramᵉ cᵉ)

  extensionality-cone-inverse-sequential-diagramᵉ :
    (cᵉ c'ᵉ : cone-inverse-sequential-diagramᵉ Aᵉ Xᵉ) →
    (cᵉ ＝ᵉ c'ᵉ) ≃ᵉ htpy-cone-inverse-sequential-diagramᵉ cᵉ c'ᵉ
  pr1ᵉ (extensionality-cone-inverse-sequential-diagramᵉ cᵉ c'ᵉ) =
    htpy-eq-cone-inverse-sequential-diagramᵉ cᵉ c'ᵉ
  pr2ᵉ (extensionality-cone-inverse-sequential-diagramᵉ cᵉ c'ᵉ) =
    is-equiv-htpy-eq-cone-inverse-sequential-diagramᵉ cᵉ c'ᵉ

  eq-htpy-cone-inverse-sequential-diagramᵉ :
    (cᵉ c'ᵉ : cone-inverse-sequential-diagramᵉ Aᵉ Xᵉ) →
    htpy-cone-inverse-sequential-diagramᵉ cᵉ c'ᵉ → cᵉ ＝ᵉ c'ᵉ
  eq-htpy-cone-inverse-sequential-diagramᵉ cᵉ c'ᵉ =
    map-inv-equivᵉ (extensionality-cone-inverse-sequential-diagramᵉ cᵉ c'ᵉ)
```

### Precomposing cones over inverse sequential diagrams with a map

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Aᵉ : inverse-sequential-diagramᵉ l1ᵉ) {Xᵉ : UUᵉ l2ᵉ} {Yᵉ : UUᵉ l3ᵉ}
  where

  cone-map-inverse-sequential-diagramᵉ :
    cone-inverse-sequential-diagramᵉ Aᵉ Xᵉ →
    (Yᵉ → Xᵉ) → cone-inverse-sequential-diagramᵉ Aᵉ Yᵉ
  pr1ᵉ (cone-map-inverse-sequential-diagramᵉ cᵉ fᵉ) nᵉ xᵉ =
    map-cone-inverse-sequential-diagramᵉ Aᵉ cᵉ nᵉ (fᵉ xᵉ)
  pr2ᵉ (cone-map-inverse-sequential-diagramᵉ cᵉ fᵉ) nᵉ xᵉ =
    coherence-cone-inverse-sequential-diagramᵉ Aᵉ cᵉ nᵉ (fᵉ xᵉ)
```

### Postcomposition cones over postcomposition inverse sequential diagrams

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Xᵉ : UUᵉ l1ᵉ) (Aᵉ : inverse-sequential-diagramᵉ l2ᵉ)
  {Yᵉ : UUᵉ l3ᵉ} (cᵉ : cone-inverse-sequential-diagramᵉ Aᵉ Yᵉ)
  where

  cone-postcomp-inverse-sequential-diagramᵉ :
    cone-inverse-sequential-diagramᵉ
      ( postcomp-inverse-sequential-diagramᵉ Xᵉ Aᵉ)
      ( Xᵉ → Yᵉ)
  pr1ᵉ cone-postcomp-inverse-sequential-diagramᵉ nᵉ gᵉ xᵉ =
    map-cone-inverse-sequential-diagramᵉ Aᵉ cᵉ nᵉ (gᵉ xᵉ)
  pr2ᵉ cone-postcomp-inverse-sequential-diagramᵉ nᵉ gᵉ =
    eq-htpyᵉ (λ xᵉ → coherence-cone-inverse-sequential-diagramᵉ Aᵉ cᵉ nᵉ (gᵉ xᵉ))
```

## Table of files about sequential limits

Theᵉ followingᵉ tableᵉ listsᵉ filesᵉ thatᵉ areᵉ aboutᵉ sequentialᵉ limitsᵉ asᵉ aᵉ generalᵉ
concept.ᵉ

{{#includeᵉ tables/sequential-limits.mdᵉ}}