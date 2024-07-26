# Morphisms of inverse sequential diagrams of types

```agda
module foundation.morphisms-inverse-sequential-diagramsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.binary-homotopiesᵉ
open import foundation.dependent-inverse-sequential-diagramsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equality-dependent-function-typesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.homotopy-inductionᵉ
open import foundation.inverse-sequential-diagramsᵉ
open import foundation.structure-identity-principleᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ

open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.torsorial-type-familiesᵉ
```

</details>

## Idea

Aᵉ **morphismᵉ ofᵉ inverseᵉ sequentialᵉ diagrams**ᵉ `Aᵉ → B`ᵉ isᵉ aᵉ commutingᵉ diagramᵉ ofᵉ
theᵉ formᵉ

```text
  ⋯ᵉ ---->ᵉ Aₙ₊₁ᵉ ---->ᵉ Aₙᵉ ---->ᵉ ⋯ᵉ ---->ᵉ A₁ᵉ ---->ᵉ A₀ᵉ
           |         |       |       |        |
  ⋯ᵉ        |         |       ⋯ᵉ       |        |
           ∨ᵉ         ∨ᵉ       ∨ᵉ       ∨ᵉ        ∨ᵉ
  ⋯ᵉ ---->ᵉ Bₙ₊₁ᵉ ---->ᵉ Bₙᵉ ---->ᵉ ⋯ᵉ ---->ᵉ B₁ᵉ ---->ᵉ B₀.ᵉ
```

## Definitions

### Morphisms of inverse sequential diagrams of types

```agda
naturality-hom-inverse-sequential-diagramᵉ :
  {l1ᵉ l2ᵉ : Level}
  (Aᵉ : inverse-sequential-diagramᵉ l1ᵉ)
  (Bᵉ : inverse-sequential-diagramᵉ l2ᵉ)
  (hᵉ :
    (nᵉ : ℕᵉ) →
    family-inverse-sequential-diagramᵉ Aᵉ nᵉ →
    family-inverse-sequential-diagramᵉ Bᵉ nᵉ)
  (nᵉ : ℕᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
naturality-hom-inverse-sequential-diagramᵉ Aᵉ Bᵉ =
  naturality-section-dependent-inverse-sequential-diagramᵉ Aᵉ
    ( const-dependent-inverse-sequential-diagramᵉ Aᵉ Bᵉ)

hom-inverse-sequential-diagramᵉ :
  {l1ᵉ l2ᵉ : Level}
  (Aᵉ : inverse-sequential-diagramᵉ l1ᵉ)
  (Bᵉ : inverse-sequential-diagramᵉ l2ᵉ) →
  UUᵉ (l1ᵉ ⊔ l2ᵉ)
hom-inverse-sequential-diagramᵉ Aᵉ Bᵉ =
  section-dependent-inverse-sequential-diagramᵉ Aᵉ
    ( const-dependent-inverse-sequential-diagramᵉ Aᵉ Bᵉ)

module _
  {l1ᵉ l2ᵉ : Level}
  (Aᵉ : inverse-sequential-diagramᵉ l1ᵉ)
  (Bᵉ : inverse-sequential-diagramᵉ l2ᵉ)
  where

  map-hom-inverse-sequential-diagramᵉ :
    hom-inverse-sequential-diagramᵉ Aᵉ Bᵉ → (nᵉ : ℕᵉ) →
    family-inverse-sequential-diagramᵉ Aᵉ nᵉ →
    family-inverse-sequential-diagramᵉ Bᵉ nᵉ
  map-hom-inverse-sequential-diagramᵉ =
    map-section-dependent-inverse-sequential-diagramᵉ Aᵉ
      ( const-dependent-inverse-sequential-diagramᵉ Aᵉ Bᵉ)

  naturality-map-hom-inverse-sequential-diagramᵉ :
    (fᵉ : hom-inverse-sequential-diagramᵉ Aᵉ Bᵉ) (nᵉ : ℕᵉ) →
    naturality-hom-inverse-sequential-diagramᵉ Aᵉ Bᵉ
      ( map-hom-inverse-sequential-diagramᵉ fᵉ)
      ( nᵉ)
  naturality-map-hom-inverse-sequential-diagramᵉ =
    naturality-map-section-dependent-inverse-sequential-diagramᵉ Aᵉ
      ( const-dependent-inverse-sequential-diagramᵉ Aᵉ Bᵉ)
```

### Identity morphism on inverse sequential diagrams of types

```agda
id-hom-inverse-sequential-diagramᵉ :
  {lᵉ : Level} (Aᵉ : inverse-sequential-diagramᵉ lᵉ) →
  hom-inverse-sequential-diagramᵉ Aᵉ Aᵉ
pr1ᵉ (id-hom-inverse-sequential-diagramᵉ Aᵉ) nᵉ = idᵉ
pr2ᵉ (id-hom-inverse-sequential-diagramᵉ Aᵉ) nᵉ = refl-htpyᵉ
```

### Composition of morphisms of inverse sequential diagrams of types

```agda
map-comp-hom-inverse-sequential-diagramᵉ :
  {lᵉ : Level} (Aᵉ Bᵉ Cᵉ : inverse-sequential-diagramᵉ lᵉ) →
  hom-inverse-sequential-diagramᵉ Bᵉ Cᵉ → hom-inverse-sequential-diagramᵉ Aᵉ Bᵉ →
  (nᵉ : ℕᵉ) →
  family-inverse-sequential-diagramᵉ Aᵉ nᵉ → family-inverse-sequential-diagramᵉ Cᵉ nᵉ
map-comp-hom-inverse-sequential-diagramᵉ Aᵉ Bᵉ Cᵉ gᵉ fᵉ nᵉ =
  map-hom-inverse-sequential-diagramᵉ Bᵉ Cᵉ gᵉ nᵉ ∘ᵉ
  map-hom-inverse-sequential-diagramᵉ Aᵉ Bᵉ fᵉ nᵉ

naturality-comp-hom-inverse-sequential-diagramᵉ :
  {lᵉ : Level} (Aᵉ Bᵉ Cᵉ : inverse-sequential-diagramᵉ lᵉ)
  (gᵉ : hom-inverse-sequential-diagramᵉ Bᵉ Cᵉ)
  (fᵉ : hom-inverse-sequential-diagramᵉ Aᵉ Bᵉ)
  (nᵉ : ℕᵉ) →
  naturality-hom-inverse-sequential-diagramᵉ Aᵉ Cᵉ
    ( map-comp-hom-inverse-sequential-diagramᵉ Aᵉ Bᵉ Cᵉ gᵉ fᵉ)
    ( nᵉ)
naturality-comp-hom-inverse-sequential-diagramᵉ Aᵉ Bᵉ Cᵉ gᵉ fᵉ nᵉ xᵉ =
  ( apᵉ
    ( map-hom-inverse-sequential-diagramᵉ Bᵉ Cᵉ gᵉ nᵉ)
    ( naturality-map-hom-inverse-sequential-diagramᵉ Aᵉ Bᵉ fᵉ nᵉ xᵉ)) ∙ᵉ
  ( naturality-map-hom-inverse-sequential-diagramᵉ Bᵉ Cᵉ gᵉ nᵉ
    ( map-hom-inverse-sequential-diagramᵉ Aᵉ Bᵉ fᵉ (succ-ℕᵉ nᵉ) xᵉ))

comp-hom-inverse-sequential-diagramᵉ :
  {lᵉ : Level} (Aᵉ Bᵉ Cᵉ : inverse-sequential-diagramᵉ lᵉ) →
  hom-inverse-sequential-diagramᵉ Bᵉ Cᵉ →
  hom-inverse-sequential-diagramᵉ Aᵉ Bᵉ →
  hom-inverse-sequential-diagramᵉ Aᵉ Cᵉ
pr1ᵉ (comp-hom-inverse-sequential-diagramᵉ Aᵉ Bᵉ Cᵉ gᵉ fᵉ) =
  map-comp-hom-inverse-sequential-diagramᵉ Aᵉ Bᵉ Cᵉ gᵉ fᵉ
pr2ᵉ (comp-hom-inverse-sequential-diagramᵉ Aᵉ Bᵉ Cᵉ gᵉ fᵉ) =
  naturality-comp-hom-inverse-sequential-diagramᵉ Aᵉ Bᵉ Cᵉ gᵉ fᵉ
```

## Properties

### Characterization of equality of morphisms of inverse sequential diagrams of types

```agda
module _
  {l1ᵉ l2ᵉ : Level}
  (Aᵉ : inverse-sequential-diagramᵉ l1ᵉ)
  (Bᵉ : inverse-sequential-diagramᵉ l2ᵉ)
  where

  coherence-htpy-hom-inverse-sequential-diagramᵉ :
    (fᵉ gᵉ : hom-inverse-sequential-diagramᵉ Aᵉ Bᵉ) →
    ((nᵉ : ℕᵉ) →
      map-hom-inverse-sequential-diagramᵉ Aᵉ Bᵉ fᵉ nᵉ ~ᵉ
      map-hom-inverse-sequential-diagramᵉ Aᵉ Bᵉ gᵉ nᵉ) →
    (nᵉ : ℕᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  coherence-htpy-hom-inverse-sequential-diagramᵉ fᵉ gᵉ Hᵉ nᵉ =
    ( naturality-map-hom-inverse-sequential-diagramᵉ Aᵉ Bᵉ fᵉ nᵉ ∙hᵉ
      map-inverse-sequential-diagramᵉ Bᵉ nᵉ ·lᵉ Hᵉ (succ-ℕᵉ nᵉ)) ~ᵉ
    ( Hᵉ nᵉ ·rᵉ map-inverse-sequential-diagramᵉ Aᵉ nᵉ ∙hᵉ
      naturality-map-hom-inverse-sequential-diagramᵉ Aᵉ Bᵉ gᵉ nᵉ)

  htpy-hom-inverse-sequential-diagramᵉ :
    (fᵉ gᵉ : hom-inverse-sequential-diagramᵉ Aᵉ Bᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  htpy-hom-inverse-sequential-diagramᵉ fᵉ gᵉ =
    Σᵉ ( (nᵉ : ℕᵉ) →
        map-hom-inverse-sequential-diagramᵉ Aᵉ Bᵉ fᵉ nᵉ ~ᵉ
        map-hom-inverse-sequential-diagramᵉ Aᵉ Bᵉ gᵉ nᵉ)
      ( λ Hᵉ → (nᵉ : ℕᵉ) → coherence-htpy-hom-inverse-sequential-diagramᵉ fᵉ gᵉ Hᵉ nᵉ)

  refl-htpy-hom-inverse-sequential-diagramᵉ :
    (fᵉ : hom-inverse-sequential-diagramᵉ Aᵉ Bᵉ) →
    htpy-hom-inverse-sequential-diagramᵉ fᵉ fᵉ
  pr1ᵉ (refl-htpy-hom-inverse-sequential-diagramᵉ fᵉ) nᵉ = refl-htpyᵉ
  pr2ᵉ (refl-htpy-hom-inverse-sequential-diagramᵉ fᵉ) nᵉ = right-unit-htpyᵉ

  htpy-eq-hom-inverse-sequential-diagramᵉ :
    (fᵉ gᵉ : hom-inverse-sequential-diagramᵉ Aᵉ Bᵉ) → fᵉ ＝ᵉ gᵉ →
    htpy-hom-inverse-sequential-diagramᵉ fᵉ gᵉ
  htpy-eq-hom-inverse-sequential-diagramᵉ fᵉ .fᵉ reflᵉ =
    refl-htpy-hom-inverse-sequential-diagramᵉ fᵉ

  is-torsorial-htpy-hom-inverse-sequential-diagramᵉ :
    (fᵉ : hom-inverse-sequential-diagramᵉ Aᵉ Bᵉ) →
    is-torsorialᵉ (htpy-hom-inverse-sequential-diagramᵉ fᵉ)
  is-torsorial-htpy-hom-inverse-sequential-diagramᵉ fᵉ =
    is-torsorial-Eq-structureᵉ
      ( is-torsorial-binary-htpyᵉ (map-hom-inverse-sequential-diagramᵉ Aᵉ Bᵉ fᵉ))
      ( map-hom-inverse-sequential-diagramᵉ Aᵉ Bᵉ fᵉ ,ᵉ
        refl-binary-htpyᵉ (map-hom-inverse-sequential-diagramᵉ Aᵉ Bᵉ fᵉ))
      ( is-torsorial-Eq-Πᵉ
        ( λ nᵉ →
          is-torsorial-htpyᵉ
            ( naturality-map-hom-inverse-sequential-diagramᵉ Aᵉ Bᵉ fᵉ nᵉ ∙hᵉ
              refl-htpyᵉ)))

  is-equiv-htpy-eq-hom-inverse-sequential-diagramᵉ :
    (fᵉ gᵉ : hom-inverse-sequential-diagramᵉ Aᵉ Bᵉ) →
    is-equivᵉ (htpy-eq-hom-inverse-sequential-diagramᵉ fᵉ gᵉ)
  is-equiv-htpy-eq-hom-inverse-sequential-diagramᵉ fᵉ =
    fundamental-theorem-idᵉ
      ( is-torsorial-htpy-hom-inverse-sequential-diagramᵉ fᵉ)
      ( htpy-eq-hom-inverse-sequential-diagramᵉ fᵉ)

  extensionality-hom-inverse-sequential-diagramᵉ :
    (fᵉ gᵉ : hom-inverse-sequential-diagramᵉ Aᵉ Bᵉ) →
    (fᵉ ＝ᵉ gᵉ) ≃ᵉ htpy-hom-inverse-sequential-diagramᵉ fᵉ gᵉ
  pr1ᵉ (extensionality-hom-inverse-sequential-diagramᵉ fᵉ gᵉ) =
    htpy-eq-hom-inverse-sequential-diagramᵉ fᵉ gᵉ
  pr2ᵉ (extensionality-hom-inverse-sequential-diagramᵉ fᵉ gᵉ) =
    is-equiv-htpy-eq-hom-inverse-sequential-diagramᵉ fᵉ gᵉ

  eq-htpy-hom-inverse-sequential-diagramᵉ :
    (fᵉ gᵉ : hom-inverse-sequential-diagramᵉ Aᵉ Bᵉ) →
    htpy-hom-inverse-sequential-diagramᵉ fᵉ gᵉ → fᵉ ＝ᵉ gᵉ
  eq-htpy-hom-inverse-sequential-diagramᵉ fᵉ gᵉ =
    map-inv-equivᵉ (extensionality-hom-inverse-sequential-diagramᵉ fᵉ gᵉ)
```

## Table of files about sequential limits

Theᵉ followingᵉ tableᵉ listsᵉ filesᵉ thatᵉ areᵉ aboutᵉ sequentialᵉ limitsᵉ asᵉ aᵉ generalᵉ
concept.ᵉ

{{#includeᵉ tables/sequential-limits.mdᵉ}}