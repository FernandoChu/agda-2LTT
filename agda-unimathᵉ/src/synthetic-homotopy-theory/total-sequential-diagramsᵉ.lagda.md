# Total sequential diagrams of dependent sequential diagrams

```agda
module synthetic-homotopy-theory.total-sequential-diagramsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.universe-levelsᵉ

open import synthetic-homotopy-theory.cocones-under-sequential-diagramsᵉ
open import synthetic-homotopy-theory.dependent-sequential-diagramsᵉ
open import synthetic-homotopy-theory.equivalences-dependent-sequential-diagramsᵉ
open import synthetic-homotopy-theory.equivalences-sequential-diagramsᵉ
open import synthetic-homotopy-theory.functoriality-sequential-colimitsᵉ
open import synthetic-homotopy-theory.morphisms-sequential-diagramsᵉ
open import synthetic-homotopy-theory.sequential-colimitsᵉ
open import synthetic-homotopy-theory.sequential-diagramsᵉ
open import synthetic-homotopy-theory.universal-property-sequential-colimitsᵉ
```

</details>

## Idea

Theᵉ
{{#conceptᵉ "totalᵉ diagram"ᵉ Disambiguation="dependentᵉ sequentialᵉ diagrams"ᵉ Agda=total-sequential-diagramᵉ}}
ofᵉ aᵉ
[dependentᵉ sequentialᵉ diagram](synthetic-homotopy-theory.dependent-sequential-diagrams.mdᵉ)
`Bᵉ : (A,ᵉ aᵉ) → 𝒰`ᵉ isᵉ theᵉ
[sequentialᵉ diagram](synthetic-homotopy-theory.sequential-diagrams.mdᵉ)
consistingᵉ ofᵉ [totalᵉ spaces](foundation.dependent-pair-types.mdᵉ) `Σᵉ Aₙᵉ Bₙ`ᵉ andᵉ
totalᵉ maps.ᵉ

## Definitions

### The total sequential diagram of a dependent sequential diagram

```agda
module _
  {l1ᵉ l2ᵉ : Level}
  {Aᵉ : sequential-diagramᵉ l1ᵉ} (Bᵉ : dependent-sequential-diagramᵉ Aᵉ l2ᵉ)
  where

  family-total-sequential-diagramᵉ : ℕᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  family-total-sequential-diagramᵉ nᵉ =
    Σᵉ (family-sequential-diagramᵉ Aᵉ nᵉ)
      (family-dependent-sequential-diagramᵉ Bᵉ nᵉ)

  map-total-sequential-diagramᵉ :
    (nᵉ : ℕᵉ) → family-total-sequential-diagramᵉ nᵉ →
    family-total-sequential-diagramᵉ (succ-ℕᵉ nᵉ)
  map-total-sequential-diagramᵉ nᵉ =
    map-Σᵉ
      ( family-dependent-sequential-diagramᵉ Bᵉ (succ-ℕᵉ nᵉ))
      ( map-sequential-diagramᵉ Aᵉ nᵉ)
      ( map-dependent-sequential-diagramᵉ Bᵉ nᵉ)

  total-sequential-diagramᵉ : sequential-diagramᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ total-sequential-diagramᵉ = family-total-sequential-diagramᵉ
  pr2ᵉ total-sequential-diagramᵉ = map-total-sequential-diagramᵉ
```

### The projection morphism onto the base of the total sequential diagram

```agda
module _
  {l1ᵉ l2ᵉ : Level}
  {Aᵉ : sequential-diagramᵉ l1ᵉ} (Bᵉ : dependent-sequential-diagramᵉ Aᵉ l2ᵉ)
  where

  pr1-total-sequential-diagramᵉ :
    hom-sequential-diagramᵉ
      ( total-sequential-diagramᵉ Bᵉ)
      ( Aᵉ)
  pr1ᵉ pr1-total-sequential-diagramᵉ nᵉ = pr1ᵉ
  pr2ᵉ pr1-total-sequential-diagramᵉ nᵉ = refl-htpyᵉ
```

### The induced projection map on sequential colimits

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  {Aᵉ : sequential-diagramᵉ l1ᵉ} (Bᵉ : dependent-sequential-diagramᵉ Aᵉ l2ᵉ)
  {Xᵉ : UUᵉ l3ᵉ} {cᵉ : cocone-sequential-diagramᵉ (total-sequential-diagramᵉ Bᵉ) Xᵉ}
  (up-cᵉ : universal-property-sequential-colimitᵉ cᵉ)
  {Yᵉ : UUᵉ l4ᵉ} (c'ᵉ : cocone-sequential-diagramᵉ Aᵉ Yᵉ)
  where

  pr1-sequential-colimit-total-sequential-diagramᵉ : Xᵉ → Yᵉ
  pr1-sequential-colimit-total-sequential-diagramᵉ =
    map-sequential-colimit-hom-sequential-diagramᵉ
      ( up-cᵉ)
      ( c'ᵉ)
      ( pr1-total-sequential-diagramᵉ Bᵉ)
```

### The induced projection map on standard sequential colimits

```agda
module _
  {l1ᵉ l2ᵉ : Level}
  {Aᵉ : sequential-diagramᵉ l1ᵉ} (Bᵉ : dependent-sequential-diagramᵉ Aᵉ l2ᵉ)
  where

  pr1-standard-sequential-colimit-total-sequential-diagramᵉ :
    standard-sequential-colimitᵉ (total-sequential-diagramᵉ Bᵉ) →
    standard-sequential-colimitᵉ Aᵉ
  pr1-standard-sequential-colimit-total-sequential-diagramᵉ =
    map-hom-standard-sequential-colimitᵉ Aᵉ
      ( pr1-total-sequential-diagramᵉ Bᵉ)
```

## Properties

### Equivalences of dependent sequential diagrams induce equivalences on the total sequential diagrams

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ}
  (Bᵉ : dependent-sequential-diagramᵉ Aᵉ l2ᵉ)
  (Cᵉ : dependent-sequential-diagramᵉ Aᵉ l3ᵉ)
  (eᵉ : equiv-dependent-sequential-diagramᵉ Bᵉ Cᵉ)
  where

  equiv-total-sequential-diagram-equiv-dependent-sequential-diagramᵉ :
    equiv-sequential-diagramᵉ
      ( total-sequential-diagramᵉ Bᵉ)
      ( total-sequential-diagramᵉ Cᵉ)
  pr1ᵉ equiv-total-sequential-diagram-equiv-dependent-sequential-diagramᵉ nᵉ =
    equiv-totᵉ (equiv-equiv-dependent-sequential-diagramᵉ Cᵉ eᵉ nᵉ)
  pr2ᵉ equiv-total-sequential-diagram-equiv-dependent-sequential-diagramᵉ nᵉ =
    coherence-square-maps-Σᵉ
      ( family-dependent-sequential-diagramᵉ Cᵉ (succ-ℕᵉ nᵉ))
      ( map-dependent-sequential-diagramᵉ Bᵉ nᵉ)
      ( map-equiv-dependent-sequential-diagramᵉ Cᵉ eᵉ nᵉ)
      ( map-equiv-dependent-sequential-diagramᵉ Cᵉ eᵉ (succ-ℕᵉ nᵉ))
      ( map-dependent-sequential-diagramᵉ Cᵉ nᵉ)
      { refl-htpyᵉ}
      ( λ aᵉ → inv-htpyᵉ (coh-equiv-dependent-sequential-diagramᵉ Cᵉ eᵉ nᵉ aᵉ))
```