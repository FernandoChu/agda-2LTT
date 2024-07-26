# Descent data for sequential colimits

```agda
module synthetic-homotopy-theory.descent-data-sequential-colimitsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.universe-levelsᵉ

open import synthetic-homotopy-theory.cocones-under-sequential-diagramsᵉ
open import synthetic-homotopy-theory.dependent-sequential-diagramsᵉ
open import synthetic-homotopy-theory.equifibered-sequential-diagramsᵉ
open import synthetic-homotopy-theory.equivalences-dependent-sequential-diagramsᵉ
open import synthetic-homotopy-theory.morphisms-dependent-sequential-diagramsᵉ
open import synthetic-homotopy-theory.sequential-diagramsᵉ
```

</details>

## Idea

Givenᵉ aᵉ [sequentialᵉ diagram](synthetic-homotopy-theory.sequential-diagrams.mdᵉ)
`(A,ᵉ a)`,ᵉ weᵉ mayᵉ askᵉ howᵉ to constructᵉ typeᵉ familiesᵉ overᵉ itsᵉ
[sequentialᵉ colimit](synthetic-homotopy-theory.universal-property-sequential-colimits.md).ᵉ

Theᵉ data requiredᵉ to constructᵉ aᵉ typeᵉ familyᵉ isᵉ calledᵉ
{{#conceptᵉ "descentᵉ data"ᵉ Disambiguation="sequentialᵉ colimits"ᵉ Agda=descent-data-sequential-colimitᵉ}}
forᵉ sequentialᵉ colimits,ᵉ andᵉ itᵉ isᵉ exactlyᵉ anᵉ
[equifiberedᵉ sequentialᵉ diagram](synthetic-homotopy-theory.equifibered-sequential-diagrams.md).ᵉ

Theᵉ factᵉ thatᵉ theᵉ typeᵉ ofᵉ descentᵉ data forᵉ aᵉ sequentialᵉ diagramᵉ isᵉ equivalentᵉ to
theᵉ typeᵉ ofᵉ typeᵉ familiesᵉ overᵉ itsᵉ colimitᵉ isᵉ recordedᵉ in
[`descent-property-sequential-colimits`](synthetic-homotopy-theory.descent-property-sequential-colimits.md).ᵉ

## Definitions

### Descent data for sequential colimits

```agda
module _
  {l1ᵉ : Level} (Aᵉ : sequential-diagramᵉ l1ᵉ)
  where

  descent-data-sequential-colimitᵉ : (l2ᵉ : Level) → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
  descent-data-sequential-colimitᵉ =
    equifibered-sequential-diagramᵉ Aᵉ
```

### Components of descent data for sequential colimits

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ}
  (Bᵉ : descent-data-sequential-colimitᵉ Aᵉ l2ᵉ)
  where

  family-descent-data-sequential-colimitᵉ :
    (nᵉ : ℕᵉ) → family-sequential-diagramᵉ Aᵉ nᵉ → UUᵉ l2ᵉ
  family-descent-data-sequential-colimitᵉ = pr1ᵉ Bᵉ

  equiv-family-descent-data-sequential-colimitᵉ :
    (nᵉ : ℕᵉ) (aᵉ : family-sequential-diagramᵉ Aᵉ nᵉ) →
    family-descent-data-sequential-colimitᵉ nᵉ aᵉ ≃ᵉ
    family-descent-data-sequential-colimitᵉ
      ( succ-ℕᵉ nᵉ)
      ( map-sequential-diagramᵉ Aᵉ nᵉ aᵉ)
  equiv-family-descent-data-sequential-colimitᵉ = pr2ᵉ Bᵉ

  map-family-descent-data-sequential-colimitᵉ :
    (nᵉ : ℕᵉ) (aᵉ : family-sequential-diagramᵉ Aᵉ nᵉ) →
    family-descent-data-sequential-colimitᵉ nᵉ aᵉ →
    family-descent-data-sequential-colimitᵉ
      ( succ-ℕᵉ nᵉ)
      ( map-sequential-diagramᵉ Aᵉ nᵉ aᵉ)
  map-family-descent-data-sequential-colimitᵉ nᵉ aᵉ =
    map-equivᵉ (equiv-family-descent-data-sequential-colimitᵉ nᵉ aᵉ)

  is-equiv-map-family-descent-data-sequential-colimitᵉ :
    (nᵉ : ℕᵉ) (aᵉ : family-sequential-diagramᵉ Aᵉ nᵉ) →
    is-equivᵉ (map-family-descent-data-sequential-colimitᵉ nᵉ aᵉ)
  is-equiv-map-family-descent-data-sequential-colimitᵉ nᵉ aᵉ =
    is-equiv-map-equivᵉ (equiv-family-descent-data-sequential-colimitᵉ nᵉ aᵉ)

  dependent-sequential-diagram-descent-dataᵉ : dependent-sequential-diagramᵉ Aᵉ l2ᵉ
  dependent-sequential-diagram-descent-dataᵉ =
    dependent-sequential-diagram-equifibered-sequential-diagramᵉ Bᵉ
```

### Morphisms of descent data for sequential colimits

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ}
  (Bᵉ : descent-data-sequential-colimitᵉ Aᵉ l2ᵉ)
  (Cᵉ : descent-data-sequential-colimitᵉ Aᵉ l3ᵉ)
  where

  hom-descent-data-sequential-colimitᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  hom-descent-data-sequential-colimitᵉ =
    hom-dependent-sequential-diagramᵉ
      ( dependent-sequential-diagram-equifibered-sequential-diagramᵉ Bᵉ)
      ( dependent-sequential-diagram-equifibered-sequential-diagramᵉ Cᵉ)
```

### Equivalences of descent data for sequential colimits

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ}
  (Bᵉ : descent-data-sequential-colimitᵉ Aᵉ l2ᵉ)
  (Cᵉ : descent-data-sequential-colimitᵉ Aᵉ l3ᵉ)
  where

  equiv-descent-data-sequential-colimitᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  equiv-descent-data-sequential-colimitᵉ =
    equiv-dependent-sequential-diagramᵉ
      ( dependent-sequential-diagram-equifibered-sequential-diagramᵉ Bᵉ)
      ( dependent-sequential-diagram-equifibered-sequential-diagramᵉ Cᵉ)

  module _
    (eᵉ : equiv-descent-data-sequential-colimitᵉ)
    where

    equiv-equiv-descent-data-sequential-colimitᵉ :
      (nᵉ : ℕᵉ) (aᵉ : family-sequential-diagramᵉ Aᵉ nᵉ) →
      family-descent-data-sequential-colimitᵉ Bᵉ nᵉ aᵉ ≃ᵉ
      family-descent-data-sequential-colimitᵉ Cᵉ nᵉ aᵉ
    equiv-equiv-descent-data-sequential-colimitᵉ =
      equiv-equiv-dependent-sequential-diagramᵉ
        ( dependent-sequential-diagram-equifibered-sequential-diagramᵉ Cᵉ)
        ( eᵉ)

    map-equiv-descent-data-sequential-colimitᵉ :
      (nᵉ : ℕᵉ) (aᵉ : family-sequential-diagramᵉ Aᵉ nᵉ) →
      family-descent-data-sequential-colimitᵉ Bᵉ nᵉ aᵉ →
      family-descent-data-sequential-colimitᵉ Cᵉ nᵉ aᵉ
    map-equiv-descent-data-sequential-colimitᵉ =
      map-equiv-dependent-sequential-diagramᵉ
        ( dependent-sequential-diagram-equifibered-sequential-diagramᵉ Cᵉ)
        ( eᵉ)

    is-equiv-map-equiv-descent-data-sequential-colimitᵉ :
      (nᵉ : ℕᵉ) (aᵉ : family-sequential-diagramᵉ Aᵉ nᵉ) →
      is-equivᵉ (map-equiv-descent-data-sequential-colimitᵉ nᵉ aᵉ)
    is-equiv-map-equiv-descent-data-sequential-colimitᵉ =
      is-equiv-map-equiv-dependent-sequential-diagramᵉ
        ( dependent-sequential-diagram-equifibered-sequential-diagramᵉ Cᵉ)
        ( eᵉ)

    coh-equiv-descent-data-sequential-colimitᵉ :
      coherence-equiv-dependent-sequential-diagramᵉ
        ( dependent-sequential-diagram-equifibered-sequential-diagramᵉ Bᵉ)
        ( dependent-sequential-diagram-equifibered-sequential-diagramᵉ Cᵉ)
        ( equiv-equiv-descent-data-sequential-colimitᵉ)
    coh-equiv-descent-data-sequential-colimitᵉ =
      coh-equiv-dependent-sequential-diagramᵉ
        ( dependent-sequential-diagram-equifibered-sequential-diagramᵉ Cᵉ)
        ( eᵉ)

    hom-equiv-descent-data-sequential-colimitᵉ :
      hom-descent-data-sequential-colimitᵉ Bᵉ Cᵉ
    hom-equiv-descent-data-sequential-colimitᵉ =
      hom-equiv-dependent-sequential-diagramᵉ
        ( dependent-sequential-diagram-equifibered-sequential-diagramᵉ Cᵉ)
        ( eᵉ)

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ}
  (Bᵉ : descent-data-sequential-colimitᵉ Aᵉ l2ᵉ)
  where

  id-equiv-descent-data-sequential-colimitᵉ :
    equiv-descent-data-sequential-colimitᵉ Bᵉ Bᵉ
  id-equiv-descent-data-sequential-colimitᵉ =
    id-equiv-dependent-sequential-diagramᵉ
      ( dependent-sequential-diagram-equifibered-sequential-diagramᵉ Bᵉ)
```

### Descent data induced by families over cocones under sequential diagrams

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ}
  {Xᵉ : UUᵉ l2ᵉ} (cᵉ : cocone-sequential-diagramᵉ Aᵉ Xᵉ)
  where

  descent-data-family-cocone-sequential-diagramᵉ :
    {l3ᵉ : Level} → (Xᵉ → UUᵉ l3ᵉ) → descent-data-sequential-colimitᵉ Aᵉ l3ᵉ
  descent-data-family-cocone-sequential-diagramᵉ =
    equifibered-sequential-diagram-family-coconeᵉ cᵉ
```