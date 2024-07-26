# Families with descent data for sequential colimits

```agda
module synthetic-homotopy-theory.families-descent-data-sequential-colimitsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.commuting-squares-of-mapsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.universe-levelsᵉ

open import synthetic-homotopy-theory.cocones-under-sequential-diagramsᵉ
open import synthetic-homotopy-theory.dependent-sequential-diagramsᵉ
open import synthetic-homotopy-theory.descent-data-sequential-colimitsᵉ
open import synthetic-homotopy-theory.sequential-diagramsᵉ
```

</details>

## Idea

Asᵉ shownᵉ in
[`descent-property-sequential-colimits`](synthetic-homotopy-theory.descent-property-sequential-colimits.md),ᵉ
theᵉ typeᵉ ofᵉ typeᵉ familiesᵉ overᵉ
[sequentialᵉ colimits](synthetic-homotopy-theory.universal-property-sequential-colimits.mdᵉ)
isᵉ [equivalent](foundation-core.equivalences.mdᵉ) to
[descentᵉ data](synthetic-homotopy-theory.descent-data-sequential-colimits.md).ᵉ

Sometimesᵉ itᵉ isᵉ usefulᵉ to considerᵉ tripesᵉ `(P,ᵉ B,ᵉ e)`ᵉ where `Pᵉ : Xᵉ → 𝒰`ᵉ isᵉ aᵉ
typeᵉ family,ᵉ `B`ᵉ isᵉ descentᵉ data,ᵉ andᵉ `e`ᵉ isᵉ anᵉ equivalenceᵉ betweenᵉ `B`ᵉ andᵉ theᵉ
descentᵉ data inducedᵉ byᵉ `P`.ᵉ Theᵉ typeᵉ ofᵉ suchᵉ pairsᵉ `(B,ᵉ e)`ᵉ isᵉ
[contractible](foundation-core.contractible-types.md),ᵉ soᵉ theᵉ typeᵉ ofᵉ theseᵉ
triplesᵉ isᵉ equivalentᵉ to theᵉ typeᵉ ofᵉ typeᵉ familiesᵉ overᵉ `X`,ᵉ butᵉ itᵉ mayᵉ beᵉ moreᵉ
ergonomicᵉ to characterizeᵉ descentᵉ data ofᵉ aᵉ particularᵉ typeᵉ family,ᵉ andᵉ thenᵉ
haveᵉ theoremsᵉ knowᵉ aboutᵉ thisᵉ characterization,ᵉ ratherᵉ thanᵉ transportingᵉ alongᵉ
suchᵉ aᵉ characterizationᵉ afterᵉ theᵉ fact.ᵉ

## Definitions

### Families over a cocone equipped with corresponding descent data for sequential colimits

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ}
  {Xᵉ : UUᵉ l2ᵉ} (cᵉ : cocone-sequential-diagramᵉ Aᵉ Xᵉ)
  where

  family-with-descent-data-sequential-colimitᵉ :
    (l3ᵉ : Level) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ lsuc l3ᵉ)
  family-with-descent-data-sequential-colimitᵉ l3ᵉ =
    Σᵉ ( Xᵉ → UUᵉ l3ᵉ)
      ( λ Pᵉ →
        Σᵉ ( descent-data-sequential-colimitᵉ Aᵉ l3ᵉ)
          ( λ Bᵉ →
            equiv-descent-data-sequential-colimitᵉ
              ( Bᵉ)
              ( descent-data-family-cocone-sequential-diagramᵉ cᵉ Pᵉ)))
```

### Components of a family with corresponding descent data for sequential colimits

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ}
  {Xᵉ : UUᵉ l2ᵉ} {cᵉ : cocone-sequential-diagramᵉ Aᵉ Xᵉ}
  (Pᵉ : family-with-descent-data-sequential-colimitᵉ cᵉ l3ᵉ)
  where

  family-cocone-family-with-descent-data-sequential-colimitᵉ : Xᵉ → UUᵉ l3ᵉ
  family-cocone-family-with-descent-data-sequential-colimitᵉ = pr1ᵉ Pᵉ

  descent-data-family-with-descent-data-sequential-colimitᵉ :
    descent-data-sequential-colimitᵉ Aᵉ l3ᵉ
  descent-data-family-with-descent-data-sequential-colimitᵉ = pr1ᵉ (pr2ᵉ Pᵉ)

  family-family-with-descent-data-sequential-colimitᵉ :
    (nᵉ : ℕᵉ) → family-sequential-diagramᵉ Aᵉ nᵉ → UUᵉ l3ᵉ
  family-family-with-descent-data-sequential-colimitᵉ =
    family-descent-data-sequential-colimitᵉ
      ( descent-data-family-with-descent-data-sequential-colimitᵉ)

  equiv-family-family-with-descent-data-sequential-colimitᵉ :
    (nᵉ : ℕᵉ) (aᵉ : family-sequential-diagramᵉ Aᵉ nᵉ) →
    family-family-with-descent-data-sequential-colimitᵉ nᵉ aᵉ ≃ᵉ
    family-family-with-descent-data-sequential-colimitᵉ
      ( succ-ℕᵉ nᵉ)
      ( map-sequential-diagramᵉ Aᵉ nᵉ aᵉ)
  equiv-family-family-with-descent-data-sequential-colimitᵉ =
    equiv-family-descent-data-sequential-colimitᵉ
      ( descent-data-family-with-descent-data-sequential-colimitᵉ)

  map-family-family-with-descent-data-sequential-colimitᵉ :
    (nᵉ : ℕᵉ) (aᵉ : family-sequential-diagramᵉ Aᵉ nᵉ) →
    family-family-with-descent-data-sequential-colimitᵉ nᵉ aᵉ →
    family-family-with-descent-data-sequential-colimitᵉ
      ( succ-ℕᵉ nᵉ)
      ( map-sequential-diagramᵉ Aᵉ nᵉ aᵉ)
  map-family-family-with-descent-data-sequential-colimitᵉ =
    map-family-descent-data-sequential-colimitᵉ
      ( descent-data-family-with-descent-data-sequential-colimitᵉ)

  is-equiv-map-family-family-with-descent-data-sequential-colimitᵉ :
    (nᵉ : ℕᵉ) (aᵉ : family-sequential-diagramᵉ Aᵉ nᵉ) →
    is-equivᵉ (map-family-family-with-descent-data-sequential-colimitᵉ nᵉ aᵉ)
  is-equiv-map-family-family-with-descent-data-sequential-colimitᵉ =
    is-equiv-map-family-descent-data-sequential-colimitᵉ
      ( descent-data-family-with-descent-data-sequential-colimitᵉ)

  dependent-sequential-diagram-family-with-descent-data-sequential-colimitᵉ :
    dependent-sequential-diagramᵉ Aᵉ l3ᵉ
  dependent-sequential-diagram-family-with-descent-data-sequential-colimitᵉ =
    dependent-sequential-diagram-descent-dataᵉ
      ( descent-data-family-with-descent-data-sequential-colimitᵉ)

  equiv-descent-data-family-with-descent-data-sequential-colimitᵉ :
    equiv-descent-data-sequential-colimitᵉ
      ( descent-data-family-with-descent-data-sequential-colimitᵉ)
      ( descent-data-family-cocone-sequential-diagramᵉ cᵉ
        ( family-cocone-family-with-descent-data-sequential-colimitᵉ))
  equiv-descent-data-family-with-descent-data-sequential-colimitᵉ = pr2ᵉ (pr2ᵉ Pᵉ)

  equiv-equiv-descent-data-family-with-descent-data-sequential-colimitᵉ :
    (nᵉ : ℕᵉ) (aᵉ : family-sequential-diagramᵉ Aᵉ nᵉ) →
    family-descent-data-sequential-colimitᵉ
      ( descent-data-family-with-descent-data-sequential-colimitᵉ)
      ( nᵉ)
      ( aᵉ) ≃ᵉ
    family-cocone-family-with-descent-data-sequential-colimitᵉ
      ( map-cocone-sequential-diagramᵉ cᵉ nᵉ aᵉ)
  equiv-equiv-descent-data-family-with-descent-data-sequential-colimitᵉ =
    equiv-equiv-descent-data-sequential-colimitᵉ
      ( descent-data-family-with-descent-data-sequential-colimitᵉ)
      ( descent-data-family-cocone-sequential-diagramᵉ cᵉ
        ( family-cocone-family-with-descent-data-sequential-colimitᵉ))
      ( equiv-descent-data-family-with-descent-data-sequential-colimitᵉ)

  map-equiv-descent-data-family-with-descent-data-sequential-colimitᵉ :
    (nᵉ : ℕᵉ) (aᵉ : family-sequential-diagramᵉ Aᵉ nᵉ) →
    family-descent-data-sequential-colimitᵉ
      ( descent-data-family-with-descent-data-sequential-colimitᵉ)
      ( nᵉ)
      ( aᵉ) →
    family-cocone-family-with-descent-data-sequential-colimitᵉ
      ( map-cocone-sequential-diagramᵉ cᵉ nᵉ aᵉ)
  map-equiv-descent-data-family-with-descent-data-sequential-colimitᵉ =
    map-equiv-descent-data-sequential-colimitᵉ
      ( descent-data-family-with-descent-data-sequential-colimitᵉ)
      ( descent-data-family-cocone-sequential-diagramᵉ cᵉ
        ( family-cocone-family-with-descent-data-sequential-colimitᵉ))
      ( equiv-descent-data-family-with-descent-data-sequential-colimitᵉ)

  is-equiv-map-equiv-descent-data-family-with-descent-data-sequential-colimitᵉ :
    (nᵉ : ℕᵉ) (aᵉ : family-sequential-diagramᵉ Aᵉ nᵉ) →
    is-equivᵉ
      ( map-equiv-descent-data-family-with-descent-data-sequential-colimitᵉ nᵉ aᵉ)
  is-equiv-map-equiv-descent-data-family-with-descent-data-sequential-colimitᵉ =
    is-equiv-map-equiv-descent-data-sequential-colimitᵉ
      ( descent-data-family-with-descent-data-sequential-colimitᵉ)
      ( descent-data-family-cocone-sequential-diagramᵉ cᵉ
        ( family-cocone-family-with-descent-data-sequential-colimitᵉ))
      ( equiv-descent-data-family-with-descent-data-sequential-colimitᵉ)

  coherence-square-equiv-descent-data-family-with-descent-data-sequential-colimitᵉ :
    (nᵉ : ℕᵉ) (aᵉ : family-sequential-diagramᵉ Aᵉ nᵉ) →
    coherence-square-mapsᵉ
      ( map-equiv-descent-data-family-with-descent-data-sequential-colimitᵉ nᵉ aᵉ)
      ( map-family-family-with-descent-data-sequential-colimitᵉ nᵉ aᵉ)
      ( trᵉ
        ( family-cocone-family-with-descent-data-sequential-colimitᵉ)
        ( coherence-cocone-sequential-diagramᵉ cᵉ nᵉ aᵉ))
      ( map-equiv-descent-data-family-with-descent-data-sequential-colimitᵉ
        ( succ-ℕᵉ nᵉ)
        ( map-sequential-diagramᵉ Aᵉ nᵉ aᵉ))
  coherence-square-equiv-descent-data-family-with-descent-data-sequential-colimitᵉ =
    coh-equiv-descent-data-sequential-colimitᵉ
      ( descent-data-family-with-descent-data-sequential-colimitᵉ)
      ( descent-data-family-cocone-sequential-diagramᵉ cᵉ
        ( family-cocone-family-with-descent-data-sequential-colimitᵉ))
      ( equiv-descent-data-family-with-descent-data-sequential-colimitᵉ)
```

### A type family equipped with its induced descent data for sequential colimits

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ}
  {Xᵉ : UUᵉ l2ᵉ} (cᵉ : cocone-sequential-diagramᵉ Aᵉ Xᵉ)
  (Pᵉ : Xᵉ → UUᵉ l3ᵉ)
  where

  family-with-descent-data-family-cocone-sequential-diagramᵉ :
    family-with-descent-data-sequential-colimitᵉ cᵉ l3ᵉ
  pr1ᵉ family-with-descent-data-family-cocone-sequential-diagramᵉ = Pᵉ
  pr1ᵉ (pr2ᵉ family-with-descent-data-family-cocone-sequential-diagramᵉ) =
    descent-data-family-cocone-sequential-diagramᵉ cᵉ Pᵉ
  pr2ᵉ (pr2ᵉ family-with-descent-data-family-cocone-sequential-diagramᵉ) =
    id-equiv-descent-data-sequential-colimitᵉ
      ( descent-data-family-cocone-sequential-diagramᵉ cᵉ Pᵉ)
```