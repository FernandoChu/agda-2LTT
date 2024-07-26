# Families with descent data for pushouts

```agda
module synthetic-homotopy-theory.families-descent-data-pushoutsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-squares-of-mapsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.span-diagramsᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.universe-levelsᵉ

open import synthetic-homotopy-theory.cocones-under-spansᵉ
open import synthetic-homotopy-theory.descent-data-pushoutsᵉ
open import synthetic-homotopy-theory.equivalences-descent-data-pushoutsᵉ
```

</details>

## Idea

Inᵉ
[`descent-property-pushouts`](synthetic-homotopy-theory.descent-property-pushouts.mdᵉ)
weᵉ showᵉ thatᵉ givenᵉ
[descentᵉ data](synthetic-homotopy-theory.descent-data-pushouts.mdᵉ)
`(PA,ᵉ PB,ᵉ PS)`ᵉ overᵉ aᵉ [spanᵉ diagram](foundation.span-diagrams.mdᵉ) `𝒮`,ᵉ thereᵉ isᵉ
aᵉ uniqueᵉ typeᵉ familyᵉ `P`ᵉ overᵉ itsᵉ
[pushout](synthetic-homotopy-theory.pushouts.mdᵉ) suchᵉ thatᵉ itsᵉ inducedᵉ descentᵉ
data isᵉ
[equivalent](synthetic-homotopy-theory.equivalences-descent-data-pushouts.mdᵉ) to
`(PA,ᵉ PB,ᵉ PS)`.ᵉ Whenᵉ statingᵉ theorems,ᵉ itᵉ isᵉ sometimesᵉ usefulᵉ to parameterizeᵉ
overᵉ aᵉ user-providedᵉ typeᵉ family,ᵉ descentᵉ data,ᵉ andᵉ theᵉ appropriateᵉ equivalence,ᵉ
evenᵉ thoughᵉ weᵉ technicallyᵉ canᵉ contractᵉ awayᵉ theᵉ equivalenceᵉ andᵉ eitherᵉ ofᵉ theᵉ
endpoints.ᵉ Weᵉ callᵉ suchᵉ aᵉ tripleᵉ `(P,ᵉ (PA,ᵉ PB,ᵉ PS),ᵉ e)`ᵉ aᵉ
{{#conceptᵉ "familyᵉ with descentᵉ data"ᵉ Disambiguation="pushouts"ᵉ Agda=family-with-descent-data-pushout}},ᵉ
andᵉ denoteᵉ itᵉ `Pᵉ ≈ᵉ (PA,ᵉ PB,ᵉ PS)`.ᵉ

## Definitions

### Type families over a cocone equipped with corresponding descent data for pushouts

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {𝒮ᵉ : span-diagramᵉ l1ᵉ l2ᵉ l3ᵉ}
  {Xᵉ : UUᵉ l4ᵉ} (cᵉ : cocone-span-diagramᵉ 𝒮ᵉ Xᵉ)
  where

  family-with-descent-data-pushoutᵉ :
    (l5ᵉ : Level) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ ⊔ lsuc l5ᵉ)
  family-with-descent-data-pushoutᵉ l5ᵉ =
    Σᵉ ( Xᵉ → UUᵉ l5ᵉ)
      ( λ Pᵉ →
        Σᵉ ( descent-data-pushoutᵉ 𝒮ᵉ l5ᵉ)
          ( λ Qᵉ →
            equiv-descent-data-pushoutᵉ
              ( descent-data-family-cocone-span-diagramᵉ cᵉ Pᵉ)
              ( Qᵉ)))
```

### Components of a family with corresponding descent data

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level} {𝒮ᵉ : span-diagramᵉ l1ᵉ l2ᵉ l3ᵉ}
  {Xᵉ : UUᵉ l4ᵉ} {cᵉ : cocone-span-diagramᵉ 𝒮ᵉ Xᵉ}
  (Pᵉ : family-with-descent-data-pushoutᵉ cᵉ l5ᵉ)
  where

  family-cocone-family-with-descent-data-pushoutᵉ : Xᵉ → UUᵉ l5ᵉ
  family-cocone-family-with-descent-data-pushoutᵉ = pr1ᵉ Pᵉ

  descent-data-family-with-descent-data-pushoutᵉ : descent-data-pushoutᵉ 𝒮ᵉ l5ᵉ
  descent-data-family-with-descent-data-pushoutᵉ = pr1ᵉ (pr2ᵉ Pᵉ)

  left-family-family-with-descent-data-pushoutᵉ :
    domain-span-diagramᵉ 𝒮ᵉ → UUᵉ l5ᵉ
  left-family-family-with-descent-data-pushoutᵉ =
    left-family-descent-data-pushoutᵉ
      ( descent-data-family-with-descent-data-pushoutᵉ)

  right-family-family-with-descent-data-pushoutᵉ :
    codomain-span-diagramᵉ 𝒮ᵉ → UUᵉ l5ᵉ
  right-family-family-with-descent-data-pushoutᵉ =
    right-family-descent-data-pushoutᵉ
      ( descent-data-family-with-descent-data-pushoutᵉ)

  equiv-family-family-with-descent-data-pushoutᵉ :
    (sᵉ : spanning-type-span-diagramᵉ 𝒮ᵉ) →
    left-family-family-with-descent-data-pushoutᵉ (left-map-span-diagramᵉ 𝒮ᵉ sᵉ) ≃ᵉ
    right-family-family-with-descent-data-pushoutᵉ (right-map-span-diagramᵉ 𝒮ᵉ sᵉ)
  equiv-family-family-with-descent-data-pushoutᵉ =
    equiv-family-descent-data-pushoutᵉ
      ( descent-data-family-with-descent-data-pushoutᵉ)

  map-family-family-with-descent-data-pushoutᵉ :
    (sᵉ : spanning-type-span-diagramᵉ 𝒮ᵉ) →
    left-family-family-with-descent-data-pushoutᵉ (left-map-span-diagramᵉ 𝒮ᵉ sᵉ) →
    right-family-family-with-descent-data-pushoutᵉ (right-map-span-diagramᵉ 𝒮ᵉ sᵉ)
  map-family-family-with-descent-data-pushoutᵉ =
    map-family-descent-data-pushoutᵉ
      ( descent-data-family-with-descent-data-pushoutᵉ)

  equiv-descent-data-family-with-descent-data-pushoutᵉ :
    equiv-descent-data-pushoutᵉ
      ( descent-data-family-cocone-span-diagramᵉ cᵉ
        ( family-cocone-family-with-descent-data-pushoutᵉ))
      ( descent-data-family-with-descent-data-pushoutᵉ)
  equiv-descent-data-family-with-descent-data-pushoutᵉ = pr2ᵉ (pr2ᵉ Pᵉ)

  inv-equiv-descent-data-family-with-descent-data-pushoutᵉ :
    equiv-descent-data-pushoutᵉ
      ( descent-data-family-with-descent-data-pushoutᵉ)
      ( descent-data-family-cocone-span-diagramᵉ cᵉ
        ( family-cocone-family-with-descent-data-pushoutᵉ))
  inv-equiv-descent-data-family-with-descent-data-pushoutᵉ =
    inv-equiv-descent-data-pushoutᵉ
      ( descent-data-family-cocone-span-diagramᵉ cᵉ
        ( family-cocone-family-with-descent-data-pushoutᵉ))
      ( descent-data-family-with-descent-data-pushoutᵉ)
      ( equiv-descent-data-family-with-descent-data-pushoutᵉ)

  left-equiv-family-with-descent-data-pushoutᵉ :
    (aᵉ : domain-span-diagramᵉ 𝒮ᵉ) →
    family-cocone-family-with-descent-data-pushoutᵉ
      ( horizontal-map-coconeᵉ _ _ cᵉ aᵉ) ≃ᵉ
    left-family-family-with-descent-data-pushoutᵉ aᵉ
  left-equiv-family-with-descent-data-pushoutᵉ =
    left-equiv-equiv-descent-data-pushoutᵉ
      ( descent-data-family-cocone-span-diagramᵉ cᵉ
        ( family-cocone-family-with-descent-data-pushoutᵉ))
      ( descent-data-family-with-descent-data-pushoutᵉ)
      ( equiv-descent-data-family-with-descent-data-pushoutᵉ)

  left-map-family-with-descent-data-pushoutᵉ :
    (aᵉ : domain-span-diagramᵉ 𝒮ᵉ) →
    family-cocone-family-with-descent-data-pushoutᵉ
      ( horizontal-map-coconeᵉ _ _ cᵉ aᵉ) →
    left-family-family-with-descent-data-pushoutᵉ aᵉ
  left-map-family-with-descent-data-pushoutᵉ =
    left-map-equiv-descent-data-pushoutᵉ
      ( descent-data-family-cocone-span-diagramᵉ cᵉ
        ( family-cocone-family-with-descent-data-pushoutᵉ))
      ( descent-data-family-with-descent-data-pushoutᵉ)
      ( equiv-descent-data-family-with-descent-data-pushoutᵉ)

  is-equiv-left-map-family-with-descent-data-pushoutᵉ :
    (aᵉ : domain-span-diagramᵉ 𝒮ᵉ) →
    is-equivᵉ (left-map-family-with-descent-data-pushoutᵉ aᵉ)
  is-equiv-left-map-family-with-descent-data-pushoutᵉ =
    is-equiv-left-map-equiv-descent-data-pushoutᵉ
      ( descent-data-family-cocone-span-diagramᵉ cᵉ
        ( family-cocone-family-with-descent-data-pushoutᵉ))
      ( descent-data-family-with-descent-data-pushoutᵉ)
      ( equiv-descent-data-family-with-descent-data-pushoutᵉ)

  inv-left-map-family-with-descent-data-pushoutᵉ :
    (aᵉ : domain-span-diagramᵉ 𝒮ᵉ) →
    left-family-family-with-descent-data-pushoutᵉ aᵉ →
    family-cocone-family-with-descent-data-pushoutᵉ
      ( horizontal-map-coconeᵉ _ _ cᵉ aᵉ)
  inv-left-map-family-with-descent-data-pushoutᵉ =
    inv-left-map-equiv-descent-data-pushoutᵉ
      ( descent-data-family-cocone-span-diagramᵉ cᵉ
        ( family-cocone-family-with-descent-data-pushoutᵉ))
      ( descent-data-family-with-descent-data-pushoutᵉ)
      ( equiv-descent-data-family-with-descent-data-pushoutᵉ)

  right-equiv-family-with-descent-data-pushoutᵉ :
    (bᵉ : codomain-span-diagramᵉ 𝒮ᵉ) →
    family-cocone-family-with-descent-data-pushoutᵉ
      ( vertical-map-coconeᵉ _ _ cᵉ bᵉ) ≃ᵉ
    right-family-family-with-descent-data-pushoutᵉ bᵉ
  right-equiv-family-with-descent-data-pushoutᵉ =
    right-equiv-equiv-descent-data-pushoutᵉ
      ( descent-data-family-cocone-span-diagramᵉ cᵉ
        ( family-cocone-family-with-descent-data-pushoutᵉ))
      ( descent-data-family-with-descent-data-pushoutᵉ)
      ( equiv-descent-data-family-with-descent-data-pushoutᵉ)

  right-map-family-with-descent-data-pushoutᵉ :
    (bᵉ : codomain-span-diagramᵉ 𝒮ᵉ) →
    family-cocone-family-with-descent-data-pushoutᵉ
      ( vertical-map-coconeᵉ _ _ cᵉ bᵉ) →
    right-family-family-with-descent-data-pushoutᵉ bᵉ
  right-map-family-with-descent-data-pushoutᵉ =
    right-map-equiv-descent-data-pushoutᵉ
      ( descent-data-family-cocone-span-diagramᵉ cᵉ
        ( family-cocone-family-with-descent-data-pushoutᵉ))
      ( descent-data-family-with-descent-data-pushoutᵉ)
      ( equiv-descent-data-family-with-descent-data-pushoutᵉ)

  is-equiv-right-map-family-with-descent-data-pushoutᵉ :
    (bᵉ : codomain-span-diagramᵉ 𝒮ᵉ) →
    is-equivᵉ (right-map-family-with-descent-data-pushoutᵉ bᵉ)
  is-equiv-right-map-family-with-descent-data-pushoutᵉ =
    is-equiv-right-map-equiv-descent-data-pushoutᵉ
      ( descent-data-family-cocone-span-diagramᵉ cᵉ
        ( family-cocone-family-with-descent-data-pushoutᵉ))
      ( descent-data-family-with-descent-data-pushoutᵉ)
      ( equiv-descent-data-family-with-descent-data-pushoutᵉ)

  inv-right-map-family-with-descent-data-pushoutᵉ :
    (bᵉ : codomain-span-diagramᵉ 𝒮ᵉ) →
    right-family-family-with-descent-data-pushoutᵉ bᵉ →
    family-cocone-family-with-descent-data-pushoutᵉ
      ( vertical-map-coconeᵉ _ _ cᵉ bᵉ)
  inv-right-map-family-with-descent-data-pushoutᵉ =
    inv-right-map-equiv-descent-data-pushoutᵉ
      ( descent-data-family-cocone-span-diagramᵉ cᵉ
        ( family-cocone-family-with-descent-data-pushoutᵉ))
      ( descent-data-family-with-descent-data-pushoutᵉ)
      ( equiv-descent-data-family-with-descent-data-pushoutᵉ)

  coherence-family-with-descent-data-pushoutᵉ :
    (sᵉ : spanning-type-span-diagramᵉ 𝒮ᵉ) →
    coherence-square-mapsᵉ
      ( left-map-family-with-descent-data-pushoutᵉ
        ( left-map-span-diagramᵉ 𝒮ᵉ sᵉ))
      ( trᵉ
        ( family-cocone-family-with-descent-data-pushoutᵉ)
        ( coherence-square-coconeᵉ _ _ cᵉ sᵉ))
      ( map-family-family-with-descent-data-pushoutᵉ sᵉ)
      ( right-map-family-with-descent-data-pushoutᵉ
        ( right-map-span-diagramᵉ 𝒮ᵉ sᵉ))
  coherence-family-with-descent-data-pushoutᵉ =
    coherence-equiv-descent-data-pushoutᵉ
      ( descent-data-family-cocone-span-diagramᵉ cᵉ
        ( family-cocone-family-with-descent-data-pushoutᵉ))
      ( descent-data-family-with-descent-data-pushoutᵉ)
      ( equiv-descent-data-family-with-descent-data-pushoutᵉ)
```

### Type family together with its induced descent data

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {𝒮ᵉ : span-diagramᵉ l1ᵉ l2ᵉ l3ᵉ}
  {Xᵉ : UUᵉ l4ᵉ} (cᵉ : cocone-span-diagramᵉ 𝒮ᵉ Xᵉ)
  where

  family-with-descent-data-pushout-family-coconeᵉ :
    {l5ᵉ : Level} (Pᵉ : Xᵉ → UUᵉ l5ᵉ) →
    family-with-descent-data-pushoutᵉ cᵉ l5ᵉ
  pr1ᵉ (family-with-descent-data-pushout-family-coconeᵉ Pᵉ) = Pᵉ
  pr1ᵉ (pr2ᵉ (family-with-descent-data-pushout-family-coconeᵉ Pᵉ)) =
    descent-data-family-cocone-span-diagramᵉ cᵉ Pᵉ
  pr2ᵉ (pr2ᵉ (family-with-descent-data-pushout-family-coconeᵉ Pᵉ)) =
    id-equiv-descent-data-pushoutᵉ
      ( descent-data-family-cocone-span-diagramᵉ cᵉ Pᵉ)
```