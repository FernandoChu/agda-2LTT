# Descent data for pushouts

```agda
module synthetic-homotopy-theory.descent-data-pushoutsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.span-diagramsᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.universe-levelsᵉ

open import synthetic-homotopy-theory.cocones-under-spansᵉ
```

</details>

## Idea

{{#conceptᵉ "Descentᵉ data"ᵉ Disambiguation="pushouts"ᵉ Agda=descent-data-pushoutᵉ WDID=NAᵉ}}
forᵉ theᵉ [pushout](synthetic-homotopy-theory.universal-property-pushouts.mdᵉ) ofᵉ aᵉ
[spanᵉ diagram](foundation.span-diagrams.mdᵉ) `𝒮`ᵉ

```text
     fᵉ     gᵉ
  Aᵉ <--ᵉ Sᵉ -->ᵉ Bᵉ
```

isᵉ aᵉ tripleᵉ `(PA,ᵉ PB,ᵉ PS)`,ᵉ where `PAᵉ : Aᵉ → 𝒰`ᵉ isᵉ aᵉ typeᵉ familyᵉ overᵉ `A`,ᵉ
`PBᵉ : Bᵉ → 𝒰`ᵉ isᵉ aᵉ typeᵉ familyᵉ overᵉ `B`,ᵉ andᵉ `PS`ᵉ isᵉ aᵉ familyᵉ ofᵉ
[equivalences](foundation-core.equivalences.mdᵉ)

```text
  PSᵉ : (sᵉ : Sᵉ) → PAᵉ (fᵉ aᵉ) ≃ᵉ PBᵉ (gᵉ a).ᵉ
```

Inᵉ
[`descent-property-pushouts`](synthetic-homotopy-theory.descent-property-pushouts.md),ᵉ
weᵉ showᵉ thatᵉ thisᵉ isᵉ exactlyᵉ theᵉ data oneᵉ needsᵉ to "glueᵉ together"ᵉ aᵉ typeᵉ familyᵉ
`Pᵉ : Xᵉ → 𝒰`ᵉ overᵉ theᵉ pushoutᵉ `X`ᵉ ofᵉ `𝒮`.ᵉ

Theᵉ [identityᵉ type](foundation-core.identity-types.mdᵉ) ofᵉ descentᵉ data isᵉ
characterizedᵉ in
[`equivalences-descent-data-pushouts`](synthetic-homotopy-theory.equivalences-descent-data-pushouts.md).ᵉ

Itᵉ mayᵉ notᵉ beᵉ immediatelyᵉ clearᵉ whyᵉ "descentᵉ data"ᵉ isᵉ anᵉ appropriateᵉ nameᵉ forᵉ
thisᵉ concept,ᵉ becauseᵉ thereᵉ isᵉ noᵉ apparentᵉ downwardᵉ motion.ᵉ Traditionally,ᵉ
descentᵉ isᵉ studiedᵉ in theᵉ contextᵉ ofᵉ aᵉ collectionᵉ ofᵉ objectsᵉ `Xᵢ`ᵉ coveringᵉ aᵉ
singleᵉ objectᵉ `X`,ᵉ andᵉ localᵉ structureᵉ onᵉ theᵉ individualᵉ `Xᵢ`'sᵉ descendingᵉ ontoᵉ
`X`,ᵉ collectingᵉ intoᵉ aᵉ globalᵉ structure,ᵉ givenᵉ thatᵉ theᵉ piecesᵉ areᵉ appropriatelyᵉ
compatibleᵉ onᵉ anyᵉ "overlaps".ᵉ Aᵉ pushoutᵉ ofᵉ `𝒮`ᵉ isᵉ coveredᵉ byᵉ `A`ᵉ andᵉ `B`,ᵉ andᵉ
theᵉ overlapsᵉ areᵉ encodedᵉ in `f`ᵉ andᵉ `g`.ᵉ Thenᵉ structureᵉ onᵉ `A`ᵉ andᵉ `B`,ᵉ
expressedᵉ asᵉ typeᵉ familiesᵉ `PA`ᵉ andᵉ `PB`,ᵉ "descends"ᵉ to aᵉ structureᵉ onᵉ `X`ᵉ (aᵉ
typeᵉ familyᵉ overᵉ `X`).ᵉ Twoᵉ elementsᵉ "overlap"ᵉ in `X`ᵉ ifᵉ thereᵉ isᵉ anᵉ
identificationᵉ betweenᵉ themᵉ comingᵉ fromᵉ `S`,ᵉ andᵉ theᵉ gluing/compatibilityᵉ
conditionᵉ exactlyᵉ requiresᵉ theᵉ localᵉ structureᵉ ofᵉ `PA`ᵉ andᵉ `PB`ᵉ to agreeᵉ onᵉ suchᵉ
elements,ᵉ i.e.ᵉ asksᵉ forᵉ anᵉ equivalenceᵉ `PA(fsᵉ) ≃ᵉ PB(gs)`.ᵉ

## Definitions

### Descent data for pushouts

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (𝒮ᵉ : span-diagramᵉ l1ᵉ l2ᵉ l3ᵉ)
  where

  descent-data-pushoutᵉ : (l4ᵉ : Level) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ lsuc l4ᵉ)
  descent-data-pushoutᵉ lᵉ =
    Σᵉ ( domain-span-diagramᵉ 𝒮ᵉ → UUᵉ lᵉ)
      ( λ PAᵉ →
        Σᵉ ( codomain-span-diagramᵉ 𝒮ᵉ → UUᵉ lᵉ)
          ( λ PBᵉ →
            (sᵉ : spanning-type-span-diagramᵉ 𝒮ᵉ) →
            PAᵉ (left-map-span-diagramᵉ 𝒮ᵉ sᵉ) ≃ᵉ PBᵉ (right-map-span-diagramᵉ 𝒮ᵉ sᵉ)))
```

### Components of descent data for pushouts

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {𝒮ᵉ : span-diagramᵉ l1ᵉ l2ᵉ l3ᵉ}
  (Pᵉ : descent-data-pushoutᵉ 𝒮ᵉ l4ᵉ)
  where

  left-family-descent-data-pushoutᵉ : domain-span-diagramᵉ 𝒮ᵉ → UUᵉ l4ᵉ
  left-family-descent-data-pushoutᵉ = pr1ᵉ Pᵉ

  right-family-descent-data-pushoutᵉ : codomain-span-diagramᵉ 𝒮ᵉ → UUᵉ l4ᵉ
  right-family-descent-data-pushoutᵉ = pr1ᵉ (pr2ᵉ Pᵉ)

  equiv-family-descent-data-pushoutᵉ :
    (sᵉ : spanning-type-span-diagramᵉ 𝒮ᵉ) →
    left-family-descent-data-pushoutᵉ (left-map-span-diagramᵉ 𝒮ᵉ sᵉ) ≃ᵉ
    right-family-descent-data-pushoutᵉ (right-map-span-diagramᵉ 𝒮ᵉ sᵉ)
  equiv-family-descent-data-pushoutᵉ = pr2ᵉ (pr2ᵉ Pᵉ)

  map-family-descent-data-pushoutᵉ :
    (sᵉ : spanning-type-span-diagramᵉ 𝒮ᵉ) →
    left-family-descent-data-pushoutᵉ (left-map-span-diagramᵉ 𝒮ᵉ sᵉ) →
    right-family-descent-data-pushoutᵉ (right-map-span-diagramᵉ 𝒮ᵉ sᵉ)
  map-family-descent-data-pushoutᵉ sᵉ =
    map-equivᵉ (equiv-family-descent-data-pushoutᵉ sᵉ)

  is-equiv-map-family-descent-data-pushoutᵉ :
    (sᵉ : spanning-type-span-diagramᵉ 𝒮ᵉ) →
    is-equivᵉ (map-family-descent-data-pushoutᵉ sᵉ)
  is-equiv-map-family-descent-data-pushoutᵉ sᵉ =
    is-equiv-map-equivᵉ (equiv-family-descent-data-pushoutᵉ sᵉ)
```

### Descent data induced by families over cocones

Givenᵉ aᵉ [cocone](synthetic-homotopy-theory.cocones-under-spans.mdᵉ)

```text
        gᵉ
    Sᵉ ----->ᵉ Bᵉ
    |        |
  fᵉ |        | jᵉ
    ∨ᵉ        ∨ᵉ
    Aᵉ ----->ᵉ Xᵉ
        iᵉ
```

andᵉ aᵉ familyᵉ `Pᵉ : Xᵉ → 𝒰`,ᵉ weᵉ canᵉ obtainᵉ `PA`ᵉ andᵉ `PB`ᵉ byᵉ precomposingᵉ with `i`ᵉ
andᵉ `j`,ᵉ respectively.ᵉ Thenᵉ to produceᵉ anᵉ equivalenceᵉ
`PSᵉ sᵉ : Pᵉ (ifsᵉ) ≃ᵉ Pᵉ (jgs)`,ᵉ weᵉ
[transport](foundation-core.transport-along-identifications.mdᵉ) alongᵉ theᵉ
coherenceᵉ `Hᵉ sᵉ : ifsᵉ = jgs`,ᵉ whichᵉ isᵉ anᵉ equivalence.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {𝒮ᵉ : span-diagramᵉ l1ᵉ l2ᵉ l3ᵉ}
  {Xᵉ : UUᵉ l4ᵉ} (cᵉ : cocone-span-diagramᵉ 𝒮ᵉ Xᵉ)
  where

  descent-data-family-cocone-span-diagramᵉ :
    {l5ᵉ : Level} → (Xᵉ → UUᵉ l5ᵉ) → descent-data-pushoutᵉ 𝒮ᵉ l5ᵉ
  pr1ᵉ (descent-data-family-cocone-span-diagramᵉ Pᵉ) =
    Pᵉ ∘ᵉ horizontal-map-coconeᵉ _ _ cᵉ
  pr1ᵉ (pr2ᵉ (descent-data-family-cocone-span-diagramᵉ Pᵉ)) =
    Pᵉ ∘ᵉ vertical-map-coconeᵉ _ _ cᵉ
  pr2ᵉ (pr2ᵉ (descent-data-family-cocone-span-diagramᵉ Pᵉ)) sᵉ =
    equiv-trᵉ Pᵉ (coherence-square-coconeᵉ _ _ cᵉ sᵉ)
```