# Descent property of pushouts

```agda
module synthetic-homotopy-theory.descent-property-pushoutsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-triangles-of-mapsᵉ
open import foundation.contractible-mapsᵉ
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equality-dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.fibers-of-mapsᵉ
open import foundation.function-extensionalityᵉ
open import foundation.functoriality-dependent-function-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.span-diagramsᵉ
open import foundation.univalenceᵉ
open import foundation.universe-levelsᵉ

open import synthetic-homotopy-theory.cocones-under-spansᵉ
open import synthetic-homotopy-theory.descent-data-pushoutsᵉ
open import synthetic-homotopy-theory.equivalences-descent-data-pushoutsᵉ
open import synthetic-homotopy-theory.families-descent-data-pushoutsᵉ
open import synthetic-homotopy-theory.universal-property-pushoutsᵉ
```

</details>

## Idea

Theᵉ
{{#conceptᵉ "descentᵉ property"ᵉ Disambiguation="pushouts"ᵉ Agda=uniqueness-family-cocone-descent-data-pushoutᵉ WDID=Q5263725ᵉ WD="descent"ᵉ}}
ofᵉ [pushouts](synthetic-homotopy-theory.pushouts.mdᵉ) statesᵉ thatᵉ givenᵉ aᵉ pushoutᵉ

```text
        gᵉ
    Sᵉ ----->ᵉ Bᵉ
    |        |
  fᵉ |        | jᵉ
    ∨ᵉ        ∨ᵉ
    Aᵉ ----->ᵉ X,ᵉ
        iᵉ
```

thereᵉ isᵉ anᵉ [equivalence](foundation-core.equivalences.mdᵉ) betweenᵉ theᵉ typeᵉ ofᵉ
typeᵉ familiesᵉ `Xᵉ → 𝒰`ᵉ andᵉ theᵉ typeᵉ ofᵉ
[descentᵉ data](synthetic-homotopy-theory.descent-data-pushouts.mdᵉ) forᵉ theᵉ span.ᵉ

**Proof:**ᵉ Weᵉ observeᵉ thatᵉ thereᵉ isᵉ aᵉ commutingᵉ triangleᵉ

```text
           cocone-mapᵉ
  (Xᵉ → 𝒰ᵉ) ----------->ᵉ coconeᵉ 𝒰ᵉ
         \ᵉ             /ᵉ
           \ᵉ         /ᵉ
             ∨ᵉ     ∨ᵉ
          descent-data.ᵉ
```

Theᵉ leftᵉ mapᵉ constructsᵉ descentᵉ data outᵉ ofᵉ aᵉ typeᵉ familyᵉ byᵉ precomposingᵉ theᵉ
coconeᵉ legsᵉ andᵉ transportingᵉ alongᵉ theᵉ commutingᵉ square,ᵉ asᵉ definedᵉ in
[`descent-data-pushouts`](synthetic-homotopy-theory.descent-data-pushouts.md).ᵉ
Theᵉ rightᵉ mapᵉ takesᵉ aᵉ coconeᵉ `(PA,ᵉ PB,ᵉ K)`ᵉ to theᵉ descentᵉ data where theᵉ
equivalencesᵉ `PA(fsᵉ) ≃ᵉ PB(gs)`ᵉ areᵉ obtainedᵉ fromᵉ theᵉ
[identifications](foundation-core.identity-types.mdᵉ) `Kᵉ sᵉ : PA(fsᵉ) = PB(gs)`.ᵉ

Theᵉ topᵉ mapᵉ isᵉ anᵉ equivalenceᵉ byᵉ assumption,ᵉ sinceᵉ weᵉ assumeᵉ thatᵉ theᵉ coconeᵉ isᵉ
aᵉ pushout,ᵉ andᵉ theᵉ rightᵉ mapᵉ isᵉ anᵉ equivalenceᵉ byᵉ
[univalence](foundation-core.univalence.md).ᵉ Itᵉ followsᵉ thatᵉ theᵉ leftᵉ mapᵉ isᵉ anᵉ
equivalenceᵉ byᵉ theᵉ 3-for-2ᵉ propertyᵉ ofᵉ equivalences.ᵉ

Insteadᵉ ofᵉ onlyᵉ statingᵉ thatᵉ thereᵉ isᵉ suchᵉ anᵉ equivalence,ᵉ weᵉ showᵉ aᵉ uniquenessᵉ
propertyᵉ: forᵉ anyᵉ descentᵉ data `(PA,ᵉ PB,ᵉ PS)`,ᵉ theᵉ typeᵉ ofᵉ typeᵉ familiesᵉ
`Pᵉ : Xᵉ → 𝒰`ᵉ equippedᵉ with anᵉ
[equivalenceᵉ ofᵉ descentᵉ data](synthetic-homotopy-theory.equivalences-descent-data-pushouts.mdᵉ)
`(Pᵉ ∘ᵉ i,ᵉ Pᵉ ∘ᵉ j,ᵉ λ sᵉ → trᵉ Pᵉ (Hᵉ sᵉ)) ≃ᵉ (PA,ᵉ PB,ᵉ PS)`ᵉ isᵉ
[contractible](foundation-core.contractible-types.md).ᵉ Inᵉ otherᵉ words,ᵉ thereᵉ isᵉ
aᵉ uniqueᵉ typeᵉ familyᵉ `Pᵉ : Xᵉ → 𝒰`ᵉ suchᵉ thatᵉ thereᵉ areᵉ equivalencesᵉ

```text
  eAᵉ : (aᵉ : Aᵉ) → P(iaᵉ) ≃ᵉ PAᵉ aᵉ
  eBᵉ : (bᵉ : Bᵉ) → P(jbᵉ) ≃ᵉ PBᵉ bᵉ
```

andᵉ theᵉ squareᵉ

```text
           eAᵉ (fsᵉ)
  P(ifsᵉ) -------->ᵉ PA(fsᵉ)
     |                 |
     | trᵉ Pᵉ (Hᵉ sᵉ)      | PSᵉ sᵉ
     |                 |
     ∨ᵉ                 ∨ᵉ
  P(jgsᵉ) -------->ᵉ PB(gsᵉ)
           eBᵉ (gsᵉ)
```

[commutes](foundation-core.commuting-squares-of-maps.mdᵉ) forᵉ allᵉ `sᵉ : S`.ᵉ

**Proof:**ᵉ Theᵉ mapᵉ sendingᵉ typeᵉ familiesᵉ overᵉ `X`ᵉ to descentᵉ data isᵉ anᵉ
equivalence,ᵉ henceᵉ itᵉ isᵉ aᵉ
[contractibleᵉ map](foundation-core.contractible-maps.md).ᵉ Theᵉ contractibleᵉ fiberᵉ
atᵉ `(PA,ᵉ PB,ᵉ PS)`ᵉ isᵉ theᵉ typeᵉ ofᵉ typeᵉ familiesᵉ `Pᵉ : Xᵉ → 𝒰`ᵉ equippedᵉ with anᵉ
identificationᵉ `(Pᵉ ∘ᵉ i,ᵉ Pᵉ ∘ᵉ j,ᵉ λ sᵉ → trᵉ Pᵉ (Hᵉ sᵉ)) = (PA,ᵉ PB,ᵉ PS)`,ᵉ andᵉ theᵉ typeᵉ
ofᵉ suchᵉ identificationsᵉ isᵉ equivalentᵉ to theᵉ typeᵉ ofᵉ equivalencesᵉ ofᵉ descentᵉ
data.ᵉ

## Theorem

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {𝒮ᵉ : span-diagramᵉ l1ᵉ l2ᵉ l3ᵉ}
  where

  equiv-descent-data-cocone-span-diagram-UUᵉ :
    (l4ᵉ : Level) →
    cocone-span-diagramᵉ 𝒮ᵉ (UUᵉ l4ᵉ) ≃ᵉ
    descent-data-pushoutᵉ 𝒮ᵉ l4ᵉ
  equiv-descent-data-cocone-span-diagram-UUᵉ _ =
    equiv-totᵉ
      ( λ PAᵉ →
        equiv-totᵉ
          ( λ PBᵉ →
            ( equiv-Π-equiv-familyᵉ (λ sᵉ → equiv-univalenceᵉ))))

  descent-data-cocone-span-diagram-UUᵉ :
    {l4ᵉ : Level} →
    cocone-span-diagramᵉ 𝒮ᵉ (UUᵉ l4ᵉ) →
    descent-data-pushoutᵉ 𝒮ᵉ l4ᵉ
  descent-data-cocone-span-diagram-UUᵉ {l4ᵉ} =
    map-equivᵉ (equiv-descent-data-cocone-span-diagram-UUᵉ l4ᵉ)

  is-equiv-descent-data-cocone-span-diagram-UUᵉ :
    {l4ᵉ : Level} → is-equivᵉ (descent-data-cocone-span-diagram-UUᵉ {l4ᵉ})
  is-equiv-descent-data-cocone-span-diagram-UUᵉ {l4ᵉ} =
    is-equiv-map-equivᵉ (equiv-descent-data-cocone-span-diagram-UUᵉ l4ᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {𝒮ᵉ : span-diagramᵉ l1ᵉ l2ᵉ l3ᵉ}
  {Xᵉ : UUᵉ l4ᵉ} (cᵉ : cocone-span-diagramᵉ 𝒮ᵉ Xᵉ)
  where

  triangle-descent-data-family-cocone-span-diagramᵉ :
    {l5ᵉ : Level} →
    coherence-triangle-mapsᵉ
      ( descent-data-family-cocone-span-diagramᵉ cᵉ)
      ( descent-data-cocone-span-diagram-UUᵉ {l4ᵉ = l5ᵉ})
      ( cocone-map-span-diagramᵉ cᵉ)
  triangle-descent-data-family-cocone-span-diagramᵉ Pᵉ =
    eq-pair-eq-fiberᵉ
      ( eq-pair-eq-fiberᵉ
        ( eq-htpyᵉ
          ( λ sᵉ → invᵉ (compute-equiv-eq-apᵉ (coherence-square-coconeᵉ _ _ cᵉ sᵉ)))))

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {𝒮ᵉ : span-diagramᵉ l1ᵉ l2ᵉ l3ᵉ}
  {Xᵉ : UUᵉ l4ᵉ} {cᵉ : cocone-span-diagramᵉ 𝒮ᵉ Xᵉ}
  (up-cᵉ : universal-property-pushoutᵉ _ _ cᵉ)
  where

  is-equiv-descent-data-family-cocone-span-diagramᵉ :
    {l5ᵉ : Level} →
    is-equivᵉ (descent-data-family-cocone-span-diagramᵉ cᵉ {l5ᵉ})
  is-equiv-descent-data-family-cocone-span-diagramᵉ {l5ᵉ} =
    is-equiv-left-map-triangleᵉ _ _ _
      ( triangle-descent-data-family-cocone-span-diagramᵉ cᵉ)
      ( up-cᵉ (UUᵉ l5ᵉ))
      ( is-equiv-descent-data-cocone-span-diagram-UUᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level} {𝒮ᵉ : span-diagramᵉ l1ᵉ l2ᵉ l3ᵉ}
  {Xᵉ : UUᵉ l4ᵉ} {cᵉ : cocone-span-diagramᵉ 𝒮ᵉ Xᵉ}
  (up-cᵉ : universal-property-pushoutᵉ _ _ cᵉ)
  (Pᵉ : descent-data-pushoutᵉ 𝒮ᵉ l5ᵉ)
  where

  abstract
    uniqueness-family-cocone-descent-data-pushoutᵉ :
      is-contrᵉ
        ( Σᵉ ( Xᵉ → UUᵉ l5ᵉ)
            ( λ Qᵉ →
              equiv-descent-data-pushoutᵉ
                ( descent-data-family-cocone-span-diagramᵉ cᵉ Qᵉ)
                ( Pᵉ)))
    uniqueness-family-cocone-descent-data-pushoutᵉ =
      is-contr-equiv'ᵉ
        ( fiberᵉ (descent-data-family-cocone-span-diagramᵉ cᵉ) Pᵉ)
        ( equiv-totᵉ
          ( λ Qᵉ →
            extensionality-descent-data-pushoutᵉ
              ( descent-data-family-cocone-span-diagramᵉ cᵉ Qᵉ)
              ( Pᵉ)))
        ( is-contr-map-is-equivᵉ
          ( is-equiv-descent-data-family-cocone-span-diagramᵉ up-cᵉ)
          ( Pᵉ))

  family-cocone-descent-data-pushoutᵉ : Xᵉ → UUᵉ l5ᵉ
  family-cocone-descent-data-pushoutᵉ =
    pr1ᵉ (centerᵉ uniqueness-family-cocone-descent-data-pushoutᵉ)

  equiv-family-cocone-descent-data-pushoutᵉ :
    equiv-descent-data-pushoutᵉ
      ( descent-data-family-cocone-span-diagramᵉ cᵉ
        ( family-cocone-descent-data-pushoutᵉ))
      ( Pᵉ)
  equiv-family-cocone-descent-data-pushoutᵉ =
    pr2ᵉ (centerᵉ uniqueness-family-cocone-descent-data-pushoutᵉ)

  compute-left-family-cocone-descent-data-pushoutᵉ :
    (aᵉ : domain-span-diagramᵉ 𝒮ᵉ) →
    family-cocone-descent-data-pushoutᵉ (horizontal-map-coconeᵉ _ _ cᵉ aᵉ) ≃ᵉ
    left-family-descent-data-pushoutᵉ Pᵉ aᵉ
  compute-left-family-cocone-descent-data-pushoutᵉ =
    left-equiv-equiv-descent-data-pushoutᵉ
      ( descent-data-family-cocone-span-diagramᵉ cᵉ
        ( family-cocone-descent-data-pushoutᵉ))
      ( Pᵉ)
      ( equiv-family-cocone-descent-data-pushoutᵉ)

  map-compute-left-family-cocone-descent-data-pushoutᵉ :
    (aᵉ : domain-span-diagramᵉ 𝒮ᵉ) →
    family-cocone-descent-data-pushoutᵉ (horizontal-map-coconeᵉ _ _ cᵉ aᵉ) →
    left-family-descent-data-pushoutᵉ Pᵉ aᵉ
  map-compute-left-family-cocone-descent-data-pushoutᵉ aᵉ =
    map-equivᵉ (compute-left-family-cocone-descent-data-pushoutᵉ aᵉ)

  compute-right-family-cocone-descent-data-pushoutᵉ :
    (bᵉ : codomain-span-diagramᵉ 𝒮ᵉ) →
    family-cocone-descent-data-pushoutᵉ (vertical-map-coconeᵉ _ _ cᵉ bᵉ) ≃ᵉ
    right-family-descent-data-pushoutᵉ Pᵉ bᵉ
  compute-right-family-cocone-descent-data-pushoutᵉ =
    right-equiv-equiv-descent-data-pushoutᵉ
      ( descent-data-family-cocone-span-diagramᵉ cᵉ
        ( family-cocone-descent-data-pushoutᵉ))
      ( Pᵉ)
      ( equiv-family-cocone-descent-data-pushoutᵉ)

  map-compute-right-family-cocone-descent-data-pushoutᵉ :
    (bᵉ : codomain-span-diagramᵉ 𝒮ᵉ) →
    family-cocone-descent-data-pushoutᵉ (vertical-map-coconeᵉ _ _ cᵉ bᵉ) →
    right-family-descent-data-pushoutᵉ Pᵉ bᵉ
  map-compute-right-family-cocone-descent-data-pushoutᵉ bᵉ =
    map-equivᵉ (compute-right-family-cocone-descent-data-pushoutᵉ bᵉ)

  inv-equiv-family-cocone-descent-data-pushoutᵉ :
    equiv-descent-data-pushoutᵉ Pᵉ
      ( descent-data-family-cocone-span-diagramᵉ cᵉ
        ( family-cocone-descent-data-pushoutᵉ))
  inv-equiv-family-cocone-descent-data-pushoutᵉ =
    inv-equiv-descent-data-pushoutᵉ
      ( descent-data-family-cocone-span-diagramᵉ cᵉ
        ( family-cocone-descent-data-pushoutᵉ))
      ( Pᵉ)
      ( equiv-family-cocone-descent-data-pushoutᵉ)

  compute-inv-left-family-cocone-descent-data-pushoutᵉ :
    (aᵉ : domain-span-diagramᵉ 𝒮ᵉ) →
    left-family-descent-data-pushoutᵉ Pᵉ aᵉ ≃ᵉ
    family-cocone-descent-data-pushoutᵉ (horizontal-map-coconeᵉ _ _ cᵉ aᵉ)
  compute-inv-left-family-cocone-descent-data-pushoutᵉ =
    left-equiv-equiv-descent-data-pushoutᵉ Pᵉ
      ( descent-data-family-cocone-span-diagramᵉ cᵉ
        ( family-cocone-descent-data-pushoutᵉ))
      ( inv-equiv-family-cocone-descent-data-pushoutᵉ)

  map-compute-inv-left-family-cocone-descent-data-pushoutᵉ :
    (aᵉ : domain-span-diagramᵉ 𝒮ᵉ) →
    left-family-descent-data-pushoutᵉ Pᵉ aᵉ →
    family-cocone-descent-data-pushoutᵉ (horizontal-map-coconeᵉ _ _ cᵉ aᵉ)
  map-compute-inv-left-family-cocone-descent-data-pushoutᵉ aᵉ =
    map-equivᵉ (compute-inv-left-family-cocone-descent-data-pushoutᵉ aᵉ)

  compute-inv-right-family-cocone-descent-data-pushoutᵉ :
    (bᵉ : codomain-span-diagramᵉ 𝒮ᵉ) →
    right-family-descent-data-pushoutᵉ Pᵉ bᵉ ≃ᵉ
    family-cocone-descent-data-pushoutᵉ (vertical-map-coconeᵉ _ _ cᵉ bᵉ)
  compute-inv-right-family-cocone-descent-data-pushoutᵉ =
    right-equiv-equiv-descent-data-pushoutᵉ Pᵉ
      ( descent-data-family-cocone-span-diagramᵉ cᵉ
        ( family-cocone-descent-data-pushoutᵉ))
      ( inv-equiv-family-cocone-descent-data-pushoutᵉ)

  map-compute-inv-right-family-cocone-descent-data-pushoutᵉ :
    (bᵉ : codomain-span-diagramᵉ 𝒮ᵉ) →
    right-family-descent-data-pushoutᵉ Pᵉ bᵉ →
    family-cocone-descent-data-pushoutᵉ (vertical-map-coconeᵉ _ _ cᵉ bᵉ)
  map-compute-inv-right-family-cocone-descent-data-pushoutᵉ bᵉ =
    map-equivᵉ (compute-inv-right-family-cocone-descent-data-pushoutᵉ bᵉ)

  family-with-descent-data-pushout-descent-data-pushoutᵉ :
    family-with-descent-data-pushoutᵉ cᵉ l5ᵉ
  pr1ᵉ family-with-descent-data-pushout-descent-data-pushoutᵉ =
    family-cocone-descent-data-pushoutᵉ
  pr1ᵉ (pr2ᵉ family-with-descent-data-pushout-descent-data-pushoutᵉ) =
    Pᵉ
  pr2ᵉ (pr2ᵉ family-with-descent-data-pushout-descent-data-pushoutᵉ) =
    equiv-family-cocone-descent-data-pushoutᵉ
```