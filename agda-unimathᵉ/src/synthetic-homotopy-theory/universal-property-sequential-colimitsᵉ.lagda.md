# The universal property of sequential colimits

```agda
module synthetic-homotopy-theory.universal-property-sequential-colimitsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.commuting-squares-of-homotopiesᵉ
open import foundation.commuting-triangles-of-mapsᵉ
open import foundation.contractible-mapsᵉ
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.fibers-of-mapsᵉ
open import foundation.function-extensionalityᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.precomposition-functionsᵉ
open import foundation.retractionsᵉ
open import foundation.sectionsᵉ
open import foundation.subtype-identity-principleᵉ
open import foundation.universal-property-equivalencesᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-higher-homotopies-compositionᵉ
open import foundation.whiskering-homotopies-compositionᵉ

open import synthetic-homotopy-theory.cocones-under-sequential-diagramsᵉ
open import synthetic-homotopy-theory.coforksᵉ
open import synthetic-homotopy-theory.coforks-cocones-under-sequential-diagramsᵉ
open import synthetic-homotopy-theory.equivalences-cocones-under-equivalences-sequential-diagramsᵉ
open import synthetic-homotopy-theory.equivalences-sequential-diagramsᵉ
open import synthetic-homotopy-theory.sequential-diagramsᵉ
open import synthetic-homotopy-theory.universal-property-coequalizersᵉ
```

</details>

## Idea

Givenᵉ aᵉ [sequentialᵉ diagram](synthetic-homotopy-theory.sequential-diagrams.mdᵉ)
`(A,ᵉ a)`,ᵉ considerᵉ aᵉ
[coconeᵉ underᵉ it](synthetic-homotopy-theory.cocones-under-sequential-diagrams.mdᵉ)
`c`ᵉ with vertexᵉ `X`.ᵉ Theᵉ **universalᵉ propertyᵉ ofᵉ sequentialᵉ colimits**ᵉ isᵉ theᵉ
statementᵉ thatᵉ theᵉ coconeᵉ postcompositionᵉ mapᵉ

```text
cocone-map-sequential-diagramᵉ : (Xᵉ → Yᵉ) → cocone-sequential-diagramᵉ Yᵉ
```

isᵉ anᵉ [equivalence](foundation.equivalences.md).ᵉ

Aᵉ sequentialᵉ colimitᵉ `X`ᵉ mayᵉ beᵉ visualizedᵉ asᵉ aᵉ "pointᵉ in infinity"ᵉ in theᵉ
diagramᵉ

```text
     a₀ᵉ      a₁ᵉ      a₂ᵉ     iᵉ
 A₀ᵉ --->ᵉ A₁ᵉ --->ᵉ A₂ᵉ --->ᵉ ⋯ᵉ -->ᵉ X.ᵉ
```

## Definitions

### The universal property of sequential colimits

```agda
module _
  { l1ᵉ l2ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ} {Xᵉ : UUᵉ l2ᵉ}
  ( cᵉ : cocone-sequential-diagramᵉ Aᵉ Xᵉ)
  where

  universal-property-sequential-colimitᵉ : UUωᵉ
  universal-property-sequential-colimitᵉ =
    {lᵉ : Level} (Yᵉ : UUᵉ lᵉ) → is-equivᵉ (cocone-map-sequential-diagramᵉ cᵉ {Yᵉ = Yᵉ})
```

### The map induced by the universal property of sequential colimits

Theᵉ universalᵉ propertyᵉ allowsᵉ usᵉ to constructᵉ aᵉ mapᵉ fromᵉ theᵉ colimitᵉ byᵉ
providingᵉ aᵉ coconeᵉ underᵉ theᵉ sequentialᵉ diagram.ᵉ

```agda
module _
  { l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ} {Xᵉ : UUᵉ l2ᵉ}
  { cᵉ : cocone-sequential-diagramᵉ Aᵉ Xᵉ} {Yᵉ : UUᵉ l3ᵉ}
  ( up-sequential-colimitᵉ : universal-property-sequential-colimitᵉ cᵉ)
  where

  equiv-universal-property-sequential-colimitᵉ :
    (Xᵉ → Yᵉ) ≃ᵉ cocone-sequential-diagramᵉ Aᵉ Yᵉ
  pr1ᵉ equiv-universal-property-sequential-colimitᵉ =
    cocone-map-sequential-diagramᵉ cᵉ
  pr2ᵉ equiv-universal-property-sequential-colimitᵉ =
    up-sequential-colimitᵉ Yᵉ

  map-universal-property-sequential-colimitᵉ :
    cocone-sequential-diagramᵉ Aᵉ Yᵉ → (Xᵉ → Yᵉ)
  map-universal-property-sequential-colimitᵉ =
    map-inv-is-equivᵉ (up-sequential-colimitᵉ Yᵉ)
```

## Properties

### The mediating map obtained by the universal property is unique

```agda
module _
  { l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ} {Xᵉ : UUᵉ l2ᵉ}
  { cᵉ : cocone-sequential-diagramᵉ Aᵉ Xᵉ} {Yᵉ : UUᵉ l3ᵉ}
  ( up-sequential-colimitᵉ : universal-property-sequential-colimitᵉ cᵉ)
  ( c'ᵉ : cocone-sequential-diagramᵉ Aᵉ Yᵉ)
  where

  htpy-cocone-universal-property-sequential-colimitᵉ :
    htpy-cocone-sequential-diagramᵉ
      ( cocone-map-sequential-diagramᵉ cᵉ
        ( map-universal-property-sequential-colimitᵉ
          ( up-sequential-colimitᵉ)
          ( c'ᵉ)))
      ( c'ᵉ)
  htpy-cocone-universal-property-sequential-colimitᵉ =
    htpy-eq-cocone-sequential-diagramᵉ Aᵉ
      ( cocone-map-sequential-diagramᵉ cᵉ
        ( map-universal-property-sequential-colimitᵉ
          ( up-sequential-colimitᵉ)
          ( c'ᵉ)))
      ( c'ᵉ)
      ( is-section-map-inv-is-equivᵉ (up-sequential-colimitᵉ Yᵉ) c'ᵉ)

  abstract
    uniqueness-map-universal-property-sequential-colimitᵉ :
      is-contrᵉ
        ( Σᵉ ( Xᵉ → Yᵉ)
            ( λ hᵉ →
              htpy-cocone-sequential-diagramᵉ
                ( cocone-map-sequential-diagramᵉ cᵉ hᵉ)
                ( c'ᵉ)))
    uniqueness-map-universal-property-sequential-colimitᵉ =
      is-contr-equiv'ᵉ
        ( fiberᵉ (cocone-map-sequential-diagramᵉ cᵉ) c'ᵉ)
        ( equiv-totᵉ
          ( λ hᵉ →
            extensionality-cocone-sequential-diagramᵉ Aᵉ
              ( cocone-map-sequential-diagramᵉ cᵉ hᵉ)
              ( c'ᵉ)))
        ( is-contr-map-is-equivᵉ (up-sequential-colimitᵉ Yᵉ) c'ᵉ)
```

### The cocone of a sequential colimit induces the identity function by its universal property

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ}
  {Xᵉ : UUᵉ l2ᵉ} {cᵉ : cocone-sequential-diagramᵉ Aᵉ Xᵉ}
  (up-cᵉ : universal-property-sequential-colimitᵉ cᵉ)
  where

  compute-map-universal-property-sequential-colimit-idᵉ :
    map-universal-property-sequential-colimitᵉ up-cᵉ cᵉ ~ᵉ idᵉ
  compute-map-universal-property-sequential-colimit-idᵉ =
    htpy-eqᵉ
      ( apᵉ pr1ᵉ
        ( eq-is-contr'ᵉ
          ( uniqueness-map-universal-property-sequential-colimitᵉ up-cᵉ cᵉ)
          ( ( map-universal-property-sequential-colimitᵉ up-cᵉ cᵉ) ,ᵉ
            ( htpy-cocone-universal-property-sequential-colimitᵉ up-cᵉ cᵉ))
          ( idᵉ ,ᵉ htpy-cocone-map-id-sequential-diagramᵉ Aᵉ cᵉ)))
```

### Homotopies between cocones under sequential diagrams induce homotopies between the induced maps out of sequential colimits

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ}
  {Xᵉ : UUᵉ l2ᵉ} {cᵉ : cocone-sequential-diagramᵉ Aᵉ Xᵉ}
  (up-cᵉ : universal-property-sequential-colimitᵉ cᵉ)
  {Yᵉ : UUᵉ l3ᵉ} {c'ᵉ c''ᵉ : cocone-sequential-diagramᵉ Aᵉ Yᵉ}
  (Hᵉ : htpy-cocone-sequential-diagramᵉ c'ᵉ c''ᵉ)
  where

  htpy-map-universal-property-htpy-cocone-sequential-diagramᵉ :
    map-universal-property-sequential-colimitᵉ up-cᵉ c'ᵉ ~ᵉ
    map-universal-property-sequential-colimitᵉ up-cᵉ c''ᵉ
  htpy-map-universal-property-htpy-cocone-sequential-diagramᵉ =
    htpy-eqᵉ
      ( apᵉ
        ( map-universal-property-sequential-colimitᵉ up-cᵉ)
        ( eq-htpy-cocone-sequential-diagramᵉ Aᵉ c'ᵉ c''ᵉ Hᵉ))
```

### Correspondence between universal properties of sequential colimits and coequalizers

Aᵉ coconeᵉ underᵉ aᵉ sequentialᵉ diagramᵉ hasᵉ theᵉ universalᵉ propertyᵉ ofᵉ sequentialᵉ
colimitsᵉ ifᵉ andᵉ onlyᵉ ifᵉ theᵉ
[correspondingᵉ cofork](synthetic-homotopy-theory.cocones-under-sequential-diagrams.mdᵉ)
hasᵉ theᵉ universalᵉ propertyᵉ ofᵉ coequalizers.ᵉ

```agda
module _
  { l1ᵉ l2ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ} {Xᵉ : UUᵉ l2ᵉ}
  ( cᵉ : cocone-sequential-diagramᵉ Aᵉ Xᵉ)
  where

  universal-property-sequential-colimit-universal-property-coequalizerᵉ :
    universal-property-coequalizerᵉ
      ( double-arrow-sequential-diagramᵉ Aᵉ)
      ( cofork-cocone-sequential-diagramᵉ cᵉ) →
    universal-property-sequential-colimitᵉ cᵉ
  universal-property-sequential-colimit-universal-property-coequalizerᵉ
    ( up-coforkᵉ)
    ( Yᵉ) =
    is-equiv-left-map-triangleᵉ
      ( cocone-map-sequential-diagramᵉ cᵉ)
      ( cocone-sequential-diagram-coforkᵉ)
      ( cofork-mapᵉ
        ( double-arrow-sequential-diagramᵉ Aᵉ)
        ( cofork-cocone-sequential-diagramᵉ cᵉ))
      ( triangle-cocone-sequential-diagram-coforkᵉ cᵉ)
      ( up-coforkᵉ Yᵉ)
      ( is-equiv-cocone-sequential-diagram-coforkᵉ)

  universal-property-coequalizer-universal-property-sequential-colimitᵉ :
    universal-property-sequential-colimitᵉ cᵉ →
    universal-property-coequalizerᵉ
      ( double-arrow-sequential-diagramᵉ Aᵉ)
      ( cofork-cocone-sequential-diagramᵉ cᵉ)
  universal-property-coequalizer-universal-property-sequential-colimitᵉ
    ( up-sequential-colimitᵉ)
    ( Yᵉ) =
    is-equiv-top-map-triangleᵉ
      ( cocone-map-sequential-diagramᵉ cᵉ)
      ( cocone-sequential-diagram-coforkᵉ)
      ( cofork-mapᵉ
        ( double-arrow-sequential-diagramᵉ Aᵉ)
        ( cofork-cocone-sequential-diagramᵉ cᵉ))
      ( triangle-cocone-sequential-diagram-coforkᵉ cᵉ)
      ( is-equiv-cocone-sequential-diagram-coforkᵉ)
      ( up-sequential-colimitᵉ Yᵉ)
```

### The universal property of colimits is preserved by equivalences of cocones under equivalences of sequential diagrams

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  {Aᵉ : sequential-diagramᵉ l1ᵉ} {Xᵉ : UUᵉ l2ᵉ} {cᵉ : cocone-sequential-diagramᵉ Aᵉ Xᵉ}
  {Bᵉ : sequential-diagramᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ} {c'ᵉ : cocone-sequential-diagramᵉ Bᵉ Yᵉ}
  (eᵉ : equiv-sequential-diagramᵉ Aᵉ Bᵉ)
  (e'ᵉ : equiv-cocone-equiv-sequential-diagramᵉ cᵉ c'ᵉ eᵉ)
  where

  universal-property-sequential-colimit-equiv-cocone-equiv-sequential-diagramᵉ :
    universal-property-sequential-colimitᵉ c'ᵉ →
    universal-property-sequential-colimitᵉ cᵉ
  universal-property-sequential-colimit-equiv-cocone-equiv-sequential-diagramᵉ
    up-c'ᵉ =
    universal-property-sequential-colimit-universal-property-coequalizerᵉ cᵉ
      ( universal-property-coequalizer-equiv-cofork-equiv-double-arrowᵉ
        ( cofork-cocone-sequential-diagramᵉ cᵉ)
        ( cofork-cocone-sequential-diagramᵉ c'ᵉ)
        ( equiv-double-arrow-equiv-sequential-diagramᵉ Aᵉ Bᵉ eᵉ)
        ( equiv-cofork-equiv-cocone-equiv-sequential-diagramᵉ cᵉ c'ᵉ eᵉ e'ᵉ)
        ( universal-property-coequalizer-universal-property-sequential-colimitᵉ _
          ( up-c'ᵉ)))

  universal-property-sequential-colimit-equiv-cocone-equiv-sequential-diagram'ᵉ :
    universal-property-sequential-colimitᵉ cᵉ →
    universal-property-sequential-colimitᵉ c'ᵉ
  universal-property-sequential-colimit-equiv-cocone-equiv-sequential-diagram'ᵉ
    up-cᵉ =
    universal-property-sequential-colimit-universal-property-coequalizerᵉ c'ᵉ
      ( universal-property-coequalizer-equiv-cofork-equiv-double-arrow'ᵉ
        ( cofork-cocone-sequential-diagramᵉ cᵉ)
        ( cofork-cocone-sequential-diagramᵉ c'ᵉ)
        ( equiv-double-arrow-equiv-sequential-diagramᵉ Aᵉ Bᵉ eᵉ)
        ( equiv-cofork-equiv-cocone-equiv-sequential-diagramᵉ cᵉ c'ᵉ eᵉ e'ᵉ)
        ( universal-property-coequalizer-universal-property-sequential-colimitᵉ _
          ( up-cᵉ)))
```

### The 3-for-2 property of the universal property of sequential colimits

Givenᵉ twoᵉ coconesᵉ underᵉ aᵉ sequentialᵉ diagram,ᵉ oneᵉ ofᵉ whichᵉ hasᵉ theᵉ universalᵉ
propertyᵉ ofᵉ sequentialᵉ colimits,ᵉ andᵉ aᵉ mapᵉ betweenᵉ theirᵉ vertices,ᵉ weᵉ proveᵉ thatᵉ
theᵉ otherᵉ hasᵉ theᵉ universalᵉ propertyᵉ ifᵉ andᵉ onlyᵉ ifᵉ theᵉ mapᵉ isᵉ anᵉ
[equivalence](foundation.equivalences.md).ᵉ

```agda
module _
  { l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ} {Xᵉ : UUᵉ l2ᵉ} {Yᵉ : UUᵉ l3ᵉ}
  ( cᵉ : cocone-sequential-diagramᵉ Aᵉ Xᵉ)
  ( c'ᵉ : cocone-sequential-diagramᵉ Aᵉ Yᵉ)
  ( hᵉ : Xᵉ → Yᵉ)
  ( Hᵉ :
    htpy-cocone-sequential-diagramᵉ (cocone-map-sequential-diagramᵉ cᵉ hᵉ) c'ᵉ)
  where

  inv-triangle-cocone-map-precomp-sequential-diagramᵉ :
    { l4ᵉ : Level} (Zᵉ : UUᵉ l4ᵉ) →
    coherence-triangle-maps'ᵉ
      ( cocone-map-sequential-diagramᵉ c'ᵉ)
      ( cocone-map-sequential-diagramᵉ cᵉ)
      ( precompᵉ hᵉ Zᵉ)
  inv-triangle-cocone-map-precomp-sequential-diagramᵉ Zᵉ kᵉ =
    ( cocone-map-comp-sequential-diagramᵉ Aᵉ cᵉ hᵉ kᵉ) ∙ᵉ
    ( apᵉ
      ( λ dᵉ → cocone-map-sequential-diagramᵉ dᵉ kᵉ)
      ( eq-htpy-cocone-sequential-diagramᵉ Aᵉ
        ( cocone-map-sequential-diagramᵉ cᵉ hᵉ)
        ( c'ᵉ)
        ( Hᵉ)))

  triangle-cocone-map-precomp-sequential-diagramᵉ :
    { l4ᵉ : Level} (Zᵉ : UUᵉ l4ᵉ) →
    coherence-triangle-mapsᵉ
      ( cocone-map-sequential-diagramᵉ c'ᵉ)
      ( cocone-map-sequential-diagramᵉ cᵉ)
      ( precompᵉ hᵉ Zᵉ)
  triangle-cocone-map-precomp-sequential-diagramᵉ Zᵉ =
    inv-htpyᵉ (inv-triangle-cocone-map-precomp-sequential-diagramᵉ Zᵉ)

  abstract
    is-equiv-universal-property-sequential-colimit-universal-property-sequential-colimitᵉ :
      universal-property-sequential-colimitᵉ cᵉ →
      universal-property-sequential-colimitᵉ c'ᵉ →
      is-equivᵉ hᵉ
    is-equiv-universal-property-sequential-colimit-universal-property-sequential-colimitᵉ
      ( up-sequential-colimitᵉ)
      ( up-sequential-colimit'ᵉ) =
      is-equiv-is-equiv-precompᵉ hᵉ
        ( λ Zᵉ →
          is-equiv-top-map-triangleᵉ
            ( cocone-map-sequential-diagramᵉ c'ᵉ)
            ( cocone-map-sequential-diagramᵉ cᵉ)
            ( precompᵉ hᵉ Zᵉ)
            ( triangle-cocone-map-precomp-sequential-diagramᵉ Zᵉ)
            ( up-sequential-colimitᵉ Zᵉ)
            ( up-sequential-colimit'ᵉ Zᵉ))

    universal-property-sequential-colimit-is-equiv-universal-property-sequential-colimitᵉ :
      universal-property-sequential-colimitᵉ cᵉ →
      is-equivᵉ hᵉ →
      universal-property-sequential-colimitᵉ c'ᵉ
    universal-property-sequential-colimit-is-equiv-universal-property-sequential-colimitᵉ
      ( up-sequential-colimitᵉ)
      ( is-equiv-hᵉ)
      ( Zᵉ) =
      is-equiv-left-map-triangleᵉ
        ( cocone-map-sequential-diagramᵉ c'ᵉ)
        ( cocone-map-sequential-diagramᵉ cᵉ)
        ( precompᵉ hᵉ Zᵉ)
        ( triangle-cocone-map-precomp-sequential-diagramᵉ Zᵉ)
        ( is-equiv-precomp-is-equivᵉ hᵉ is-equiv-hᵉ Zᵉ)
        ( up-sequential-colimitᵉ Zᵉ)

    universal-property-sequential-colimit-universal-property-sequential-colimit-is-equivᵉ :
      is-equivᵉ hᵉ →
      universal-property-sequential-colimitᵉ c'ᵉ →
      universal-property-sequential-colimitᵉ cᵉ
    universal-property-sequential-colimit-universal-property-sequential-colimit-is-equivᵉ
      ( is-equiv-hᵉ)
      ( up-sequential-colimitᵉ)
      ( Zᵉ) =
      is-equiv-right-map-triangleᵉ
        ( cocone-map-sequential-diagramᵉ c'ᵉ)
        ( cocone-map-sequential-diagramᵉ cᵉ)
        ( precompᵉ hᵉ Zᵉ)
        ( triangle-cocone-map-precomp-sequential-diagramᵉ Zᵉ)
        ( up-sequential-colimitᵉ Zᵉ)
        ( is-equiv-precomp-is-equivᵉ hᵉ is-equiv-hᵉ Zᵉ)
```

### Unique uniqueness of of sequential colimits

```agda
module _
  { l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ} {Xᵉ : UUᵉ l2ᵉ} {Yᵉ : UUᵉ l3ᵉ}
  { cᵉ : cocone-sequential-diagramᵉ Aᵉ Xᵉ}
  ( up-cᵉ : universal-property-sequential-colimitᵉ cᵉ)
  { c'ᵉ : cocone-sequential-diagramᵉ Aᵉ Yᵉ}
  ( up-c'ᵉ : universal-property-sequential-colimitᵉ c'ᵉ)
  where

  abstract
    uniquely-unique-sequential-colimitᵉ :
      is-contrᵉ
        ( Σᵉ ( Xᵉ ≃ᵉ Yᵉ)
            ( λ eᵉ →
              htpy-cocone-sequential-diagramᵉ
                ( cocone-map-sequential-diagramᵉ cᵉ (map-equivᵉ eᵉ))
                ( c'ᵉ)))
    uniquely-unique-sequential-colimitᵉ =
      is-torsorial-Eq-subtypeᵉ
        ( uniqueness-map-universal-property-sequential-colimitᵉ up-cᵉ c'ᵉ)
        ( is-property-is-equivᵉ)
        ( map-universal-property-sequential-colimitᵉ up-cᵉ c'ᵉ)
        ( htpy-cocone-universal-property-sequential-colimitᵉ up-cᵉ c'ᵉ)
        ( is-equiv-universal-property-sequential-colimit-universal-property-sequential-colimitᵉ
          ( cᵉ)
          ( c'ᵉ)
          ( map-universal-property-sequential-colimitᵉ up-cᵉ c'ᵉ)
          ( htpy-cocone-universal-property-sequential-colimitᵉ up-cᵉ c'ᵉ)
          ( up-cᵉ)
          ( up-c'ᵉ))
```

### Inclusion maps of a sequential colimit under a sequential diagram of equivalences are equivalences

Ifᵉ aᵉ sequentialᵉ diagramᵉ `(A,ᵉ a)`ᵉ with aᵉ colimitᵉ `X`ᵉ andᵉ inclusionᵉ mapsᵉ
`iₙᵉ : Aₙᵉ → X`ᵉ hasᵉ theᵉ propertyᵉ thatᵉ allᵉ `aₙᵉ : Aₙᵉ → Aₙ₊₁`ᵉ areᵉ equivalences,ᵉ thenᵉ
allᵉ theᵉ inclusionᵉ mapsᵉ areᵉ alsoᵉ equivalences.ᵉ

Itᵉ sufficesᵉ to showᵉ thatᵉ `i₀ᵉ : A₀ᵉ → X`ᵉ isᵉ anᵉ equivalence,ᵉ sinceᵉ thenᵉ theᵉ
statementᵉ followsᵉ byᵉ inductionᵉ onᵉ `n`ᵉ andᵉ theᵉ 3-for-2ᵉ propertyᵉ ofᵉ equivalencesᵉ:
weᵉ haveᵉ [commutingᵉ triangles](foundation-core.commuting-triangles-of-maps.mdᵉ)

```text
        aₙᵉ
  Aₙᵉ ------>ᵉ Aₙ₊₁ᵉ
    \ᵉ   ≃ᵉ   /ᵉ
  ≃ᵉ  \ᵉ     /ᵉ
   iₙᵉ \ᵉ   /ᵉ iₙ₊₁ᵉ
       ∨ᵉ ∨ᵉ
        Xᵉ ,ᵉ
```

where `aₙ`ᵉ isᵉ anᵉ equivalenceᵉ byᵉ assumption,ᵉ andᵉ `iₙ`ᵉ isᵉ anᵉ equivalenceᵉ byᵉ theᵉ
inductionᵉ hypothesis,ᵉ makingᵉ `iₙ₊₁`ᵉ anᵉ equivalence.ᵉ

Toᵉ showᵉ thatᵉ `i₀`ᵉ isᵉ anᵉ equivalence,ᵉ weᵉ useᵉ theᵉ mapᵉ

```text
  first-map-cocone-sequential-colimitᵉ : {Yᵉ : 𝒰ᵉ} → coconeᵉ Aᵉ Yᵉ → (A₀ᵉ → Yᵉ)
```

selectingᵉ theᵉ firstᵉ mapᵉ ofᵉ aᵉ coconeᵉ `j₀ᵉ : A₀ᵉ → Y`,ᵉ whichᵉ makesᵉ theᵉ followingᵉ
triangleᵉ commuteᵉ:

```text
        cocone-mapᵉ
  Xᵉ → Yᵉ ---------->ᵉ coconeᵉ Aᵉ Yᵉ
        \ᵉ         /ᵉ
         \ᵉ       /ᵉ
   -ᵉ ∘ᵉ i₀ᵉ \ᵉ     /ᵉ first-map-cocone-sequential-colimitᵉ
           \ᵉ   /ᵉ
            ∨ᵉ ∨ᵉ
          A₀ᵉ → Yᵉ .ᵉ
```

Byᵉ `X`ᵉ beingᵉ aᵉ colimitᵉ weᵉ haveᵉ thatᵉ `cocone-map`ᵉ isᵉ anᵉ equivalence.ᵉ Thenᵉ itᵉ
sufficesᵉ to showᵉ thatᵉ `first-map-cocone-sequential-colimit`ᵉ isᵉ anᵉ equivalence,ᵉ
becauseᵉ itᵉ wouldᵉ followᵉ thatᵉ `-ᵉ ∘ᵉ i₀`ᵉ isᵉ anᵉ equivalence,ᵉ whichᵉ byᵉ theᵉ
[universalᵉ propertyᵉ ofᵉ equivalences](foundation.universal-property-equivalences.mdᵉ)
impliesᵉ thatᵉ `iₒ`ᵉ isᵉ anᵉ equivalence.ᵉ

Toᵉ showᵉ thatᵉ `first-map-cocone-sequential-colimit`ᵉ isᵉ anᵉ equivalence,ᵉ weᵉ
constructᵉ anᵉ inverseᵉ mapᵉ

```text
  cocone-first-map-is-equiv-sequential-diagramᵉ : {Yᵉ : 𝒰ᵉ} → (A₀ᵉ → Yᵉ) → coconeᵉ Aᵉ Yᵉ ,ᵉ
```

whichᵉ to everyᵉ `fᵉ : A₀ᵉ → Y`ᵉ assignsᵉ theᵉ coconeᵉ

```text
       a₀ᵉ       a₁ᵉ
  A₀ᵉ ---->ᵉ A₁ᵉ ---->ᵉ A₂ᵉ ---->ᵉ ⋯ᵉ
    \ᵉ      |      /ᵉ
     \ᵉ     |     /ᵉ
      \ᵉ fᵉ ∘ᵉ a₀⁻¹/ᵉ
     fᵉ \ᵉ   |   /ᵉ fᵉ ∘ᵉ a₁⁻¹ᵉ ∘ᵉ a₀⁻¹ᵉ
        \ᵉ  |  /ᵉ
         ∨ᵉ ∨ᵉ ∨ᵉ
           Yᵉ ,ᵉ
```

where theᵉ coherencesᵉ areᵉ witnessesᵉ thatᵉ `aₙ⁻¹`ᵉ areᵉ retractionsᵉ ofᵉ `aₙ`.ᵉ

Sinceᵉ theᵉ firstᵉ inclusionᵉ mapᵉ in thisᵉ coconeᵉ isᵉ `f`,ᵉ itᵉ isᵉ immediateᵉ thatᵉ
`cocone-first-map-is-equiv-sequential-diagram`ᵉ isᵉ aᵉ sectionᵉ ofᵉ
`first-map-cocone-sequential-colimit`.ᵉ Toᵉ showᵉ thatᵉ itᵉ isᵉ aᵉ retractionᵉ weᵉ needᵉ aᵉ
homotopyᵉ forᵉ anyᵉ coconeᵉ `c`ᵉ betweenᵉ itselfᵉ andᵉ theᵉ coconeᵉ inducedᵉ byᵉ itsᵉ firstᵉ
mapᵉ `j₀ᵉ : A₀ᵉ → Y`.ᵉ Weᵉ referᵉ to theᵉ coconeᵉ inducedᵉ byᵉ `j₀`ᵉ asᵉ `(j₀')`.ᵉ

Theᵉ homotopyᵉ ofᵉ coconesᵉ consistsᵉ ofᵉ homotopiesᵉ

```text
  Kₙᵉ : (j₀')ₙᵉ ~ᵉ jₙᵉ ,ᵉ
```

whichᵉ weᵉ constructᵉ byᵉ inductionᵉ asᵉ

```text
  K₀ᵉ : (j₀')₀ᵉ ≐ᵉ j₀ᵉ ~ᵉ j₀ᵉ     byᵉ reflexivityᵉ
  Kₙ₊₁ᵉ : (j₀')ₙ₊₁ᵉ
       ≐ᵉ (j₀')ₙᵉ ∘ᵉ aₙ⁻¹ᵉ      byᵉ definitionᵉ
       ~ᵉ jₙᵉ ∘ᵉ aₙ⁻¹ᵉ          byᵉ Kₙᵉ
       ~ᵉ jₙ₊₁ᵉ ∘ᵉ aₙᵉ ∘ᵉ aₙ⁻¹ᵉ   byᵉ coherenceᵉ Hₙᵉ ofᵉ cᵉ
       ~ᵉ jₙ₊₁ᵉ               byᵉ aₙ⁻¹ᵉ beingᵉ aᵉ sectionᵉ ofᵉ aₙᵉ ,ᵉ
```

andᵉ aᵉ coherenceᵉ datumᵉ whichᵉ uponᵉ someᵉ ponderingᵉ boilsᵉ downᵉ to theᵉ followingᵉ
[commutingᵉ squareᵉ ofᵉ homotopies](foundation-core.commuting-squares-of-homotopies.mdᵉ):

```text
                        Kₙᵉ ·rᵉ (aₙ⁻¹ᵉ ∘ᵉ aₙᵉ)                Hₙᵉ ·rᵉ (aₙ⁻¹ᵉ ∘ᵉ aₙᵉ)
     (j₀')ₙᵉ ∘ᵉ aₙ⁻¹ᵉ ∘ᵉ aₙᵉ ---------------->ᵉ jₙᵉ ∘ᵉ aₙ⁻¹ᵉ ∘ᵉ aₙᵉ ---------------->ᵉ jₙ₊₁ᵉ ∘ᵉ aₙᵉ ∘ᵉ aₙ⁻¹ᵉ ∘ᵉ aₙᵉ
              |                                 |                                    |
              |                                 |                                    |
  (j₀')ₙᵉ ·lᵉ is-retractionᵉ aₙ⁻¹ᵉ      jₙᵉ ·lᵉ is-retractionᵉ aₙ⁻¹ᵉ            jₙ₊₁ᵉ ·lᵉ is-sectionᵉ aₙ⁻¹ᵉ ·rᵉ aₙᵉ
              |                                 |                                    |
              ∨ᵉ                                 ∨ᵉ                                    ∨ᵉ
           (j₀')ₙᵉ ---------------------------->ᵉ jₙᵉ -------------------------->ᵉ  jₙ₊₁ᵉ ∘ᵉ aₙᵉ .ᵉ
                               Kₙᵉ                                 Hₙᵉ
```

Thisᵉ rectangleᵉ isᵉ almostᵉ aᵉ pastingᵉ ofᵉ theᵉ squaresᵉ ofᵉ naturalityᵉ ofᵉ `Kₙ`ᵉ andᵉ `Hₙ`ᵉ
with respectᵉ to `is-retraction`ᵉ ---ᵉ itᵉ remainsᵉ to passᵉ fromᵉ
`(jₙ₊₁ᵉ ∘ᵉ aₙᵉ) ·lᵉ is-retractionᵉ aₙ⁻¹`ᵉ to `jₙ₊₁ᵉ ·lᵉ is-sectionᵉ aₙ⁻¹ᵉ ·rᵉ aₙ`,ᵉ whichᵉ weᵉ
canᵉ do byᵉ applyingᵉ theᵉ coherenceᵉ ofᵉ
[coherentlyᵉ invertibleᵉ maps](foundation-core.coherently-invertible-maps.md).ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ}
  (equivsᵉ : (nᵉ : ℕᵉ) → is-equivᵉ (map-sequential-diagramᵉ Aᵉ nᵉ))
  where

  map-cocone-first-map-is-equiv-sequential-diagramᵉ :
    (family-sequential-diagramᵉ Aᵉ 0 → Yᵉ) →
    (nᵉ : ℕᵉ) →
    family-sequential-diagramᵉ Aᵉ nᵉ → Yᵉ
  map-cocone-first-map-is-equiv-sequential-diagramᵉ fᵉ zero-ℕᵉ =
    fᵉ
  map-cocone-first-map-is-equiv-sequential-diagramᵉ fᵉ (succ-ℕᵉ nᵉ) =
    ( map-cocone-first-map-is-equiv-sequential-diagramᵉ fᵉ nᵉ) ∘ᵉ
    ( map-inv-is-equivᵉ (equivsᵉ nᵉ))

  inv-htpy-cocone-first-map-is-equiv-sequential-diagramᵉ :
    (fᵉ : family-sequential-diagramᵉ Aᵉ 0 → Yᵉ) →
    (nᵉ : ℕᵉ) →
    coherence-triangle-maps'ᵉ
      ( map-cocone-first-map-is-equiv-sequential-diagramᵉ fᵉ nᵉ)
      ( ( map-cocone-first-map-is-equiv-sequential-diagramᵉ fᵉ nᵉ) ∘ᵉ
        ( map-inv-is-equivᵉ (equivsᵉ nᵉ)))
      ( map-sequential-diagramᵉ Aᵉ nᵉ)
  inv-htpy-cocone-first-map-is-equiv-sequential-diagramᵉ fᵉ nᵉ =
    ( map-cocone-first-map-is-equiv-sequential-diagramᵉ fᵉ nᵉ) ·lᵉ
    ( is-retraction-map-inv-is-equivᵉ (equivsᵉ nᵉ))

  htpy-cocone-first-map-is-equiv-sequential-diagramᵉ :
    (fᵉ : family-sequential-diagramᵉ Aᵉ 0 → Yᵉ) →
    (nᵉ : ℕᵉ) →
    coherence-triangle-mapsᵉ
      ( map-cocone-first-map-is-equiv-sequential-diagramᵉ fᵉ nᵉ)
      ( ( map-cocone-first-map-is-equiv-sequential-diagramᵉ fᵉ nᵉ) ∘ᵉ
        ( map-inv-is-equivᵉ (equivsᵉ nᵉ)))
      ( map-sequential-diagramᵉ Aᵉ nᵉ)
  htpy-cocone-first-map-is-equiv-sequential-diagramᵉ fᵉ nᵉ =
    inv-htpyᵉ (inv-htpy-cocone-first-map-is-equiv-sequential-diagramᵉ fᵉ nᵉ)

  cocone-first-map-is-equiv-sequential-diagramᵉ :
    (family-sequential-diagramᵉ Aᵉ 0 → Yᵉ) → cocone-sequential-diagramᵉ Aᵉ Yᵉ
  pr1ᵉ (cocone-first-map-is-equiv-sequential-diagramᵉ fᵉ) =
    map-cocone-first-map-is-equiv-sequential-diagramᵉ fᵉ
  pr2ᵉ (cocone-first-map-is-equiv-sequential-diagramᵉ fᵉ) =
    htpy-cocone-first-map-is-equiv-sequential-diagramᵉ fᵉ

  is-section-cocone-first-map-is-equiv-sequential-diagramᵉ :
    is-sectionᵉ
      ( first-map-cocone-sequential-diagramᵉ)
      ( cocone-first-map-is-equiv-sequential-diagramᵉ)
  is-section-cocone-first-map-is-equiv-sequential-diagramᵉ = refl-htpyᵉ

  htpy-htpy-is-retraction-cocone-first-map-is-equiv-sequential-diagramᵉ :
    (cᵉ : cocone-sequential-diagramᵉ Aᵉ Yᵉ) →
    (nᵉ : ℕᵉ) →
    map-cocone-first-map-is-equiv-sequential-diagramᵉ
      ( first-map-cocone-sequential-diagramᵉ cᵉ)
      ( nᵉ) ~ᵉ
    map-cocone-sequential-diagramᵉ cᵉ nᵉ
  htpy-htpy-is-retraction-cocone-first-map-is-equiv-sequential-diagramᵉ
    cᵉ zero-ℕᵉ = refl-htpyᵉ
  htpy-htpy-is-retraction-cocone-first-map-is-equiv-sequential-diagramᵉ
    cᵉ (succ-ℕᵉ nᵉ) =
    ( ( htpy-htpy-is-retraction-cocone-first-map-is-equiv-sequential-diagramᵉ cᵉ
        ( nᵉ)) ·rᵉ
      ( map-inv-is-equivᵉ (equivsᵉ nᵉ))) ∙hᵉ
    ( ( coherence-cocone-sequential-diagramᵉ cᵉ nᵉ) ·rᵉ
      ( map-inv-is-equivᵉ (equivsᵉ nᵉ))) ∙hᵉ
    ( ( map-cocone-sequential-diagramᵉ cᵉ (succ-ℕᵉ nᵉ)) ·lᵉ
      ( is-section-map-inv-is-equivᵉ (equivsᵉ nᵉ)))

  coh-htpy-is-retraction-cocone-first-map-is-equiv-sequential-diagramᵉ :
    (cᵉ : cocone-sequential-diagramᵉ Aᵉ Yᵉ) →
    coherence-htpy-cocone-sequential-diagramᵉ
      ( cocone-first-map-is-equiv-sequential-diagramᵉ
        ( first-map-cocone-sequential-diagramᵉ cᵉ))
      ( cᵉ)
      ( htpy-htpy-is-retraction-cocone-first-map-is-equiv-sequential-diagramᵉ cᵉ)
  coh-htpy-is-retraction-cocone-first-map-is-equiv-sequential-diagramᵉ cᵉ nᵉ =
    inv-htpy-left-transpose-htpy-concatᵉ
      ( inv-htpy-cocone-first-map-is-equiv-sequential-diagramᵉ
        ( first-map-cocone-sequential-diagramᵉ cᵉ)
        ( nᵉ))
      ( ( htpy-htpy-is-retraction-cocone-first-map-is-equiv-sequential-diagramᵉ cᵉ
          ( nᵉ)) ∙hᵉ
        ( coherence-cocone-sequential-diagramᵉ cᵉ nᵉ))
      ( ( htpy-htpy-is-retraction-cocone-first-map-is-equiv-sequential-diagramᵉ cᵉ
          ( succ-ℕᵉ nᵉ)) ·rᵉ
        ( map-sequential-diagramᵉ Aᵉ nᵉ))
      ( concat-right-homotopy-coherence-square-homotopiesᵉ
        ( ( ( htpy-htpy-is-retraction-cocone-first-map-is-equiv-sequential-diagramᵉ
              ( cᵉ)
              ( nᵉ)) ∙hᵉ
            ( coherence-cocone-sequential-diagramᵉ cᵉ nᵉ)) ·rᵉ
          ( map-inv-is-equivᵉ (equivsᵉ nᵉ) ∘ᵉ map-sequential-diagramᵉ Aᵉ nᵉ))
        ( ( map-cocone-first-map-is-equiv-sequential-diagramᵉ
            ( first-map-cocone-sequential-diagramᵉ cᵉ)
            ( nᵉ)) ·lᵉ
          ( is-retraction-map-inv-is-equivᵉ (equivsᵉ nᵉ)))
        ( ( ( map-cocone-sequential-diagramᵉ cᵉ (succ-ℕᵉ nᵉ)) ∘ᵉ
            ( map-sequential-diagramᵉ Aᵉ nᵉ)) ·lᵉ
          ( is-retraction-map-inv-is-equivᵉ (equivsᵉ nᵉ)))
        ( ( htpy-htpy-is-retraction-cocone-first-map-is-equiv-sequential-diagramᵉ
            ( cᵉ)
            ( nᵉ)) ∙hᵉ
          ( coherence-cocone-sequential-diagramᵉ cᵉ nᵉ))
        ( ( inv-preserves-comp-left-whisker-compᵉ
            ( map-cocone-sequential-diagramᵉ cᵉ (succ-ℕᵉ nᵉ))
            ( map-sequential-diagramᵉ Aᵉ nᵉ)
            ( is-retraction-map-inv-is-equivᵉ (equivsᵉ nᵉ))) ∙hᵉ
          ( left-whisker-comp²ᵉ
            ( map-cocone-sequential-diagramᵉ cᵉ (succ-ℕᵉ nᵉ))
            ( inv-htpyᵉ (coherence-map-inv-is-equivᵉ (equivsᵉ nᵉ)))))
        ( λ aᵉ →
          inv-nat-htpyᵉ
            ( ( htpy-htpy-is-retraction-cocone-first-map-is-equiv-sequential-diagramᵉ
                ( cᵉ)
                ( nᵉ)) ∙hᵉ
              ( coherence-cocone-sequential-diagramᵉ cᵉ nᵉ))
            ( is-retraction-map-inv-is-equivᵉ (equivsᵉ nᵉ) aᵉ)))

  abstract
    is-retraction-cocone-first-map-is-equiv-sequential-diagramᵉ :
      is-retractionᵉ
        ( first-map-cocone-sequential-diagramᵉ)
        ( cocone-first-map-is-equiv-sequential-diagramᵉ)
    is-retraction-cocone-first-map-is-equiv-sequential-diagramᵉ cᵉ =
      eq-htpy-cocone-sequential-diagramᵉ Aᵉ _ _
        ( ( htpy-htpy-is-retraction-cocone-first-map-is-equiv-sequential-diagramᵉ
            ( cᵉ)) ,ᵉ
          ( coh-htpy-is-retraction-cocone-first-map-is-equiv-sequential-diagramᵉ
            ( cᵉ)))

  is-equiv-first-map-cocone-is-equiv-sequential-diagramᵉ :
    is-equivᵉ first-map-cocone-sequential-diagramᵉ
  is-equiv-first-map-cocone-is-equiv-sequential-diagramᵉ =
    is-equiv-is-invertibleᵉ
      ( cocone-first-map-is-equiv-sequential-diagramᵉ)
      ( is-section-cocone-first-map-is-equiv-sequential-diagramᵉ)
      ( is-retraction-cocone-first-map-is-equiv-sequential-diagramᵉ)

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ}
  {Xᵉ : UUᵉ l2ᵉ} {cᵉ : cocone-sequential-diagramᵉ Aᵉ Xᵉ}
  (up-cᵉ : universal-property-sequential-colimitᵉ cᵉ)
  (equivsᵉ : (nᵉ : ℕᵉ) → is-equivᵉ (map-sequential-diagramᵉ Aᵉ nᵉ))
  where

  triangle-first-map-cocone-sequential-colimit-is-equivᵉ :
    {l3ᵉ : Level} {Yᵉ : UUᵉ l3ᵉ} →
    coherence-triangle-mapsᵉ
      ( precompᵉ (first-map-cocone-sequential-diagramᵉ cᵉ) Yᵉ)
      ( first-map-cocone-sequential-diagramᵉ)
      ( cocone-map-sequential-diagramᵉ cᵉ)
  triangle-first-map-cocone-sequential-colimit-is-equivᵉ = refl-htpyᵉ

  is-equiv-first-map-cocone-sequential-colimit-is-equivᵉ :
    is-equivᵉ (first-map-cocone-sequential-diagramᵉ cᵉ)
  is-equiv-first-map-cocone-sequential-colimit-is-equivᵉ =
    is-equiv-is-equiv-precompᵉ
      ( first-map-cocone-sequential-diagramᵉ cᵉ)
      ( λ Yᵉ →
        is-equiv-left-map-triangleᵉ
          ( precompᵉ (first-map-cocone-sequential-diagramᵉ cᵉ) Yᵉ)
          ( first-map-cocone-sequential-diagramᵉ)
          ( cocone-map-sequential-diagramᵉ cᵉ)
          ( triangle-first-map-cocone-sequential-colimit-is-equivᵉ)
          ( up-cᵉ Yᵉ)
          ( is-equiv-first-map-cocone-is-equiv-sequential-diagramᵉ equivsᵉ))

  is-equiv-map-cocone-sequential-colimit-is-equivᵉ :
    (nᵉ : ℕᵉ) → is-equivᵉ (map-cocone-sequential-diagramᵉ cᵉ nᵉ)
  is-equiv-map-cocone-sequential-colimit-is-equivᵉ zero-ℕᵉ =
    is-equiv-first-map-cocone-sequential-colimit-is-equivᵉ
  is-equiv-map-cocone-sequential-colimit-is-equivᵉ (succ-ℕᵉ nᵉ) =
    is-equiv-right-map-triangleᵉ
      ( map-cocone-sequential-diagramᵉ cᵉ nᵉ)
      ( map-cocone-sequential-diagramᵉ cᵉ (succ-ℕᵉ nᵉ))
      ( map-sequential-diagramᵉ Aᵉ nᵉ)
      ( coherence-cocone-sequential-diagramᵉ cᵉ nᵉ)
      ( is-equiv-map-cocone-sequential-colimit-is-equivᵉ nᵉ)
      ( equivsᵉ nᵉ)
```

### A sequential colimit of contractible types is contractible

Aᵉ sequentialᵉ diagramᵉ ofᵉ contractibleᵉ typesᵉ consistsᵉ ofᵉ equivalences,ᵉ asᵉ shownᵉ in
[`sequential-diagrams`](synthetic-homotopy-theory.sequential-diagrams.md),ᵉ soᵉ
theᵉ inclusionᵉ mapsᵉ intoᵉ aᵉ colimitᵉ areᵉ equivalencesᵉ asᵉ well,ᵉ asᵉ shownᵉ above.ᵉ Inᵉ
particular,ᵉ thereᵉ isᵉ anᵉ equivalenceᵉ `i₀ᵉ : A₀ᵉ ≃ᵉ X`,ᵉ andᵉ sinceᵉ `A₀`ᵉ isᵉ
contractible,ᵉ itᵉ followsᵉ thatᵉ `X`ᵉ isᵉ contractible.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ}
  {Xᵉ : UUᵉ l2ᵉ} {cᵉ : cocone-sequential-diagramᵉ Aᵉ Xᵉ}
  (up-cᵉ : universal-property-sequential-colimitᵉ cᵉ)
  where

  is-contr-sequential-colimit-is-contr-sequential-diagramᵉ :
    ((nᵉ : ℕᵉ) → is-contrᵉ (family-sequential-diagramᵉ Aᵉ nᵉ)) →
    is-contrᵉ Xᵉ
  is-contr-sequential-colimit-is-contr-sequential-diagramᵉ contrsᵉ =
    is-contr-is-equiv'ᵉ
      ( family-sequential-diagramᵉ Aᵉ 0ᵉ)
      ( map-cocone-sequential-diagramᵉ cᵉ 0ᵉ)
      ( is-equiv-map-cocone-sequential-colimit-is-equivᵉ
        ( up-cᵉ)
        ( is-equiv-sequential-diagram-is-contrᵉ contrsᵉ)
        ( 0ᵉ))
      ( contrsᵉ 0ᵉ)
```