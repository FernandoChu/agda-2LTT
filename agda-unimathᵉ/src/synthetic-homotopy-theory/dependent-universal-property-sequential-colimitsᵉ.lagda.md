# The dependent universal property of sequential colimits

```agda
module synthetic-homotopy-theory.dependent-universal-property-sequential-colimitsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.commuting-triangles-of-mapsᵉ
open import foundation.contractible-mapsᵉ
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.fibers-of-mapsᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.precomposition-dependent-functionsᵉ
open import foundation.precomposition-functionsᵉ
open import foundation.subtype-identity-principleᵉ
open import foundation.universal-property-equivalencesᵉ
open import foundation.universe-levelsᵉ

open import synthetic-homotopy-theory.cocones-under-sequential-diagramsᵉ
open import synthetic-homotopy-theory.coforksᵉ
open import synthetic-homotopy-theory.coforks-cocones-under-sequential-diagramsᵉ
open import synthetic-homotopy-theory.dependent-cocones-under-sequential-diagramsᵉ
open import synthetic-homotopy-theory.dependent-coforksᵉ
open import synthetic-homotopy-theory.dependent-universal-property-coequalizersᵉ
open import synthetic-homotopy-theory.sequential-diagramsᵉ
open import synthetic-homotopy-theory.universal-property-coequalizersᵉ
open import synthetic-homotopy-theory.universal-property-sequential-colimitsᵉ
```

</details>

## Idea

Givenᵉ aᵉ [sequentialᵉ diagram](synthetic-homotopy-theory.sequential-diagrams.mdᵉ)
`(A,ᵉ a)`,ᵉ considerᵉ aᵉ
[coconeᵉ underᵉ it](synthetic-homotopy-theory.cocones-under-sequential-diagrams.mdᵉ)
`c`ᵉ with vertexᵉ `X`.ᵉ Theᵉ **dependentᵉ universalᵉ propertyᵉ ofᵉ sequentialᵉ colimits**ᵉ
isᵉ theᵉ statementᵉ thatᵉ theᵉ dependentᵉ coconeᵉ postcompositionᵉ mapᵉ

```text
dependent-cocone-map-sequential-diagramᵉ :
  ((xᵉ : Xᵉ) → Pᵉ xᵉ) → dependent-cocone-sequential-diagramᵉ Pᵉ
```

isᵉ anᵉ [equivalence](foundation.equivalences.md).ᵉ

## Definitions

### The dependent universal property of sequential colimits

```agda
module _
  { l1ᵉ l2ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ} {Xᵉ : UUᵉ l2ᵉ}
  ( cᵉ : cocone-sequential-diagramᵉ Aᵉ Xᵉ)
  where

  dependent-universal-property-sequential-colimitᵉ : UUωᵉ
  dependent-universal-property-sequential-colimitᵉ =
    {lᵉ : Level} (Pᵉ : Xᵉ → UUᵉ lᵉ) →
    is-equivᵉ (dependent-cocone-map-sequential-diagramᵉ cᵉ Pᵉ)
```

### The map induced by the dependent universal property of sequential colimits

```agda
module _
  { l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ} {Xᵉ : UUᵉ l2ᵉ}
  { cᵉ : cocone-sequential-diagramᵉ Aᵉ Xᵉ} {Pᵉ : Xᵉ → UUᵉ l3ᵉ}
  ( dup-cᵉ :
    dependent-universal-property-sequential-colimitᵉ cᵉ)
  where

  equiv-dependent-universal-property-sequential-colimitᵉ :
    ((xᵉ : Xᵉ) → Pᵉ xᵉ) ≃ᵉ dependent-cocone-sequential-diagramᵉ cᵉ Pᵉ
  pr1ᵉ equiv-dependent-universal-property-sequential-colimitᵉ =
    dependent-cocone-map-sequential-diagramᵉ cᵉ Pᵉ
  pr2ᵉ equiv-dependent-universal-property-sequential-colimitᵉ = dup-cᵉ Pᵉ

  map-dependent-universal-property-sequential-colimitᵉ :
    dependent-cocone-sequential-diagramᵉ cᵉ Pᵉ →
    ( xᵉ : Xᵉ) → Pᵉ xᵉ
  map-dependent-universal-property-sequential-colimitᵉ =
    map-inv-is-equivᵉ (dup-cᵉ Pᵉ)
```

## Properties

### The mediating map obtained by the dependent universal property is unique

```agda
module _
  { l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ} {Xᵉ : UUᵉ l2ᵉ}
  { cᵉ : cocone-sequential-diagramᵉ Aᵉ Xᵉ} {Pᵉ : Xᵉ → UUᵉ l3ᵉ}
  ( dup-cᵉ :
    dependent-universal-property-sequential-colimitᵉ cᵉ)
  ( dᵉ : dependent-cocone-sequential-diagramᵉ cᵉ Pᵉ)
  where

  htpy-dependent-cocone-dependent-universal-property-sequential-colimitᵉ :
    htpy-dependent-cocone-sequential-diagramᵉ Pᵉ
      ( dependent-cocone-map-sequential-diagramᵉ cᵉ Pᵉ
        ( map-dependent-universal-property-sequential-colimitᵉ
          ( dup-cᵉ)
          ( dᵉ)))
      ( dᵉ)
  htpy-dependent-cocone-dependent-universal-property-sequential-colimitᵉ =
    htpy-eq-dependent-cocone-sequential-diagramᵉ Pᵉ
      ( dependent-cocone-map-sequential-diagramᵉ cᵉ Pᵉ
        ( map-dependent-universal-property-sequential-colimitᵉ
          ( dup-cᵉ)
          ( dᵉ)))
      ( dᵉ)
      ( is-section-map-inv-is-equivᵉ (dup-cᵉ Pᵉ) dᵉ)

  abstract
    uniqueness-dependent-universal-property-sequential-colimitᵉ :
      is-contrᵉ
        ( Σᵉ ( ( xᵉ : Xᵉ) → Pᵉ xᵉ)
            ( λ hᵉ →
              htpy-dependent-cocone-sequential-diagramᵉ Pᵉ
                ( dependent-cocone-map-sequential-diagramᵉ cᵉ Pᵉ hᵉ)
                ( dᵉ)))
    uniqueness-dependent-universal-property-sequential-colimitᵉ =
      is-contr-equiv'ᵉ
        ( fiberᵉ (dependent-cocone-map-sequential-diagramᵉ cᵉ Pᵉ) dᵉ)
        ( equiv-totᵉ
          ( λ hᵉ →
            extensionality-dependent-cocone-sequential-diagramᵉ Pᵉ
              ( dependent-cocone-map-sequential-diagramᵉ cᵉ Pᵉ hᵉ)
              ( dᵉ)))
        ( is-contr-map-is-equivᵉ (dup-cᵉ Pᵉ) dᵉ)
```

### Correspondence between dependent universal properties of sequential colimits and coequalizers

Aᵉ coconeᵉ underᵉ aᵉ sequentialᵉ diagramᵉ hasᵉ theᵉ dependentᵉ universalᵉ propertyᵉ ofᵉ
sequentialᵉ colimitsᵉ ifᵉ andᵉ onlyᵉ ifᵉ theᵉ correspondingᵉ coforkᵉ hasᵉ theᵉ dependentᵉ
universalᵉ propertyᵉ ofᵉ coequalizers.ᵉ

```agda
module _
  { l1ᵉ l2ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ} {Xᵉ : UUᵉ l2ᵉ}
  ( cᵉ : cocone-sequential-diagramᵉ Aᵉ Xᵉ)
  where

  dependent-universal-property-sequential-colimit-dependent-universal-property-coequalizerᵉ :
    dependent-universal-property-coequalizerᵉ
      ( double-arrow-sequential-diagramᵉ Aᵉ)
      ( cofork-cocone-sequential-diagramᵉ cᵉ) →
    dependent-universal-property-sequential-colimitᵉ cᵉ
  dependent-universal-property-sequential-colimit-dependent-universal-property-coequalizerᵉ
    ( dup-coequalizerᵉ)
    ( Pᵉ) =
    is-equiv-left-map-triangleᵉ
      ( dependent-cocone-map-sequential-diagramᵉ cᵉ Pᵉ)
      ( dependent-cocone-sequential-diagram-dependent-coforkᵉ Pᵉ)
      ( dependent-cofork-mapᵉ
        ( double-arrow-sequential-diagramᵉ Aᵉ)
        ( cofork-cocone-sequential-diagramᵉ cᵉ))
      ( triangle-dependent-cocone-sequential-diagram-dependent-coforkᵉ Pᵉ)
      ( dup-coequalizerᵉ Pᵉ)
      ( is-equiv-dependent-cocone-sequential-diagram-dependent-coforkᵉ Pᵉ)

  dependent-universal-property-coequalizer-dependent-universal-property-sequential-colimitᵉ :
    dependent-universal-property-sequential-colimitᵉ cᵉ →
    dependent-universal-property-coequalizerᵉ
      ( double-arrow-sequential-diagramᵉ Aᵉ)
      ( cofork-cocone-sequential-diagramᵉ cᵉ)
  dependent-universal-property-coequalizer-dependent-universal-property-sequential-colimitᵉ
    ( dup-cᵉ)
    ( Pᵉ) =
    is-equiv-top-map-triangleᵉ
      ( dependent-cocone-map-sequential-diagramᵉ cᵉ Pᵉ)
      ( dependent-cocone-sequential-diagram-dependent-coforkᵉ Pᵉ)
      ( dependent-cofork-mapᵉ
        ( double-arrow-sequential-diagramᵉ Aᵉ)
        ( cofork-cocone-sequential-diagramᵉ cᵉ))
      ( triangle-dependent-cocone-sequential-diagram-dependent-coforkᵉ Pᵉ)
      ( is-equiv-dependent-cocone-sequential-diagram-dependent-coforkᵉ Pᵉ)
      ( dup-cᵉ Pᵉ)
```

### The nondependent and dependent universal properties of sequential colimits are logically equivalent

```agda
module _
  { l1ᵉ l2ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ} {Xᵉ : UUᵉ l2ᵉ}
  ( cᵉ : cocone-sequential-diagramᵉ Aᵉ Xᵉ)
  where

  universal-property-dependent-universal-property-sequential-colimitᵉ :
    dependent-universal-property-sequential-colimitᵉ cᵉ →
    universal-property-sequential-colimitᵉ cᵉ
  universal-property-dependent-universal-property-sequential-colimitᵉ
    ( dup-cᵉ)
    ( Yᵉ) =
    is-equiv-left-map-triangleᵉ
      ( cocone-map-sequential-diagramᵉ cᵉ)
      ( map-compute-dependent-cocone-sequential-diagram-constant-familyᵉ Yᵉ)
      ( dependent-cocone-map-sequential-diagramᵉ cᵉ (λ _ → Yᵉ))
      ( triangle-compute-dependent-cocone-sequential-diagram-constant-familyᵉ
        ( Yᵉ))
      ( dup-cᵉ (λ _ → Yᵉ))
      ( is-equiv-map-equivᵉ
        ( compute-dependent-cocone-sequential-diagram-constant-familyᵉ Yᵉ))

  dependent-universal-property-universal-property-sequential-colimitᵉ :
    universal-property-sequential-colimitᵉ cᵉ →
    dependent-universal-property-sequential-colimitᵉ cᵉ
  dependent-universal-property-universal-property-sequential-colimitᵉ
    ( up-sequential-diagramᵉ) =
    dependent-universal-property-sequential-colimit-dependent-universal-property-coequalizerᵉ
      ( cᵉ)
      ( dependent-universal-property-universal-property-coequalizerᵉ
        ( double-arrow-sequential-diagramᵉ Aᵉ)
        ( cofork-cocone-sequential-diagramᵉ cᵉ)
        ( universal-property-coequalizer-universal-property-sequential-colimitᵉ
          ( cᵉ)
          ( up-sequential-diagramᵉ)))
```

### The 3-for-2 property of the dependent universal property of sequential colimits

Givenᵉ twoᵉ coconesᵉ underᵉ aᵉ sequentialᵉ diagram,ᵉ oneᵉ ofᵉ whichᵉ hasᵉ theᵉ dependentᵉ
universalᵉ propertyᵉ ofᵉ sequentialᵉ colimits,ᵉ andᵉ aᵉ mapᵉ betweenᵉ theirᵉ vertices,ᵉ weᵉ
proveᵉ thatᵉ theᵉ otherᵉ hasᵉ theᵉ dependentᵉ universalᵉ propertyᵉ ifᵉ andᵉ onlyᵉ ifᵉ theᵉ mapᵉ
isᵉ anᵉ [equivalence](foundation.equivalences.md).ᵉ

```agda
module _
  { l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ} {Xᵉ : UUᵉ l2ᵉ} {Yᵉ : UUᵉ l3ᵉ}
  ( cᵉ : cocone-sequential-diagramᵉ Aᵉ Xᵉ)
  ( c'ᵉ : cocone-sequential-diagramᵉ Aᵉ Yᵉ)
  ( hᵉ : Xᵉ → Yᵉ)
  ( Hᵉ : htpy-cocone-sequential-diagramᵉ (cocone-map-sequential-diagramᵉ cᵉ hᵉ) c'ᵉ)
  where

  abstract
    is-equiv-dependent-universal-property-sequential-colimit-dependent-universal-property-sequential-colimitᵉ :
      dependent-universal-property-sequential-colimitᵉ cᵉ →
      dependent-universal-property-sequential-colimitᵉ c'ᵉ →
      is-equivᵉ hᵉ
    is-equiv-dependent-universal-property-sequential-colimit-dependent-universal-property-sequential-colimitᵉ
      ( dup-cᵉ)
      ( dup-c'ᵉ) =
        is-equiv-universal-property-sequential-colimit-universal-property-sequential-colimitᵉ
          ( cᵉ)
          ( c'ᵉ)
          ( hᵉ)
          ( Hᵉ)
          ( universal-property-dependent-universal-property-sequential-colimitᵉ cᵉ
            ( dup-cᵉ))
          ( universal-property-dependent-universal-property-sequential-colimitᵉ
            ( c'ᵉ)
            ( dup-c'ᵉ))

    dependent-universal-property-sequential-colimit-is-equiv-dependent-universal-property-sequential-colimitᵉ :
      dependent-universal-property-sequential-colimitᵉ cᵉ →
      is-equivᵉ hᵉ →
      dependent-universal-property-sequential-colimitᵉ c'ᵉ
    dependent-universal-property-sequential-colimit-is-equiv-dependent-universal-property-sequential-colimitᵉ
      ( dup-cᵉ) (is-equiv-hᵉ) =
      dependent-universal-property-universal-property-sequential-colimitᵉ c'ᵉ
        ( universal-property-sequential-colimit-is-equiv-universal-property-sequential-colimitᵉ
          ( cᵉ)
          ( c'ᵉ)
          ( hᵉ)
          ( Hᵉ)
          ( universal-property-dependent-universal-property-sequential-colimitᵉ cᵉ
            ( dup-cᵉ))
          ( is-equiv-hᵉ))

    dependent-universal-property-sequential-colimit-dependent-universal-property-sequential-colimit-is-equivᵉ :
      is-equivᵉ hᵉ →
      dependent-universal-property-sequential-colimitᵉ c'ᵉ →
      dependent-universal-property-sequential-colimitᵉ cᵉ
    dependent-universal-property-sequential-colimit-dependent-universal-property-sequential-colimit-is-equivᵉ
      ( is-equiv-hᵉ)
      ( dup-c'ᵉ) =
      dependent-universal-property-universal-property-sequential-colimitᵉ cᵉ
        ( universal-property-sequential-colimit-universal-property-sequential-colimit-is-equivᵉ
          ( cᵉ)
          ( c'ᵉ)
          ( hᵉ)
          ( Hᵉ)
          ( is-equiv-hᵉ)
          ( universal-property-dependent-universal-property-sequential-colimitᵉ
            ( c'ᵉ)
            ( dup-c'ᵉ)))
```