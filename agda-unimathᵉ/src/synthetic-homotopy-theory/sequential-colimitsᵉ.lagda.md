# Sequential colimits

```agda
module synthetic-homotopy-theory.sequential-colimitsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.commuting-triangles-of-mapsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-dependent-function-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.propositionsᵉ
open import foundation.universe-levelsᵉ

open import synthetic-homotopy-theory.cocones-under-sequential-diagramsᵉ
open import synthetic-homotopy-theory.coequalizersᵉ
open import synthetic-homotopy-theory.coforks-cocones-under-sequential-diagramsᵉ
open import synthetic-homotopy-theory.dependent-cocones-under-sequential-diagramsᵉ
open import synthetic-homotopy-theory.dependent-universal-property-sequential-colimitsᵉ
open import synthetic-homotopy-theory.sequential-diagramsᵉ
open import synthetic-homotopy-theory.universal-property-sequential-colimitsᵉ
```

</details>

## Idea

Givenᵉ aᵉ [sequentialᵉ diagram](synthetic-homotopy-theory.sequential-diagrams.mdᵉ)
`(A,ᵉ a)`,ᵉ weᵉ canᵉ constructᵉ itsᵉ **standardᵉ sequentialᵉ colimit**ᵉ `A∞`,ᵉ whichᵉ isᵉ aᵉ
[coconeᵉ underᵉ it](synthetic-homotopy-theory.cocones-under-sequential-diagrams.mdᵉ)
satisfyingᵉ theᵉ
[universalᵉ propertyᵉ ofᵉ sequentialᵉ colimits](synthetic-homotopy-theory.universal-property-sequential-colimits.md).ᵉ

Inᵉ otherᵉ words,ᵉ theᵉ sequentialᵉ colimitᵉ universallyᵉ completesᵉ theᵉ diagramᵉ

```text
     a₀ᵉ      a₁ᵉ      a₂ᵉ
 A₀ᵉ --->ᵉ A₁ᵉ --->ᵉ A₂ᵉ --->ᵉ ⋯ᵉ --->ᵉ A∞ᵉ .ᵉ
```

Weᵉ oftenᵉ abuseᵉ notationᵉ andᵉ writeᵉ `A∞`ᵉ forᵉ justᵉ theᵉ codomainᵉ ofᵉ theᵉ universalᵉ
cocone.ᵉ Youᵉ mayᵉ alsoᵉ seeᵉ theᵉ colimitᵉ writtenᵉ asᵉ `colimₙᵉ Aₙ`.ᵉ

## Definitions

### Homotopies between maps out of sequential colimits

```agda
module _
  { l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ} {Xᵉ : UUᵉ l2ᵉ}
  ( cᵉ : cocone-sequential-diagramᵉ Aᵉ Xᵉ)
  where

  htpy-out-of-sequential-colimitᵉ : {Yᵉ : UUᵉ l3ᵉ} (fᵉ gᵉ : Xᵉ → Yᵉ) → UUᵉ (l1ᵉ ⊔ l3ᵉ)
  htpy-out-of-sequential-colimitᵉ fᵉ gᵉ =
    htpy-cocone-sequential-diagramᵉ
      ( cocone-map-sequential-diagramᵉ cᵉ fᵉ)
      ( cocone-map-sequential-diagramᵉ cᵉ gᵉ)

  equiv-htpy-htpy-out-of-sequential-colimitᵉ :
    universal-property-sequential-colimitᵉ cᵉ →
    {Yᵉ : UUᵉ l3ᵉ} (fᵉ gᵉ : Xᵉ → Yᵉ) →
    htpy-out-of-sequential-colimitᵉ fᵉ gᵉ ≃ᵉ (fᵉ ~ᵉ gᵉ)
  equiv-htpy-htpy-out-of-sequential-colimitᵉ up-cᵉ fᵉ gᵉ =
    ( inv-equivᵉ
      ( equiv-dependent-universal-property-sequential-colimitᵉ
        ( dependent-universal-property-universal-property-sequential-colimitᵉ cᵉ
          ( up-cᵉ)))) ∘eᵉ
    ( equiv-totᵉ
      ( λ Kᵉ →
        equiv-Π-equiv-familyᵉ
          ( λ nᵉ →
            equiv-Π-equiv-familyᵉ
              ( λ aᵉ →
                compute-dependent-identification-eq-value-functionᵉ fᵉ gᵉ
                  ( coherence-cocone-sequential-diagramᵉ cᵉ nᵉ aᵉ)
                  ( Kᵉ nᵉ aᵉ)
                  ( Kᵉ (succ-ℕᵉ nᵉ) (map-sequential-diagramᵉ Aᵉ nᵉ aᵉ))))))
```

### Components of a homotopy between maps out of sequential colimits

```agda
module _
  { l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ} {Xᵉ : UUᵉ l2ᵉ}
  { cᵉ : cocone-sequential-diagramᵉ Aᵉ Xᵉ}
  ( up-cᵉ : universal-property-sequential-colimitᵉ cᵉ) {Yᵉ : UUᵉ l3ᵉ} {fᵉ gᵉ : Xᵉ → Yᵉ}
  ( Hᵉ : htpy-out-of-sequential-colimitᵉ cᵉ fᵉ gᵉ)
  where

  htpy-htpy-out-of-sequential-colimitᵉ : fᵉ ~ᵉ gᵉ
  htpy-htpy-out-of-sequential-colimitᵉ =
    map-equivᵉ (equiv-htpy-htpy-out-of-sequential-colimitᵉ cᵉ up-cᵉ fᵉ gᵉ) Hᵉ
```

## Properties

### All sequential diagrams admit a standard colimit

Theᵉ standardᵉ colimitᵉ mayᵉ beᵉ constructedᵉ fromᵉ
[coequalizers](synthetic-homotopy-theory.coequalizers.md),ᵉ becauseᵉ weᵉ
[haveᵉ shown](synthetic-homotopy-theory.universal-property-sequential-colimits.mdᵉ)
thatᵉ coconesᵉ ofᵉ sequentialᵉ diagramsᵉ correspondᵉ to aᵉ certainᵉ classᵉ ofᵉ
[coforks](synthetic-homotopy-theory.coforks.md),ᵉ andᵉ theᵉ coequalizersᵉ correspondᵉ
to sequentialᵉ colimits.ᵉ Sinceᵉ allᵉ coequalizersᵉ exist,ᵉ weᵉ concludeᵉ thatᵉ allᵉ
sequentialᵉ colimitsᵉ exist.ᵉ

```agda
abstract
  standard-sequential-colimitᵉ : {lᵉ : Level} (Aᵉ : sequential-diagramᵉ lᵉ) → UUᵉ lᵉ
  standard-sequential-colimitᵉ Aᵉ =
    standard-coequalizerᵉ (double-arrow-sequential-diagramᵉ Aᵉ)

  cocone-standard-sequential-colimitᵉ :
    { lᵉ : Level} (Aᵉ : sequential-diagramᵉ lᵉ) →
    cocone-sequential-diagramᵉ Aᵉ (standard-sequential-colimitᵉ Aᵉ)
  cocone-standard-sequential-colimitᵉ Aᵉ =
    cocone-sequential-diagram-coforkᵉ
      ( cofork-standard-coequalizerᵉ (double-arrow-sequential-diagramᵉ Aᵉ))

  dup-standard-sequential-colimitᵉ :
    { lᵉ : Level} {Aᵉ : sequential-diagramᵉ lᵉ} →
    dependent-universal-property-sequential-colimitᵉ
      ( cocone-standard-sequential-colimitᵉ Aᵉ)
  dup-standard-sequential-colimitᵉ {Aᵉ = Aᵉ} =
    dependent-universal-property-sequential-colimit-dependent-universal-property-coequalizerᵉ
      ( cocone-standard-sequential-colimitᵉ Aᵉ)
      ( dup-standard-coequalizerᵉ (double-arrow-sequential-diagramᵉ Aᵉ))

  up-standard-sequential-colimitᵉ :
    { lᵉ : Level} {Aᵉ : sequential-diagramᵉ lᵉ} →
    universal-property-sequential-colimitᵉ
      ( cocone-standard-sequential-colimitᵉ Aᵉ)
  up-standard-sequential-colimitᵉ {Aᵉ = Aᵉ} =
    universal-property-dependent-universal-property-sequential-colimitᵉ
      ( cocone-standard-sequential-colimitᵉ Aᵉ)
      ( dup-standard-sequential-colimitᵉ)

module _
  { lᵉ : Level} {Aᵉ : sequential-diagramᵉ lᵉ}
  where

  map-cocone-standard-sequential-colimitᵉ :
    ( nᵉ : ℕᵉ) → family-sequential-diagramᵉ Aᵉ nᵉ → standard-sequential-colimitᵉ Aᵉ
  map-cocone-standard-sequential-colimitᵉ =
    map-cocone-sequential-diagramᵉ (cocone-standard-sequential-colimitᵉ Aᵉ)

  coherence-cocone-standard-sequential-colimitᵉ :
    ( nᵉ : ℕᵉ) →
    coherence-triangle-mapsᵉ
      ( map-cocone-standard-sequential-colimitᵉ nᵉ)
      ( map-cocone-standard-sequential-colimitᵉ (succ-ℕᵉ nᵉ))
      ( map-sequential-diagramᵉ Aᵉ nᵉ)
  coherence-cocone-standard-sequential-colimitᵉ =
    coherence-cocone-sequential-diagramᵉ
      ( cocone-standard-sequential-colimitᵉ Aᵉ)
```

### Corollaries of the universal property of sequential colimits

```agda
module _
  { l1ᵉ l2ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ}
  where

  equiv-up-standard-sequential-colimitᵉ :
    { Xᵉ : UUᵉ l2ᵉ} →
    (standard-sequential-colimitᵉ Aᵉ → Xᵉ) ≃ᵉ (cocone-sequential-diagramᵉ Aᵉ Xᵉ)
  pr1ᵉ equiv-up-standard-sequential-colimitᵉ =
    cocone-map-sequential-diagramᵉ (cocone-standard-sequential-colimitᵉ Aᵉ)
  pr2ᵉ (equiv-up-standard-sequential-colimitᵉ) =
    up-standard-sequential-colimitᵉ _

  cogap-standard-sequential-colimitᵉ :
    { Xᵉ : UUᵉ l2ᵉ} →
    cocone-sequential-diagramᵉ Aᵉ Xᵉ → standard-sequential-colimitᵉ Aᵉ → Xᵉ
  cogap-standard-sequential-colimitᵉ =
    map-inv-equivᵉ equiv-up-standard-sequential-colimitᵉ

  equiv-dup-standard-sequential-colimitᵉ :
    { Pᵉ : standard-sequential-colimitᵉ Aᵉ → UUᵉ l2ᵉ} →
    ( (xᵉ : standard-sequential-colimitᵉ Aᵉ) → Pᵉ xᵉ) ≃ᵉ
    ( dependent-cocone-sequential-diagramᵉ
      ( cocone-standard-sequential-colimitᵉ Aᵉ)
      ( Pᵉ))
  pr1ᵉ equiv-dup-standard-sequential-colimitᵉ =
    dependent-cocone-map-sequential-diagramᵉ
      ( cocone-standard-sequential-colimitᵉ Aᵉ)
      ( _)
  pr2ᵉ equiv-dup-standard-sequential-colimitᵉ =
    dup-standard-sequential-colimitᵉ _

  dependent-cogap-standard-sequential-colimitᵉ :
    { Pᵉ : standard-sequential-colimitᵉ Aᵉ → UUᵉ l2ᵉ} →
    dependent-cocone-sequential-diagramᵉ
      ( cocone-standard-sequential-colimitᵉ Aᵉ)
      ( Pᵉ) →
    ( xᵉ : standard-sequential-colimitᵉ Aᵉ) → Pᵉ xᵉ
  dependent-cogap-standard-sequential-colimitᵉ =
    map-inv-equivᵉ equiv-dup-standard-sequential-colimitᵉ
```

### The small predicate of being a sequential colimit cocone

Theᵉ [proposition](foundation-core.propositions.mdᵉ) `is-sequential-colimit`ᵉ isᵉ
theᵉ assertionᵉ thatᵉ theᵉ cogapᵉ mapᵉ isᵉ anᵉ
[equivalence](foundation-core.equivalences.md).ᵉ Noteᵉ thatᵉ thisᵉ propositionᵉ isᵉ
[small](foundation-core.small-types.md),ᵉ whereasᵉ
[theᵉ universalᵉ property](synthetic-homotopy-theory.universal-property-sequential-colimits.mdᵉ)
isᵉ aᵉ largeᵉ proposition.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ} {Xᵉ : UUᵉ l2ᵉ}
  (cᵉ : cocone-sequential-diagramᵉ Aᵉ Xᵉ)
  where

  is-sequential-colimitᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-sequential-colimitᵉ = is-equivᵉ (cogap-standard-sequential-colimitᵉ cᵉ)

  is-prop-is-sequential-colimitᵉ : is-propᵉ is-sequential-colimitᵉ
  is-prop-is-sequential-colimitᵉ =
    is-property-is-equivᵉ (cogap-standard-sequential-colimitᵉ cᵉ)

  is-sequential-colimit-Propᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ is-sequential-colimit-Propᵉ = is-sequential-colimitᵉ
  pr2ᵉ is-sequential-colimit-Propᵉ = is-prop-is-sequential-colimitᵉ
```

### Homotopies between maps from the standard sequential colimit

Mapsᵉ fromᵉ theᵉ standardᵉ sequentialᵉ colimitᵉ induceᵉ coconesᵉ underᵉ theᵉ sequentialᵉ
diagrams,ᵉ andᵉ aᵉ [homotopy](foundation-core.homotopies.mdᵉ) betweenᵉ theᵉ mapsᵉ isᵉ
exactlyᵉ aᵉ homotopyᵉ ofᵉ theᵉ cocones.ᵉ

```agda
module _
  { l1ᵉ l2ᵉ : Level} (Aᵉ : sequential-diagramᵉ l1ᵉ) {Xᵉ : UUᵉ l2ᵉ}
  ( fᵉ gᵉ : standard-sequential-colimitᵉ Aᵉ → Xᵉ)
  where

  htpy-out-of-standard-sequential-colimitᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  htpy-out-of-standard-sequential-colimitᵉ =
    htpy-out-of-sequential-colimitᵉ (cocone-standard-sequential-colimitᵉ Aᵉ) fᵉ gᵉ

  equiv-htpy-htpy-out-of-standard-sequential-colimitᵉ :
    htpy-out-of-standard-sequential-colimitᵉ ≃ᵉ (fᵉ ~ᵉ gᵉ)
  equiv-htpy-htpy-out-of-standard-sequential-colimitᵉ =
    equiv-htpy-htpy-out-of-sequential-colimitᵉ
      ( cocone-standard-sequential-colimitᵉ Aᵉ)
      ( up-standard-sequential-colimitᵉ)
      ( fᵉ)
      ( gᵉ)
```

Weᵉ mayᵉ thenᵉ obtainᵉ aᵉ homotopyᵉ ofᵉ mapsᵉ fromᵉ aᵉ homotopyᵉ ofᵉ theirᵉ inducedᵉ cocones.ᵉ

```agda
module _
  { l1ᵉ l2ᵉ : Level} (Aᵉ : sequential-diagramᵉ l1ᵉ) {Xᵉ : UUᵉ l2ᵉ}
  { fᵉ gᵉ : standard-sequential-colimitᵉ Aᵉ → Xᵉ}
  ( Hᵉ : htpy-out-of-standard-sequential-colimitᵉ Aᵉ fᵉ gᵉ)
  where

  htpy-htpy-out-of-standard-sequential-colimitᵉ : fᵉ ~ᵉ gᵉ
  htpy-htpy-out-of-standard-sequential-colimitᵉ =
    htpy-htpy-out-of-sequential-colimitᵉ
      ( up-standard-sequential-colimitᵉ)
      ( Hᵉ)
```

### A type satisfies `is-sequential-colimit` if and only if it has the (dependent) universal property of sequential colimits

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ} {Xᵉ : UUᵉ l2ᵉ}
  (cᵉ : cocone-sequential-diagramᵉ Aᵉ Xᵉ)
  where

  universal-property-is-sequential-colimitᵉ :
    is-sequential-colimitᵉ cᵉ → universal-property-sequential-colimitᵉ cᵉ
  universal-property-is-sequential-colimitᵉ =
    universal-property-sequential-colimit-is-equiv-universal-property-sequential-colimitᵉ
      ( cocone-standard-sequential-colimitᵉ Aᵉ)
      ( cᵉ)
      ( cogap-standard-sequential-colimitᵉ cᵉ)
      ( htpy-cocone-universal-property-sequential-colimitᵉ
        ( up-standard-sequential-colimitᵉ)
        ( cᵉ))
      ( up-standard-sequential-colimitᵉ)

  dependent-universal-property-is-sequential-colimitᵉ :
    is-sequential-colimitᵉ cᵉ →
    dependent-universal-property-sequential-colimitᵉ cᵉ
  dependent-universal-property-is-sequential-colimitᵉ =
    dependent-universal-property-sequential-colimit-is-equiv-dependent-universal-property-sequential-colimitᵉ
      ( cocone-standard-sequential-colimitᵉ Aᵉ)
      ( cᵉ)
      ( cogap-standard-sequential-colimitᵉ cᵉ)
      ( htpy-cocone-universal-property-sequential-colimitᵉ
        ( up-standard-sequential-colimitᵉ)
        ( cᵉ))
      ( dup-standard-sequential-colimitᵉ)

  is-sequential-colimit-universal-propertyᵉ :
    universal-property-sequential-colimitᵉ cᵉ → is-sequential-colimitᵉ cᵉ
  is-sequential-colimit-universal-propertyᵉ =
    is-equiv-universal-property-sequential-colimit-universal-property-sequential-colimitᵉ
      ( cocone-standard-sequential-colimitᵉ Aᵉ)
      ( cᵉ)
      ( cogap-standard-sequential-colimitᵉ cᵉ)
      ( htpy-cocone-universal-property-sequential-colimitᵉ
        ( up-standard-sequential-colimitᵉ)
        ( cᵉ))
      ( up-standard-sequential-colimitᵉ)

  is-sequential-colimit-dependent-universal-propertyᵉ :
    dependent-universal-property-sequential-colimitᵉ cᵉ →
    is-sequential-colimitᵉ cᵉ
  is-sequential-colimit-dependent-universal-propertyᵉ =
    is-equiv-dependent-universal-property-sequential-colimit-dependent-universal-property-sequential-colimitᵉ
      ( cocone-standard-sequential-colimitᵉ Aᵉ)
      ( cᵉ)
      ( cogap-standard-sequential-colimitᵉ cᵉ)
      ( htpy-cocone-universal-property-sequential-colimitᵉ
        ( up-standard-sequential-colimitᵉ)
        ( cᵉ))
      ( dup-standard-sequential-colimitᵉ)
```