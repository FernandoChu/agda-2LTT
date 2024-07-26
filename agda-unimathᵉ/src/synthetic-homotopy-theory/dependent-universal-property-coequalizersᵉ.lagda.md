# The dependent universal property of coequalizers

```agda
module synthetic-homotopy-theory.dependent-universal-property-coequalizersᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-mapsᵉ
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.double-arrowsᵉ
open import foundation.equivalencesᵉ
open import foundation.fibers-of-mapsᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import synthetic-homotopy-theory.coforksᵉ
open import synthetic-homotopy-theory.dependent-cocones-under-spansᵉ
open import synthetic-homotopy-theory.dependent-coforksᵉ
open import synthetic-homotopy-theory.dependent-universal-property-pushoutsᵉ
open import synthetic-homotopy-theory.universal-property-coequalizersᵉ
```

</details>

## Idea

Theᵉ **dependentᵉ universalᵉ propertyᵉ ofᵉ coequalizers**ᵉ isᵉ aᵉ propertyᵉ ofᵉ
[coequalizers](synthetic-homotopy-theory.coequalizers.mdᵉ) ofᵉ aᵉ
[doubleᵉ arrow](foundation.double-arrows.mdᵉ) `f,ᵉ gᵉ : Aᵉ → B`,ᵉ assertingᵉ thatᵉ forᵉ
anyᵉ typeᵉ familyᵉ `Pᵉ : Xᵉ → 𝒰`ᵉ overᵉ theᵉ coequalizerᵉ `eᵉ : Bᵉ → X`,ᵉ thereᵉ isᵉ anᵉ
equivalenceᵉ betweenᵉ sectionsᵉ ofᵉ `P`ᵉ andᵉ dependentᵉ coconesᵉ onᵉ `P`ᵉ overᵉ `e`,ᵉ givenᵉ
byᵉ theᵉ mapᵉ

```text
dependent-cofork-mapᵉ : ((xᵉ : Xᵉ) → Pᵉ xᵉ) → dependent-coconeᵉ eᵉ P.ᵉ
```

## Definitions

### The dependent universal property of coequalizers

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (aᵉ : double-arrowᵉ l1ᵉ l2ᵉ) {Xᵉ : UUᵉ l3ᵉ}
  (eᵉ : coforkᵉ aᵉ Xᵉ)
  where

  dependent-universal-property-coequalizerᵉ : UUωᵉ
  dependent-universal-property-coequalizerᵉ =
    {lᵉ : Level} (Pᵉ : Xᵉ → UUᵉ lᵉ) → is-equivᵉ (dependent-cofork-mapᵉ aᵉ eᵉ {Pᵉ = Pᵉ})

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (aᵉ : double-arrowᵉ l1ᵉ l2ᵉ) {Xᵉ : UUᵉ l3ᵉ}
  (eᵉ : coforkᵉ aᵉ Xᵉ) {Pᵉ : Xᵉ → UUᵉ l4ᵉ}
  (dup-coequalizerᵉ : dependent-universal-property-coequalizerᵉ aᵉ eᵉ)
  where

  map-dependent-universal-property-coequalizerᵉ :
    dependent-coforkᵉ aᵉ eᵉ Pᵉ →
    (xᵉ : Xᵉ) → Pᵉ xᵉ
  map-dependent-universal-property-coequalizerᵉ =
    map-inv-is-equivᵉ (dup-coequalizerᵉ Pᵉ)
```

## Properties

### The mediating dependent map obtained by the dependent universal property is unique

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (aᵉ : double-arrowᵉ l1ᵉ l2ᵉ) {Xᵉ : UUᵉ l3ᵉ}
  (eᵉ : coforkᵉ aᵉ Xᵉ) {Pᵉ : Xᵉ → UUᵉ l4ᵉ}
  (dup-coequalizerᵉ : dependent-universal-property-coequalizerᵉ aᵉ eᵉ)
  (kᵉ : dependent-coforkᵉ aᵉ eᵉ Pᵉ)
  where

  htpy-dependent-cofork-dependent-universal-property-coequalizerᵉ :
    htpy-dependent-coforkᵉ aᵉ Pᵉ
      ( dependent-cofork-mapᵉ aᵉ eᵉ
        ( map-dependent-universal-property-coequalizerᵉ aᵉ eᵉ
          ( dup-coequalizerᵉ)
          ( kᵉ)))
      ( kᵉ)
  htpy-dependent-cofork-dependent-universal-property-coequalizerᵉ =
    htpy-dependent-cofork-eqᵉ aᵉ Pᵉ
      ( dependent-cofork-mapᵉ aᵉ eᵉ
        ( map-dependent-universal-property-coequalizerᵉ aᵉ eᵉ
          ( dup-coequalizerᵉ)
          ( kᵉ)))
      ( kᵉ)
      ( is-section-map-inv-is-equivᵉ (dup-coequalizerᵉ Pᵉ) kᵉ)

  abstract
    uniqueness-dependent-universal-property-coequalizerᵉ :
      is-contrᵉ
        ( Σᵉ ((xᵉ : Xᵉ) → Pᵉ xᵉ)
          ( λ hᵉ → htpy-dependent-coforkᵉ aᵉ Pᵉ (dependent-cofork-mapᵉ aᵉ eᵉ hᵉ) kᵉ))
    uniqueness-dependent-universal-property-coequalizerᵉ =
      is-contr-is-equiv'ᵉ
        ( fiberᵉ (dependent-cofork-mapᵉ aᵉ eᵉ) kᵉ)
        ( totᵉ
          ( λ hᵉ →
            htpy-dependent-cofork-eqᵉ aᵉ Pᵉ (dependent-cofork-mapᵉ aᵉ eᵉ hᵉ) kᵉ))
        ( is-equiv-tot-is-fiberwise-equivᵉ
          ( λ hᵉ →
            is-equiv-htpy-dependent-cofork-eqᵉ aᵉ Pᵉ
              ( dependent-cofork-mapᵉ aᵉ eᵉ hᵉ)
              ( kᵉ)))
        ( is-contr-map-is-equivᵉ (dup-coequalizerᵉ Pᵉ) kᵉ)
```

### A cofork has the dependent universal property of coequalizers if and only if the corresponding cocone has the dependent universal property of pushouts

Asᵉ mentionedᵉ in [`coforks`](synthetic-homotopy-theory.coforks.md),ᵉ coforksᵉ canᵉ
beᵉ thoughtᵉ ofᵉ asᵉ specialᵉ casesᵉ ofᵉ coconesᵉ underᵉ spans.ᵉ Thisᵉ theoremᵉ makesᵉ itᵉ
moreᵉ precise,ᵉ assertingᵉ thatᵉ underᵉ thisᵉ mapping,ᵉ
[coequalizers](synthetic-homotopy-theory.coequalizers.mdᵉ) correspondᵉ to
[pushouts](synthetic-homotopy-theory.pushouts.md).ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (aᵉ : double-arrowᵉ l1ᵉ l2ᵉ) {Xᵉ : UUᵉ l3ᵉ}
  (eᵉ : coforkᵉ aᵉ Xᵉ)
  where

  dependent-universal-property-coequalizer-dependent-universal-property-pushoutᵉ :
    dependent-universal-property-pushoutᵉ
      ( vertical-map-span-cocone-coforkᵉ aᵉ)
      ( horizontal-map-span-cocone-coforkᵉ aᵉ)
      ( cocone-codiagonal-coforkᵉ aᵉ eᵉ) →
    dependent-universal-property-coequalizerᵉ aᵉ eᵉ
  dependent-universal-property-coequalizer-dependent-universal-property-pushoutᵉ
    ( dup-pushoutᵉ)
    ( Pᵉ) =
    is-equiv-left-map-triangleᵉ
      ( dependent-cofork-mapᵉ aᵉ eᵉ)
      ( dependent-cofork-dependent-cocone-codiagonalᵉ aᵉ eᵉ Pᵉ)
      ( dependent-cocone-mapᵉ
        ( vertical-map-span-cocone-coforkᵉ aᵉ)
        ( horizontal-map-span-cocone-coforkᵉ aᵉ)
        ( cocone-codiagonal-coforkᵉ aᵉ eᵉ)
        ( Pᵉ))
      ( triangle-dependent-cofork-dependent-cocone-codiagonalᵉ aᵉ eᵉ Pᵉ)
      ( dup-pushoutᵉ Pᵉ)
      ( is-equiv-dependent-cofork-dependent-cocone-codiagonalᵉ aᵉ eᵉ Pᵉ)

  dependent-universal-property-pushout-dependent-universal-property-coequalizerᵉ :
    dependent-universal-property-coequalizerᵉ aᵉ eᵉ →
    dependent-universal-property-pushoutᵉ
      ( vertical-map-span-cocone-coforkᵉ aᵉ)
      ( horizontal-map-span-cocone-coforkᵉ aᵉ)
      ( cocone-codiagonal-coforkᵉ aᵉ eᵉ)
  dependent-universal-property-pushout-dependent-universal-property-coequalizerᵉ
    ( dup-coequalizerᵉ)
    ( Pᵉ) =
    is-equiv-top-map-triangleᵉ
      ( dependent-cofork-mapᵉ aᵉ eᵉ)
      ( dependent-cofork-dependent-cocone-codiagonalᵉ aᵉ eᵉ Pᵉ)
      ( dependent-cocone-mapᵉ
        ( vertical-map-span-cocone-coforkᵉ aᵉ)
        ( horizontal-map-span-cocone-coforkᵉ aᵉ)
        ( cocone-codiagonal-coforkᵉ aᵉ eᵉ)
        ( Pᵉ))
      ( triangle-dependent-cofork-dependent-cocone-codiagonalᵉ aᵉ eᵉ Pᵉ)
      ( is-equiv-dependent-cofork-dependent-cocone-codiagonalᵉ aᵉ eᵉ Pᵉ)
      ( dup-coequalizerᵉ Pᵉ)
```

### The universal property of coequalizers is equivalent to the dependent universal property of coequalizers

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (aᵉ : double-arrowᵉ l1ᵉ l2ᵉ) {Xᵉ : UUᵉ l3ᵉ}
  (eᵉ : coforkᵉ aᵉ Xᵉ)
  where

  universal-property-dependent-universal-property-coequalizerᵉ :
    dependent-universal-property-coequalizerᵉ aᵉ eᵉ →
    universal-property-coequalizerᵉ aᵉ eᵉ
  universal-property-dependent-universal-property-coequalizerᵉ
    ( dup-coequalizerᵉ)
    ( Yᵉ) =
    is-equiv-left-map-triangleᵉ
      ( cofork-mapᵉ aᵉ eᵉ)
      ( map-compute-dependent-cofork-constant-familyᵉ aᵉ eᵉ Yᵉ)
      ( dependent-cofork-mapᵉ aᵉ eᵉ)
      ( triangle-compute-dependent-cofork-constant-familyᵉ aᵉ eᵉ Yᵉ)
      ( dup-coequalizerᵉ (λ _ → Yᵉ))
      ( is-equiv-map-equivᵉ
        ( compute-dependent-cofork-constant-familyᵉ aᵉ eᵉ Yᵉ))

  dependent-universal-property-universal-property-coequalizerᵉ :
    universal-property-coequalizerᵉ aᵉ eᵉ →
    dependent-universal-property-coequalizerᵉ aᵉ eᵉ
  dependent-universal-property-universal-property-coequalizerᵉ up-coequalizerᵉ =
    dependent-universal-property-coequalizer-dependent-universal-property-pushoutᵉ
      ( aᵉ)
      ( eᵉ)
      ( dependent-universal-property-universal-property-pushoutᵉ
          ( vertical-map-span-cocone-coforkᵉ aᵉ)
          ( horizontal-map-span-cocone-coforkᵉ aᵉ)
          ( cocone-codiagonal-coforkᵉ aᵉ eᵉ)
          ( universal-property-pushout-universal-property-coequalizerᵉ aᵉ eᵉ
            ( up-coequalizerᵉ)))
```