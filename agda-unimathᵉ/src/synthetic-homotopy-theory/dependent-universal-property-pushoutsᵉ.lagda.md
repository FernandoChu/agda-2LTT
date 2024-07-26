# The dependent universal property of pushouts

```agda
module synthetic-homotopy-theory.dependent-universal-property-pushoutsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functionsᵉ
open import foundation.contractible-mapsᵉ
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equality-dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.fibers-of-mapsᵉ
open import foundation.function-extensionalityᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.retractionsᵉ
open import foundation.standard-pullbacksᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.universe-levelsᵉ

open import synthetic-homotopy-theory.cocones-under-spansᵉ
open import synthetic-homotopy-theory.dependent-cocones-under-spansᵉ
open import synthetic-homotopy-theory.dependent-pullback-property-pushoutsᵉ
open import synthetic-homotopy-theory.induction-principle-pushoutsᵉ
open import synthetic-homotopy-theory.universal-property-pushoutsᵉ
```

</details>

## Idea

Theᵉ **dependentᵉ universalᵉ propertyᵉ ofᵉ pushouts**ᵉ assertsᵉ thatᵉ everyᵉ sectionᵉ ofᵉ aᵉ
typeᵉ familyᵉ overᵉ aᵉ [pushout](synthetic-homotopy-theory.pushouts.mdᵉ) correspondsᵉ
in aᵉ canonicalᵉ wayᵉ uniquelyᵉ to aᵉ
[dependentᵉ cocone](synthetic-homotopy-theory.dependent-cocones-under-spans.mdᵉ)
overᵉ theᵉ [coconeᵉ structure](synthetic-homotopy-theory.cocones-under-spans.mdᵉ) onᵉ
theᵉ pushout.ᵉ

## Definition

### The dependent universal property of pushouts

```agda
dependent-universal-property-pushoutᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Sᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ}
  (fᵉ : Sᵉ → Aᵉ) (gᵉ : Sᵉ → Bᵉ) {Xᵉ : UUᵉ l4ᵉ} (cᵉ : coconeᵉ fᵉ gᵉ Xᵉ) →
  UUωᵉ
dependent-universal-property-pushoutᵉ fᵉ gᵉ {Xᵉ} cᵉ =
  {lᵉ : Level} (Pᵉ : Xᵉ → UUᵉ lᵉ) → is-equivᵉ (dependent-cocone-mapᵉ fᵉ gᵉ cᵉ Pᵉ)
```

## Properties

### Sections defined by the dependent universal property are unique up to homotopy

```agda
abstract
  uniqueness-dependent-universal-property-pushoutᵉ :
    { l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Sᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ} {Xᵉ : UUᵉ l4ᵉ} →
    ( fᵉ : Sᵉ → Aᵉ) (gᵉ : Sᵉ → Bᵉ) (cᵉ : coconeᵉ fᵉ gᵉ Xᵉ)
    ( dup-cᵉ : dependent-universal-property-pushoutᵉ fᵉ gᵉ cᵉ) →
    {lᵉ : Level} (Pᵉ : Xᵉ → UUᵉ lᵉ) ( hᵉ : dependent-coconeᵉ fᵉ gᵉ cᵉ Pᵉ) →
    is-contrᵉ
      ( Σᵉ ( (xᵉ : Xᵉ) → Pᵉ xᵉ)
          ( λ kᵉ →
            htpy-dependent-coconeᵉ fᵉ gᵉ cᵉ Pᵉ (dependent-cocone-mapᵉ fᵉ gᵉ cᵉ Pᵉ kᵉ) hᵉ))
  uniqueness-dependent-universal-property-pushoutᵉ fᵉ gᵉ cᵉ dup-cᵉ Pᵉ hᵉ =
    is-contr-is-equiv'ᵉ
      ( fiberᵉ (dependent-cocone-mapᵉ fᵉ gᵉ cᵉ Pᵉ) hᵉ)
      ( totᵉ
        ( λ kᵉ →
          htpy-eq-dependent-coconeᵉ fᵉ gᵉ cᵉ Pᵉ (dependent-cocone-mapᵉ fᵉ gᵉ cᵉ Pᵉ kᵉ) hᵉ))
      ( is-equiv-tot-is-fiberwise-equivᵉ
        ( λ kᵉ →
          is-equiv-htpy-eq-dependent-coconeᵉ fᵉ gᵉ cᵉ Pᵉ
            ( dependent-cocone-mapᵉ fᵉ gᵉ cᵉ Pᵉ kᵉ)
            ( hᵉ)))
      ( is-contr-map-is-equivᵉ (dup-cᵉ Pᵉ) hᵉ)
```

### The induction principle of pushouts is equivalent to the dependent universal property of pushouts

#### The induction principle of pushouts implies the dependent universal property of pushouts

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Sᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ}
  (fᵉ : Sᵉ → Aᵉ) (gᵉ : Sᵉ → Bᵉ) {Xᵉ : UUᵉ l4ᵉ} (cᵉ : coconeᵉ fᵉ gᵉ Xᵉ)
  where

  htpy-eq-dependent-cocone-mapᵉ :
    induction-principle-pushoutᵉ fᵉ gᵉ cᵉ →
    { lᵉ : Level} {Pᵉ : Xᵉ → UUᵉ lᵉ} (hᵉ h'ᵉ : (xᵉ : Xᵉ) → Pᵉ xᵉ) →
    dependent-cocone-mapᵉ fᵉ gᵉ cᵉ Pᵉ hᵉ ＝ᵉ dependent-cocone-mapᵉ fᵉ gᵉ cᵉ Pᵉ h'ᵉ → hᵉ ~ᵉ h'ᵉ
  htpy-eq-dependent-cocone-mapᵉ ind-cᵉ {Pᵉ = Pᵉ} hᵉ h'ᵉ pᵉ =
    ind-induction-principle-pushoutᵉ fᵉ gᵉ cᵉ ind-cᵉ
      ( λ xᵉ → hᵉ xᵉ ＝ᵉ h'ᵉ xᵉ)
      ( ( horizontal-htpy-eq-dependent-coconeᵉ fᵉ gᵉ cᵉ Pᵉ
          ( dependent-cocone-mapᵉ fᵉ gᵉ cᵉ Pᵉ hᵉ)
          ( dependent-cocone-mapᵉ fᵉ gᵉ cᵉ Pᵉ h'ᵉ)
          ( pᵉ)) ,ᵉ
        ( vertical-htpy-eq-dependent-coconeᵉ fᵉ gᵉ cᵉ Pᵉ
          ( dependent-cocone-mapᵉ fᵉ gᵉ cᵉ Pᵉ hᵉ)
          ( dependent-cocone-mapᵉ fᵉ gᵉ cᵉ Pᵉ h'ᵉ)
          ( pᵉ)) ,ᵉ
        ( λ sᵉ →
          map-compute-dependent-identification-eq-valueᵉ hᵉ h'ᵉ
            ( coherence-square-coconeᵉ fᵉ gᵉ cᵉ sᵉ)
            ( horizontal-htpy-eq-dependent-coconeᵉ fᵉ gᵉ cᵉ Pᵉ
              ( dependent-cocone-mapᵉ fᵉ gᵉ cᵉ Pᵉ hᵉ)
              ( dependent-cocone-mapᵉ fᵉ gᵉ cᵉ Pᵉ h'ᵉ)
              ( pᵉ)
              ( fᵉ sᵉ))
            ( vertical-htpy-eq-dependent-coconeᵉ fᵉ gᵉ cᵉ Pᵉ
              ( dependent-cocone-mapᵉ fᵉ gᵉ cᵉ Pᵉ hᵉ)
              ( dependent-cocone-mapᵉ fᵉ gᵉ cᵉ Pᵉ h'ᵉ)
              ( pᵉ)
              ( gᵉ sᵉ))
            ( coherence-square-htpy-eq-dependent-coconeᵉ fᵉ gᵉ cᵉ Pᵉ
              ( dependent-cocone-mapᵉ fᵉ gᵉ cᵉ Pᵉ hᵉ)
              ( dependent-cocone-mapᵉ fᵉ gᵉ cᵉ Pᵉ h'ᵉ)
              ( pᵉ)
              ( sᵉ))))

  is-retraction-ind-induction-principle-pushoutᵉ :
    (Hᵉ : induction-principle-pushoutᵉ fᵉ gᵉ cᵉ) →
    {lᵉ : Level} (Pᵉ : Xᵉ → UUᵉ lᵉ) →
    is-retractionᵉ
      ( dependent-cocone-mapᵉ fᵉ gᵉ cᵉ Pᵉ)
      ( ind-induction-principle-pushoutᵉ fᵉ gᵉ cᵉ Hᵉ Pᵉ)
  is-retraction-ind-induction-principle-pushoutᵉ ind-cᵉ Pᵉ hᵉ =
    eq-htpyᵉ
      ( htpy-eq-dependent-cocone-mapᵉ
        ( ind-cᵉ)
        ( ind-induction-principle-pushoutᵉ fᵉ gᵉ cᵉ
          ( ind-cᵉ)
          ( Pᵉ)
          ( dependent-cocone-mapᵉ fᵉ gᵉ cᵉ Pᵉ hᵉ))
        ( hᵉ)
        ( eq-compute-ind-induction-principle-pushoutᵉ fᵉ gᵉ cᵉ ind-cᵉ Pᵉ
          ( dependent-cocone-mapᵉ fᵉ gᵉ cᵉ Pᵉ hᵉ)))

  dependent-universal-property-pushout-induction-principle-pushoutᵉ :
    induction-principle-pushoutᵉ fᵉ gᵉ cᵉ →
    dependent-universal-property-pushoutᵉ fᵉ gᵉ cᵉ
  dependent-universal-property-pushout-induction-principle-pushoutᵉ ind-cᵉ Pᵉ =
    is-equiv-is-invertibleᵉ
      ( ind-induction-principle-pushoutᵉ fᵉ gᵉ cᵉ ind-cᵉ Pᵉ)
      ( eq-compute-ind-induction-principle-pushoutᵉ fᵉ gᵉ cᵉ ind-cᵉ Pᵉ)
      ( is-retraction-ind-induction-principle-pushoutᵉ ind-cᵉ Pᵉ)
```

#### The dependent universal property of pushouts implies the induction principle of pushouts

```agda
induction-principle-pushout-dependent-universal-property-pushoutᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Sᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ}
  (fᵉ : Sᵉ → Aᵉ) (gᵉ : Sᵉ → Bᵉ) {Xᵉ : UUᵉ l4ᵉ} (cᵉ : coconeᵉ fᵉ gᵉ Xᵉ) →
  dependent-universal-property-pushoutᵉ fᵉ gᵉ cᵉ →
  induction-principle-pushoutᵉ fᵉ gᵉ cᵉ
induction-principle-pushout-dependent-universal-property-pushoutᵉ
  fᵉ gᵉ cᵉ dup-cᵉ Pᵉ = pr1ᵉ (dup-cᵉ Pᵉ)
```

### The dependent pullback property of pushouts is equivalent to the dependent universal property of pushouts

#### The dependent universal property of pushouts implies the dependent pullback property of pushouts

```agda
triangle-dependent-pullback-property-pushoutᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level} {Sᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ}
  (fᵉ : Sᵉ → Aᵉ) (gᵉ : Sᵉ → Bᵉ) {Xᵉ : UUᵉ l4ᵉ} (cᵉ : coconeᵉ fᵉ gᵉ Xᵉ) (Pᵉ : Xᵉ → UUᵉ l5ᵉ) →
  let iᵉ = pr1ᵉ cᵉ
      jᵉ = pr1ᵉ (pr2ᵉ cᵉ)
      Hᵉ = pr2ᵉ (pr2ᵉ cᵉ)
  in
  ( dependent-cocone-mapᵉ fᵉ gᵉ cᵉ Pᵉ) ~ᵉ
  ( ( totᵉ (λ hᵉ → totᵉ (λ h'ᵉ → htpy-eqᵉ))) ∘ᵉ
    ( gapᵉ
      ( λ (hᵉ : (aᵉ : Aᵉ) → Pᵉ (iᵉ aᵉ)) → λ sᵉ → trᵉ Pᵉ (Hᵉ sᵉ) (hᵉ (fᵉ sᵉ)))
      ( λ (hᵉ : (bᵉ : Bᵉ) → Pᵉ (jᵉ bᵉ)) → λ sᵉ → hᵉ (gᵉ sᵉ))
      ( cone-dependent-pullback-property-pushoutᵉ fᵉ gᵉ cᵉ Pᵉ)))
triangle-dependent-pullback-property-pushoutᵉ fᵉ gᵉ (pairᵉ iᵉ (pairᵉ jᵉ Hᵉ)) Pᵉ hᵉ =
  eq-pair-eq-fiberᵉ (eq-pair-eq-fiberᵉ (invᵉ (is-section-eq-htpyᵉ (apdᵉ hᵉ ∘ᵉ Hᵉ))))

dependent-pullback-property-dependent-universal-property-pushoutᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Sᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ}
  (fᵉ : Sᵉ → Aᵉ) (gᵉ : Sᵉ → Bᵉ) {Xᵉ : UUᵉ l4ᵉ} (cᵉ : coconeᵉ fᵉ gᵉ Xᵉ) →
  dependent-universal-property-pushoutᵉ fᵉ gᵉ cᵉ →
  dependent-pullback-property-pushoutᵉ fᵉ gᵉ cᵉ
dependent-pullback-property-dependent-universal-property-pushoutᵉ
  fᵉ gᵉ (pairᵉ iᵉ (pairᵉ jᵉ Hᵉ)) Iᵉ Pᵉ =
  let cᵉ = (pairᵉ iᵉ (pairᵉ jᵉ Hᵉ)) in
  is-equiv-top-map-triangleᵉ
    ( dependent-cocone-mapᵉ fᵉ gᵉ cᵉ Pᵉ)
    ( totᵉ (λ hᵉ → totᵉ (λ h'ᵉ → htpy-eqᵉ)))
    ( gapᵉ
      ( λ hᵉ xᵉ → trᵉ Pᵉ (Hᵉ xᵉ) (hᵉ (fᵉ xᵉ)))
      ( _∘ᵉ gᵉ)
      ( cone-dependent-pullback-property-pushoutᵉ fᵉ gᵉ cᵉ Pᵉ))
    ( triangle-dependent-pullback-property-pushoutᵉ fᵉ gᵉ cᵉ Pᵉ)
    ( is-equiv-tot-is-fiberwise-equivᵉ
      ( λ hᵉ →
        is-equiv-tot-is-fiberwise-equivᵉ
          ( λ h'ᵉ → funextᵉ (λ xᵉ → trᵉ Pᵉ (Hᵉ xᵉ) (hᵉ (fᵉ xᵉ))) (h'ᵉ ∘ᵉ gᵉ))))
    ( Iᵉ Pᵉ)
```

#### The dependent pullback property of pushouts implies the dependent universal property of pushouts

```agda
dependent-universal-property-dependent-pullback-property-pushoutᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Sᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ}
  (fᵉ : Sᵉ → Aᵉ) (gᵉ : Sᵉ → Bᵉ) {Xᵉ : UUᵉ l4ᵉ} (cᵉ : coconeᵉ fᵉ gᵉ Xᵉ) →
  dependent-pullback-property-pushoutᵉ fᵉ gᵉ cᵉ →
  dependent-universal-property-pushoutᵉ fᵉ gᵉ cᵉ
dependent-universal-property-dependent-pullback-property-pushoutᵉ
  fᵉ gᵉ (pairᵉ iᵉ (pairᵉ jᵉ Hᵉ)) dpullback-cᵉ Pᵉ =
  let cᵉ = (pairᵉ iᵉ (pairᵉ jᵉ Hᵉ)) in
  is-equiv-left-map-triangleᵉ
    ( dependent-cocone-mapᵉ fᵉ gᵉ cᵉ Pᵉ)
    ( totᵉ (λ hᵉ → totᵉ (λ h'ᵉ → htpy-eqᵉ)))
    ( gapᵉ
      ( λ hᵉ xᵉ → trᵉ Pᵉ (Hᵉ xᵉ) (hᵉ (fᵉ xᵉ)))
      ( _∘ᵉ gᵉ)
      ( cone-dependent-pullback-property-pushoutᵉ fᵉ gᵉ cᵉ Pᵉ))
    ( triangle-dependent-pullback-property-pushoutᵉ fᵉ gᵉ cᵉ Pᵉ)
    ( dpullback-cᵉ Pᵉ)
    ( is-equiv-tot-is-fiberwise-equivᵉ
      ( λ hᵉ →
        is-equiv-tot-is-fiberwise-equivᵉ
          ( λ h'ᵉ → funextᵉ (λ xᵉ → trᵉ Pᵉ (Hᵉ xᵉ) (hᵉ (fᵉ xᵉ))) (h'ᵉ ∘ᵉ gᵉ))))
```

### The nondependent and dependent universal property of pushouts are logically equivalent

Thisᵉ followsᵉ fromᵉ theᵉ factᵉ thatᵉ theᵉ
[dependentᵉ pullbackᵉ propertyᵉ ofᵉ pushouts](synthetic-homotopy-theory.dependent-pullback-property-pushouts.mdᵉ)
isᵉ logicallyᵉ equivalentᵉ to theᵉ
[pullbackᵉ propertyᵉ ofᵉ pushouts](synthetic-homotopy-theory.pullback-property-pushouts.md).ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Sᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ} {Xᵉ : UUᵉ l4ᵉ}
  (fᵉ : Sᵉ → Aᵉ) (gᵉ : Sᵉ → Bᵉ) (cᵉ : coconeᵉ fᵉ gᵉ Xᵉ)
  where

  abstract
    universal-property-dependent-universal-property-pushoutᵉ :
      dependent-universal-property-pushoutᵉ fᵉ gᵉ cᵉ →
      universal-property-pushoutᵉ fᵉ gᵉ cᵉ
    universal-property-dependent-universal-property-pushoutᵉ dup-cᵉ {lᵉ} =
      universal-property-pushout-pullback-property-pushoutᵉ fᵉ gᵉ cᵉ
        ( pullback-property-dependent-pullback-property-pushoutᵉ fᵉ gᵉ cᵉ
          ( dependent-pullback-property-dependent-universal-property-pushoutᵉ fᵉ gᵉ
            ( cᵉ)
            ( dup-cᵉ)))

    dependent-universal-property-universal-property-pushoutᵉ :
      universal-property-pushoutᵉ fᵉ gᵉ cᵉ →
      dependent-universal-property-pushoutᵉ fᵉ gᵉ cᵉ
    dependent-universal-property-universal-property-pushoutᵉ up-cᵉ =
      dependent-universal-property-dependent-pullback-property-pushoutᵉ fᵉ gᵉ cᵉ
        ( dependent-pullback-property-pullback-property-pushoutᵉ fᵉ gᵉ cᵉ
          ( pullback-property-pushout-universal-property-pushoutᵉ fᵉ gᵉ cᵉ up-cᵉ))
```