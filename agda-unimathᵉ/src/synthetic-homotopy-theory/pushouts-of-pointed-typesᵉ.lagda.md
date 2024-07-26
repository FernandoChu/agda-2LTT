# Pushouts of pointed types

```agda
module synthetic-homotopy-theory.pushouts-of-pointed-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ

open import structured-types.pointed-mapsᵉ
open import structured-types.pointed-typesᵉ

open import synthetic-homotopy-theory.cocones-under-pointed-span-diagramsᵉ
open import synthetic-homotopy-theory.pushoutsᵉ
```

</details>

## Idea

Givenᵉ aᵉ spanᵉ ofᵉ [pointedᵉ maps](structured-types.pointed-maps.md),ᵉ thenᵉ theᵉ
[pushout](synthetic-homotopy-theory.pushouts.mdᵉ) isᵉ in factᵉ aᵉ pushoutᵉ diagramᵉ in
theᵉ (wildᵉ) categoryᵉ ofᵉ [pointedᵉ types](structured-types.pointed-types.md).ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level}
  {Sᵉ : Pointed-Typeᵉ l1ᵉ} {Aᵉ : Pointed-Typeᵉ l2ᵉ} {Bᵉ : Pointed-Typeᵉ l3ᵉ}
  where

  pushout-Pointed-Typeᵉ :
    (fᵉ : Sᵉ →∗ᵉ Aᵉ) (gᵉ : Sᵉ →∗ᵉ Bᵉ) → Pointed-Typeᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  pr1ᵉ (pushout-Pointed-Typeᵉ fᵉ gᵉ) =
    pushoutᵉ (map-pointed-mapᵉ fᵉ) (map-pointed-mapᵉ gᵉ)
  pr2ᵉ (pushout-Pointed-Typeᵉ fᵉ gᵉ) =
    inl-pushoutᵉ
      ( map-pointed-mapᵉ fᵉ)
      ( map-pointed-mapᵉ gᵉ)
      ( point-Pointed-Typeᵉ Aᵉ)
```

## Properties

### The pushout of a pointed map along a pointed map is pointed

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level}
  {Sᵉ : Pointed-Typeᵉ l1ᵉ} {Aᵉ : Pointed-Typeᵉ l2ᵉ} {Bᵉ : Pointed-Typeᵉ l3ᵉ}
  where

  inl-pushout-Pointed-Typeᵉ :
      (fᵉ : Sᵉ →∗ᵉ Aᵉ) (gᵉ : Sᵉ →∗ᵉ Bᵉ) → Aᵉ →∗ᵉ pushout-Pointed-Typeᵉ fᵉ gᵉ
  pr1ᵉ (inl-pushout-Pointed-Typeᵉ fᵉ gᵉ) =
    inl-pushoutᵉ (map-pointed-mapᵉ fᵉ) (map-pointed-mapᵉ gᵉ)
  pr2ᵉ (inl-pushout-Pointed-Typeᵉ fᵉ gᵉ) = reflᵉ

  inr-pushout-Pointed-Typeᵉ :
      (fᵉ : Sᵉ →∗ᵉ Aᵉ) (gᵉ : Sᵉ →∗ᵉ Bᵉ) → Bᵉ →∗ᵉ pushout-Pointed-Typeᵉ fᵉ gᵉ
  pr1ᵉ (inr-pushout-Pointed-Typeᵉ fᵉ gᵉ) =
    inr-pushoutᵉ (map-pointed-mapᵉ fᵉ) (map-pointed-mapᵉ gᵉ)
  pr2ᵉ (inr-pushout-Pointed-Typeᵉ fᵉ gᵉ) =
      ( ( apᵉ
          ( inr-pushoutᵉ (map-pointed-mapᵉ fᵉ) (map-pointed-mapᵉ gᵉ))
          ( invᵉ (preserves-point-pointed-mapᵉ gᵉ))) ∙ᵉ
        ( invᵉ
          ( glue-pushoutᵉ
            ( map-pointed-mapᵉ fᵉ)
            ( map-pointed-mapᵉ gᵉ)
            ( point-Pointed-Typeᵉ Sᵉ)))) ∙ᵉ
      ( apᵉ
        ( inl-pushoutᵉ (map-pointed-mapᵉ fᵉ) (map-pointed-mapᵉ gᵉ))
        ( preserves-point-pointed-mapᵉ fᵉ))
```

### The cogap map for pushouts of pointed types

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level}
  {Sᵉ : Pointed-Typeᵉ l1ᵉ} {Aᵉ : Pointed-Typeᵉ l2ᵉ} {Bᵉ : Pointed-Typeᵉ l3ᵉ}
  where

  map-cogap-Pointed-Typeᵉ :
    {l4ᵉ : Level}
    (fᵉ : Sᵉ →∗ᵉ Aᵉ) (gᵉ : Sᵉ →∗ᵉ Bᵉ) →
    {Xᵉ : Pointed-Typeᵉ l4ᵉ} →
    cocone-Pointed-Typeᵉ fᵉ gᵉ Xᵉ →
    type-Pointed-Typeᵉ (pushout-Pointed-Typeᵉ fᵉ gᵉ) → type-Pointed-Typeᵉ Xᵉ
  map-cogap-Pointed-Typeᵉ fᵉ gᵉ cᵉ =
    cogapᵉ
      ( map-pointed-mapᵉ fᵉ)
      ( map-pointed-mapᵉ gᵉ)
      ( cocone-cocone-Pointed-Typeᵉ fᵉ gᵉ cᵉ)

  cogap-Pointed-Typeᵉ :
    {l4ᵉ : Level}
    (fᵉ : Sᵉ →∗ᵉ Aᵉ) (gᵉ : Sᵉ →∗ᵉ Bᵉ) →
    {Xᵉ : Pointed-Typeᵉ l4ᵉ} →
    cocone-Pointed-Typeᵉ fᵉ gᵉ Xᵉ → pushout-Pointed-Typeᵉ fᵉ gᵉ →∗ᵉ Xᵉ
  pr1ᵉ (cogap-Pointed-Typeᵉ fᵉ gᵉ cᵉ) = map-cogap-Pointed-Typeᵉ fᵉ gᵉ cᵉ
  pr2ᵉ (cogap-Pointed-Typeᵉ fᵉ gᵉ {Xᵉ} cᵉ) =
    ( compute-inl-cogapᵉ
      ( map-pointed-mapᵉ fᵉ)
      ( map-pointed-mapᵉ gᵉ)
      ( cocone-cocone-Pointed-Typeᵉ fᵉ gᵉ cᵉ)
      ( point-Pointed-Typeᵉ Aᵉ)) ∙ᵉ
    ( preserves-point-pointed-mapᵉ
      ( horizontal-pointed-map-cocone-Pointed-Typeᵉ fᵉ gᵉ cᵉ))
```

### Computation with the cogap map for pointed types

```agda
module _
  { l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  {Sᵉ : Pointed-Typeᵉ l1ᵉ} {Aᵉ : Pointed-Typeᵉ l2ᵉ} {Bᵉ : Pointed-Typeᵉ l3ᵉ}
  ( fᵉ : Sᵉ →∗ᵉ Aᵉ) (gᵉ : Sᵉ →∗ᵉ Bᵉ)
  { Xᵉ : Pointed-Typeᵉ l4ᵉ} (cᵉ : cocone-Pointed-Typeᵉ fᵉ gᵉ Xᵉ)
  where

  compute-inl-cogap-Pointed-Typeᵉ :
    ( xᵉ : type-Pointed-Typeᵉ Aᵉ) →
    ( map-cogap-Pointed-Typeᵉ
      ( fᵉ)
      ( gᵉ)
      ( cᵉ)
      ( map-pointed-mapᵉ (inl-pushout-Pointed-Typeᵉ fᵉ gᵉ) xᵉ)) ＝ᵉ
    ( horizontal-map-cocone-Pointed-Typeᵉ fᵉ gᵉ cᵉ xᵉ)
  compute-inl-cogap-Pointed-Typeᵉ =
    compute-inl-cogapᵉ
      ( map-pointed-mapᵉ fᵉ)
      ( map-pointed-mapᵉ gᵉ)
      ( cocone-cocone-Pointed-Typeᵉ fᵉ gᵉ cᵉ)

  compute-inr-cogap-Pointed-Typeᵉ :
    ( yᵉ : type-Pointed-Typeᵉ Bᵉ) →
    ( map-cogap-Pointed-Typeᵉ
      ( fᵉ)
      ( gᵉ)
      ( cᵉ)
      ( map-pointed-mapᵉ (inr-pushout-Pointed-Typeᵉ fᵉ gᵉ) yᵉ)) ＝ᵉ
    ( vertical-map-cocone-Pointed-Typeᵉ fᵉ gᵉ cᵉ yᵉ)
  compute-inr-cogap-Pointed-Typeᵉ =
    compute-inr-cogapᵉ
      ( map-pointed-mapᵉ fᵉ)
      ( map-pointed-mapᵉ gᵉ)
      ( cocone-cocone-Pointed-Typeᵉ fᵉ gᵉ cᵉ)
```