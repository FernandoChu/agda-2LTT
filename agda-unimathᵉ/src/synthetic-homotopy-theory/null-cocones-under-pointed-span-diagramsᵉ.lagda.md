# Null cocones under pointed span diagrams

```agda
module synthetic-homotopy-theory.null-cocones-under-pointed-span-diagramsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.commuting-squares-of-mapsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-identifications-concatenationᵉ

open import structured-types.commuting-squares-of-pointed-mapsᵉ
open import structured-types.constant-pointed-mapsᵉ
open import structured-types.pointed-homotopiesᵉ
open import structured-types.pointed-mapsᵉ
open import structured-types.pointed-span-diagramsᵉ
open import structured-types.pointed-typesᵉ

open import synthetic-homotopy-theory.cocones-under-pointed-span-diagramsᵉ
```

</details>

## Idea

Theᵉ {{#conceptᵉ "nullᵉ cocone"ᵉ Disambiguation="pointedᵉ spanᵉ diagram"ᵉ}} underᵉ aᵉ
[pointedᵉ spanᵉ diagram](structured-types.pointed-span-diagrams.mdᵉ) `𝒮`ᵉ givenᵉ byᵉ

```text
      fᵉ       gᵉ
  Aᵉ <----ᵉ Sᵉ ---->ᵉ Bᵉ
```

with codomainᵉ `X`ᵉ isᵉ theᵉ
[cocone](synthetic-homotopy-theory.cocones-under-pointed-span-diagrams.mdᵉ) underᵉ
`𝒮`ᵉ consistingᵉ ofᵉ theᵉ
[constantᵉ pointedᵉ maps](structured-types.constant-pointed-maps.mdᵉ) `Aᵉ →∗ᵉ X`ᵉ andᵉ
`Bᵉ →∗ᵉ X`ᵉ andᵉ theᵉ canonicalᵉ homotopyᵉ witnessingᵉ thatᵉ theᵉ squareᵉ ofᵉ pointedᵉ mapsᵉ

```text
        gᵉ
    Sᵉ ----->ᵉ Bᵉ
    |        |
  fᵉ |        | constᵉ
    ∨ᵉ        ∨ᵉ
    Aᵉ ----->ᵉ Xᵉ
      constᵉ
```

[commutes](structured-types.commuting-squares-of-pointed-maps.md).ᵉ Theᵉ nullᵉ
coconeᵉ underᵉ `𝒮`ᵉ providesᵉ aᵉ canonicalᵉ pointingᵉ ofᵉ theᵉ typeᵉ
`cocone-Pointed-Typeᵉ fᵉ g`.ᵉ

## Definitions

### Null cocones under pointed span diagrams

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (𝒮ᵉ : pointed-span-diagramᵉ l1ᵉ l2ᵉ l3ᵉ)
  (Xᵉ : Pointed-Typeᵉ l4ᵉ)
  where

  left-pointed-map-null-cocone-Pointed-Typeᵉ :
    pointed-domain-pointed-span-diagramᵉ 𝒮ᵉ →∗ᵉ Xᵉ
  left-pointed-map-null-cocone-Pointed-Typeᵉ = constant-pointed-mapᵉ _ Xᵉ

  left-map-null-cocone-Pointed-Typeᵉ :
    domain-pointed-span-diagramᵉ 𝒮ᵉ → type-Pointed-Typeᵉ Xᵉ
  left-map-null-cocone-Pointed-Typeᵉ =
    map-pointed-mapᵉ left-pointed-map-null-cocone-Pointed-Typeᵉ

  preserves-point-left-map-null-cocone-Pointed-Typeᵉ :
    left-map-null-cocone-Pointed-Typeᵉ (point-domain-pointed-span-diagramᵉ 𝒮ᵉ) ＝ᵉ
    point-Pointed-Typeᵉ Xᵉ
  preserves-point-left-map-null-cocone-Pointed-Typeᵉ =
    preserves-point-pointed-mapᵉ left-pointed-map-null-cocone-Pointed-Typeᵉ

  right-pointed-map-null-cocone-Pointed-Typeᵉ :
    pointed-codomain-pointed-span-diagramᵉ 𝒮ᵉ →∗ᵉ Xᵉ
  right-pointed-map-null-cocone-Pointed-Typeᵉ = constant-pointed-mapᵉ _ Xᵉ

  right-map-null-cocone-Pointed-Typeᵉ :
    codomain-pointed-span-diagramᵉ 𝒮ᵉ → type-Pointed-Typeᵉ Xᵉ
  right-map-null-cocone-Pointed-Typeᵉ =
    map-pointed-mapᵉ right-pointed-map-null-cocone-Pointed-Typeᵉ

  preserves-point-right-map-null-cocone-Pointed-Typeᵉ :
    right-map-null-cocone-Pointed-Typeᵉ
      ( point-codomain-pointed-span-diagramᵉ 𝒮ᵉ) ＝ᵉ
    point-Pointed-Typeᵉ Xᵉ
  preserves-point-right-map-null-cocone-Pointed-Typeᵉ =
    preserves-point-pointed-mapᵉ right-pointed-map-null-cocone-Pointed-Typeᵉ

  htpy-coherence-square-null-cocone-Pointed-Typeᵉ :
    coherence-square-mapsᵉ
      ( map-pointed-mapᵉ (right-pointed-map-pointed-span-diagramᵉ 𝒮ᵉ))
      ( map-pointed-mapᵉ (left-pointed-map-pointed-span-diagramᵉ 𝒮ᵉ))
      ( map-constant-pointed-mapᵉ (pointed-codomain-pointed-span-diagramᵉ 𝒮ᵉ) Xᵉ)
      ( map-constant-pointed-mapᵉ (pointed-domain-pointed-span-diagramᵉ 𝒮ᵉ) Xᵉ)
  htpy-coherence-square-null-cocone-Pointed-Typeᵉ = refl-htpyᵉ

  coherence-point-coherence-square-null-cocone-Pointed-Typeᵉ :
    coherence-point-unpointed-htpy-pointed-Πᵉ
      ( constant-pointed-mapᵉ _ Xᵉ ∘∗ᵉ (left-pointed-map-pointed-span-diagramᵉ 𝒮ᵉ))
      ( constant-pointed-mapᵉ _ Xᵉ ∘∗ᵉ (right-pointed-map-pointed-span-diagramᵉ 𝒮ᵉ))
      ( htpy-coherence-square-null-cocone-Pointed-Typeᵉ)
  coherence-point-coherence-square-null-cocone-Pointed-Typeᵉ =
    right-whisker-concatᵉ
      ( ( ap-constᵉ
          ( point-Pointed-Typeᵉ Xᵉ)
          ( preserves-point-left-map-pointed-span-diagramᵉ 𝒮ᵉ)) ∙ᵉ
        ( invᵉ
          ( ap-constᵉ
            ( point-Pointed-Typeᵉ Xᵉ)
            ( preserves-point-right-map-pointed-span-diagramᵉ 𝒮ᵉ))))
      ( reflᵉ)

  coherence-square-null-cocone-Pointed-Typeᵉ :
    coherence-square-pointed-mapsᵉ
      ( right-pointed-map-pointed-span-diagramᵉ 𝒮ᵉ)
      ( left-pointed-map-pointed-span-diagramᵉ 𝒮ᵉ)
      ( right-pointed-map-null-cocone-Pointed-Typeᵉ)
      ( left-pointed-map-null-cocone-Pointed-Typeᵉ)
  pr1ᵉ coherence-square-null-cocone-Pointed-Typeᵉ =
    htpy-coherence-square-null-cocone-Pointed-Typeᵉ
  pr2ᵉ coherence-square-null-cocone-Pointed-Typeᵉ =
    coherence-point-coherence-square-null-cocone-Pointed-Typeᵉ

  null-cocone-Pointed-Typeᵉ :
    cocone-Pointed-Typeᵉ
      ( left-pointed-map-pointed-span-diagramᵉ 𝒮ᵉ)
      ( right-pointed-map-pointed-span-diagramᵉ 𝒮ᵉ)
      ( Xᵉ)
  pr1ᵉ null-cocone-Pointed-Typeᵉ =
    left-pointed-map-null-cocone-Pointed-Typeᵉ
  pr1ᵉ (pr2ᵉ null-cocone-Pointed-Typeᵉ) =
    right-pointed-map-null-cocone-Pointed-Typeᵉ
  pr2ᵉ (pr2ᵉ null-cocone-Pointed-Typeᵉ) =
    coherence-square-null-cocone-Pointed-Typeᵉ
```

### The pointed type of cocones under pointed span diagrams

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (𝒮ᵉ : pointed-span-diagramᵉ l1ᵉ l2ᵉ l3ᵉ)
  (Xᵉ : Pointed-Typeᵉ l4ᵉ)
  where

  type-cocone-pointed-type-Pointed-Typeᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  type-cocone-pointed-type-Pointed-Typeᵉ =
    cocone-Pointed-Typeᵉ
      ( left-pointed-map-pointed-span-diagramᵉ 𝒮ᵉ)
      ( right-pointed-map-pointed-span-diagramᵉ 𝒮ᵉ)
      ( Xᵉ)

  cocone-pointed-type-Pointed-Typeᵉ : Pointed-Typeᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  pr1ᵉ cocone-pointed-type-Pointed-Typeᵉ = type-cocone-pointed-type-Pointed-Typeᵉ
  pr2ᵉ cocone-pointed-type-Pointed-Typeᵉ = null-cocone-Pointed-Typeᵉ 𝒮ᵉ Xᵉ
```