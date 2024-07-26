# Cocones under pointed span diagrams

```agda
module synthetic-homotopy-theory.cocones-under-pointed-span-diagramsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ

open import structured-types.commuting-squares-of-pointed-mapsᵉ
open import structured-types.pointed-mapsᵉ
open import structured-types.pointed-typesᵉ

open import synthetic-homotopy-theory.cocones-under-spansᵉ
```

</details>

## Idea

Aᵉ [coconeᵉ underᵉ aᵉ span](synthetic-homotopy-theory.cocones-under-spans.mdᵉ) ofᵉ
[pointedᵉ types](structured-types.pointed-types.mdᵉ) isᵉ aᵉ **pointedᵉ cocone**ᵉ ifᵉ itᵉ
consistsᵉ ofᵉ [pointedᵉ maps](structured-types.pointed-maps.mdᵉ) equippedᵉ with aᵉ
[pointedᵉ homotopy](structured-types.pointed-homotopies.mdᵉ) witnessingᵉ thatᵉ theᵉ
naturalityᵉ squareᵉ
[commutes](structured-types.commuting-squares-of-pointed-maps.md).ᵉ

Theᵉ typeᵉ ofᵉ pointedᵉ coconesᵉ underᵉ aᵉ spanᵉ ofᵉ pointedᵉ typesᵉ isᵉ againᵉ canonicallyᵉ
pointedᵉ atᵉ theᵉ constantᵉ cocone,ᵉ with `refl`ᵉ asᵉ coherenceᵉ proof.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level}
  {Sᵉ : Pointed-Typeᵉ l1ᵉ} {Aᵉ : Pointed-Typeᵉ l2ᵉ}
  {Bᵉ : Pointed-Typeᵉ l3ᵉ}
  (fᵉ : Sᵉ →∗ᵉ Aᵉ) (gᵉ : Sᵉ →∗ᵉ Bᵉ)
  where

  cocone-Pointed-Typeᵉ :
    {l4ᵉ : Level} → Pointed-Typeᵉ l4ᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  cocone-Pointed-Typeᵉ Xᵉ =
    Σᵉ ( Aᵉ →∗ᵉ Xᵉ)
      ( λ iᵉ →
        Σᵉ ( Bᵉ →∗ᵉ Xᵉ)
          ( λ jᵉ → coherence-square-pointed-mapsᵉ gᵉ fᵉ jᵉ iᵉ))
```

### Components of a cocone of pointed types

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  {Sᵉ : Pointed-Typeᵉ l1ᵉ} {Aᵉ : Pointed-Typeᵉ l2ᵉ}
  {Bᵉ : Pointed-Typeᵉ l3ᵉ} {Xᵉ : Pointed-Typeᵉ l4ᵉ}
  (fᵉ : Sᵉ →∗ᵉ Aᵉ) (gᵉ : Sᵉ →∗ᵉ Bᵉ) (cᵉ : cocone-Pointed-Typeᵉ fᵉ gᵉ Xᵉ)
  where

  horizontal-pointed-map-cocone-Pointed-Typeᵉ : Aᵉ →∗ᵉ Xᵉ
  horizontal-pointed-map-cocone-Pointed-Typeᵉ = pr1ᵉ cᵉ

  horizontal-map-cocone-Pointed-Typeᵉ :
    type-Pointed-Typeᵉ Aᵉ → type-Pointed-Typeᵉ Xᵉ
  horizontal-map-cocone-Pointed-Typeᵉ =
    pr1ᵉ horizontal-pointed-map-cocone-Pointed-Typeᵉ

  vertical-pointed-map-cocone-Pointed-Typeᵉ : Bᵉ →∗ᵉ Xᵉ
  vertical-pointed-map-cocone-Pointed-Typeᵉ = pr1ᵉ (pr2ᵉ cᵉ)

  vertical-map-cocone-Pointed-Typeᵉ :
    type-Pointed-Typeᵉ Bᵉ → type-Pointed-Typeᵉ Xᵉ
  vertical-map-cocone-Pointed-Typeᵉ =
    pr1ᵉ vertical-pointed-map-cocone-Pointed-Typeᵉ

  coherence-square-cocone-Pointed-Typeᵉ :
    coherence-square-pointed-mapsᵉ
      ( gᵉ)
      ( fᵉ)
      ( vertical-pointed-map-cocone-Pointed-Typeᵉ)
      ( horizontal-pointed-map-cocone-Pointed-Typeᵉ)
  coherence-square-cocone-Pointed-Typeᵉ = pr2ᵉ (pr2ᵉ cᵉ)

  cocone-cocone-Pointed-Typeᵉ : coconeᵉ (pr1ᵉ fᵉ) (pr1ᵉ gᵉ) (pr1ᵉ Xᵉ)
  pr1ᵉ cocone-cocone-Pointed-Typeᵉ = horizontal-map-cocone-Pointed-Typeᵉ
  pr1ᵉ (pr2ᵉ cocone-cocone-Pointed-Typeᵉ) = vertical-map-cocone-Pointed-Typeᵉ
  pr2ᵉ (pr2ᵉ cocone-cocone-Pointed-Typeᵉ) =
    pr1ᵉ coherence-square-cocone-Pointed-Typeᵉ
```

## See also

-ᵉ [Pushoutsᵉ ofᵉ pointedᵉ types](synthetic-homotopy-theory.pushouts-of-pointed-types.mdᵉ)
-ᵉ [Nullᵉ coconesᵉ underᵉ pointedᵉ spanᵉ diagrams](synthetic-homotopy-theory.null-cocones-under-pointed-span-diagrams.mdᵉ)