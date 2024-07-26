# Truncation images of maps

```agda
module foundation.truncation-images-of-mapsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.connected-mapsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.fibers-of-mapsᵉ
open import foundation.functoriality-truncationᵉ
open import foundation.identity-typesᵉ
open import foundation.truncationsᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.equality-dependent-pair-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.functoriality-dependent-pair-typesᵉ
open import foundation-core.transport-along-identificationsᵉ
open import foundation-core.truncated-mapsᵉ
open import foundation-core.truncation-levelsᵉ
```

</details>

## Idea

Theᵉ **`k`-truncationᵉ image**ᵉ ofᵉ aᵉ mapᵉ `fᵉ : Aᵉ → B`ᵉ isᵉ theᵉ typeᵉ `trunc-imᵉ kᵉ f`ᵉ
thatᵉ fitsᵉ in theᵉ (`k`-connected,`k`-truncatedᵉ) factorizationᵉ ofᵉ `f`.ᵉ Itᵉ isᵉ
definedᵉ asᵉ theᵉ typeᵉ

```text
  trunc-imᵉ kᵉ fᵉ :=ᵉ Σᵉ (yᵉ : B),ᵉ type-truncᵉ kᵉ (fiberᵉ fᵉ yᵉ)
```

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} (kᵉ : 𝕋ᵉ) {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ)
  where

  trunc-imᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  trunc-imᵉ = Σᵉ Bᵉ (λ yᵉ → type-truncᵉ kᵉ (fiberᵉ fᵉ yᵉ))

  unit-trunc-imᵉ : Aᵉ → trunc-imᵉ
  pr1ᵉ (unit-trunc-imᵉ xᵉ) = fᵉ xᵉ
  pr2ᵉ (unit-trunc-imᵉ xᵉ) = unit-truncᵉ (pairᵉ xᵉ reflᵉ)

  projection-trunc-imᵉ : trunc-imᵉ → Bᵉ
  projection-trunc-imᵉ = pr1ᵉ
```

## Properties

### Characterization of the identity types of `k+1`-truncation images

```agda
module _
  {l1ᵉ l2ᵉ : Level} (kᵉ : 𝕋ᵉ) {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ)
  where

  Eq-unit-trunc-imᵉ : Aᵉ → Aᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  Eq-unit-trunc-imᵉ xᵉ yᵉ = trunc-imᵉ kᵉ (apᵉ fᵉ {xᵉ} {yᵉ})

  extensionality-trunc-imᵉ :
    (xᵉ yᵉ : Aᵉ) →
    ( unit-trunc-imᵉ (succ-𝕋ᵉ kᵉ) fᵉ xᵉ ＝ᵉ unit-trunc-imᵉ (succ-𝕋ᵉ kᵉ) fᵉ yᵉ) ≃ᵉ
    ( Eq-unit-trunc-imᵉ xᵉ yᵉ)
  extensionality-trunc-imᵉ xᵉ yᵉ =
    ( equiv-totᵉ
      ( λ qᵉ →
        ( equiv-truncᵉ kᵉ
          ( ( equiv-totᵉ
              ( λ pᵉ → equiv-concatᵉ (invᵉ right-unitᵉ) qᵉ)) ∘eᵉ
            ( equiv-Eq-eq-fiberᵉ fᵉ (fᵉ yᵉ)))) ∘eᵉ
        ( inv-equivᵉ (effectiveness-truncᵉ kᵉ (xᵉ ,ᵉ qᵉ) (yᵉ ,ᵉ reflᵉ))) ∘eᵉ
        ( equiv-concatᵉ
          ( apᵉ unit-truncᵉ (compute-tr-fiberᵉ fᵉ qᵉ (xᵉ ,ᵉ reflᵉ)))
          ( unit-truncᵉ (yᵉ ,ᵉ reflᵉ))) ∘eᵉ
        ( equiv-concatᵉ
          ( preserves-trᵉ (λ _ → unit-truncᵉ) qᵉ (xᵉ ,ᵉ reflᵉ))
          ( unit-truncᵉ (yᵉ ,ᵉ reflᵉ))))) ∘eᵉ
    ( equiv-pair-eq-Σᵉ
      ( unit-trunc-imᵉ (succ-𝕋ᵉ kᵉ) fᵉ xᵉ)
      ( unit-trunc-imᵉ (succ-𝕋ᵉ kᵉ) fᵉ yᵉ))
```

### The map projection-trunc-im k is k-truncated

```agda
module _
  {l1ᵉ l2ᵉ : Level} (kᵉ : 𝕋ᵉ) {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ)
  where

  is-trunc-map-projection-trunc-imᵉ : is-trunc-mapᵉ kᵉ (projection-trunc-imᵉ kᵉ fᵉ)
  is-trunc-map-projection-trunc-imᵉ =
    is-trunc-map-pr1ᵉ kᵉ (λ _ → is-trunc-type-truncᵉ)
```

### The map unit-trunc-im k is k-connected

```agda
module _
  {l1ᵉ l2ᵉ : Level} (kᵉ : 𝕋ᵉ) {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ)
  where

  is-connected-map-unit-trunc-imᵉ : is-connected-mapᵉ kᵉ (unit-trunc-imᵉ kᵉ fᵉ)
  is-connected-map-unit-trunc-imᵉ =
    is-connected-map-compᵉ kᵉ
      ( is-connected-map-tot-is-fiberwise-connected-mapᵉ kᵉ
        ( λ bᵉ → unit-truncᵉ)
        ( λ bᵉ → is-connected-map-unit-truncᵉ kᵉ))
      ( is-connected-map-is-equivᵉ (is-equiv-map-inv-equiv-total-fiberᵉ fᵉ))
```