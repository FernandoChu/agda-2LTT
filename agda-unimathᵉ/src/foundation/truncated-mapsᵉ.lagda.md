# Truncated maps

```agda
module foundation.truncated-mapsᵉ where

open import foundation-core.truncated-mapsᵉ public
```

<details><summary>Imports</summary>

```agda
open import foundation.cones-over-cospan-diagramsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.functoriality-fibers-of-mapsᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.fibers-of-mapsᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.pullbacksᵉ
open import foundation-core.truncated-typesᵉ
open import foundation-core.truncation-levelsᵉ
```

</details>

## Properties

### Being a truncated map is a property

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  is-prop-is-trunc-mapᵉ : (kᵉ : 𝕋ᵉ) (fᵉ : Aᵉ → Bᵉ) → is-propᵉ (is-trunc-mapᵉ kᵉ fᵉ)
  is-prop-is-trunc-mapᵉ kᵉ fᵉ = is-prop-Πᵉ (λ xᵉ → is-prop-is-truncᵉ kᵉ (fiberᵉ fᵉ xᵉ))

  is-trunc-map-Propᵉ : (kᵉ : 𝕋ᵉ) → (Aᵉ → Bᵉ) → Propᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ (is-trunc-map-Propᵉ kᵉ fᵉ) = is-trunc-mapᵉ kᵉ fᵉ
  pr2ᵉ (is-trunc-map-Propᵉ kᵉ fᵉ) = is-prop-is-trunc-mapᵉ kᵉ fᵉ
```

### Pullbacks of truncated maps are truncated maps

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (kᵉ : 𝕋ᵉ) {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ}
  {Xᵉ : UUᵉ l4ᵉ} (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ) (cᵉ : coneᵉ fᵉ gᵉ Cᵉ)
  where

  abstract
    is-trunc-vertical-map-is-pullbackᵉ :
      is-pullbackᵉ fᵉ gᵉ cᵉ →
      is-trunc-mapᵉ kᵉ gᵉ → is-trunc-mapᵉ kᵉ (vertical-map-coneᵉ fᵉ gᵉ cᵉ)
    is-trunc-vertical-map-is-pullbackᵉ pbᵉ is-trunc-gᵉ aᵉ =
      is-trunc-is-equivᵉ kᵉ
        ( fiberᵉ gᵉ (fᵉ aᵉ))
        ( map-fiber-vertical-map-coneᵉ fᵉ gᵉ cᵉ aᵉ)
        ( is-fiberwise-equiv-map-fiber-vertical-map-cone-is-pullbackᵉ fᵉ gᵉ cᵉ pbᵉ aᵉ)
        ( is-trunc-gᵉ (fᵉ aᵉ))

abstract
  is-trunc-horizontal-map-is-pullbackᵉ :
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (kᵉ : 𝕋ᵉ)
    {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} {Xᵉ : UUᵉ l4ᵉ}
    (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ) (cᵉ : coneᵉ fᵉ gᵉ Cᵉ) →
    is-pullbackᵉ fᵉ gᵉ cᵉ →
    is-trunc-mapᵉ kᵉ fᵉ → is-trunc-mapᵉ kᵉ (horizontal-map-coneᵉ fᵉ gᵉ cᵉ)
  is-trunc-horizontal-map-is-pullbackᵉ kᵉ fᵉ gᵉ (pairᵉ pᵉ (pairᵉ qᵉ Hᵉ)) pbᵉ is-trunc-fᵉ =
    is-trunc-vertical-map-is-pullbackᵉ kᵉ gᵉ fᵉ
      ( swap-coneᵉ fᵉ gᵉ (tripleᵉ pᵉ qᵉ Hᵉ))
      ( is-pullback-swap-coneᵉ fᵉ gᵉ (tripleᵉ pᵉ qᵉ Hᵉ) pbᵉ)
      is-trunc-fᵉ
```