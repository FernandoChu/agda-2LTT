# Decidable maps

```agda
module foundation.decidable-mapsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.decidable-equalityᵉ
open import foundation.decidable-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.equivalencesᵉ
open import foundation-core.fibers-of-mapsᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.functoriality-dependent-pair-typesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.retractionsᵉ
```

</details>

## Definition

Aᵉ mapᵉ isᵉ saidᵉ to beᵉ decidableᵉ ifᵉ itsᵉ fibersᵉ areᵉ decidableᵉ types.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  is-decidable-mapᵉ : (Aᵉ → Bᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-decidable-mapᵉ fᵉ = (yᵉ : Bᵉ) → is-decidableᵉ (fiberᵉ fᵉ yᵉ)
```

```agda
is-decidable-map-retractionᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} → has-decidable-equalityᵉ Bᵉ →
  (iᵉ : Aᵉ → Bᵉ) → retractionᵉ iᵉ → is-decidable-mapᵉ iᵉ
is-decidable-map-retractionᵉ dᵉ iᵉ (pairᵉ rᵉ Rᵉ) bᵉ =
  is-decidable-iffᵉ
    ( λ (pᵉ : iᵉ (rᵉ bᵉ) ＝ᵉ bᵉ) → pairᵉ (rᵉ bᵉ) pᵉ)
    ( λ tᵉ → apᵉ (iᵉ ∘ᵉ rᵉ) (invᵉ (pr2ᵉ tᵉ)) ∙ᵉ (apᵉ iᵉ (Rᵉ (pr1ᵉ tᵉ)) ∙ᵉ pr2ᵉ tᵉ))
    ( dᵉ (iᵉ (rᵉ bᵉ)) bᵉ)
```

## Properties

### The map on total spaces induced by a family of decidable embeddings is a decidable embeddings

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {Cᵉ : Aᵉ → UUᵉ l3ᵉ}
  where

  is-decidable-map-totᵉ :
    {fᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ → Cᵉ xᵉ} →
    ((xᵉ : Aᵉ) → is-decidable-mapᵉ (fᵉ xᵉ)) → is-decidable-mapᵉ (totᵉ fᵉ)
  is-decidable-map-totᵉ {fᵉ} Hᵉ xᵉ =
    is-decidable-is-equivᵉ
      ( is-equiv-map-equivᵉ
        ( compute-fiber-totᵉ fᵉ xᵉ))
      ( Hᵉ (pr1ᵉ xᵉ) (pr2ᵉ xᵉ))
```