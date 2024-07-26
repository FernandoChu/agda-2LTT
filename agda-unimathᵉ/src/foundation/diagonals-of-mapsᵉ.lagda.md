# Diagonals of maps

```agda
module foundation.diagonals-of-mapsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equality-fibers-of-mapsᵉ
open import foundation.standard-pullbacksᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.contractible-mapsᵉ
open import foundation-core.embeddingsᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.fibers-of-mapsᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.propositional-mapsᵉ
open import foundation-core.retractionsᵉ
open import foundation-core.sectionsᵉ
open import foundation-core.truncated-mapsᵉ
open import foundation-core.truncated-typesᵉ
open import foundation-core.truncation-levelsᵉ
```

</details>

## Definition

```agda
diagonal-mapᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) →
  Aᵉ → standard-pullbackᵉ fᵉ fᵉ
diagonal-mapᵉ fᵉ xᵉ = (xᵉ ,ᵉ xᵉ ,ᵉ reflᵉ)
```

## Properties

### The fiber of the diagonal of a map

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ)
  (tᵉ : standard-pullbackᵉ fᵉ fᵉ)
  where

  fiber-ap-fiber-diagonal-mapᵉ :
    fiberᵉ (diagonal-mapᵉ fᵉ) tᵉ → fiberᵉ (apᵉ fᵉ) (pr2ᵉ (pr2ᵉ tᵉ))
  fiber-ap-fiber-diagonal-mapᵉ (zᵉ ,ᵉ reflᵉ) = (reflᵉ ,ᵉ reflᵉ)

  fiber-diagonal-map-fiber-apᵉ :
    fiberᵉ (apᵉ fᵉ) (pr2ᵉ (pr2ᵉ tᵉ)) → fiberᵉ (diagonal-mapᵉ fᵉ) tᵉ
  fiber-diagonal-map-fiber-apᵉ (reflᵉ ,ᵉ reflᵉ) = (pr1ᵉ tᵉ ,ᵉ reflᵉ)

  abstract
    is-section-fiber-diagonal-map-fiber-apᵉ :
      is-sectionᵉ fiber-ap-fiber-diagonal-mapᵉ fiber-diagonal-map-fiber-apᵉ
    is-section-fiber-diagonal-map-fiber-apᵉ (reflᵉ ,ᵉ reflᵉ) = reflᵉ

  abstract
    is-retraction-fiber-diagonal-map-fiber-apᵉ :
      is-retractionᵉ fiber-ap-fiber-diagonal-mapᵉ fiber-diagonal-map-fiber-apᵉ
    is-retraction-fiber-diagonal-map-fiber-apᵉ (xᵉ ,ᵉ reflᵉ) = reflᵉ

  abstract
    is-equiv-fiber-ap-fiber-diagonal-mapᵉ :
      is-equivᵉ fiber-ap-fiber-diagonal-mapᵉ
    is-equiv-fiber-ap-fiber-diagonal-mapᵉ =
      is-equiv-is-invertibleᵉ
        ( fiber-diagonal-map-fiber-apᵉ)
        ( is-section-fiber-diagonal-map-fiber-apᵉ)
        ( is-retraction-fiber-diagonal-map-fiber-apᵉ)
```

### A map is `k+1`-truncated if and only if its diagonal is `k`-truncated

```agda
abstract
  is-trunc-diagonal-map-is-trunc-mapᵉ :
    {l1ᵉ l2ᵉ : Level} (kᵉ : 𝕋ᵉ) {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) →
    is-trunc-mapᵉ (succ-𝕋ᵉ kᵉ) fᵉ → is-trunc-mapᵉ kᵉ (diagonal-mapᵉ fᵉ)
  is-trunc-diagonal-map-is-trunc-mapᵉ kᵉ fᵉ is-trunc-fᵉ (xᵉ ,ᵉ yᵉ ,ᵉ pᵉ) =
    is-trunc-is-equivᵉ kᵉ (fiberᵉ (apᵉ fᵉ) pᵉ)
      ( fiber-ap-fiber-diagonal-mapᵉ fᵉ (tripleᵉ xᵉ yᵉ pᵉ))
      ( is-equiv-fiber-ap-fiber-diagonal-mapᵉ fᵉ (tripleᵉ xᵉ yᵉ pᵉ))
      ( is-trunc-map-ap-is-trunc-mapᵉ kᵉ fᵉ is-trunc-fᵉ xᵉ yᵉ pᵉ)

abstract
  is-trunc-map-is-trunc-diagonal-mapᵉ :
    {l1ᵉ l2ᵉ : Level} (kᵉ : 𝕋ᵉ) {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) →
    is-trunc-mapᵉ kᵉ (diagonal-mapᵉ fᵉ) → is-trunc-mapᵉ (succ-𝕋ᵉ kᵉ) fᵉ
  is-trunc-map-is-trunc-diagonal-mapᵉ kᵉ fᵉ is-trunc-δᵉ bᵉ (xᵉ ,ᵉ pᵉ) (x'ᵉ ,ᵉ p'ᵉ) =
    is-trunc-is-equivᵉ kᵉ
      ( fiberᵉ (apᵉ fᵉ) (pᵉ ∙ᵉ (invᵉ p'ᵉ)))
      ( fiber-ap-eq-fiberᵉ fᵉ (xᵉ ,ᵉ pᵉ) (x'ᵉ ,ᵉ p'ᵉ))
      ( is-equiv-fiber-ap-eq-fiberᵉ fᵉ (xᵉ ,ᵉ pᵉ) (x'ᵉ ,ᵉ p'ᵉ))
      ( is-trunc-is-equiv'ᵉ kᵉ
        ( fiberᵉ (diagonal-mapᵉ fᵉ) (tripleᵉ xᵉ x'ᵉ (pᵉ ∙ᵉ (invᵉ p'ᵉ))))
        ( fiber-ap-fiber-diagonal-mapᵉ fᵉ (tripleᵉ xᵉ x'ᵉ (pᵉ ∙ᵉ (invᵉ p'ᵉ))))
        ( is-equiv-fiber-ap-fiber-diagonal-mapᵉ fᵉ (tripleᵉ xᵉ x'ᵉ (pᵉ ∙ᵉ (invᵉ p'ᵉ))))
        ( is-trunc-δᵉ (tripleᵉ xᵉ x'ᵉ (pᵉ ∙ᵉ (invᵉ p'ᵉ)))))

abstract
  is-equiv-diagonal-map-is-embᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) →
    is-embᵉ fᵉ → is-equivᵉ (diagonal-mapᵉ fᵉ)
  is-equiv-diagonal-map-is-embᵉ fᵉ is-emb-fᵉ =
    is-equiv-is-contr-mapᵉ
      ( is-trunc-diagonal-map-is-trunc-mapᵉ neg-two-𝕋ᵉ fᵉ
        ( is-prop-map-is-embᵉ is-emb-fᵉ))

abstract
  is-emb-is-equiv-diagonal-mapᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) →
    is-equivᵉ (diagonal-mapᵉ fᵉ) → is-embᵉ fᵉ
  is-emb-is-equiv-diagonal-mapᵉ fᵉ is-equiv-δᵉ =
    is-emb-is-prop-mapᵉ
      ( is-trunc-map-is-trunc-diagonal-mapᵉ neg-two-𝕋ᵉ fᵉ
        ( is-contr-map-is-equivᵉ is-equiv-δᵉ))
```