# Diagonal maps into cartesian products of types

```agda
module foundation-core.diagonal-maps-cartesian-products-of-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equality-cartesian-product-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.cartesian-product-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.fibers-of-mapsᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.retractionsᵉ
open import foundation-core.sectionsᵉ
```

</details>

## Idea

Theᵉ
{{#conceptᵉ "diagonalᵉ map"ᵉ Disambiguation="ofᵉ aᵉ typeᵉ intoᵉ itsᵉ cartesianᵉ product"ᵉ Agda=diagonal-productᵉ}}
thatᵉ includesᵉ aᵉ typeᵉ `A`ᵉ intoᵉ itsᵉ
[cartesianᵉ product](foundation-core.cartesian-product-types.mdᵉ) `Aᵉ ×ᵉ A`ᵉ isᵉ theᵉ
mapᵉ thatᵉ mapsᵉ `x`ᵉ to theᵉ pairᵉ `(xᵉ ,ᵉ x)`.ᵉ

## Definition

```agda
module _
  {lᵉ : Level} (Aᵉ : UUᵉ lᵉ)
  where

  diagonal-productᵉ : Aᵉ → Aᵉ ×ᵉ Aᵉ
  diagonal-productᵉ xᵉ = (xᵉ ,ᵉ xᵉ)
```

## Properties

### The action on paths of a diagonal

```agda
compute-ap-diagonal-productᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {xᵉ yᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) →
  apᵉ (diagonal-productᵉ Aᵉ) pᵉ ＝ᵉ eq-pairᵉ pᵉ pᵉ
compute-ap-diagonal-productᵉ reflᵉ = reflᵉ
```

### If the diagonal of `A` is an equivalence, then `A` is a proposition

```agda
module _
  {lᵉ : Level} (Aᵉ : UUᵉ lᵉ)
  where

  abstract
    is-prop-is-equiv-diagonal-productᵉ :
      is-equivᵉ (diagonal-productᵉ Aᵉ) → is-propᵉ Aᵉ
    is-prop-is-equiv-diagonal-productᵉ is-equiv-dᵉ =
      is-prop-all-elements-equalᵉ
        ( λ xᵉ yᵉ →
          ( invᵉ (apᵉ pr1ᵉ (is-section-map-inv-is-equivᵉ is-equiv-dᵉ (xᵉ ,ᵉ yᵉ)))) ∙ᵉ
          ( apᵉ pr2ᵉ (is-section-map-inv-is-equivᵉ is-equiv-dᵉ (xᵉ ,ᵉ yᵉ))))

  equiv-diagonal-product-is-propᵉ :
    is-propᵉ Aᵉ → Aᵉ ≃ᵉ Aᵉ ×ᵉ Aᵉ
  pr1ᵉ (equiv-diagonal-product-is-propᵉ is-prop-Aᵉ) =
    diagonal-productᵉ Aᵉ
  pr2ᵉ (equiv-diagonal-product-is-propᵉ is-prop-Aᵉ) =
    is-equiv-is-invertibleᵉ
      ( pr1ᵉ)
      ( λ _ → eq-pairᵉ (eq-is-propᵉ is-prop-Aᵉ) (eq-is-propᵉ is-prop-Aᵉ))
      ( λ aᵉ → eq-is-propᵉ is-prop-Aᵉ)
```

### The fibers of the diagonal map

```agda
module _
  {lᵉ : Level} (Aᵉ : UUᵉ lᵉ)
  where

  eq-fiber-diagonal-productᵉ :
    (tᵉ : Aᵉ ×ᵉ Aᵉ) → fiberᵉ (diagonal-productᵉ Aᵉ) tᵉ → pr1ᵉ tᵉ ＝ᵉ pr2ᵉ tᵉ
  eq-fiber-diagonal-productᵉ (xᵉ ,ᵉ yᵉ) (zᵉ ,ᵉ αᵉ) = invᵉ (apᵉ pr1ᵉ αᵉ) ∙ᵉ apᵉ pr2ᵉ αᵉ

  fiber-diagonal-product-eqᵉ :
    (tᵉ : Aᵉ ×ᵉ Aᵉ) → pr1ᵉ tᵉ ＝ᵉ pr2ᵉ tᵉ → fiberᵉ (diagonal-productᵉ Aᵉ) tᵉ
  fiber-diagonal-product-eqᵉ (xᵉ ,ᵉ yᵉ) βᵉ = (xᵉ ,ᵉ eq-pairᵉ reflᵉ βᵉ)

  is-section-fiber-diagonal-product-eqᵉ :
    (tᵉ : Aᵉ ×ᵉ Aᵉ) →
    is-sectionᵉ (eq-fiber-diagonal-productᵉ tᵉ) (fiber-diagonal-product-eqᵉ tᵉ)
  is-section-fiber-diagonal-product-eqᵉ (xᵉ ,ᵉ .xᵉ) reflᵉ = reflᵉ

  is-retraction-fiber-diagonal-product-eqᵉ :
    (tᵉ : Aᵉ ×ᵉ Aᵉ) →
    is-retractionᵉ (eq-fiber-diagonal-productᵉ tᵉ) (fiber-diagonal-product-eqᵉ tᵉ)
  is-retraction-fiber-diagonal-product-eqᵉ .(zᵉ ,ᵉ zᵉ) (zᵉ ,ᵉ reflᵉ) = reflᵉ

  abstract
    is-equiv-eq-fiber-diagonal-productᵉ :
      (tᵉ : Aᵉ ×ᵉ Aᵉ) → is-equivᵉ (eq-fiber-diagonal-productᵉ tᵉ)
    is-equiv-eq-fiber-diagonal-productᵉ tᵉ =
      is-equiv-is-invertibleᵉ
        ( fiber-diagonal-product-eqᵉ tᵉ)
        ( is-section-fiber-diagonal-product-eqᵉ tᵉ)
        ( is-retraction-fiber-diagonal-product-eqᵉ tᵉ)
```