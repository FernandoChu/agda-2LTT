# Diagonal maps into cartesian products of types

```agda
module foundation.diagonal-maps-cartesian-products-of-typesᵉ where

open import foundation-core.diagonal-maps-cartesian-products-of-typesᵉ public
```

<details><summary>Imports</summary>

```agda
open import foundation.0-mapsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.faithful-mapsᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.1-typesᵉ
open import foundation-core.cartesian-product-typesᵉ
open import foundation-core.contractible-mapsᵉ
open import foundation-core.embeddingsᵉ
open import foundation-core.fibers-of-mapsᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.propositional-mapsᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.setsᵉ
open import foundation-core.truncated-mapsᵉ
open import foundation-core.truncated-typesᵉ
open import foundation-core.truncation-levelsᵉ
```

</details>

## Properties

### A type is `k+1`-truncated if and only if the diagonal is `k`-truncated

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  abstract
    is-trunc-is-trunc-map-diagonal-productᵉ :
      (kᵉ : 𝕋ᵉ) → is-trunc-mapᵉ kᵉ (diagonal-productᵉ Aᵉ) → is-truncᵉ (succ-𝕋ᵉ kᵉ) Aᵉ
    is-trunc-is-trunc-map-diagonal-productᵉ kᵉ is-trunc-dᵉ xᵉ yᵉ =
      is-trunc-is-equiv'ᵉ kᵉ
        ( fiberᵉ (diagonal-productᵉ Aᵉ) (pairᵉ xᵉ yᵉ))
        ( eq-fiber-diagonal-productᵉ Aᵉ (pairᵉ xᵉ yᵉ))
        ( is-equiv-eq-fiber-diagonal-productᵉ Aᵉ (pairᵉ xᵉ yᵉ))
        ( is-trunc-dᵉ (pairᵉ xᵉ yᵉ))

  abstract
    is-prop-is-contr-map-diagonal-productᵉ :
      is-contr-mapᵉ (diagonal-productᵉ Aᵉ) → is-propᵉ Aᵉ
    is-prop-is-contr-map-diagonal-productᵉ =
      is-trunc-is-trunc-map-diagonal-productᵉ neg-two-𝕋ᵉ

  abstract
    is-set-is-prop-map-diagonal-productᵉ :
      is-prop-mapᵉ (diagonal-productᵉ Aᵉ) → is-setᵉ Aᵉ
    is-set-is-prop-map-diagonal-productᵉ =
      is-trunc-is-trunc-map-diagonal-productᵉ neg-one-𝕋ᵉ

  abstract
    is-set-is-emb-diagonal-productᵉ : is-embᵉ (diagonal-productᵉ Aᵉ) → is-setᵉ Aᵉ
    is-set-is-emb-diagonal-productᵉ Hᵉ =
      is-set-is-prop-map-diagonal-productᵉ (is-prop-map-is-embᵉ Hᵉ)

  abstract
    is-1-type-is-0-map-diagonal-productᵉ :
      is-0-mapᵉ (diagonal-productᵉ Aᵉ) → is-1-typeᵉ Aᵉ
    is-1-type-is-0-map-diagonal-productᵉ =
      is-trunc-is-trunc-map-diagonal-productᵉ zero-𝕋ᵉ

  abstract
    is-1-type-is-faithful-diagonal-productᵉ :
      is-faithfulᵉ (diagonal-productᵉ Aᵉ) → is-1-typeᵉ Aᵉ
    is-1-type-is-faithful-diagonal-productᵉ Hᵉ =
      is-1-type-is-0-map-diagonal-productᵉ (is-0-map-is-faithfulᵉ Hᵉ)

  abstract
    is-trunc-map-diagonal-product-is-truncᵉ :
      (kᵉ : 𝕋ᵉ) → is-truncᵉ (succ-𝕋ᵉ kᵉ) Aᵉ → is-trunc-mapᵉ kᵉ (diagonal-productᵉ Aᵉ)
    is-trunc-map-diagonal-product-is-truncᵉ kᵉ is-trunc-Aᵉ tᵉ =
      is-trunc-is-equivᵉ kᵉ
        ( pr1ᵉ tᵉ ＝ᵉ pr2ᵉ tᵉ)
        ( eq-fiber-diagonal-productᵉ Aᵉ tᵉ)
        ( is-equiv-eq-fiber-diagonal-productᵉ Aᵉ tᵉ)
          ( is-trunc-Aᵉ (pr1ᵉ tᵉ) (pr2ᵉ tᵉ))

  abstract
    is-contr-map-diagonal-product-is-propᵉ :
      is-propᵉ Aᵉ → is-contr-mapᵉ (diagonal-productᵉ Aᵉ)
    is-contr-map-diagonal-product-is-propᵉ =
      is-trunc-map-diagonal-product-is-truncᵉ neg-two-𝕋ᵉ

  abstract
    is-prop-map-diagonal-product-is-setᵉ :
      is-setᵉ Aᵉ → is-prop-mapᵉ (diagonal-productᵉ Aᵉ)
    is-prop-map-diagonal-product-is-setᵉ =
      is-trunc-map-diagonal-product-is-truncᵉ neg-one-𝕋ᵉ

  abstract
    is-emb-diagonal-product-is-setᵉ : is-setᵉ Aᵉ → is-embᵉ (diagonal-productᵉ Aᵉ)
    is-emb-diagonal-product-is-setᵉ Hᵉ =
      is-emb-is-prop-mapᵉ (is-prop-map-diagonal-product-is-setᵉ Hᵉ)

  abstract
    is-0-map-diagonal-product-is-1-typeᵉ :
      is-1-typeᵉ Aᵉ → is-0-mapᵉ (diagonal-productᵉ Aᵉ)
    is-0-map-diagonal-product-is-1-typeᵉ =
      is-trunc-map-diagonal-product-is-truncᵉ zero-𝕋ᵉ

  abstract
    is-faithful-diagonal-product-is-1-typeᵉ :
      is-1-typeᵉ Aᵉ → is-faithfulᵉ (diagonal-productᵉ Aᵉ)
    is-faithful-diagonal-product-is-1-typeᵉ Hᵉ =
      is-faithful-is-0-mapᵉ (is-0-map-diagonal-product-is-1-typeᵉ Hᵉ)

diagonal-product-embᵉ :
  {lᵉ : Level} (Aᵉ : Setᵉ lᵉ) → type-Setᵉ Aᵉ ↪ᵉ type-Setᵉ Aᵉ ×ᵉ type-Setᵉ Aᵉ
pr1ᵉ (diagonal-product-embᵉ Aᵉ) =
  diagonal-productᵉ (type-Setᵉ Aᵉ)
pr2ᵉ (diagonal-product-embᵉ Aᵉ) =
  is-emb-diagonal-product-is-setᵉ (is-set-type-Setᵉ Aᵉ)

diagonal-product-faithful-mapᵉ :
  {lᵉ : Level} (Aᵉ : 1-Typeᵉ lᵉ) →
  faithful-mapᵉ (type-1-Typeᵉ Aᵉ) (type-1-Typeᵉ Aᵉ ×ᵉ type-1-Typeᵉ Aᵉ)
pr1ᵉ (diagonal-product-faithful-mapᵉ Aᵉ) =
  diagonal-productᵉ (type-1-Typeᵉ Aᵉ)
pr2ᵉ (diagonal-product-faithful-mapᵉ Aᵉ) =
  is-faithful-diagonal-product-is-1-typeᵉ (is-1-type-type-1-Typeᵉ Aᵉ)
```