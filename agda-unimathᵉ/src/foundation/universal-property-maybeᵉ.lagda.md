# The universal property of maybe

```agda
module foundation.universal-property-maybeᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.maybeᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.cartesian-product-typesᵉ
open import foundation-core.coproduct-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
```

</details>

## Idea

Weᵉ combineᵉ theᵉ universalᵉ propertyᵉ ofᵉ coproductsᵉ andᵉ theᵉ unitᵉ typeᵉ to obtainᵉ aᵉ
universalᵉ propertyᵉ ofᵉ theᵉ maybeᵉ modality.ᵉ

## Definitions

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Maybeᵉ Aᵉ → UUᵉ l2ᵉ}
  where

  ev-Maybeᵉ :
    ((xᵉ : Maybeᵉ Aᵉ) → Bᵉ xᵉ) → ((xᵉ : Aᵉ) → Bᵉ (unit-Maybeᵉ xᵉ)) ×ᵉ Bᵉ exception-Maybeᵉ
  pr1ᵉ (ev-Maybeᵉ hᵉ) xᵉ = hᵉ (unit-Maybeᵉ xᵉ)
  pr2ᵉ (ev-Maybeᵉ hᵉ) = hᵉ exception-Maybeᵉ

  ind-Maybeᵉ :
    ((xᵉ : Aᵉ) → Bᵉ (unit-Maybeᵉ xᵉ)) ×ᵉ (Bᵉ exception-Maybeᵉ) → (xᵉ : Maybeᵉ Aᵉ) → Bᵉ xᵉ
  ind-Maybeᵉ (pairᵉ hᵉ bᵉ) (inlᵉ xᵉ) = hᵉ xᵉ
  ind-Maybeᵉ (pairᵉ hᵉ bᵉ) (inrᵉ _) = bᵉ

  abstract
    is-section-ind-Maybeᵉ : (ev-Maybeᵉ ∘ᵉ ind-Maybeᵉ) ~ᵉ idᵉ
    is-section-ind-Maybeᵉ (pairᵉ hᵉ bᵉ) = reflᵉ

    is-retraction-ind-Maybe'ᵉ :
      (hᵉ : (xᵉ : Maybeᵉ Aᵉ) → Bᵉ xᵉ) → (ind-Maybeᵉ (ev-Maybeᵉ hᵉ)) ~ᵉ hᵉ
    is-retraction-ind-Maybe'ᵉ hᵉ (inlᵉ xᵉ) = reflᵉ
    is-retraction-ind-Maybe'ᵉ hᵉ (inrᵉ _) = reflᵉ

    is-retraction-ind-Maybeᵉ : (ind-Maybeᵉ ∘ᵉ ev-Maybeᵉ) ~ᵉ idᵉ
    is-retraction-ind-Maybeᵉ hᵉ = eq-htpyᵉ (is-retraction-ind-Maybe'ᵉ hᵉ)

    dependent-universal-property-Maybeᵉ :
      is-equivᵉ ev-Maybeᵉ
    dependent-universal-property-Maybeᵉ =
      is-equiv-is-invertibleᵉ
        ind-Maybeᵉ
        is-section-ind-Maybeᵉ
        is-retraction-ind-Maybeᵉ

equiv-dependent-universal-property-Maybeᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : Maybeᵉ Aᵉ → UUᵉ l2ᵉ) →
  ((xᵉ : Maybeᵉ Aᵉ) → Bᵉ xᵉ) ≃ᵉ (((xᵉ : Aᵉ) → Bᵉ (unit-Maybeᵉ xᵉ)) ×ᵉ Bᵉ exception-Maybeᵉ)
pr1ᵉ (equiv-dependent-universal-property-Maybeᵉ Bᵉ) = ev-Maybeᵉ
pr2ᵉ (equiv-dependent-universal-property-Maybeᵉ Bᵉ) =
  dependent-universal-property-Maybeᵉ

equiv-universal-property-Maybeᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} → (Maybeᵉ Aᵉ → Bᵉ) ≃ᵉ ((Aᵉ → Bᵉ) ×ᵉ Bᵉ)
equiv-universal-property-Maybeᵉ {l1ᵉ} {l2ᵉ} {Aᵉ} {Bᵉ} =
  equiv-dependent-universal-property-Maybeᵉ (λ xᵉ → Bᵉ)
```