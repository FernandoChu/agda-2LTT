# Products of Cauchy series of species of types in subuniverses

```agda
module species.products-cauchy-series-species-of-types-in-subuniversesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-typesᵉ
open import foundation.coproduct-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.functoriality-cartesian-product-typesᵉ
open import foundation.global-subuniversesᵉ
open import foundation.subuniversesᵉ
open import foundation.universe-levelsᵉ

open import species.cauchy-products-species-of-typesᵉ
open import species.cauchy-products-species-of-types-in-subuniversesᵉ
open import species.cauchy-series-species-of-typesᵉ
open import species.cauchy-series-species-of-types-in-subuniversesᵉ
open import species.products-cauchy-series-species-of-typesᵉ
open import species.species-of-types-in-subuniversesᵉ
```

</details>

## Idea

Theᵉ productᵉ ofᵉ twoᵉ Cauchyᵉ seriesᵉ isᵉ justᵉ theᵉ pointwiseᵉ product.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level}
  (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ)
  (Qᵉ : global-subuniverseᵉ (λ lᵉ → lᵉ))
  (Sᵉ : species-subuniverseᵉ Pᵉ (subuniverse-global-subuniverseᵉ Qᵉ l3ᵉ))
  (Tᵉ : species-subuniverseᵉ Pᵉ (subuniverse-global-subuniverseᵉ Qᵉ l4ᵉ))
  (Xᵉ : UUᵉ l5ᵉ)
  where

  product-cauchy-series-species-subuniverseᵉ :
    UUᵉ (lsuc l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ ⊔ l5ᵉ)
  product-cauchy-series-species-subuniverseᵉ =
    ( cauchy-series-species-subuniverseᵉ
      Pᵉ (subuniverse-global-subuniverseᵉ Qᵉ l3ᵉ) Sᵉ Xᵉ) ×ᵉ
    ( cauchy-series-species-subuniverseᵉ
      Pᵉ (subuniverse-global-subuniverseᵉ Qᵉ l4ᵉ) Tᵉ Xᵉ)
```

## Properties

### Equivalent with species of types

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level}
  (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ)
  (Qᵉ : global-subuniverseᵉ (λ lᵉ → lᵉ))
  (Sᵉ : species-subuniverseᵉ Pᵉ (subuniverse-global-subuniverseᵉ Qᵉ l3ᵉ))
  (Tᵉ : species-subuniverseᵉ Pᵉ (subuniverse-global-subuniverseᵉ Qᵉ l4ᵉ))
  (Xᵉ : UUᵉ l5ᵉ)
  where

  equiv-product-cauchy-series-Σ-extension-species-subuniverseᵉ :
    ( product-cauchy-series-species-typesᵉ
      ( Σ-extension-species-subuniverseᵉ
          ( Pᵉ)
          ( subuniverse-global-subuniverseᵉ Qᵉ l3ᵉ)
          ( Sᵉ))
      ( Σ-extension-species-subuniverseᵉ
          ( Pᵉ)
          ( subuniverse-global-subuniverseᵉ Qᵉ l4ᵉ)
          ( Tᵉ))
      Xᵉ)
      ≃ᵉ
    product-cauchy-series-species-subuniverseᵉ Pᵉ Qᵉ Sᵉ Tᵉ Xᵉ
  equiv-product-cauchy-series-Σ-extension-species-subuniverseᵉ =
    equiv-productᵉ
          ( inv-equivᵉ
            ( equiv-cauchy-series-Σ-extension-species-subuniverseᵉ
                ( Pᵉ)
                ( subuniverse-global-subuniverseᵉ Qᵉ l3ᵉ)
                ( Sᵉ)
                ( Xᵉ)))
          ( inv-equivᵉ
            ( equiv-cauchy-series-Σ-extension-species-subuniverseᵉ
                ( Pᵉ)
                ( subuniverse-global-subuniverseᵉ Qᵉ l4ᵉ)
                ( Tᵉ)
                ( Xᵉ)))
```

### The Cauchy series associated to the Cauchy product of `S` and `T` is equal to the product of theirs Cauchy series

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level}
  (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ)
  (Qᵉ : global-subuniverseᵉ (λ lᵉ → lᵉ))
  (C1ᵉ : is-closed-under-cauchy-product-species-subuniverseᵉ Pᵉ Qᵉ)
  (C2ᵉ : is-closed-under-coproducts-subuniverseᵉ Pᵉ)
  (Sᵉ : species-subuniverseᵉ Pᵉ (subuniverse-global-subuniverseᵉ Qᵉ l3ᵉ))
  (Tᵉ : species-subuniverseᵉ Pᵉ (subuniverse-global-subuniverseᵉ Qᵉ l4ᵉ))
  (Xᵉ : UUᵉ l5ᵉ)
  where

  equiv-cauchy-series-cauchy-product-species-subuniverseᵉ :
    cauchy-series-species-subuniverseᵉ
      ( Pᵉ)
      ( subuniverse-global-subuniverseᵉ Qᵉ (lsuc l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ))
      ( cauchy-product-species-subuniverseᵉ Pᵉ Qᵉ C1ᵉ Sᵉ Tᵉ)
      ( Xᵉ) ≃ᵉ
    product-cauchy-series-species-subuniverseᵉ Pᵉ Qᵉ Sᵉ Tᵉ Xᵉ
  equiv-cauchy-series-cauchy-product-species-subuniverseᵉ =
    ( equiv-product-cauchy-series-Σ-extension-species-subuniverseᵉ Pᵉ Qᵉ Sᵉ Tᵉ Xᵉ ∘eᵉ
      ( ( equiv-cauchy-series-cauchy-product-species-typesᵉ
            ( Σ-extension-species-subuniverseᵉ
                ( Pᵉ)
                ( subuniverse-global-subuniverseᵉ Qᵉ l3ᵉ)
                ( Sᵉ))
            ( Σ-extension-species-subuniverseᵉ
                ( Pᵉ)
                ( subuniverse-global-subuniverseᵉ Qᵉ l4ᵉ)
                ( Tᵉ))
            ( Xᵉ)) ∘eᵉ
        ( ( equiv-cauchy-series-equiv-species-typesᵉ
              ( λ zᵉ →
                Σ-extension-species-subuniverseᵉ
                  ( Pᵉ)
                  ( subuniverse-global-subuniverseᵉ Qᵉ (lsuc l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ))
                  ( cauchy-product-species-subuniverseᵉ Pᵉ Qᵉ C1ᵉ Sᵉ Tᵉ) zᵉ)
              ( λ zᵉ →
                cauchy-product-species-typesᵉ
                  ( Σ-extension-species-subuniverseᵉ
                      ( Pᵉ)
                      ( subuniverse-global-subuniverseᵉ Qᵉ l3ᵉ)
                      ( Sᵉ))
                  ( Σ-extension-species-subuniverseᵉ
                      ( Pᵉ)
                      ( subuniverse-global-subuniverseᵉ Qᵉ l4ᵉ)
                      ( Tᵉ))
                  zᵉ)
              ( equiv-cauchy-product-Σ-extension-species-subuniverseᵉ
                  Pᵉ Qᵉ C1ᵉ C2ᵉ Sᵉ Tᵉ)
              ( Xᵉ)) ∘eᵉ
          ( ( equiv-cauchy-series-Σ-extension-species-subuniverseᵉ
                ( Pᵉ)
                ( subuniverse-global-subuniverseᵉ Qᵉ (lsuc l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ))
                ( cauchy-product-species-subuniverseᵉ Pᵉ Qᵉ C1ᵉ Sᵉ Tᵉ)
                ( Xᵉ))))))
```