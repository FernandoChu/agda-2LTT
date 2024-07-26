# Products of Dirichlet series of species of types in subuniverses

```agda
module species.products-dirichlet-series-species-of-types-in-subuniversesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-typesᵉ
open import foundation.coproduct-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.functoriality-cartesian-product-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.global-subuniversesᵉ
open import foundation.homotopiesᵉ
open import foundation.postcomposition-functionsᵉ
open import foundation.subuniversesᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.universal-property-cartesian-product-typesᵉ
open import foundation.universe-levelsᵉ

open import species.dirichlet-products-species-of-types-in-subuniversesᵉ
open import species.dirichlet-series-species-of-types-in-subuniversesᵉ
open import species.species-of-types-in-subuniversesᵉ
```

</details>

## Idea

Theᵉ productᵉ ofᵉ twoᵉ Dirichletᵉ seriesᵉ isᵉ theᵉ pointwiseᵉ product.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level}
  (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ)
  (Qᵉ : global-subuniverseᵉ (λ lᵉ → lᵉ))
  (C1ᵉ : is-closed-under-products-subuniverseᵉ Pᵉ)
  (Hᵉ : species-subuniverse-domainᵉ l5ᵉ Pᵉ)
  (C2ᵉ : preserves-product-species-subuniverse-domainᵉ Pᵉ C1ᵉ Hᵉ)
  (Sᵉ : species-subuniverseᵉ Pᵉ (subuniverse-global-subuniverseᵉ Qᵉ l3ᵉ))
  (Tᵉ : species-subuniverseᵉ Pᵉ (subuniverse-global-subuniverseᵉ Qᵉ l4ᵉ))
  (Xᵉ : UUᵉ l6ᵉ)
  where

  product-dirichlet-series-species-subuniverseᵉ :
    UUᵉ (lsuc l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ ⊔ l5ᵉ ⊔ l6ᵉ)
  product-dirichlet-series-species-subuniverseᵉ =
    dirichlet-series-species-subuniverseᵉ
      ( Pᵉ)
      ( subuniverse-global-subuniverseᵉ Qᵉ l3ᵉ)
      ( C1ᵉ)
      ( Hᵉ)
      ( C2ᵉ)
      ( Sᵉ)
      ( Xᵉ) ×ᵉ
    dirichlet-series-species-subuniverseᵉ
      ( Pᵉ)
      ( subuniverse-global-subuniverseᵉ Qᵉ l4ᵉ)
      ( C1ᵉ)
      ( Hᵉ)
      ( C2ᵉ)
      ( Tᵉ)
      ( Xᵉ)
```

## Properties

### The Dirichlet series associated to the Dirichlet product of `S` and `T` is equal to the product of their Dirichlet series

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level}
  (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ)
  (Qᵉ : global-subuniverseᵉ (λ lᵉ → lᵉ))
  (C1ᵉ : is-closed-under-products-subuniverseᵉ Pᵉ)
  (Hᵉ : species-subuniverse-domainᵉ l5ᵉ Pᵉ)
  (C2ᵉ : preserves-product-species-subuniverse-domainᵉ Pᵉ C1ᵉ Hᵉ)
  (C3ᵉ : is-closed-under-dirichlet-product-species-subuniverseᵉ Pᵉ Qᵉ)
  (C4ᵉ : is-closed-under-coproducts-subuniverseᵉ Pᵉ)
  (Sᵉ : species-subuniverseᵉ Pᵉ (subuniverse-global-subuniverseᵉ Qᵉ l3ᵉ))
  (Tᵉ : species-subuniverseᵉ Pᵉ (subuniverse-global-subuniverseᵉ Qᵉ l4ᵉ))
  (Xᵉ : UUᵉ l5ᵉ)
  where

  private
    reassociateᵉ :
      dirichlet-series-species-subuniverseᵉ
        ( Pᵉ)
        ( subuniverse-global-subuniverseᵉ Qᵉ (lsuc l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ))
        ( C1ᵉ)
        ( Hᵉ)
        ( C2ᵉ)
        ( dirichlet-product-species-subuniverseᵉ Pᵉ Qᵉ C3ᵉ Sᵉ Tᵉ) Xᵉ ≃ᵉ
      Σᵉ ( type-subuniverseᵉ Pᵉ)
        ( λ Aᵉ →
          Σᵉ ( type-subuniverseᵉ Pᵉ)
            ( λ Bᵉ →
              Σᵉ ( Σᵉ ( type-subuniverseᵉ Pᵉ)
                    ( λ Fᵉ →
                      inclusion-subuniverseᵉ Pᵉ Fᵉ ≃ᵉ
                      ( inclusion-subuniverseᵉ Pᵉ Aᵉ ×ᵉ inclusion-subuniverseᵉ Pᵉ Bᵉ)))
                ( λ Fᵉ →
                  ( ( inclusion-subuniverseᵉ
                      ( subuniverse-global-subuniverseᵉ Qᵉ l3ᵉ)
                      ( Sᵉ Aᵉ)) ×ᵉ
                    ( inclusion-subuniverseᵉ
                      ( subuniverse-global-subuniverseᵉ Qᵉ l4ᵉ)
                      ( Tᵉ Bᵉ))) ×ᵉ (Xᵉ → Hᵉ (pr1ᵉ Fᵉ)))))
    pr1ᵉ reassociateᵉ (Fᵉ ,ᵉ ((Aᵉ ,ᵉ Bᵉ ,ᵉ eᵉ) ,ᵉ xᵉ) ,ᵉ yᵉ) = (Aᵉ ,ᵉ Bᵉ ,ᵉ (Fᵉ ,ᵉ eᵉ) ,ᵉ xᵉ ,ᵉ yᵉ)
    pr2ᵉ reassociateᵉ =
      is-equiv-is-invertibleᵉ
        ( λ (Aᵉ ,ᵉ Bᵉ ,ᵉ (Fᵉ ,ᵉ eᵉ) ,ᵉ xᵉ ,ᵉ yᵉ) → (Fᵉ ,ᵉ ((Aᵉ ,ᵉ Bᵉ ,ᵉ eᵉ) ,ᵉ xᵉ) ,ᵉ yᵉ))
        ( refl-htpyᵉ)
        ( refl-htpyᵉ)

    reassociate'ᵉ :
      Σᵉ ( type-subuniverseᵉ Pᵉ)
        ( λ Aᵉ →
          Σᵉ ( type-subuniverseᵉ Pᵉ)
            ( λ Bᵉ →
              ( ( inclusion-subuniverseᵉ
                  ( subuniverse-global-subuniverseᵉ Qᵉ l3ᵉ)
                  ( Sᵉ Aᵉ)) ×ᵉ
                inclusion-subuniverseᵉ
                  ( subuniverse-global-subuniverseᵉ Qᵉ l4ᵉ)
                  ( Tᵉ Bᵉ)) ×ᵉ
              ( (Xᵉ → Hᵉ Aᵉ) ×ᵉ (Xᵉ → Hᵉ Bᵉ)))) ≃ᵉ
      product-dirichlet-series-species-subuniverseᵉ Pᵉ Qᵉ C1ᵉ Hᵉ C2ᵉ Sᵉ Tᵉ Xᵉ
    pr1ᵉ reassociate'ᵉ (Aᵉ ,ᵉ Bᵉ ,ᵉ (sᵉ ,ᵉ tᵉ) ,ᵉ (fsᵉ ,ᵉ ftᵉ)) =
      ((Aᵉ ,ᵉ (sᵉ ,ᵉ fsᵉ)) ,ᵉ (Bᵉ ,ᵉ (tᵉ ,ᵉ ftᵉ)))
    pr2ᵉ reassociate'ᵉ =
      is-equiv-is-invertibleᵉ
        ( λ ((Aᵉ ,ᵉ (sᵉ ,ᵉ fsᵉ)) ,ᵉ (Bᵉ ,ᵉ (tᵉ ,ᵉ ftᵉ))) →
          (Aᵉ ,ᵉ Bᵉ ,ᵉ (sᵉ ,ᵉ tᵉ) ,ᵉ (fsᵉ ,ᵉ ftᵉ)))
        ( refl-htpyᵉ)
        ( refl-htpyᵉ)

  equiv-dirichlet-series-dirichlet-product-species-subuniverseᵉ :
    dirichlet-series-species-subuniverseᵉ
      ( Pᵉ)
      ( subuniverse-global-subuniverseᵉ Qᵉ (lsuc l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ))
      ( C1ᵉ)
      ( Hᵉ)
      ( C2ᵉ)
      ( dirichlet-product-species-subuniverseᵉ Pᵉ Qᵉ C3ᵉ Sᵉ Tᵉ)
      ( Xᵉ) ≃ᵉ
    product-dirichlet-series-species-subuniverseᵉ Pᵉ Qᵉ C1ᵉ Hᵉ C2ᵉ Sᵉ Tᵉ Xᵉ
  equiv-dirichlet-series-dirichlet-product-species-subuniverseᵉ =
    ( reassociate'ᵉ) ∘eᵉ
    ( ( equiv-totᵉ
        ( λ Aᵉ →
          equiv-totᵉ
            ( λ Bᵉ →
              ( equiv-productᵉ
                ( id-equivᵉ)
                ( equiv-up-productᵉ ∘eᵉ equiv-postcompᵉ Xᵉ (C2ᵉ Aᵉ Bᵉ))) ∘eᵉ
              left-unit-law-Σ-is-contrᵉ
                ( is-torsorial-equiv-subuniverse'ᵉ
                  ( Pᵉ)
                  ( inclusion-subuniverseᵉ Pᵉ Aᵉ ×ᵉ
                    inclusion-subuniverseᵉ Pᵉ Bᵉ ,ᵉ
                    C1ᵉ
                      ( is-in-subuniverse-inclusion-subuniverseᵉ Pᵉ Aᵉ)
                      ( is-in-subuniverse-inclusion-subuniverseᵉ Pᵉ Bᵉ)))
                ( ( inclusion-subuniverseᵉ Pᵉ Aᵉ ×ᵉ inclusion-subuniverseᵉ Pᵉ Bᵉ ,ᵉ
                    C1ᵉ
                      ( is-in-subuniverse-inclusion-subuniverseᵉ Pᵉ Aᵉ)
                      ( is-in-subuniverse-inclusion-subuniverseᵉ Pᵉ Bᵉ)) ,ᵉ
                  id-equivᵉ)))) ∘eᵉ
      ( reassociateᵉ))
```