# Products of Dirichlet series of species of types

```agda
module species.products-dirichlet-series-species-of-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.functoriality-cartesian-product-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.postcomposition-functionsᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.univalenceᵉ
open import foundation.universal-property-cartesian-product-typesᵉ
open import foundation.universe-levelsᵉ

open import species.dirichlet-products-species-of-typesᵉ
open import species.dirichlet-series-species-of-typesᵉ
open import species.species-of-typesᵉ
```

</details>

## Idea

Theᵉ productᵉ ofᵉ twoᵉ Dirichletᵉ seriesᵉ isᵉ theᵉ pointwiseᵉ product.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level}
  (Hᵉ : species-typesᵉ l1ᵉ l2ᵉ)
  (C1ᵉ : preserves-product-species-typesᵉ Hᵉ)
  (Sᵉ : species-typesᵉ l1ᵉ l3ᵉ)
  (Tᵉ : species-typesᵉ l1ᵉ l4ᵉ)
  (Xᵉ : UUᵉ l5ᵉ)
  where

  product-dirichlet-series-species-typesᵉ : UUᵉ (lsuc l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ ⊔ l5ᵉ)
  product-dirichlet-series-species-typesᵉ =
    dirichlet-series-species-typesᵉ Hᵉ C1ᵉ Sᵉ Xᵉ ×ᵉ
    dirichlet-series-species-typesᵉ Hᵉ C1ᵉ Tᵉ Xᵉ
```

## Properties

### The Dirichlet series associated to the Dirichlet product of `S` and `T` is equal to the product of theirs Dirichlet series

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Hᵉ : species-typesᵉ l1ᵉ l2ᵉ)
  (C1ᵉ : preserves-product-species-typesᵉ Hᵉ)
  (Sᵉ : species-typesᵉ l1ᵉ l2ᵉ)
  (Tᵉ : species-typesᵉ l1ᵉ l3ᵉ)
  (Xᵉ : UUᵉ l4ᵉ)
  where

  private
    reassociateᵉ :
      dirichlet-series-species-typesᵉ
        ( Hᵉ)
        ( C1ᵉ)
        ( dirichlet-product-species-typesᵉ Sᵉ Tᵉ) Xᵉ ≃ᵉ
      Σᵉ ( UUᵉ l1ᵉ)
        ( λ Aᵉ →
          Σᵉ ( UUᵉ l1ᵉ)
            ( λ Bᵉ →
              Σᵉ ( Σᵉ ( UUᵉ l1ᵉ) (λ Fᵉ → Fᵉ ≃ᵉ (Aᵉ ×ᵉ Bᵉ)))
                ( λ Fᵉ → ((Sᵉ Aᵉ) ×ᵉ (Tᵉ Bᵉ)) ×ᵉ (Xᵉ → Hᵉ (pr1ᵉ Fᵉ)))))
    pr1ᵉ reassociateᵉ (Fᵉ ,ᵉ ((Aᵉ ,ᵉ Bᵉ ,ᵉ eᵉ) ,ᵉ xᵉ) ,ᵉ yᵉ) = (Aᵉ ,ᵉ Bᵉ ,ᵉ (Fᵉ ,ᵉ eᵉ) ,ᵉ xᵉ ,ᵉ yᵉ)
    pr2ᵉ reassociateᵉ =
      is-equiv-is-invertibleᵉ
        ( λ (Aᵉ ,ᵉ Bᵉ ,ᵉ (Fᵉ ,ᵉ eᵉ) ,ᵉ xᵉ ,ᵉ yᵉ) → (Fᵉ ,ᵉ ((Aᵉ ,ᵉ Bᵉ ,ᵉ eᵉ) ,ᵉ xᵉ) ,ᵉ yᵉ))
        ( refl-htpyᵉ)
        ( refl-htpyᵉ)

    reassociate'ᵉ :
      Σᵉ ( UUᵉ l1ᵉ)
        ( λ Aᵉ → Σᵉ (UUᵉ l1ᵉ) (λ Bᵉ → (Sᵉ Aᵉ ×ᵉ Tᵉ Bᵉ) ×ᵉ ((Xᵉ → Hᵉ Aᵉ) ×ᵉ (Xᵉ → Hᵉ Bᵉ)))) ≃ᵉ
      product-dirichlet-series-species-typesᵉ Hᵉ C1ᵉ Sᵉ Tᵉ Xᵉ
    pr1ᵉ reassociate'ᵉ (Aᵉ ,ᵉ Bᵉ ,ᵉ (sᵉ ,ᵉ tᵉ) ,ᵉ (fsᵉ ,ᵉ ftᵉ)) =
      ((Aᵉ ,ᵉ (sᵉ ,ᵉ fsᵉ)) ,ᵉ (Bᵉ ,ᵉ (tᵉ ,ᵉ ftᵉ)))
    pr2ᵉ reassociate'ᵉ =
      is-equiv-is-invertibleᵉ
        ( λ ((Aᵉ ,ᵉ (sᵉ ,ᵉ fsᵉ)) ,ᵉ (Bᵉ ,ᵉ (tᵉ ,ᵉ ftᵉ))) →
          (Aᵉ ,ᵉ Bᵉ ,ᵉ (sᵉ ,ᵉ tᵉ) ,ᵉ (fsᵉ ,ᵉ ftᵉ)))
        ( refl-htpyᵉ)
        ( refl-htpyᵉ)

  equiv-dirichlet-series-dirichlet-product-species-typesᵉ :
    dirichlet-series-species-typesᵉ
      ( Hᵉ)
      ( C1ᵉ)
      ( dirichlet-product-species-typesᵉ Sᵉ Tᵉ)
      ( Xᵉ) ≃ᵉ
    product-dirichlet-series-species-typesᵉ Hᵉ C1ᵉ Sᵉ Tᵉ Xᵉ
  equiv-dirichlet-series-dirichlet-product-species-typesᵉ =
    ( reassociate'ᵉ) ∘eᵉ
    ( ( equiv-totᵉ
        ( λ Aᵉ →
          equiv-totᵉ
            ( λ Bᵉ →
              ( equiv-productᵉ
                ( id-equivᵉ)
                ( equiv-up-productᵉ ∘eᵉ equiv-postcompᵉ Xᵉ (C1ᵉ Aᵉ Bᵉ))) ∘eᵉ
              ( left-unit-law-Σ-is-contrᵉ
                ( is-torsorial-equiv'ᵉ (Aᵉ ×ᵉ Bᵉ))
                ( Aᵉ ×ᵉ Bᵉ ,ᵉ id-equivᵉ))))) ∘eᵉ
      ( reassociateᵉ))
```