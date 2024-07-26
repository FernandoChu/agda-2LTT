# Products of Cauchy series of species of types

```agda
module species.products-cauchy-series-species-of-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-typesᵉ
open import foundation.coproduct-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.functoriality-cartesian-product-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.univalenceᵉ
open import foundation.universal-property-coproduct-typesᵉ
open import foundation.universe-levelsᵉ

open import species.cauchy-products-species-of-typesᵉ
open import species.cauchy-series-species-of-typesᵉ
open import species.species-of-typesᵉ
```

</details>

## Idea

Theᵉ productᵉ ofᵉ twoᵉ Cauchyᵉ seriesᵉ isᵉ justᵉ theᵉ pointwiseᵉ product.ᵉ

## Definition

```agda
product-cauchy-series-species-typesᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} → species-typesᵉ l1ᵉ l2ᵉ → species-typesᵉ l1ᵉ l3ᵉ →
  UUᵉ l4ᵉ → UUᵉ (lsuc l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
product-cauchy-series-species-typesᵉ Sᵉ Tᵉ Xᵉ =
  cauchy-series-species-typesᵉ Sᵉ Xᵉ ×ᵉ cauchy-series-species-typesᵉ Tᵉ Xᵉ
```

## Properties

### The Cauchy series associated to the Cauchy product of `S` and `T` is equal to the product of theirs Cauchy series

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Sᵉ : species-typesᵉ l1ᵉ l2ᵉ)
  (Tᵉ : species-typesᵉ l1ᵉ l3ᵉ)
  (Xᵉ : UUᵉ l4ᵉ)
  where

  private
    reassociateᵉ :
      cauchy-series-species-typesᵉ (cauchy-product-species-typesᵉ Sᵉ Tᵉ) Xᵉ ≃ᵉ
      Σᵉ ( UUᵉ l1ᵉ)
        ( λ Aᵉ →
          Σᵉ ( UUᵉ l1ᵉ)
            ( λ Bᵉ →
              Σᵉ ( Σᵉ ( UUᵉ l1ᵉ) (λ Fᵉ → Fᵉ ≃ᵉ (Aᵉ +ᵉ Bᵉ)))
                ( λ Fᵉ → ((Sᵉ Aᵉ) ×ᵉ (Tᵉ Bᵉ)) ×ᵉ (pr1ᵉ Fᵉ → Xᵉ))))
    pr1ᵉ reassociateᵉ (Fᵉ ,ᵉ ((Aᵉ ,ᵉ Bᵉ ,ᵉ eᵉ) ,ᵉ xᵉ) ,ᵉ yᵉ) = (Aᵉ ,ᵉ Bᵉ ,ᵉ (Fᵉ ,ᵉ eᵉ) ,ᵉ xᵉ ,ᵉ yᵉ)
    pr2ᵉ reassociateᵉ =
      is-equiv-is-invertibleᵉ
        ( λ (Aᵉ ,ᵉ Bᵉ ,ᵉ (Fᵉ ,ᵉ eᵉ) ,ᵉ xᵉ ,ᵉ yᵉ) → (Fᵉ ,ᵉ ((Aᵉ ,ᵉ Bᵉ ,ᵉ eᵉ) ,ᵉ xᵉ) ,ᵉ yᵉ))
        ( refl-htpyᵉ)
        ( refl-htpyᵉ)

    reassociate'ᵉ :
      Σᵉ ( UUᵉ l1ᵉ)
        ( λ Aᵉ → Σᵉ (UUᵉ l1ᵉ) (λ Bᵉ → (Sᵉ Aᵉ ×ᵉ Tᵉ Bᵉ) ×ᵉ ((Aᵉ → Xᵉ) ×ᵉ (Bᵉ → Xᵉ)))) ≃ᵉ
      product-cauchy-series-species-typesᵉ Sᵉ Tᵉ Xᵉ
    pr1ᵉ reassociate'ᵉ (Aᵉ ,ᵉ Bᵉ ,ᵉ (sᵉ ,ᵉ tᵉ) ,ᵉ (fsᵉ ,ᵉ ftᵉ)) =
      ((Aᵉ ,ᵉ (sᵉ ,ᵉ fsᵉ)) ,ᵉ (Bᵉ ,ᵉ (tᵉ ,ᵉ ftᵉ)))
    pr2ᵉ reassociate'ᵉ =
      is-equiv-is-invertibleᵉ
        ( λ ((Aᵉ ,ᵉ (sᵉ ,ᵉ fsᵉ)) ,ᵉ (Bᵉ ,ᵉ (tᵉ ,ᵉ ftᵉ))) →
          (Aᵉ ,ᵉ Bᵉ ,ᵉ (sᵉ ,ᵉ tᵉ) ,ᵉ (fsᵉ ,ᵉ ftᵉ)))
        ( refl-htpyᵉ)
        ( refl-htpyᵉ)

  equiv-cauchy-series-cauchy-product-species-typesᵉ :
    cauchy-series-species-typesᵉ (cauchy-product-species-typesᵉ Sᵉ Tᵉ) Xᵉ ≃ᵉ
    product-cauchy-series-species-typesᵉ Sᵉ Tᵉ Xᵉ
  equiv-cauchy-series-cauchy-product-species-typesᵉ =
    ( reassociate'ᵉ) ∘eᵉ
    ( ( equiv-totᵉ
        ( λ Aᵉ →
          equiv-totᵉ
            ( λ Bᵉ →
              ( equiv-productᵉ
                ( id-equivᵉ)
                ( equiv-universal-property-coproductᵉ Xᵉ)) ∘eᵉ
              ( left-unit-law-Σ-is-contrᵉ
                ( is-torsorial-equiv'ᵉ (Aᵉ +ᵉ Bᵉ))
                ( Aᵉ +ᵉ Bᵉ ,ᵉ id-equivᵉ))))) ∘eᵉ
      ( reassociateᵉ))
```