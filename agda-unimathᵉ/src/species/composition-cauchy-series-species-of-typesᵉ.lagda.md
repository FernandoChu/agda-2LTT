# Composition of Cauchy series of species of types

```agda
module species.composition-cauchy-series-species-of-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.functoriality-cartesian-product-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.type-theoretic-principle-of-choiceᵉ
open import foundation.univalenceᵉ
open import foundation.universal-property-cartesian-product-typesᵉ
open import foundation.universal-property-dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import species.cauchy-composition-species-of-typesᵉ
open import species.cauchy-series-species-of-typesᵉ
open import species.species-of-typesᵉ
```

</details>

## Idea

Theᵉ compositionᵉ ofᵉ Cauchyᵉ seriesᵉ ofᵉ twoᵉ speciesᵉ ofᵉ typesᵉ `S`ᵉ andᵉ `T`ᵉ atᵉ `X`ᵉ isᵉ
definedᵉ asᵉ theᵉ Cauchyᵉ seriesᵉ ofᵉ `S`ᵉ appliedᵉ to theᵉ Cauchyᵉ seriesᵉ ofᵉ `T`ᵉ atᵉ `X`ᵉ

## Definition

```agda
composition-cauchy-series-species-typesᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} → species-typesᵉ l1ᵉ l2ᵉ → species-typesᵉ l1ᵉ l3ᵉ →
  UUᵉ l4ᵉ → UUᵉ (lsuc l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
composition-cauchy-series-species-typesᵉ Sᵉ Tᵉ Xᵉ =
  cauchy-series-species-typesᵉ Sᵉ (cauchy-series-species-typesᵉ Tᵉ Xᵉ)
```

## Property

### The Cauchy series associated to the composition of the species `S` and `T` is the composition of their Cauchy series

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Sᵉ : species-typesᵉ l1ᵉ l2ᵉ)
  (Tᵉ : species-typesᵉ l1ᵉ l3ᵉ)
  (Xᵉ : UUᵉ l4ᵉ)
  where

  private
    reassociateᵉ :
      cauchy-series-species-typesᵉ (cauchy-composition-species-typesᵉ Sᵉ Tᵉ) Xᵉ ≃ᵉ
      Σᵉ ( UUᵉ l1ᵉ)
        ( λ Uᵉ →
          Σᵉ ( Uᵉ → UUᵉ l1ᵉ)
            ( λ Vᵉ →
              Σᵉ ( Σᵉ ( UUᵉ l1ᵉ) (λ Fᵉ → Fᵉ ≃ᵉ Σᵉ Uᵉ Vᵉ))
                ( λ Fᵉ → (Sᵉ Uᵉ) ×ᵉ (((yᵉ : Uᵉ) → Tᵉ (Vᵉ yᵉ)) ×ᵉ (pr1ᵉ Fᵉ → Xᵉ)))))
    pr1ᵉ reassociateᵉ (Fᵉ ,ᵉ ((Uᵉ ,ᵉ Vᵉ ,ᵉ eᵉ) ,ᵉ sᵉ ,ᵉ fsᵉ) ,ᵉ ftᵉ) =
      (Uᵉ ,ᵉ Vᵉ ,ᵉ (Fᵉ ,ᵉ eᵉ) ,ᵉ sᵉ ,ᵉ fsᵉ ,ᵉ ftᵉ)
    pr2ᵉ reassociateᵉ =
      is-equiv-is-invertibleᵉ
        ( λ (Uᵉ ,ᵉ Vᵉ ,ᵉ (Fᵉ ,ᵉ eᵉ) ,ᵉ sᵉ ,ᵉ fsᵉ ,ᵉ ftᵉ) →
          (Fᵉ ,ᵉ ((Uᵉ ,ᵉ Vᵉ ,ᵉ eᵉ) ,ᵉ sᵉ ,ᵉ fsᵉ) ,ᵉ ftᵉ))
        ( refl-htpyᵉ)
        ( refl-htpyᵉ)

  equiv-cauchy-series-composition-species-typesᵉ :
    cauchy-series-species-typesᵉ
      ( cauchy-composition-species-typesᵉ Sᵉ Tᵉ)
      ( Xᵉ) ≃ᵉ
    composition-cauchy-series-species-typesᵉ Sᵉ Tᵉ Xᵉ
  equiv-cauchy-series-composition-species-typesᵉ =
    ( equiv-totᵉ
      ( λ Uᵉ →
        ( equiv-productᵉ
          ( id-equivᵉ)
          ( inv-equivᵉ distributive-Π-Σᵉ)) ∘eᵉ
        ( ( inv-equivᵉ left-distributive-product-Σᵉ) ∘eᵉ
          ( equiv-totᵉ
            ( λ Vᵉ →
              ( equiv-productᵉ
                ( id-equivᵉ)
                ( ( inv-equivᵉ equiv-up-productᵉ) ∘eᵉ
                  ( equiv-productᵉ id-equivᵉ equiv-ev-pairᵉ))) ∘eᵉ
              ( left-unit-law-Σ-is-contrᵉ
                ( is-torsorial-equiv'ᵉ (Σᵉ Uᵉ Vᵉ))
                ( Σᵉ Uᵉ Vᵉ ,ᵉ id-equivᵉ))))))) ∘eᵉ
      ( reassociateᵉ)
```