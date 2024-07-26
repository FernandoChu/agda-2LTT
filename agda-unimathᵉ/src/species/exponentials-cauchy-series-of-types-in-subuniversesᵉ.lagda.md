# Exponential of Cauchy series of species of types in subuniverses

```agda
module species.exponentials-cauchy-series-of-types-in-subuniversesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.global-subuniversesᵉ
open import foundation.sigma-closed-subuniversesᵉ
open import foundation.subuniversesᵉ
open import foundation.type-arithmetic-cartesian-product-typesᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import species.cauchy-composition-species-of-types-in-subuniversesᵉ
open import species.cauchy-exponentials-species-of-types-in-subuniversesᵉ
open import species.cauchy-series-species-of-types-in-subuniversesᵉ
open import species.composition-cauchy-series-species-of-types-in-subuniversesᵉ
open import species.species-of-types-in-subuniversesᵉ
```

</details>

## Definition

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level}
  (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ)
  (Qᵉ : subuniverseᵉ l3ᵉ l4ᵉ)
  (Sᵉ : species-subuniverseᵉ Pᵉ Qᵉ)
  (Xᵉ : UUᵉ l5ᵉ)
  where

  exponential-cauchy-series-species-subuniverseᵉ :
    UUᵉ (lsuc l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l5ᵉ)
  exponential-cauchy-series-species-subuniverseᵉ =
    Σᵉ ( type-subuniverseᵉ Pᵉ)
      ( λ Fᵉ →
        inclusion-subuniverseᵉ Pᵉ Fᵉ →
        Σᵉ ( type-subuniverseᵉ Pᵉ)
          ( λ Uᵉ →
            ( inclusion-subuniverseᵉ Qᵉ (Sᵉ Uᵉ)) ×ᵉ
            ( inclusion-subuniverseᵉ Pᵉ Uᵉ → Xᵉ)))
```

## Property

### The exponential of a Cauchy series as a composition

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l5ᵉ : Level}
  (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ)
  (Qᵉ : global-subuniverseᵉ (λ lᵉ → lᵉ))
  (Cᵉ : is-in-subuniverseᵉ (subuniverse-global-subuniverseᵉ Qᵉ lzero) unitᵉ)
  (Sᵉ : species-subuniverseᵉ Pᵉ (subuniverse-global-subuniverseᵉ Qᵉ l3ᵉ))
  (Xᵉ : UUᵉ l5ᵉ)
  where

  equiv-exponential-cauchy-series-composition-unit-species-subuniverseᵉ :
    composition-cauchy-series-species-subuniverseᵉ Pᵉ Qᵉ (λ _ → unitᵉ ,ᵉ Cᵉ) Sᵉ Xᵉ ≃ᵉ
    exponential-cauchy-series-species-subuniverseᵉ
      ( Pᵉ)
      ( subuniverse-global-subuniverseᵉ Qᵉ l3ᵉ)
      ( Sᵉ)
      ( Xᵉ)
  equiv-exponential-cauchy-series-composition-unit-species-subuniverseᵉ =
    equiv-totᵉ (λ Fᵉ → left-unit-law-product-is-contrᵉ is-contr-unitᵉ)
```

### The Cauchy series associated to the Cauchy exponential of `S` is equal to the exponential of its Cauchy series

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ)
  (Qᵉ : global-subuniverseᵉ (λ lᵉ → lᵉ))
  (C1ᵉ : is-closed-under-cauchy-exponential-species-subuniverseᵉ Pᵉ Qᵉ)
  (C2ᵉ : is-in-subuniverseᵉ (subuniverse-global-subuniverseᵉ Qᵉ lzero) unitᵉ)
  (C3ᵉ : is-closed-under-cauchy-composition-species-subuniverseᵉ Pᵉ Qᵉ)
  (C4ᵉ : is-closed-under-Σ-subuniverseᵉ Pᵉ)
  (Sᵉ : species-subuniverseᵉ Pᵉ (subuniverse-global-subuniverseᵉ Qᵉ l3ᵉ))
  (Xᵉ : UUᵉ l4ᵉ)
  where

  equiv-cauchy-series-cauchy-exponential-species-subuniverseᵉ :
    cauchy-series-species-subuniverseᵉ Pᵉ
      ( subuniverse-global-subuniverseᵉ Qᵉ (lsuc l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ))
      ( cauchy-exponential-species-subuniverseᵉ Pᵉ Qᵉ C1ᵉ Sᵉ)
      ( Xᵉ) ≃ᵉ
    exponential-cauchy-series-species-subuniverseᵉ Pᵉ
      ( subuniverse-global-subuniverseᵉ Qᵉ l3ᵉ)
      ( Sᵉ)
      ( Xᵉ)
  equiv-cauchy-series-cauchy-exponential-species-subuniverseᵉ =
    ( equiv-exponential-cauchy-series-composition-unit-species-subuniverseᵉ
      ( Pᵉ)
      ( Qᵉ)
      ( C2ᵉ)
      ( Sᵉ)
      ( Xᵉ)) ∘eᵉ
    ( ( equiv-cauchy-series-composition-species-subuniverseᵉ Pᵉ Qᵉ C3ᵉ C4ᵉ
        ( λ _ → unitᵉ ,ᵉ C2ᵉ)
        ( Sᵉ)
        ( Xᵉ)) ∘eᵉ
      ( equiv-cauchy-series-equiv-species-subuniverseᵉ Pᵉ Qᵉ
        ( cauchy-exponential-species-subuniverseᵉ Pᵉ Qᵉ C1ᵉ Sᵉ)
        ( cauchy-composition-species-subuniverseᵉ Pᵉ Qᵉ C3ᵉ C4ᵉ
          ( λ _ → unitᵉ ,ᵉ C2ᵉ)
          ( Sᵉ))
        ( λ Fᵉ →
          inv-equivᵉ
            ( equiv-cauchy-exponential-composition-unit-species-subuniverseᵉ
              ( Pᵉ)
              ( Qᵉ)
              ( C1ᵉ)
              ( C2ᵉ)
              ( C3ᵉ)
              ( C4ᵉ)
              ( Sᵉ)
              ( Fᵉ)))
        ( Xᵉ)))
```