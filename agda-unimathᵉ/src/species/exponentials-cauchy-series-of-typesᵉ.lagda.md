# Exponential of Cauchy series of species of types

```agda
module species.exponentials-cauchy-series-of-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.type-arithmetic-cartesian-product-typesᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import species.cauchy-composition-species-of-typesᵉ
open import species.cauchy-exponentials-species-of-typesᵉ
open import species.cauchy-series-species-of-typesᵉ
open import species.composition-cauchy-series-species-of-typesᵉ
open import species.species-of-typesᵉ
```

</details>

## Definition

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level}
  (Sᵉ : species-typesᵉ l1ᵉ l2ᵉ)
  (Xᵉ : UUᵉ l3ᵉ)
  where

  exponential-cauchy-series-species-typesᵉ :
    UUᵉ (lsuc l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  exponential-cauchy-series-species-typesᵉ =
    Σᵉ ( UUᵉ l1ᵉ)
      ( λ Fᵉ → Fᵉ → (Σᵉ ( UUᵉ l1ᵉ) (λ Uᵉ → Sᵉ Uᵉ ×ᵉ (Uᵉ → Xᵉ))))
```

## Properties

### The exponential of a Cauchy series as a composition

```agda
  equiv-exponential-cauchy-series-composition-unit-species-typesᵉ :
    composition-cauchy-series-species-typesᵉ (λ _ → unitᵉ) Sᵉ Xᵉ ≃ᵉ
    exponential-cauchy-series-species-typesᵉ
  equiv-exponential-cauchy-series-composition-unit-species-typesᵉ =
    equiv-totᵉ λ Fᵉ → left-unit-law-product-is-contrᵉ is-contr-unitᵉ
```

### The Cauchy series associated to the Cauchy exponential of `S` is equal to the exponential of its Cauchy series

```agda
  equiv-cauchy-series-cauchy-exponential-species-typesᵉ :
    cauchy-series-species-typesᵉ (cauchy-exponential-species-typesᵉ Sᵉ) Xᵉ ≃ᵉ
    exponential-cauchy-series-species-typesᵉ
  equiv-cauchy-series-cauchy-exponential-species-typesᵉ =
    ( equiv-exponential-cauchy-series-composition-unit-species-typesᵉ) ∘eᵉ
    ( ( equiv-cauchy-series-composition-species-typesᵉ (λ _ → unitᵉ) Sᵉ Xᵉ) ∘eᵉ
      ( equiv-cauchy-series-equiv-species-typesᵉ
        ( cauchy-exponential-species-typesᵉ Sᵉ)
        ( cauchy-composition-species-typesᵉ (λ _ → unitᵉ) Sᵉ)
        ( λ Fᵉ →
          inv-equivᵉ
            ( equiv-cauchy-exponential-composition-unit-species-typesᵉ Sᵉ Fᵉ))
            ( Xᵉ)))
```