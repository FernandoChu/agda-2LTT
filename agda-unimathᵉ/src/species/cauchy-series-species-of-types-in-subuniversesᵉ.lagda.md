# Cauchy series of species of types in a subuniverse

```agda
module species.cauchy-series-species-of-types-in-subuniversesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.functoriality-cartesian-product-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.global-subuniversesᵉ
open import foundation.postcomposition-functionsᵉ
open import foundation.propositionsᵉ
open import foundation.subuniversesᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import species.cauchy-series-species-of-typesᵉ
open import species.species-of-types-in-subuniversesᵉ
```

</details>

## Idea

Theᵉ **Cauchyᵉ series**ᵉ ofᵉ aᵉ speciesᵉ `S`ᵉ ofᵉ typesᵉ in subuniverseᵉ fromᵉ `P`ᵉ to `Q`ᵉ
atᵉ `X`ᵉ isᵉ definedᵉ asᵉ :

```text
Σᵉ (Uᵉ : type-subuniverseᵉ Pᵉ) (S(Uᵉ) ×ᵉ (Uᵉ → Xᵉ))
```

## Definition

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level}
  (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ)
  (Qᵉ : subuniverseᵉ l3ᵉ l4ᵉ)
  (Sᵉ : species-subuniverseᵉ Pᵉ Qᵉ)
  (Xᵉ : UUᵉ l5ᵉ)
  where

  cauchy-series-species-subuniverseᵉ :
    UUᵉ (lsuc l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l5ᵉ)
  cauchy-series-species-subuniverseᵉ =
    Σᵉ ( type-subuniverseᵉ Pᵉ)
      ( λ Uᵉ → inclusion-subuniverseᵉ Qᵉ (Sᵉ Uᵉ) ×ᵉ (inclusion-subuniverseᵉ Pᵉ Uᵉ → Xᵉ))
```

## Property

### Equivalent form with species of types

```agda
  equiv-cauchy-series-Σ-extension-species-subuniverseᵉ :
    cauchy-series-species-subuniverseᵉ ≃ᵉ
    cauchy-series-species-typesᵉ (Σ-extension-species-subuniverseᵉ Pᵉ Qᵉ Sᵉ) Xᵉ
  equiv-cauchy-series-Σ-extension-species-subuniverseᵉ =
    ( equiv-totᵉ
      ( λ Uᵉ →
        inv-associative-Σᵉ
          ( type-Propᵉ (Pᵉ Uᵉ))
          ( λ pᵉ → inclusion-subuniverseᵉ Qᵉ (Sᵉ (Uᵉ ,ᵉ pᵉ)))
          ( λ _ → Uᵉ → Xᵉ))) ∘eᵉ
    ( associative-Σᵉ
      ( UUᵉ l1ᵉ)
      ( λ Uᵉ → type-Propᵉ (Pᵉ Uᵉ))
      ( λ Uᵉ → Σᵉ ( inclusion-subuniverseᵉ Qᵉ (Sᵉ Uᵉ)) (λ _ → pr1ᵉ Uᵉ → Xᵉ)))
```

### Equivalences

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level}
  (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ)
  (Qᵉ : global-subuniverseᵉ (λ lᵉ → lᵉ))
  (Sᵉ : species-subuniverseᵉ Pᵉ (subuniverse-global-subuniverseᵉ Qᵉ l3ᵉ))
  (Tᵉ : species-subuniverseᵉ Pᵉ (subuniverse-global-subuniverseᵉ Qᵉ l4ᵉ))
  (fᵉ :
    (Fᵉ : type-subuniverseᵉ Pᵉ) →
    inclusion-subuniverseᵉ (subuniverse-global-subuniverseᵉ Qᵉ l3ᵉ) (Sᵉ Fᵉ) ≃ᵉ
    inclusion-subuniverseᵉ (subuniverse-global-subuniverseᵉ Qᵉ l4ᵉ) (Tᵉ Fᵉ))
  (Xᵉ : UUᵉ l5ᵉ)
  where

  equiv-cauchy-series-equiv-species-subuniverseᵉ :
    cauchy-series-species-subuniverseᵉ
      ( Pᵉ)
      ( subuniverse-global-subuniverseᵉ Qᵉ l3ᵉ)
      ( Sᵉ)
      ( Xᵉ) ≃ᵉ
    cauchy-series-species-subuniverseᵉ
      ( Pᵉ)
      ( subuniverse-global-subuniverseᵉ Qᵉ l4ᵉ)
      ( Tᵉ)
      ( Xᵉ)
  equiv-cauchy-series-equiv-species-subuniverseᵉ =
    equiv-totᵉ λ Xᵉ → equiv-productᵉ (fᵉ Xᵉ) id-equivᵉ

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level}
  (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ)
  (Qᵉ : subuniverseᵉ l3ᵉ l4ᵉ)
  (Sᵉ : species-subuniverseᵉ Pᵉ Qᵉ)
  (Xᵉ : UUᵉ l5ᵉ)
  (Yᵉ : UUᵉ l6ᵉ)
  (eᵉ : Xᵉ ≃ᵉ Yᵉ)
  where

  equiv-cauchy-series-species-subuniverseᵉ :
    cauchy-series-species-subuniverseᵉ Pᵉ Qᵉ Sᵉ Xᵉ ≃ᵉ
    cauchy-series-species-subuniverseᵉ Pᵉ Qᵉ Sᵉ Yᵉ
  equiv-cauchy-series-species-subuniverseᵉ =
    equiv-totᵉ
      ( λ Fᵉ →
        equiv-productᵉ id-equivᵉ (equiv-postcompᵉ (inclusion-subuniverseᵉ Pᵉ Fᵉ) eᵉ))
```