# Composition of Cauchy series of species of types in subuniverses

```agda
module species.composition-cauchy-series-species-of-types-in-subuniversesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.equivalencesᵉ
open import foundation.global-subuniversesᵉ
open import foundation.sigma-closed-subuniversesᵉ
open import foundation.subuniversesᵉ
open import foundation.universe-levelsᵉ

open import species.cauchy-composition-species-of-typesᵉ
open import species.cauchy-composition-species-of-types-in-subuniversesᵉ
open import species.cauchy-series-species-of-typesᵉ
open import species.cauchy-series-species-of-types-in-subuniversesᵉ
open import species.composition-cauchy-series-species-of-typesᵉ
open import species.species-of-types-in-subuniversesᵉ
```

</details>

## Idea

Theᵉ compositionᵉ ofᵉ Cauchyᵉ seriesᵉ ofᵉ twoᵉ speciesᵉ ofᵉ subuniverseᵉ `S`ᵉ andᵉ `T`ᵉ atᵉ
`X`ᵉ isᵉ definedᵉ asᵉ theᵉ Cauchyᵉ seriesᵉ ofᵉ `S`ᵉ appliedᵉ to theᵉ Cauchyᵉ seriesᵉ ofᵉ `T`ᵉ
atᵉ `X`ᵉ

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

  composition-cauchy-series-species-subuniverseᵉ :
    UUᵉ (lsuc l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ ⊔ l5ᵉ)
  composition-cauchy-series-species-subuniverseᵉ =
    cauchy-series-species-subuniverseᵉ
      ( Pᵉ)
      ( subuniverse-global-subuniverseᵉ Qᵉ l3ᵉ)
      ( Sᵉ)
      ( cauchy-series-species-subuniverseᵉ
        ( Pᵉ)
        ( subuniverse-global-subuniverseᵉ Qᵉ l4ᵉ)
        ( Tᵉ)
        ( Xᵉ))
```

## Property

### Equivalent form with species of types

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level}
  (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ)
  (Qᵉ : global-subuniverseᵉ (λ lᵉ → lᵉ))
  (Sᵉ : species-subuniverseᵉ Pᵉ (subuniverse-global-subuniverseᵉ Qᵉ l3ᵉ))
  (Tᵉ : species-subuniverseᵉ Pᵉ (subuniverse-global-subuniverseᵉ Qᵉ l4ᵉ))
  (Xᵉ : UUᵉ l5ᵉ)
  where

  equiv-composition-cauchy-series-Σ-extension-species-subuniverseᵉ :
    composition-cauchy-series-species-typesᵉ
      ( Σ-extension-species-subuniverseᵉ
        ( Pᵉ)
        ( subuniverse-global-subuniverseᵉ Qᵉ l3ᵉ)
        ( Sᵉ))
      ( Σ-extension-species-subuniverseᵉ
        ( Pᵉ)
        ( subuniverse-global-subuniverseᵉ Qᵉ l4ᵉ)
        ( Tᵉ))
      ( Xᵉ) ≃ᵉ
    composition-cauchy-series-species-subuniverseᵉ Pᵉ Qᵉ Sᵉ Tᵉ Xᵉ
  equiv-composition-cauchy-series-Σ-extension-species-subuniverseᵉ =
    ( inv-equivᵉ
      ( equiv-cauchy-series-Σ-extension-species-subuniverseᵉ
        ( Pᵉ)
        ( subuniverse-global-subuniverseᵉ Qᵉ l3ᵉ)
        ( Sᵉ)
        ( cauchy-series-species-subuniverseᵉ
          ( Pᵉ)
          ( subuniverse-global-subuniverseᵉ Qᵉ l4ᵉ)
          ( Tᵉ)
          ( Xᵉ)))) ∘eᵉ
      ( equiv-cauchy-series-species-typesᵉ
        ( Σ-extension-species-subuniverseᵉ
          ( Pᵉ)
          ( subuniverse-global-subuniverseᵉ Qᵉ l3ᵉ)
          ( Sᵉ))
        ( cauchy-series-species-typesᵉ
          ( Σ-extension-species-subuniverseᵉ
            ( Pᵉ)
            ( subuniverse-global-subuniverseᵉ Qᵉ l4ᵉ)
            ( Tᵉ))
          ( Xᵉ))
        ( cauchy-series-species-subuniverseᵉ
          ( Pᵉ)
          ( subuniverse-global-subuniverseᵉ Qᵉ l4ᵉ)
          ( Tᵉ)
          ( Xᵉ))
        ( inv-equivᵉ
          ( equiv-cauchy-series-Σ-extension-species-subuniverseᵉ
            ( Pᵉ)
            ( subuniverse-global-subuniverseᵉ Qᵉ l4ᵉ)
            ( Tᵉ)
            ( Xᵉ))))
```

### The Cauchy series associated to the composition of the species `S` and `T` is the composition of their Cauchy series

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level}
  (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ)
  (Qᵉ : global-subuniverseᵉ (λ lᵉ → lᵉ))
  (C1ᵉ : is-closed-under-cauchy-composition-species-subuniverseᵉ Pᵉ Qᵉ)
  (C2ᵉ : is-closed-under-Σ-subuniverseᵉ Pᵉ)
  (Sᵉ : species-subuniverseᵉ Pᵉ (subuniverse-global-subuniverseᵉ Qᵉ l3ᵉ))
  (Tᵉ : species-subuniverseᵉ Pᵉ (subuniverse-global-subuniverseᵉ Qᵉ l4ᵉ))
  (Xᵉ : UUᵉ l5ᵉ)
  where

  equiv-cauchy-series-composition-species-subuniverseᵉ :
    cauchy-series-species-subuniverseᵉ
      ( Pᵉ)
      ( subuniverse-global-subuniverseᵉ Qᵉ (lsuc l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ))
      ( cauchy-composition-species-subuniverseᵉ Pᵉ Qᵉ C1ᵉ C2ᵉ Sᵉ Tᵉ)
      ( Xᵉ) ≃ᵉ
    composition-cauchy-series-species-subuniverseᵉ Pᵉ Qᵉ Sᵉ Tᵉ Xᵉ
  equiv-cauchy-series-composition-species-subuniverseᵉ =
    ( equiv-composition-cauchy-series-Σ-extension-species-subuniverseᵉ Pᵉ Qᵉ Sᵉ Tᵉ
      ( Xᵉ)) ∘eᵉ
    ( ( equiv-cauchy-series-composition-species-typesᵉ
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
          ( Σ-extension-species-subuniverseᵉ
            ( Pᵉ)
            ( subuniverse-global-subuniverseᵉ Qᵉ (lsuc l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ))
            ( cauchy-composition-species-subuniverseᵉ Pᵉ Qᵉ C1ᵉ C2ᵉ Sᵉ Tᵉ))
          ( cauchy-composition-species-typesᵉ
            ( Σ-extension-species-subuniverseᵉ
              ( Pᵉ)
              ( subuniverse-global-subuniverseᵉ Qᵉ l3ᵉ)
              ( Sᵉ))
            ( Σ-extension-species-subuniverseᵉ
              ( Pᵉ)
              ( subuniverse-global-subuniverseᵉ Qᵉ l4ᵉ)
              ( Tᵉ)))
          ( preserves-cauchy-composition-Σ-extension-species-subuniverseᵉ
            ( Pᵉ)
            ( Qᵉ)
            ( C1ᵉ)
            ( C2ᵉ)
            ( Sᵉ)
            ( Tᵉ))
          ( Xᵉ)) ∘eᵉ
        ( equiv-cauchy-series-Σ-extension-species-subuniverseᵉ
          ( Pᵉ)
          ( subuniverse-global-subuniverseᵉ Qᵉ (lsuc l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ))
          ( cauchy-composition-species-subuniverseᵉ Pᵉ Qᵉ C1ᵉ C2ᵉ Sᵉ Tᵉ)
          ( Xᵉ))))
```