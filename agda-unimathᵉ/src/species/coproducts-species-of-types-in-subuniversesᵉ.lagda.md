# Coproducts of species of types in subuniverses

```agda
module species.coproducts-species-of-types-in-subuniversesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.coproduct-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.global-subuniversesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.subuniversesᵉ
open import foundation.universe-levelsᵉ

open import species.coproducts-species-of-typesᵉ
open import species.species-of-types-in-subuniversesᵉ
```

</details>

## Idea

Theᵉ coproductᵉ ofᵉ twoᵉ speciesᵉ ofᵉ typesᵉ ofᵉ subuniverseᵉ `F`ᵉ andᵉ `G`ᵉ isᵉ theᵉ
pointwiseᵉ coproductᵉ providedᵉ thatᵉ theᵉ domainᵉ subuniverseᵉ ofᵉ `F`ᵉ andᵉ `G`ᵉ isᵉ
stableᵉ byᵉ coproduct.ᵉ

## Definitions

### The underlying type of the coproduct of species of types in a subuniverse

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ)
  (Qᵉ : global-subuniverseᵉ (λ lᵉ → lᵉ))
  where

  type-coproduct-species-subuniverseᵉ :
    (Sᵉ : species-subuniverseᵉ Pᵉ (subuniverse-global-subuniverseᵉ Qᵉ l3ᵉ))
    (Tᵉ : species-subuniverseᵉ Pᵉ (subuniverse-global-subuniverseᵉ Qᵉ l4ᵉ))
    (Xᵉ : type-subuniverseᵉ Pᵉ) → UUᵉ (l3ᵉ ⊔ l4ᵉ)
  type-coproduct-species-subuniverseᵉ Sᵉ Tᵉ Xᵉ =
    inclusion-subuniverseᵉ
      ( subuniverse-global-subuniverseᵉ Qᵉ l3ᵉ)
      ( Sᵉ Xᵉ) +ᵉ
    inclusion-subuniverseᵉ
      ( subuniverse-global-subuniverseᵉ Qᵉ l4ᵉ)
      ( Tᵉ Xᵉ)
```

### Subuniverses closed under the coproduct of two species of types in a subuniverse

```agda
is-closed-under-coproduct-species-subuniverseᵉ :
  {l1ᵉ l2ᵉ : Level} (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ) (Qᵉ : global-subuniverseᵉ (λ lᵉ → lᵉ)) →
  UUωᵉ
is-closed-under-coproduct-species-subuniverseᵉ Pᵉ Qᵉ =
  {l3ᵉ l4ᵉ : Level}
  (Sᵉ : species-subuniverseᵉ Pᵉ (subuniverse-global-subuniverseᵉ Qᵉ l3ᵉ))
  (Tᵉ : species-subuniverseᵉ Pᵉ (subuniverse-global-subuniverseᵉ Qᵉ l4ᵉ))
  (Xᵉ : type-subuniverseᵉ Pᵉ) →
  is-in-subuniverseᵉ
    ( subuniverse-global-subuniverseᵉ Qᵉ (l3ᵉ ⊔ l4ᵉ))
    ( type-coproduct-species-subuniverseᵉ Pᵉ Qᵉ Sᵉ Tᵉ Xᵉ)
```

### The coproduct of two species of types in a subuniverse

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ)
  (Qᵉ : global-subuniverseᵉ (λ lᵉ → lᵉ))
  ( C1ᵉ : is-closed-under-coproduct-species-subuniverseᵉ Pᵉ Qᵉ)
  where

  coproduct-species-subuniverseᵉ :
    species-subuniverseᵉ Pᵉ (subuniverse-global-subuniverseᵉ Qᵉ l3ᵉ) →
    species-subuniverseᵉ Pᵉ (subuniverse-global-subuniverseᵉ Qᵉ l4ᵉ) →
    species-subuniverseᵉ Pᵉ (subuniverse-global-subuniverseᵉ Qᵉ (l3ᵉ ⊔ l4ᵉ))
  pr1ᵉ (coproduct-species-subuniverseᵉ Sᵉ Tᵉ Xᵉ) =
    type-coproduct-species-subuniverseᵉ Pᵉ Qᵉ Sᵉ Tᵉ Xᵉ
  pr2ᵉ (coproduct-species-subuniverseᵉ Sᵉ Tᵉ Xᵉ) = C1ᵉ Sᵉ Tᵉ Xᵉ
```

## Properties

### Equivalent form with species of types

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ)
  ( Qᵉ : global-subuniverseᵉ (λ lᵉ → lᵉ))
  ( C1ᵉ : is-closed-under-coproduct-species-subuniverseᵉ Pᵉ Qᵉ)
  ( Sᵉ : species-subuniverseᵉ Pᵉ (subuniverse-global-subuniverseᵉ Qᵉ l3ᵉ))
  ( Tᵉ : species-subuniverseᵉ Pᵉ (subuniverse-global-subuniverseᵉ Qᵉ l4ᵉ))
  ( Xᵉ : UUᵉ l1ᵉ)
  where

  map-coproduct-Σ-extension-species-subuniverseᵉ :
    Σ-extension-species-subuniverseᵉ
      ( Pᵉ)
      ( subuniverse-global-subuniverseᵉ Qᵉ (l3ᵉ ⊔ l4ᵉ))
      ( coproduct-species-subuniverseᵉ Pᵉ Qᵉ C1ᵉ Sᵉ Tᵉ)
      ( Xᵉ) →
    coproduct-species-typesᵉ
      ( Σ-extension-species-subuniverseᵉ
          ( Pᵉ)
          ( subuniverse-global-subuniverseᵉ Qᵉ l3ᵉ)
          ( Sᵉ))
      ( Σ-extension-species-subuniverseᵉ
          ( Pᵉ)
          ( subuniverse-global-subuniverseᵉ Qᵉ l4ᵉ)
          ( Tᵉ))
      ( Xᵉ)
  map-coproduct-Σ-extension-species-subuniverseᵉ (pᵉ ,ᵉ inlᵉ xᵉ) = inlᵉ ( pᵉ ,ᵉ xᵉ)
  map-coproduct-Σ-extension-species-subuniverseᵉ (pᵉ ,ᵉ inrᵉ xᵉ) = inrᵉ ( pᵉ ,ᵉ xᵉ)

  map-inv-coproduct-Σ-extension-species-subuniverseᵉ :
    coproduct-species-typesᵉ
      ( Σ-extension-species-subuniverseᵉ
          ( Pᵉ)
          ( subuniverse-global-subuniverseᵉ Qᵉ l3ᵉ)
          ( Sᵉ))
      ( Σ-extension-species-subuniverseᵉ
          ( Pᵉ)
          ( subuniverse-global-subuniverseᵉ Qᵉ l4ᵉ)
          ( Tᵉ))
      ( Xᵉ) →
    Σ-extension-species-subuniverseᵉ
      ( Pᵉ)
      ( subuniverse-global-subuniverseᵉ Qᵉ (l3ᵉ ⊔ l4ᵉ))
      ( coproduct-species-subuniverseᵉ Pᵉ Qᵉ C1ᵉ Sᵉ Tᵉ)
      ( Xᵉ)
  map-inv-coproduct-Σ-extension-species-subuniverseᵉ (inlᵉ xᵉ) =
    pr1ᵉ xᵉ ,ᵉ inlᵉ (pr2ᵉ xᵉ)
  map-inv-coproduct-Σ-extension-species-subuniverseᵉ (inrᵉ xᵉ) =
    pr1ᵉ xᵉ ,ᵉ inrᵉ (pr2ᵉ xᵉ)

  is-section-map-inv-coproduct-Σ-extension-species-subuniverseᵉ :
    ( map-coproduct-Σ-extension-species-subuniverseᵉ ∘ᵉ
      map-inv-coproduct-Σ-extension-species-subuniverseᵉ) ~ᵉ idᵉ
  is-section-map-inv-coproduct-Σ-extension-species-subuniverseᵉ (inlᵉ (pᵉ ,ᵉ xᵉ)) =
    reflᵉ
  is-section-map-inv-coproduct-Σ-extension-species-subuniverseᵉ (inrᵉ (pᵉ ,ᵉ xᵉ)) =
    reflᵉ

  is-retraction-map-inv-coproduct-Σ-extension-species-subuniverseᵉ :
    ( map-inv-coproduct-Σ-extension-species-subuniverseᵉ ∘ᵉ
      map-coproduct-Σ-extension-species-subuniverseᵉ) ~ᵉ
    idᵉ
  is-retraction-map-inv-coproduct-Σ-extension-species-subuniverseᵉ (pᵉ ,ᵉ inlᵉ xᵉ) =
    reflᵉ
  is-retraction-map-inv-coproduct-Σ-extension-species-subuniverseᵉ (pᵉ ,ᵉ inrᵉ xᵉ) =
    reflᵉ

  equiv-coproduct-Σ-extension-species-subuniverseᵉ :
    Σ-extension-species-subuniverseᵉ
      ( Pᵉ)
      ( subuniverse-global-subuniverseᵉ Qᵉ (l3ᵉ ⊔ l4ᵉ))
      ( coproduct-species-subuniverseᵉ Pᵉ Qᵉ C1ᵉ Sᵉ Tᵉ)
      ( Xᵉ) ≃ᵉ
    coproduct-species-typesᵉ
      ( Σ-extension-species-subuniverseᵉ
          ( Pᵉ)
          ( subuniverse-global-subuniverseᵉ Qᵉ l3ᵉ)
          ( Sᵉ))
      ( Σ-extension-species-subuniverseᵉ
          ( Pᵉ)
          ( subuniverse-global-subuniverseᵉ Qᵉ l4ᵉ)
          ( Tᵉ))
      ( Xᵉ)
  pr1ᵉ equiv-coproduct-Σ-extension-species-subuniverseᵉ =
    map-coproduct-Σ-extension-species-subuniverseᵉ
  pr2ᵉ equiv-coproduct-Σ-extension-species-subuniverseᵉ =
    is-equiv-is-invertibleᵉ
      map-inv-coproduct-Σ-extension-species-subuniverseᵉ
      is-section-map-inv-coproduct-Σ-extension-species-subuniverseᵉ
      is-retraction-map-inv-coproduct-Σ-extension-species-subuniverseᵉ
```