# Species of types in subuniverses

```agda
module species.species-of-types-in-subuniversesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.propositionsᵉ
open import foundation.subuniversesᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import species.species-of-typesᵉ
```

</details>

### Idea

Aᵉ **speciesᵉ ofᵉ typesᵉ in aᵉ subuniverse**ᵉ isᵉ aᵉ mapᵉ fromᵉ aᵉ subuniverseᵉ `P`ᵉ to aᵉ
subuniverseᵉ `Q`.ᵉ

## Definitions

### Species of types in subuniverses

```agda
species-subuniverseᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} → subuniverseᵉ l1ᵉ l2ᵉ → subuniverseᵉ l3ᵉ l4ᵉ →
  UUᵉ (lsuc l1ᵉ ⊔ l2ᵉ ⊔ lsuc l3ᵉ ⊔ l4ᵉ)
species-subuniverseᵉ Pᵉ Qᵉ = type-subuniverseᵉ Pᵉ → type-subuniverseᵉ Qᵉ

species-subuniverse-domainᵉ :
  {l1ᵉ l2ᵉ : Level} (l3ᵉ : Level) → subuniverseᵉ l1ᵉ l2ᵉ →
  UUᵉ (lsuc l1ᵉ ⊔ l2ᵉ ⊔ lsuc l3ᵉ)
species-subuniverse-domainᵉ l3ᵉ Pᵉ = type-subuniverseᵉ Pᵉ → UUᵉ l3ᵉ
```

### The predicate that a species preserves cartesian products

```agda
preserves-product-species-subuniverse-domainᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ)
  (Cᵉ : is-closed-under-products-subuniverseᵉ Pᵉ)
  (Sᵉ : species-subuniverse-domainᵉ l3ᵉ Pᵉ) →
  UUᵉ (lsuc l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
preserves-product-species-subuniverse-domainᵉ Pᵉ Cᵉ Sᵉ =
  ( Xᵉ Yᵉ : type-subuniverseᵉ Pᵉ) →
  Sᵉ
    ( inclusion-subuniverseᵉ Pᵉ Xᵉ ×ᵉ inclusion-subuniverseᵉ Pᵉ Yᵉ ,ᵉ
      Cᵉ
        ( is-in-subuniverse-inclusion-subuniverseᵉ Pᵉ Xᵉ)
        ( is-in-subuniverse-inclusion-subuniverseᵉ Pᵉ Yᵉ)) ≃ᵉ
  (Sᵉ Xᵉ ×ᵉ Sᵉ Yᵉ)
```

### Transport along equivalences of in species of types in subuniverses

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ) (Qᵉ : subuniverseᵉ l3ᵉ l4ᵉ)
  (Fᵉ : species-subuniverseᵉ Pᵉ Qᵉ)
  where

  tr-species-subuniverseᵉ :
    (Xᵉ Yᵉ : type-subuniverseᵉ Pᵉ) →
    inclusion-subuniverseᵉ Pᵉ Xᵉ ≃ᵉ inclusion-subuniverseᵉ Pᵉ Yᵉ →
    inclusion-subuniverseᵉ Qᵉ (Fᵉ Xᵉ) → inclusion-subuniverseᵉ Qᵉ (Fᵉ Yᵉ)
  tr-species-subuniverseᵉ Xᵉ Yᵉ eᵉ =
    trᵉ (inclusion-subuniverseᵉ Qᵉ ∘ᵉ Fᵉ) (eq-equiv-subuniverseᵉ Pᵉ eᵉ)
```

### Σ-extension to species of types in subuniverses

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ) (Qᵉ : subuniverseᵉ l3ᵉ l4ᵉ)
  (Fᵉ : species-subuniverseᵉ Pᵉ Qᵉ)
  where

  Σ-extension-species-subuniverseᵉ :
    species-typesᵉ l1ᵉ (l2ᵉ ⊔ l3ᵉ)
  Σ-extension-species-subuniverseᵉ Xᵉ =
    Σᵉ (is-in-subuniverseᵉ Pᵉ Xᵉ) (λ pᵉ → inclusion-subuniverseᵉ Qᵉ (Fᵉ (Xᵉ ,ᵉ pᵉ)))

  equiv-Σ-extension-species-subuniverseᵉ :
    ( Xᵉ : type-subuniverseᵉ Pᵉ) →
    inclusion-subuniverseᵉ Qᵉ (Fᵉ Xᵉ) ≃ᵉ
    Σ-extension-species-subuniverseᵉ (inclusion-subuniverseᵉ Pᵉ Xᵉ)
  equiv-Σ-extension-species-subuniverseᵉ Xᵉ =
    inv-left-unit-law-Σ-is-contrᵉ
      ( is-proof-irrelevant-is-propᵉ
        ( is-subtype-subuniverseᵉ Pᵉ (inclusion-subuniverseᵉ Pᵉ Xᵉ))
        ( pr2ᵉ Xᵉ))
      ( pr2ᵉ Xᵉ)
```

### Σ-extension to species with domain in a subuniverse

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ)
  (Fᵉ : species-subuniverse-domainᵉ l3ᵉ Pᵉ)
  where

  Σ-extension-species-subuniverse-domainᵉ :
    species-typesᵉ l1ᵉ (l2ᵉ ⊔ l3ᵉ)
  Σ-extension-species-subuniverse-domainᵉ Xᵉ =
    Σᵉ (is-in-subuniverseᵉ Pᵉ Xᵉ) (λ pᵉ → (Fᵉ (Xᵉ ,ᵉ pᵉ)))

  equiv-Σ-extension-species-subuniverse-domainᵉ :
    ( Xᵉ : type-subuniverseᵉ Pᵉ) →
    Fᵉ Xᵉ ≃ᵉ
    Σ-extension-species-subuniverse-domainᵉ (inclusion-subuniverseᵉ Pᵉ Xᵉ)
  equiv-Σ-extension-species-subuniverse-domainᵉ Xᵉ =
    inv-left-unit-law-Σ-is-contrᵉ
      ( is-proof-irrelevant-is-propᵉ
        ( is-subtype-subuniverseᵉ Pᵉ (inclusion-subuniverseᵉ Pᵉ Xᵉ))
        ( pr2ᵉ Xᵉ))
      ( pr2ᵉ Xᵉ)
```

### Π-extension to species of types in subuniverses

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ) (Qᵉ : subuniverseᵉ l3ᵉ l4ᵉ)
  (Sᵉ : species-subuniverseᵉ Pᵉ Qᵉ)
  where

  Π-extension-species-subuniverseᵉ :
    species-typesᵉ l1ᵉ (l2ᵉ ⊔ l3ᵉ)
  Π-extension-species-subuniverseᵉ Xᵉ =
    (pᵉ : is-in-subuniverseᵉ Pᵉ Xᵉ) → inclusion-subuniverseᵉ Qᵉ (Sᵉ (Xᵉ ,ᵉ pᵉ))
```