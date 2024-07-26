# Uniqueness of set truncations

```agda
module foundation.uniqueness-set-truncationsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.mere-equalityᵉ
open import foundation.setsᵉ
open import foundation.uniqueness-set-quotientsᵉ
open import foundation.universal-property-set-truncationᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.contractible-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.homotopiesᵉ
```

</details>

## Idea

Theᵉ universalᵉ propertyᵉ ofᵉ setᵉ truncationᵉ impliesᵉ thatᵉ setᵉ truncationsᵉ areᵉ
uniquelyᵉ unique.ᵉ

## Properties

### A 3-for-2 property for set truncations

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : Setᵉ l2ᵉ) (fᵉ : Aᵉ → type-Setᵉ Bᵉ)
  (Cᵉ : Setᵉ l3ᵉ) (gᵉ : Aᵉ → type-Setᵉ Cᵉ) {hᵉ : hom-Setᵉ Bᵉ Cᵉ}
  (Hᵉ : (hᵉ ∘ᵉ fᵉ) ~ᵉ gᵉ)
  where

  abstract
    is-equiv-is-set-truncation-is-set-truncationᵉ :
      is-set-truncationᵉ Bᵉ fᵉ → is-set-truncationᵉ Cᵉ gᵉ → is-equivᵉ hᵉ
    is-equiv-is-set-truncation-is-set-truncationᵉ Sfᵉ Sgᵉ =
      is-equiv-is-set-quotient-is-set-quotientᵉ
        ( mere-eq-equivalence-relationᵉ Aᵉ)
        ( Bᵉ)
        ( reflecting-map-mere-eqᵉ Bᵉ fᵉ)
        ( Cᵉ)
        ( reflecting-map-mere-eqᵉ Cᵉ gᵉ)
        ( Hᵉ)
        ( is-set-quotient-is-set-truncationᵉ Bᵉ fᵉ Sfᵉ)
        ( is-set-quotient-is-set-truncationᵉ Cᵉ gᵉ Sgᵉ)

  abstract
    is-set-truncation-is-equiv-is-set-truncationᵉ :
      is-set-truncationᵉ Cᵉ gᵉ → is-equivᵉ hᵉ → is-set-truncationᵉ Bᵉ fᵉ
    is-set-truncation-is-equiv-is-set-truncationᵉ Sgᵉ Ehᵉ =
      is-set-truncation-is-set-quotientᵉ Bᵉ fᵉ
        ( is-set-quotient-is-equiv-is-set-quotientᵉ
          ( mere-eq-equivalence-relationᵉ Aᵉ)
          ( Bᵉ)
          ( reflecting-map-mere-eqᵉ Bᵉ fᵉ)
          ( Cᵉ)
          ( reflecting-map-mere-eqᵉ Cᵉ gᵉ)
          ( Hᵉ)
          ( is-set-quotient-is-set-truncationᵉ Cᵉ gᵉ Sgᵉ)
          ( Ehᵉ))

  abstract
    is-set-truncation-is-set-truncation-is-equivᵉ :
      is-equivᵉ hᵉ → is-set-truncationᵉ Bᵉ fᵉ → is-set-truncationᵉ Cᵉ gᵉ
    is-set-truncation-is-set-truncation-is-equivᵉ Ehᵉ Sfᵉ =
      is-set-truncation-is-set-quotientᵉ Cᵉ gᵉ
        ( is-set-quotient-is-set-quotient-is-equivᵉ
          ( mere-eq-equivalence-relationᵉ Aᵉ)
          ( Bᵉ)
          ( reflecting-map-mere-eqᵉ Bᵉ fᵉ)
          ( Cᵉ)
          ( reflecting-map-mere-eqᵉ Cᵉ gᵉ)
          ( Hᵉ)
          ( Ehᵉ)
          ( is-set-quotient-is-set-truncationᵉ Bᵉ fᵉ Sfᵉ))
```

### The unique uniqueness of set truncations

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : Setᵉ l2ᵉ) (fᵉ : Aᵉ → type-Setᵉ Bᵉ)
  (Cᵉ : Setᵉ l3ᵉ) (gᵉ : Aᵉ → type-Setᵉ Cᵉ)
  (Sfᵉ : is-set-truncationᵉ Bᵉ fᵉ)
  (Sgᵉ : is-set-truncationᵉ Cᵉ gᵉ)
  where

  abstract
    uniqueness-set-truncationᵉ :
      is-contrᵉ (Σᵉ (type-Setᵉ Bᵉ ≃ᵉ type-Setᵉ Cᵉ) (λ eᵉ → (map-equivᵉ eᵉ ∘ᵉ fᵉ) ~ᵉ gᵉ))
    uniqueness-set-truncationᵉ =
      uniqueness-set-quotientᵉ
        ( mere-eq-equivalence-relationᵉ Aᵉ)
        ( Bᵉ)
        ( reflecting-map-mere-eqᵉ Bᵉ fᵉ)
        ( is-set-quotient-is-set-truncationᵉ Bᵉ fᵉ Sfᵉ)
        ( Cᵉ)
        ( reflecting-map-mere-eqᵉ Cᵉ gᵉ)
        ( is-set-quotient-is-set-truncationᵉ Cᵉ gᵉ Sgᵉ)

  equiv-uniqueness-set-truncationᵉ : type-Setᵉ Bᵉ ≃ᵉ type-Setᵉ Cᵉ
  equiv-uniqueness-set-truncationᵉ =
    pr1ᵉ (centerᵉ uniqueness-set-truncationᵉ)

  map-equiv-uniqueness-set-truncationᵉ : type-Setᵉ Bᵉ → type-Setᵉ Cᵉ
  map-equiv-uniqueness-set-truncationᵉ =
    map-equivᵉ equiv-uniqueness-set-truncationᵉ

  triangle-uniqueness-set-truncationᵉ :
    (map-equiv-uniqueness-set-truncationᵉ ∘ᵉ fᵉ) ~ᵉ gᵉ
  triangle-uniqueness-set-truncationᵉ =
    pr2ᵉ (centerᵉ uniqueness-set-truncationᵉ)
```