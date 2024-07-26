# Families of maps

```agda
module foundation.families-of-mapsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.universal-property-dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.contractible-typesᵉ
open import foundation-core.families-of-equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.functoriality-dependent-function-typesᵉ
open import foundation-core.functoriality-dependent-pair-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.subtypesᵉ
open import foundation-core.torsorial-type-familiesᵉ
open import foundation-core.type-theoretic-principle-of-choiceᵉ
```

</details>

## Idea

Givenᵉ aᵉ typeᵉ `A`ᵉ andᵉ typeᵉ familiesᵉ `Bᵉ Cᵉ : Aᵉ → Type`,ᵉ aᵉ **familyᵉ ofᵉ maps**ᵉ fromᵉ
`B`ᵉ to `C`ᵉ isᵉ anᵉ elementᵉ ofᵉ theᵉ typeᵉ `(xᵉ : Aᵉ) → Bᵉ xᵉ → Cᵉ x`.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  (Bᵉ : Aᵉ → UUᵉ l2ᵉ) (Cᵉ : Aᵉ → UUᵉ l3ᵉ)
  where

  fam-mapᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  fam-mapᵉ = (xᵉ : Aᵉ) → Bᵉ xᵉ → Cᵉ xᵉ
```

## Properties

### Families of maps are equivalent to maps of total spaces respecting the first coordinate

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  (Bᵉ : Aᵉ → UUᵉ l2ᵉ) (Cᵉ : Aᵉ → UUᵉ l3ᵉ)
  where

  equiv-fam-map-map-tot-spaceᵉ :
    fam-mapᵉ Bᵉ Cᵉ ≃ᵉ Σᵉ (Σᵉ Aᵉ Bᵉ → Σᵉ Aᵉ Cᵉ) (λ fᵉ → pr1ᵉ ~ᵉ pr1ᵉ ∘ᵉ fᵉ)
  equiv-fam-map-map-tot-spaceᵉ =
    equivalence-reasoningᵉ
      fam-mapᵉ Bᵉ Cᵉ
      ≃ᵉ (((xᵉ ,ᵉ _) : Σᵉ Aᵉ Bᵉ) → Cᵉ xᵉ)
        byᵉ
        equiv-ind-Σᵉ
      ≃ᵉ (((xᵉ ,ᵉ _) : Σᵉ Aᵉ Bᵉ) → Σᵉ (Σᵉ Aᵉ (xᵉ ＝ᵉ_)) (λ (x'ᵉ ,ᵉ _) → Cᵉ x'ᵉ))
        byᵉ
        equiv-Π-equiv-familyᵉ
          ( λ (xᵉ ,ᵉ _) →
            inv-left-unit-law-Σ-is-contrᵉ
              ( is-torsorial-Idᵉ xᵉ)
              ( xᵉ ,ᵉ reflᵉ))
      ≃ᵉ (((xᵉ ,ᵉ _) : Σᵉ Aᵉ Bᵉ) →
        Σᵉ (Σᵉ Aᵉ Cᵉ) (λ (x'ᵉ ,ᵉ _) → xᵉ ＝ᵉ x'ᵉ))
        byᵉ
        equiv-Π-equiv-familyᵉ (λ _ → equiv-right-swap-Σᵉ)
      ≃ᵉ Σᵉ (Σᵉ Aᵉ Bᵉ → Σᵉ Aᵉ Cᵉ) (λ fᵉ → pr1ᵉ ~ᵉ pr1ᵉ ∘ᵉ fᵉ)
        byᵉ
        distributive-Π-Σᵉ
```

### Families of equivalences are equivalent to equivalences of total spaces respecting the first coordinate

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  (Bᵉ : Aᵉ → UUᵉ l2ᵉ) (Cᵉ : Aᵉ → UUᵉ l3ᵉ)
  where

  equiv-fam-equiv-equiv-tot-spaceᵉ :
    fam-equivᵉ Bᵉ Cᵉ ≃ᵉ Σᵉ (Σᵉ Aᵉ Bᵉ ≃ᵉ Σᵉ Aᵉ Cᵉ) (λ eᵉ → pr1ᵉ ~ᵉ pr1ᵉ ∘ᵉ map-equivᵉ eᵉ)
  equiv-fam-equiv-equiv-tot-spaceᵉ =
    equivalence-reasoningᵉ
      fam-equivᵉ Bᵉ Cᵉ
      ≃ᵉ fiberwise-equivᵉ Bᵉ Cᵉ
        byᵉ
        equiv-fiberwise-equiv-fam-equivᵉ Bᵉ Cᵉ
      ≃ᵉ Σᵉ ( Σᵉ ( Σᵉ Aᵉ Bᵉ → Σᵉ Aᵉ Cᵉ) (λ eᵉ → pr1ᵉ ~ᵉ pr1ᵉ ∘ᵉ eᵉ))
          ( λ (eᵉ ,ᵉ _) → is-equivᵉ eᵉ)
        byᵉ
        equiv-subtype-equivᵉ
          ( equiv-fam-map-map-tot-spaceᵉ Bᵉ Cᵉ)
          ( λ fᵉ → Π-Propᵉ Aᵉ (is-equiv-Propᵉ ∘ᵉ fᵉ))
          ( λ (eᵉ ,ᵉ _) → is-equiv-Propᵉ eᵉ)
          ( λ fᵉ →
            is-equiv-tot-is-fiberwise-equivᵉ ,ᵉ is-fiberwise-equiv-is-equiv-totᵉ)
      ≃ᵉ Σᵉ (Σᵉ Aᵉ Bᵉ ≃ᵉ Σᵉ Aᵉ Cᵉ) (λ eᵉ → pr1ᵉ ~ᵉ pr1ᵉ ∘ᵉ map-equivᵉ eᵉ)
        byᵉ
        equiv-right-swap-Σᵉ
```