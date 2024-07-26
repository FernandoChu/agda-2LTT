# Full subtypes of types

```agda
module foundation.full-subtypesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.decidable-subtypesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.equivalencesᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.subtypesᵉ
open import foundation-core.transport-along-identificationsᵉ
```

</details>

## Idea

Theᵉ fullᵉ subtypeᵉ ofᵉ aᵉ typeᵉ containsᵉ everyᵉ element.ᵉ Weᵉ defineᵉ aᵉ fullᵉ subtypeᵉ atᵉ
eachᵉ universeᵉ level.ᵉ

## Definition

### Full subtypes

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Pᵉ : subtypeᵉ l2ᵉ Aᵉ)
  where

  is-full-subtype-Propᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  is-full-subtype-Propᵉ = Π-Propᵉ Aᵉ (λ xᵉ → Pᵉ xᵉ)

  is-full-subtypeᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-full-subtypeᵉ = type-Propᵉ is-full-subtype-Propᵉ

  is-prop-is-full-subtypeᵉ : is-propᵉ is-full-subtypeᵉ
  is-prop-is-full-subtypeᵉ = is-prop-type-Propᵉ is-full-subtype-Propᵉ
```

### Full decidable subtypes

```agda
is-full-decidable-subtypeᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} → decidable-subtypeᵉ l2ᵉ Aᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
is-full-decidable-subtypeᵉ Pᵉ =
  is-full-subtypeᵉ (subtype-decidable-subtypeᵉ Pᵉ)
```

### The full subtype at a universe level

```agda
full-subtypeᵉ : {l1ᵉ : Level} (l2ᵉ : Level) (Aᵉ : UUᵉ l1ᵉ) → subtypeᵉ l2ᵉ Aᵉ
full-subtypeᵉ l2ᵉ Aᵉ xᵉ = raise-unit-Propᵉ l2ᵉ

type-full-subtypeᵉ : {l1ᵉ : Level} (l2ᵉ : Level) (Aᵉ : UUᵉ l1ᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
type-full-subtypeᵉ l2ᵉ Aᵉ = type-subtypeᵉ (full-subtypeᵉ l2ᵉ Aᵉ)

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  where

  is-in-full-subtypeᵉ : (xᵉ : Aᵉ) → is-in-subtypeᵉ (full-subtypeᵉ l2ᵉ Aᵉ) xᵉ
  is-in-full-subtypeᵉ xᵉ = raise-starᵉ

  inclusion-full-subtypeᵉ : type-full-subtypeᵉ l2ᵉ Aᵉ → Aᵉ
  inclusion-full-subtypeᵉ = inclusion-subtypeᵉ (full-subtypeᵉ l2ᵉ Aᵉ)

  is-equiv-inclusion-full-subtypeᵉ : is-equivᵉ inclusion-full-subtypeᵉ
  is-equiv-inclusion-full-subtypeᵉ =
    is-equiv-pr1-is-contrᵉ (λ aᵉ → is-contr-raise-unitᵉ)
```

## Properties

### A subtype is full if and only if the inclusion is an equivalence

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Pᵉ : subtypeᵉ l2ᵉ Aᵉ)
  where

  is-equiv-inclusion-is-full-subtypeᵉ :
    is-full-subtypeᵉ Pᵉ → is-equivᵉ (inclusion-subtypeᵉ Pᵉ)
  is-equiv-inclusion-is-full-subtypeᵉ Hᵉ =
    is-equiv-pr1-is-contrᵉ
      ( λ xᵉ → is-proof-irrelevant-is-propᵉ (is-prop-is-in-subtypeᵉ Pᵉ xᵉ) (Hᵉ xᵉ))

  equiv-inclusion-is-full-subtypeᵉ :
    is-full-subtypeᵉ Pᵉ → type-subtypeᵉ Pᵉ ≃ᵉ Aᵉ
  pr1ᵉ (equiv-inclusion-is-full-subtypeᵉ Hᵉ) = inclusion-subtypeᵉ Pᵉ
  pr2ᵉ (equiv-inclusion-is-full-subtypeᵉ Hᵉ) = is-equiv-inclusion-is-full-subtypeᵉ Hᵉ

  is-full-is-equiv-inclusion-subtypeᵉ :
    is-equivᵉ (inclusion-subtypeᵉ Pᵉ) → is-full-subtypeᵉ Pᵉ
  is-full-is-equiv-inclusion-subtypeᵉ Hᵉ xᵉ =
    trᵉ
      ( is-in-subtypeᵉ Pᵉ)
      ( is-section-map-inv-is-equivᵉ Hᵉ xᵉ)
      ( pr2ᵉ (map-inv-is-equivᵉ Hᵉ xᵉ))
```