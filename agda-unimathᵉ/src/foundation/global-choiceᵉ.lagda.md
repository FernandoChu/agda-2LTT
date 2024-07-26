# Global choice

```agda
module foundation.global-choiceᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.functoriality-propositional-truncationᵉ
open import foundation.hilberts-epsilon-operatorsᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.equivalencesᵉ
open import foundation-core.negationᵉ

open import univalent-combinatorics.2-element-typesᵉ
open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

**Globalᵉ choice**ᵉ isᵉ theᵉ principleᵉ thatᵉ thereᵉ isᵉ aᵉ mapᵉ fromᵉ `type-trunc-Propᵉ A`ᵉ
backᵉ intoᵉ `A`,ᵉ forᵉ anyᵉ typeᵉ `A`.ᵉ Here,ᵉ weᵉ sayᵉ thatᵉ aᵉ typeᵉ `A`ᵉ _satisfiesᵉ globalᵉ
choiceᵉ_ ifᵉ thereᵉ isᵉ suchᵉ aᵉ map.ᵉ

## Definition

### The global choice principle

```agda
Global-Choiceᵉ : (lᵉ : Level) → UUᵉ (lsuc lᵉ)
Global-Choiceᵉ lᵉ = (Aᵉ : UUᵉ lᵉ) → ε-operator-Hilbertᵉ Aᵉ
```

## Properties

### The global choice principle is inconsistent in `agda-unimath`

```agda
abstract
  no-global-choiceᵉ :
    {lᵉ : Level} → ¬ᵉ (Global-Choiceᵉ lᵉ)
  no-global-choiceᵉ fᵉ =
    no-section-type-2-Element-Typeᵉ
      ( λ Xᵉ →
        fᵉ (pr1ᵉ Xᵉ) (map-trunc-Propᵉ (λ eᵉ → map-equivᵉ eᵉ (zero-Finᵉ 1ᵉ)) (pr2ᵉ Xᵉ)))
```