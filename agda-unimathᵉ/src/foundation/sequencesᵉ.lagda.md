# Sequences

```agda
module foundation.sequencesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-sequencesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.function-typesᵉ
```

</details>

## Idea

Aᵉ **sequence**ᵉ ofᵉ elementsᵉ in aᵉ typeᵉ `A`ᵉ isᵉ aᵉ mapᵉ `ℕᵉ → A`.ᵉ

## Definition

### Sequences of elements of a type

```agda
sequenceᵉ : {lᵉ : Level} → UUᵉ lᵉ → UUᵉ lᵉ
sequenceᵉ Aᵉ = dependent-sequenceᵉ (λ _ → Aᵉ)
```

### Functorial action on maps of sequences

```agda
map-sequenceᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} → (Aᵉ → Bᵉ) → sequenceᵉ Aᵉ → sequenceᵉ Bᵉ
map-sequenceᵉ fᵉ aᵉ = fᵉ ∘ᵉ aᵉ
```