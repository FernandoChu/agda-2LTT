# Dependent sequences

```agda
module foundation.dependent-sequencesᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.universe-levelsᵉ

open import foundation-core.function-typesᵉ
```

</details>

## Idea

Aᵉ **dependentᵉ sequence**ᵉ ofᵉ elementsᵉ in aᵉ familyᵉ ofᵉ typesᵉ `Aᵉ : ℕᵉ → UU`ᵉ isᵉ aᵉ
dependentᵉ mapᵉ `(nᵉ : ℕᵉ) → Aᵉ n`.ᵉ

## Definition

### Dependent sequences of elements in a family of types

```agda
dependent-sequenceᵉ : {lᵉ : Level} → (ℕᵉ → UUᵉ lᵉ) → UUᵉ lᵉ
dependent-sequenceᵉ Bᵉ = (nᵉ : ℕᵉ) → Bᵉ nᵉ
```

### Functorial action on maps of dependent sequences

```agda
map-dependent-sequenceᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : ℕᵉ → UUᵉ l1ᵉ} {Bᵉ : ℕᵉ → UUᵉ l2ᵉ} →
  ((nᵉ : ℕᵉ) → Aᵉ nᵉ → Bᵉ nᵉ) → dependent-sequenceᵉ Aᵉ → dependent-sequenceᵉ Bᵉ
map-dependent-sequenceᵉ fᵉ aᵉ = map-Πᵉ fᵉ aᵉ
```