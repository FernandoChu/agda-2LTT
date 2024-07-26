# Discrete types

```agda
module foundation-core.discrete-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.decidable-equalityᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.setsᵉ
```

</details>

## Idea

Aᵉ discreteᵉ typeᵉ isᵉ aᵉ typeᵉ thatᵉ hasᵉ decidableᵉ equality.ᵉ

## Definition

```agda
Discrete-Typeᵉ : (lᵉ : Level) → UUᵉ (lsuc lᵉ)
Discrete-Typeᵉ lᵉ = Σᵉ (UUᵉ lᵉ) has-decidable-equalityᵉ

module _
  {lᵉ : Level} (Xᵉ : Discrete-Typeᵉ lᵉ)
  where

  type-Discrete-Typeᵉ : UUᵉ lᵉ
  type-Discrete-Typeᵉ = pr1ᵉ Xᵉ

  has-decidable-equality-type-Discrete-Typeᵉ :
    has-decidable-equalityᵉ type-Discrete-Typeᵉ
  has-decidable-equality-type-Discrete-Typeᵉ = pr2ᵉ Xᵉ

  is-set-type-Discrete-Typeᵉ : is-setᵉ type-Discrete-Typeᵉ
  is-set-type-Discrete-Typeᵉ =
    is-set-has-decidable-equalityᵉ has-decidable-equality-type-Discrete-Typeᵉ

  set-Discrete-Typeᵉ : Setᵉ lᵉ
  pr1ᵉ set-Discrete-Typeᵉ = type-Discrete-Typeᵉ
  pr2ᵉ set-Discrete-Typeᵉ = is-set-type-Discrete-Typeᵉ
```