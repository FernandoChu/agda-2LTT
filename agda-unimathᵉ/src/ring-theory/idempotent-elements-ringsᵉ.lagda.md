# Idempotent elements in rings

```agda
module ring-theory.idempotent-elements-ringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.subtypesᵉ
open import foundation.universe-levelsᵉ

open import ring-theory.ringsᵉ
```

</details>

## Idea

Anᵉ idempotentᵉ elementᵉ in aᵉ ringᵉ isᵉ anᵉ elementᵉ `x`ᵉ suchᵉ thatᵉ `x²ᵉ = x`.ᵉ

## Definition

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ) (xᵉ : type-Ringᵉ Rᵉ)
  where

  is-idempotent-element-ring-Propᵉ : Propᵉ lᵉ
  is-idempotent-element-ring-Propᵉ = Id-Propᵉ (set-Ringᵉ Rᵉ) (mul-Ringᵉ Rᵉ xᵉ xᵉ) xᵉ

  is-idempotent-element-Ringᵉ : UUᵉ lᵉ
  is-idempotent-element-Ringᵉ = type-Propᵉ is-idempotent-element-ring-Propᵉ

  is-prop-is-idempotent-element-Ringᵉ : is-propᵉ is-idempotent-element-Ringᵉ
  is-prop-is-idempotent-element-Ringᵉ =
    is-prop-type-Propᵉ is-idempotent-element-ring-Propᵉ

idempotent-element-Ringᵉ :
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ) → UUᵉ lᵉ
idempotent-element-Ringᵉ Rᵉ = type-subtypeᵉ (is-idempotent-element-ring-Propᵉ Rᵉ)

module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ) (xᵉ : idempotent-element-Ringᵉ Rᵉ)
  where

  element-idempotent-element-Ringᵉ : type-Ringᵉ Rᵉ
  element-idempotent-element-Ringᵉ =
    inclusion-subtypeᵉ (is-idempotent-element-ring-Propᵉ Rᵉ) xᵉ

  is-idempotent-element-idempotent-element-Ringᵉ :
    is-idempotent-element-Ringᵉ Rᵉ element-idempotent-element-Ringᵉ
  is-idempotent-element-idempotent-element-Ringᵉ =
    is-in-subtype-inclusion-subtypeᵉ (is-idempotent-element-ring-Propᵉ Rᵉ) xᵉ
```