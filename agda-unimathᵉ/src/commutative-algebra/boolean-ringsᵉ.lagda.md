# Boolean rings

```agda
module commutative-algebra.boolean-ringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-ringsᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import ring-theory.idempotent-elements-ringsᵉ
```

</details>

## Idea

Aᵉ **booleanᵉ ring**ᵉ isᵉ aᵉ commutativeᵉ ringᵉ in wichᵉ everyᵉ elementᵉ isᵉ idempotent.ᵉ

## Definition

```agda
is-boolean-Commutative-Ringᵉ :
  {lᵉ : Level} (Aᵉ : Commutative-Ringᵉ lᵉ) → UUᵉ lᵉ
is-boolean-Commutative-Ringᵉ Aᵉ =
  (xᵉ : type-Commutative-Ringᵉ Aᵉ) →
  is-idempotent-element-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ) xᵉ

Boolean-Ringᵉ : (lᵉ : Level) → UUᵉ (lsuc lᵉ)
Boolean-Ringᵉ lᵉ = Σᵉ (Commutative-Ringᵉ lᵉ) is-boolean-Commutative-Ringᵉ

module _
  {lᵉ : Level} (Aᵉ : Boolean-Ringᵉ lᵉ)
  where

  commutative-ring-Boolean-Ringᵉ : Commutative-Ringᵉ lᵉ
  commutative-ring-Boolean-Ringᵉ = pr1ᵉ Aᵉ
```