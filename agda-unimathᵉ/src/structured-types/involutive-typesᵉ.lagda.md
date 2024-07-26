# Involutive types

```agda
module structured-types.involutive-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.universe-levelsᵉ

open import univalent-combinatorics.2-element-typesᵉ
```

</details>

## Idea

Involutiveᵉ typesᵉ areᵉ typesᵉ equippedᵉ with aᵉ `ℤ/2`-action.ᵉ Inᵉ otherᵉ words,ᵉ
involutiveᵉ typesᵉ areᵉ typeᵉ familiesᵉ overᵉ `2-Element-Typeᵉ lzero`.ᵉ

Similarly,ᵉ anᵉ involutiveᵉ structureᵉ onᵉ aᵉ typeᵉ `X`ᵉ consistsᵉ ofᵉ aᵉ typeᵉ familyᵉ `Y`ᵉ
overᵉ `2-Element-Typeᵉ lzero`ᵉ equippedᵉ with anᵉ equivalenceᵉ `Xᵉ ≃ᵉ Yᵉ (Finᵉ 2)`.ᵉ

## Definitions

### Involutive types

```agda
Involutive-Typeᵉ : (lᵉ : Level) → UUᵉ (lsuc lᵉ)
Involutive-Typeᵉ lᵉ = 2-Element-Typeᵉ lzero → UUᵉ lᵉ

module _
  {lᵉ : Level} (Xᵉ : Involutive-Typeᵉ lᵉ)
  where

  type-Involutive-Typeᵉ : UUᵉ lᵉ
  type-Involutive-Typeᵉ = Xᵉ (standard-2-Element-Typeᵉ lzero)
```

### Involutive structure on a type

```agda
involutive-structureᵉ :
  {l1ᵉ : Level} (l2ᵉ : Level) (Xᵉ : UUᵉ l1ᵉ) → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
involutive-structureᵉ l2ᵉ Xᵉ =
  Σᵉ (Involutive-Typeᵉ l2ᵉ) (λ Yᵉ → Xᵉ ≃ᵉ type-Involutive-Typeᵉ Yᵉ)
```