# Symmetric elements of involutive types

```agda
module structured-types.symmetric-elements-involutive-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levelsᵉ

open import structured-types.involutive-typesᵉ

open import univalent-combinatorics.2-element-typesᵉ
```

</details>

## Idea

Symmetricᵉ elementsᵉ ofᵉ involutiveᵉ typesᵉ areᵉ fixedᵉ pointsᵉ ofᵉ theᵉ involution.ᵉ Inᵉ
otherᵉ words,ᵉ theᵉ typeᵉ ofᵉ symmetricᵉ elementsᵉ ofᵉ anᵉ involutiveᵉ typeᵉ `A`ᵉ isᵉ definedᵉ
to beᵉ

```text
  (Xᵉ : 2-Element-Typeᵉ lzero) → Aᵉ Xᵉ
```

## Definition

```agda
symmetric-element-Involutive-Typeᵉ :
  {lᵉ : Level} (Aᵉ : Involutive-Typeᵉ lᵉ) → UUᵉ (lsuc lzero ⊔ lᵉ)
symmetric-element-Involutive-Typeᵉ Aᵉ = (Xᵉ : 2-Element-Typeᵉ lzero) → Aᵉ Xᵉ
```