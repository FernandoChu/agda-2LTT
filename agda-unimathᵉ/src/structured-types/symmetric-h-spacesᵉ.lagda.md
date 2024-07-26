# Symmetric H-spaces

```agda
module structured-types.symmetric-h-spacesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.symmetric-operationsᵉ
open import foundation.universe-levelsᵉ

open import structured-types.involutive-type-of-h-space-structuresᵉ
open import structured-types.pointed-typesᵉ
open import structured-types.symmetric-elements-involutive-typesᵉ
```

</details>

## Idea

**Symmetricᵉ H-spaces**ᵉ areᵉ [pointedᵉ types](structured-types.pointed-types.mdᵉ)
`A`ᵉ [equipped](foundation.structure.mdᵉ) with aᵉ symmetricᵉ elementᵉ ofᵉ theᵉ
[involutiveᵉ typeᵉ ofᵉ H-spaceᵉ structures](structured-types.involutive-type-of-h-space-structures.mdᵉ)
onᵉ `A`.ᵉ

## Definitions

### Symmetric H-space structures on a pointed type

```agda
symmetric-H-Spaceᵉ :
  {l1ᵉ : Level} (Aᵉ : Pointed-Typeᵉ l1ᵉ) → UUᵉ (lsuc lzero ⊔ l1ᵉ)
symmetric-H-Spaceᵉ Aᵉ =
  symmetric-element-Involutive-Typeᵉ (h-space-Involutive-Typeᵉ Aᵉ)
```

### The symmetric binary operation on a symmetric H-space

```agda
symmetric-mul-symmetric-H-Spaceᵉ :
  {l1ᵉ : Level} (Aᵉ : Pointed-Typeᵉ l1ᵉ) (μᵉ : symmetric-H-Spaceᵉ Aᵉ) →
  symmetric-operationᵉ (type-Pointed-Typeᵉ Aᵉ) (type-Pointed-Typeᵉ Aᵉ)
symmetric-mul-symmetric-H-Spaceᵉ Aᵉ μᵉ (Xᵉ ,ᵉ fᵉ) = pr1ᵉ (μᵉ Xᵉ) fᵉ
```