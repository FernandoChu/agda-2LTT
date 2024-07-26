# Multisets

```agda
module trees.multisetsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.empty-typesᵉ
open import foundation.function-typesᵉ
open import foundation.universe-levelsᵉ

open import trees.elementhood-relation-w-typesᵉ
open import trees.w-typesᵉ
```

</details>

## Idea

Theᵉ typeᵉ ofᵉ **multisets**ᵉ ofᵉ universeᵉ levelᵉ `l`ᵉ isᵉ theᵉ W-typeᵉ ofᵉ theᵉ universalᵉ
familyᵉ overᵉ theᵉ universeᵉ `UUᵉ l`.ᵉ

## Definitions

### The type of small multisets

```agda
𝕍ᵉ : (lᵉ : Level) → UUᵉ (lsuc lᵉ)
𝕍ᵉ lᵉ = 𝕎ᵉ (UUᵉ lᵉ) (λ Xᵉ → Xᵉ)
```

### The large type of all multisets

```agda
data
  Large-𝕍ᵉ : UUωᵉ
  where
  tree-Large-𝕍ᵉ : {lᵉ : Level} (Xᵉ : UUᵉ lᵉ) → (Xᵉ → Large-𝕍ᵉ) → Large-𝕍ᵉ
```

### The elementhood relation on multisets

```agda
infix 6 _∈-𝕍ᵉ_ _∉-𝕍ᵉ_

_∈-𝕍ᵉ_ : {lᵉ : Level} → 𝕍ᵉ lᵉ → 𝕍ᵉ lᵉ → UUᵉ (lsuc lᵉ)
Xᵉ ∈-𝕍ᵉ Yᵉ = Xᵉ ∈-𝕎ᵉ Yᵉ

_∉-𝕍ᵉ_ : {lᵉ : Level} → 𝕍ᵉ lᵉ → 𝕍ᵉ lᵉ → UUᵉ (lsuc lᵉ)
Xᵉ ∉-𝕍ᵉ Yᵉ = is-emptyᵉ (Xᵉ ∈-𝕍ᵉ Yᵉ)
```

### Comprehension for multisets

```agda
comprehension-𝕍ᵉ :
  {lᵉ : Level} (Xᵉ : 𝕍ᵉ lᵉ) (Pᵉ : shape-𝕎ᵉ Xᵉ → UUᵉ lᵉ) → 𝕍ᵉ lᵉ
comprehension-𝕍ᵉ Xᵉ Pᵉ =
  tree-𝕎ᵉ (Σᵉ (shape-𝕎ᵉ Xᵉ) Pᵉ) (component-𝕎ᵉ Xᵉ ∘ᵉ pr1ᵉ)
```