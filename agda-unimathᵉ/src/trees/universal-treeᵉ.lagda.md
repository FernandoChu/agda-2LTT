# The universal tree

```agda
{-# OPTIONSᵉ --guardednessᵉ #-}

module trees.universal-treeᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Theᵉ universalᵉ treeᵉ isᵉ theᵉ coinductiveᵉ typeᵉ associatedᵉ to theᵉ
[polynomialᵉ endofunctor](trees.polynomial-endofunctors.mdᵉ)

```text
  Xᵉ ↦ᵉ Σᵉ 𝒰ᵉ (λ Tᵉ → Xᵀ).ᵉ
```

Noteᵉ thatᵉ thisᵉ isᵉ theᵉ sameᵉ polynomialᵉ endofunctorᵉ thatᵉ weᵉ usedᵉ to defineᵉ theᵉ
typeᵉ ofᵉ [multisets](trees.multisets.md),ᵉ whichᵉ isᵉ theᵉ universalᵉ _well-foundedᵉ_
tree.ᵉ

## Definitions

### The universal tree of small trees

```agda
module _
  (lᵉ : Level)
  where

  record Universal-Treeᵉ : UUᵉ (lsuc lᵉ)
    where
    coinductiveᵉ
    field
      type-Universal-Treeᵉ :
        UUᵉ lᵉ
      branch-Universal-Treeᵉ :
        (xᵉ : type-Universal-Treeᵉ) → Universal-Treeᵉ

  open Universal-Treeᵉ public
```