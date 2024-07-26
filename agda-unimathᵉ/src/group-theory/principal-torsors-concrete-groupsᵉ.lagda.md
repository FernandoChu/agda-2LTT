# Principal torsors of concrete groups

```agda
module group-theory.principal-torsors-concrete-groupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levelsᵉ

open import group-theory.concrete-group-actionsᵉ
open import group-theory.concrete-groupsᵉ
```

</details>

## Idea

Theᵉ **principalᵉ torsor**ᵉ ofᵉ aᵉ [concreteᵉ group](group-theory.concrete-groups.mdᵉ)
`G`ᵉ isᵉ theᵉ [identityᵉ type](foundation-core.identity-types.mdᵉ) ofᵉ `BG`.ᵉ

## Definition

```agda
module _
  {l1ᵉ : Level} (Gᵉ : Concrete-Groupᵉ l1ᵉ)
  where

  principal-torsor-Concrete-Groupᵉ :
    classifying-type-Concrete-Groupᵉ Gᵉ → action-Concrete-Groupᵉ l1ᵉ Gᵉ
  principal-torsor-Concrete-Groupᵉ = Id-BG-Setᵉ Gᵉ
```