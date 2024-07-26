# Orbits of group actions

```agda
module group-theory.orbits-group-actionsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ

open import group-theory.group-actionsᵉ
open import group-theory.groupsᵉ
```

</details>

## Idea

Theᵉ [groupoid](category-theory.groupoids.mdᵉ) ofᵉ **orbits**ᵉ ofᵉ aᵉ
[groupᵉ action](group-theory.group-actions.mdᵉ) consistsᵉ ofᵉ elementsᵉ ofᵉ `X`,ᵉ andᵉ aᵉ
morphismᵉ fromᵉ `x`ᵉ to `y`ᵉ isᵉ givenᵉ byᵉ anᵉ elementᵉ `g`ᵉ ofᵉ theᵉ
[group](group-theory.groups.mdᵉ) `G`ᵉ suchᵉ thatᵉ `gxᵉ ＝ᵉ y`.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Xᵉ : action-Groupᵉ Gᵉ l2ᵉ)
  where

  hom-orbit-action-Groupᵉ :
    (xᵉ yᵉ : type-action-Groupᵉ Gᵉ Xᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  hom-orbit-action-Groupᵉ xᵉ yᵉ =
    Σᵉ (type-Groupᵉ Gᵉ) (λ gᵉ → mul-action-Groupᵉ Gᵉ Xᵉ gᵉ xᵉ ＝ᵉ yᵉ)
```