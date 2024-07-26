# Stabilizer groups

```agda
module group-theory.stabilizer-groupsᵉ where
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

Givenᵉ aᵉ [`G`-set](group-theory.group-actions.mdᵉ) `X`,ᵉ theᵉ **stabilizerᵉ group**ᵉ
atᵉ anᵉ elementᵉ `x`ᵉ ofᵉ `X`ᵉ isᵉ theᵉ [subgroup](group-theory.subgroups.mdᵉ) ofᵉ
elementsᵉ `g`ᵉ ofᵉ `G`ᵉ thatᵉ keepᵉ `x`ᵉ fixed.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Xᵉ : action-Groupᵉ Gᵉ l2ᵉ)
  where

  type-stabilizer-action-Groupᵉ : type-action-Groupᵉ Gᵉ Xᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  type-stabilizer-action-Groupᵉ xᵉ =
    Σᵉ (type-Groupᵉ Gᵉ) (λ gᵉ → mul-action-Groupᵉ Gᵉ Xᵉ gᵉ xᵉ ＝ᵉ xᵉ)
```

## External links

-ᵉ [stabilizerᵉ group](https://ncatlab.org/nlab/show/stabilizer+groupᵉ) atᵉ $n$Labᵉ
-ᵉ [Fixedᵉ pointsᵉ andᵉ stabilizerᵉ subgroups](https://en.wikipedia.org/wiki/Group_action#Fixed_points_and_stabilizer_subgroupsᵉ)
  atᵉ Wikipediaᵉ
-ᵉ [Isotropyᵉ Group](https://mathworld.wolfram.com/IsotropyGroup.htmlᵉ) atᵉ Wolframᵉ
  Mathworldᵉ
-ᵉ [Isotropyᵉ group](https://encyclopediaofmath.org/wiki/Isotropy_groupᵉ) atᵉ
  Encyclopediaᵉ ofᵉ Mathematicsᵉ