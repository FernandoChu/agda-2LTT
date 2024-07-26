# Intersections of subgroups of abelian groups

```agda
module group-theory.intersections-subgroups-abelian-groupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.subtypesᵉ
open import foundation.universe-levelsᵉ

open import group-theory.abelian-groupsᵉ
open import group-theory.intersections-subgroups-groupsᵉ
open import group-theory.subgroups-abelian-groupsᵉ
```

</details>

## Idea

Theᵉ **intersection**ᵉ ofᵉ twoᵉ
[subgroups](group-theory.subgroups-abelian-groups.mdᵉ) ofᵉ anᵉ
[abelianᵉ group](group-theory.abelian-groups.mdᵉ) `A`ᵉ consistsᵉ ofᵉ theᵉ elementsᵉ
containedᵉ in bothᵉ subgroups.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Aᵉ : Abᵉ l1ᵉ) (Bᵉ : Subgroup-Abᵉ l2ᵉ Aᵉ) (Cᵉ : Subgroup-Abᵉ l3ᵉ Aᵉ)
  where

  intersection-Subgroup-Abᵉ : Subgroup-Abᵉ (l2ᵉ ⊔ l3ᵉ) Aᵉ
  intersection-Subgroup-Abᵉ = intersection-Subgroupᵉ (group-Abᵉ Aᵉ) Bᵉ Cᵉ

  subset-intersection-Subgroup-Abᵉ : subtypeᵉ (l2ᵉ ⊔ l3ᵉ) (type-Abᵉ Aᵉ)
  subset-intersection-Subgroup-Abᵉ =
    subset-intersection-Subgroupᵉ (group-Abᵉ Aᵉ) Bᵉ Cᵉ

  is-in-intersection-Subgroup-Abᵉ : type-Abᵉ Aᵉ → UUᵉ (l2ᵉ ⊔ l3ᵉ)
  is-in-intersection-Subgroup-Abᵉ =
    is-in-intersection-Subgroupᵉ (group-Abᵉ Aᵉ) Bᵉ Cᵉ

  contains-zero-intersection-Subgroup-Abᵉ :
    contains-zero-subset-Abᵉ Aᵉ subset-intersection-Subgroup-Abᵉ
  contains-zero-intersection-Subgroup-Abᵉ =
    contains-unit-intersection-Subgroupᵉ (group-Abᵉ Aᵉ) Bᵉ Cᵉ

  is-closed-under-addition-intersection-Subgroup-Abᵉ :
    is-closed-under-addition-subset-Abᵉ Aᵉ subset-intersection-Subgroup-Abᵉ
  is-closed-under-addition-intersection-Subgroup-Abᵉ =
    is-closed-under-multiplication-intersection-Subgroupᵉ (group-Abᵉ Aᵉ) Bᵉ Cᵉ

  is-closed-under-negatives-intersection-Subgroup-Abᵉ :
    is-closed-under-negatives-subset-Abᵉ Aᵉ subset-intersection-Subgroup-Abᵉ
  is-closed-under-negatives-intersection-Subgroup-Abᵉ =
    is-closed-under-inverses-intersection-Subgroupᵉ (group-Abᵉ Aᵉ) Bᵉ Cᵉ

  is-subgroup-intersection-Subgroup-Abᵉ :
    is-subgroup-Abᵉ Aᵉ subset-intersection-Subgroup-Abᵉ
  is-subgroup-intersection-Subgroup-Abᵉ =
    is-subgroup-intersection-Subgroupᵉ (group-Abᵉ Aᵉ) Bᵉ Cᵉ
```