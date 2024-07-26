# Generating sets of groups

```agda
module group-theory.generating-sets-groupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levelsᵉ

open import group-theory.full-subgroupsᵉ
open import group-theory.groupsᵉ
open import group-theory.subgroups-generated-by-subsets-groupsᵉ
open import group-theory.subsets-groupsᵉ
```

</details>

## Idea

Aᵉ **generatingᵉ set**ᵉ ofᵉ aᵉ [group](group-theory.groups.mdᵉ) `G`ᵉ isᵉ aᵉ subsetᵉ
`Sᵉ ⊆ᵉ G`ᵉ suchᵉ thatᵉ theᵉ
[subgroupᵉ generatedᵉ byᵉ `S`](group-theory.subgroups-generated-by-subsets-groups.mdᵉ)
isᵉ theᵉ [fullᵉ subgroup](group-theory.full-subgroups.md).ᵉ

## Definition

### The predicate of being a generating set

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Sᵉ : subset-Groupᵉ l2ᵉ Gᵉ)
  where

  is-generating-set-Groupᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-generating-set-Groupᵉ = is-full-Subgroupᵉ Gᵉ (subgroup-subset-Groupᵉ Gᵉ Sᵉ)
```