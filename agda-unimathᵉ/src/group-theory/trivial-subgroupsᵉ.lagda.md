# Trivial subgroups

```agda
module group-theory.trivial-subgroupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ

open import group-theory.groupsᵉ
open import group-theory.subgroupsᵉ
```

</details>

## Idea

Aᵉ [subgroup](group-theory.subgroups.mdᵉ) `H`ᵉ ofᵉ `G`ᵉ isᵉ saidᵉ to beᵉ **trivial**ᵉ ifᵉ
itᵉ onlyᵉ containsᵉ theᵉ unitᵉ elementᵉ ofᵉ `G`.ᵉ

## Definitions

### The trivial subgroup

```agda
module _
  {l1ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ)
  where

  trivial-Subgroupᵉ : Subgroupᵉ l1ᵉ Gᵉ
  pr1ᵉ trivial-Subgroupᵉ xᵉ = is-unit-prop-Group'ᵉ Gᵉ xᵉ
  pr1ᵉ (pr2ᵉ trivial-Subgroupᵉ) = reflᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ trivial-Subgroupᵉ)) reflᵉ reflᵉ =
    invᵉ (left-unit-law-mul-Groupᵉ Gᵉ (unit-Groupᵉ Gᵉ))
  pr2ᵉ (pr2ᵉ (pr2ᵉ trivial-Subgroupᵉ)) reflᵉ =
    invᵉ (inv-unit-Groupᵉ Gᵉ)
```

### The predicate of being a trivial subgroup

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Hᵉ : Subgroupᵉ l2ᵉ Gᵉ)
  where

  is-trivial-Subgroupᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-trivial-Subgroupᵉ = leq-Subgroupᵉ Gᵉ Hᵉ (trivial-Subgroupᵉ Gᵉ)
```