# Perfect cores

```agda
module group-theory.perfect-coresᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.logical-equivalencesᵉ
open import foundation.universe-levelsᵉ

open import group-theory.groupsᵉ
open import group-theory.perfect-subgroupsᵉ
open import group-theory.subgroupsᵉ
```

</details>

## Idea

Theᵉ **perfectᵉ core**ᵉ ofᵉ aᵉ [group](group-theory.groups.mdᵉ) `G`ᵉ isᵉ theᵉ largestᵉ
[perfectᵉ subgroup](group-theory.perfect-subgroups.mdᵉ) ofᵉ `G`.ᵉ Thatᵉ is,ᵉ theᵉ
[subgroup](group-theory.subgroups.mdᵉ) `perfect-coreᵉ G`ᵉ satisfiesᵉ theᵉ followingᵉ
universalᵉ propertyᵉ:

```text
  (Hᵉ : Subgroupᵉ Gᵉ) → is-perfect-Subgroupᵉ Gᵉ Hᵉ ↔ᵉ Hᵉ ⊆ᵉ perfect-coreᵉ Gᵉ
```

## Definitions

### The predicate of being a perfect core

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Hᵉ : Subgroupᵉ l2ᵉ Gᵉ)
  where

  is-perfect-core-Subgroupᵉ : UUωᵉ
  is-perfect-core-Subgroupᵉ =
    {lᵉ : Level} (Kᵉ : Subgroupᵉ lᵉ Gᵉ) →
    is-perfect-Subgroupᵉ Gᵉ Kᵉ ↔ᵉ leq-Subgroupᵉ Gᵉ Kᵉ Hᵉ
```

## External links

-ᵉ [Perfectᵉ core](https://en.wikipedia.org/wiki/Perfect_coreᵉ) atᵉ Wikipediaᵉ

Aᵉ wikidataᵉ identifierᵉ wasᵉ notᵉ availableᵉ forᵉ thisᵉ concept.ᵉ