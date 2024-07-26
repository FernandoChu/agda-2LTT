# Perfect groups

```agda
module group-theory.perfect-groupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.propositionsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.commutator-subgroupsᵉ
open import group-theory.full-subgroupsᵉ
open import group-theory.groupsᵉ
```

</details>

## Idea

Aᵉ [group](group-theory.groups.mdᵉ) `G`ᵉ isᵉ saidᵉ to beᵉ **perfect**ᵉ ifᵉ itsᵉ
[commutatorᵉ subgroup](group-theory.commutator-subgroups.mdᵉ) isᵉ aᵉ
[full](group-theory.full-subgroups.mdᵉ) [subgroup](group-theory.subgroups.md).ᵉ

## Definitions

### The predicate of being a perfect group

```agda
module _
  {l1ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ)
  where

  is-perfect-prop-Groupᵉ : Propᵉ l1ᵉ
  is-perfect-prop-Groupᵉ = is-full-prop-Subgroupᵉ Gᵉ (commutator-subgroup-Groupᵉ Gᵉ)

  is-perfect-Groupᵉ : UUᵉ l1ᵉ
  is-perfect-Groupᵉ = type-Propᵉ is-perfect-prop-Groupᵉ

  is-prop-is-perfect-Groupᵉ : is-propᵉ is-perfect-Groupᵉ
  is-prop-is-perfect-Groupᵉ = is-prop-type-Propᵉ is-perfect-prop-Groupᵉ
```

## External links

-ᵉ [Perfectᵉ group](https://ncatlab.org/nlab/show/perfect+groupᵉ) atᵉ $n$Labᵉ
-ᵉ [Perfectᵉ group](https://en.wikipedia.org/wiki/Perfect_groupᵉ) atᵉ Wikipediaᵉ

Aᵉ wikidataᵉ identifierᵉ wasᵉ notᵉ availableᵉ forᵉ thisᵉ concept.ᵉ