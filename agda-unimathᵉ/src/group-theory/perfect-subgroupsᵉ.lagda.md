# Perfect subgroups

```agda
module group-theory.perfect-subgroupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.propositionsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.groupsᵉ
open import group-theory.perfect-groupsᵉ
open import group-theory.subgroupsᵉ
```

</details>

## Idea

Aᵉ [subgroup](group-theory.subgroups.mdᵉ) `H`ᵉ ofᵉ aᵉ [group](group-theory.groups.mdᵉ)
`G`ᵉ isᵉ aᵉ **perfectᵉ subgroup**ᵉ ifᵉ itᵉ isᵉ aᵉ
[perfectᵉ group](group-theory.perfect-groups.mdᵉ) onᵉ itsᵉ own.ᵉ

## Definitions

### The predicate of being a perfect subgroup

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Hᵉ : Subgroupᵉ l2ᵉ Gᵉ)
  where

  is-perfect-prop-Subgroupᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  is-perfect-prop-Subgroupᵉ = is-perfect-prop-Groupᵉ (group-Subgroupᵉ Gᵉ Hᵉ)

  is-perfect-Subgroupᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-perfect-Subgroupᵉ = type-Propᵉ is-perfect-prop-Subgroupᵉ

  is-prop-is-perfect-Subgroupᵉ : is-propᵉ is-perfect-Subgroupᵉ
  is-prop-is-perfect-Subgroupᵉ = is-prop-type-Propᵉ is-perfect-prop-Subgroupᵉ
```

## External links

Aᵉ wikidataᵉ identifierᵉ wasᵉ notᵉ availableᵉ forᵉ thisᵉ concept.ᵉ