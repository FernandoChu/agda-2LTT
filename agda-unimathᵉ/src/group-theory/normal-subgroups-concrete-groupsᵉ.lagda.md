# Normal subgroups of concrete groups

```agda
module group-theory.normal-subgroups-concrete-groupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levelsᵉ

open import group-theory.concrete-group-actionsᵉ
open import group-theory.concrete-groupsᵉ
open import group-theory.subgroups-concrete-groupsᵉ
open import group-theory.transitive-concrete-group-actionsᵉ
```

</details>

## Idea

Aᵉ normalᵉ subgroupᵉ isᵉ aᵉ fixedᵉ pointᵉ ofᵉ theᵉ conjugationᵉ actionᵉ onᵉ theᵉ (largeᵉ) setᵉ
ofᵉ allᵉ subgroupsᵉ

## Definition

```agda
normal-subgroup-Concrete-Groupᵉ :
  {l1ᵉ : Level} (l2ᵉ : Level) (Gᵉ : Concrete-Groupᵉ l1ᵉ) → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
normal-subgroup-Concrete-Groupᵉ l2ᵉ Gᵉ =
  (uᵉ : classifying-type-Concrete-Groupᵉ Gᵉ) →
  subgroup-action-Concrete-Groupᵉ l2ᵉ Gᵉ uᵉ

module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Concrete-Groupᵉ l1ᵉ)
  (Hᵉ : normal-subgroup-Concrete-Groupᵉ l2ᵉ Gᵉ)
  where

  subgroup-normal-subgroup-Concrete-Groupᵉ : subgroup-Concrete-Groupᵉ l2ᵉ Gᵉ
  subgroup-normal-subgroup-Concrete-Groupᵉ = Hᵉ (shape-Concrete-Groupᵉ Gᵉ)

  action-normal-subgroup-Concrete-Groupᵉ : action-Concrete-Groupᵉ l2ᵉ Gᵉ
  action-normal-subgroup-Concrete-Groupᵉ =
    action-subgroup-Concrete-Groupᵉ Gᵉ subgroup-normal-subgroup-Concrete-Groupᵉ

  transitive-action-normal-subgroup-Concrete-Groupᵉ :
    transitive-action-Concrete-Groupᵉ l2ᵉ Gᵉ
  transitive-action-normal-subgroup-Concrete-Groupᵉ =
    transitive-action-subgroup-Concrete-Groupᵉ Gᵉ
      ( subgroup-normal-subgroup-Concrete-Groupᵉ)
```