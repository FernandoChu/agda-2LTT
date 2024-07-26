# The category of group actions

```agda
module group-theory.category-of-group-actionsᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categoriesᵉ
open import category-theory.isomorphisms-in-large-precategoriesᵉ
open import category-theory.large-categoriesᵉ
open import category-theory.large-precategoriesᵉ
open import category-theory.precategoriesᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.universe-levelsᵉ

open import group-theory.group-actionsᵉ
open import group-theory.groupsᵉ
open import group-theory.homomorphisms-group-actionsᵉ
open import group-theory.isomorphisms-group-actionsᵉ
open import group-theory.precategory-of-group-actionsᵉ
```

</details>

## Idea

Theᵉ [largeᵉ category](category-theory.large-categories.mdᵉ) ofᵉ
[groupᵉ actions](group-theory.group-actions.mdᵉ) consistsᵉ ofᵉ groupᵉ actionsᵉ andᵉ
[morphismsᵉ ofᵉ groupᵉ actions](group-theory.homomorphisms-group-actions.mdᵉ)
betweenᵉ them.ᵉ

## Definitions

### The large category of `G`-sets

```agda
module _
  {l1ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ)
  where

  is-large-category-action-Group-Large-Categoryᵉ :
    is-large-category-Large-Precategoryᵉ (action-Group-Large-Precategoryᵉ Gᵉ)
  is-large-category-action-Group-Large-Categoryᵉ Xᵉ =
    fundamental-theorem-idᵉ
      ( is-torsorial-iso-action-Groupᵉ Gᵉ Xᵉ)
      ( iso-eq-Large-Precategoryᵉ (action-Group-Large-Precategoryᵉ Gᵉ) Xᵉ)

  action-Group-Large-Categoryᵉ :
    Large-Categoryᵉ (λ l2ᵉ → l1ᵉ ⊔ lsuc l2ᵉ) (λ l2ᵉ l3ᵉ → l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  large-precategory-Large-Categoryᵉ action-Group-Large-Categoryᵉ =
      action-Group-Large-Precategoryᵉ Gᵉ
  is-large-category-Large-Categoryᵉ action-Group-Large-Categoryᵉ =
    is-large-category-action-Group-Large-Categoryᵉ
```

### The small category of `G`-sets

```agda
module _
  {l1ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ)
  where

  action-Group-Categoryᵉ :
    (l2ᵉ : Level) → Categoryᵉ (l1ᵉ ⊔ lsuc l2ᵉ) (l1ᵉ ⊔ l2ᵉ)
  action-Group-Categoryᵉ =
    category-Large-Categoryᵉ (action-Group-Large-Categoryᵉ Gᵉ)
```