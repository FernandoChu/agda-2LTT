# The orbit category of a group

```agda
module group-theory.category-of-orbits-groupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categoriesᵉ
open import category-theory.full-large-subcategoriesᵉ
open import category-theory.isomorphisms-in-large-precategoriesᵉ
open import category-theory.large-categoriesᵉ
open import category-theory.large-precategoriesᵉ
open import category-theory.precategoriesᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.universe-levelsᵉ

open import group-theory.category-of-group-actionsᵉ
open import group-theory.group-actionsᵉ
open import group-theory.groupsᵉ
open import group-theory.homomorphisms-group-actionsᵉ
open import group-theory.isomorphisms-group-actionsᵉ
open import group-theory.precategory-of-group-actionsᵉ
open import group-theory.transitive-group-actionsᵉ
```

</details>

## Idea

Theᵉ **orbitᵉ categoryᵉ ofᵉ aᵉ group**ᵉ `𝒪(G)`ᵉ isᵉ theᵉ
[fullᵉ subcategory](category-theory.full-large-subcategories.mdᵉ) ofᵉ theᵉ
[categoryᵉ ofᵉ `G`-sets](group-theory.category-of-group-actions.mdᵉ) consistingᵉ ofᵉ
orbitsᵉ ofᵉ `G`,ᵉ i.e.ᵉ [transitive](group-theory.transitive-group-actions.mdᵉ)
[`G`-sets](group-theory.group-actions.md).ᵉ Equivalently,ᵉ anᵉ orbitᵉ ofᵉ `G`ᵉ isᵉ aᵉ
`G`-setᵉ thatᵉ isᵉ
[merelyᵉ equivalent](group-theory.mere-equivalences-group-actions.mdᵉ) to aᵉ
quotientᵉ `G`-setᵉ `G/H`ᵉ forᵉ someᵉ [subgroup](group-theory.subgroups.mdᵉ) `H`.ᵉ

## Definitions

### The large orbit category of a group

```agda
module _
  {l1ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ)
  where

  orbit-Group-Full-Large-Subcategoryᵉ :
    Full-Large-Subcategoryᵉ (l1ᵉ ⊔ᵉ_) (action-Group-Large-Categoryᵉ Gᵉ)
  orbit-Group-Full-Large-Subcategoryᵉ = is-transitive-prop-action-Groupᵉ Gᵉ

  orbit-Group-Large-Categoryᵉ :
    Large-Categoryᵉ (λ lᵉ → l1ᵉ ⊔ lsuc lᵉ) (λ l2ᵉ l3ᵉ → l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  orbit-Group-Large-Categoryᵉ =
    large-category-Full-Large-Subcategoryᵉ
      ( action-Group-Large-Categoryᵉ Gᵉ)
      ( orbit-Group-Full-Large-Subcategoryᵉ)
```

### The large orbit precategory of a group

```agda
module _
  {l1ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ)
  where

  orbit-Group-Large-Precategoryᵉ :
    Large-Precategoryᵉ (λ lᵉ → l1ᵉ ⊔ lsuc lᵉ) (λ l2ᵉ l3ᵉ → l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  orbit-Group-Large-Precategoryᵉ =
    large-precategory-Large-Categoryᵉ (orbit-Group-Large-Categoryᵉ Gᵉ)
```

### The small orbit category of a group

```agda
module _
  {l1ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ)
  where

  orbit-Group-Categoryᵉ : (l2ᵉ : Level) → Categoryᵉ (l1ᵉ ⊔ lsuc l2ᵉ) (l1ᵉ ⊔ l2ᵉ)
  orbit-Group-Categoryᵉ = category-Large-Categoryᵉ (orbit-Group-Large-Categoryᵉ Gᵉ)
```

### The small orbit precategory of a group

```agda
module _
  {l1ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ)
  where

  orbit-Group-Precategoryᵉ : (l2ᵉ : Level) → Precategoryᵉ (l1ᵉ ⊔ lsuc l2ᵉ) (l1ᵉ ⊔ l2ᵉ)
  orbit-Group-Precategoryᵉ =
    precategory-Large-Categoryᵉ (orbit-Group-Large-Categoryᵉ Gᵉ)
```

## External links

-ᵉ [orbitᵉ category](https://ncatlab.org/nlab/show/orbit+categoryᵉ) atᵉ $n$Labᵉ