# The category of abelian groups

```agda
module group-theory.category-of-abelian-groupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categoriesᵉ
open import category-theory.full-large-subcategoriesᵉ
open import category-theory.functors-large-categoriesᵉ
open import category-theory.large-categoriesᵉ
open import category-theory.large-precategoriesᵉ
open import category-theory.precategoriesᵉ

open import foundation.universe-levelsᵉ

open import group-theory.abelian-groupsᵉ
open import group-theory.category-of-groupsᵉ
```

</details>

## Idea

Theᵉ **categoryᵉ ofᵉ abelianᵉ groups**ᵉ isᵉ theᵉ
[fullᵉ largeᵉ subcategory](category-theory.full-large-subcategories.mdᵉ) ofᵉ theᵉ
[categoryᵉ ofᵉ groups](group-theory.category-of-groups.mdᵉ) consistingᵉ ofᵉ
[groups](group-theory.groups.mdᵉ) ofᵉ whichᵉ theᵉ groupᵉ operationᵉ isᵉ
[commutative](group-theory.abelian-groups.md).ᵉ

## Definitions

### The large category of abelian groups

```agda
Ab-Large-Categoryᵉ : Large-Categoryᵉ lsuc (_⊔ᵉ_)
Ab-Large-Categoryᵉ =
  large-category-Full-Large-Subcategoryᵉ
    ( Group-Large-Categoryᵉ)
    ( is-abelian-prop-Groupᵉ)
```

### The large precategory of abelian groups

```agda
Ab-Large-Precategoryᵉ : Large-Precategoryᵉ lsuc (_⊔ᵉ_)
Ab-Large-Precategoryᵉ =
  large-precategory-Large-Categoryᵉ Ab-Large-Categoryᵉ
```

### The category of abelian groups of a given universe level

```agda
Ab-Categoryᵉ : (lᵉ : Level) → Categoryᵉ (lsuc lᵉ) lᵉ
Ab-Categoryᵉ = category-Large-Categoryᵉ Ab-Large-Categoryᵉ
```

### The precategory of abelian groups of a given universe level

```agda
Ab-Precategoryᵉ : (lᵉ : Level) → Precategoryᵉ (lsuc lᵉ) lᵉ
Ab-Precategoryᵉ = precategory-Large-Categoryᵉ Ab-Large-Categoryᵉ
```

### The forgetful functor from abelian groups to groups

```agda
forgetful-functor-Abᵉ :
  functor-Large-Categoryᵉ (λ lᵉ → lᵉ) Ab-Large-Categoryᵉ Group-Large-Categoryᵉ
forgetful-functor-Abᵉ =
  forgetful-functor-Full-Large-Subcategoryᵉ
    ( Group-Large-Categoryᵉ)
    ( is-abelian-prop-Groupᵉ)
```