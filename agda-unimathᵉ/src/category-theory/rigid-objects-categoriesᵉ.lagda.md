# Rigid objects in a category

```agda
module category-theory.rigid-objects-categoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categoriesᵉ
open import category-theory.rigid-objects-precategoriesᵉ

open import foundation.propositionsᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Aᵉ **rigidᵉ object**ᵉ in aᵉ [category](category-theory.categories.mdᵉ) isᵉ anᵉ objectᵉ
whoseᵉ [automorphismᵉ group](group-theory.automorphism-groups.mdᵉ) isᵉ
[trivial](group-theory.trivial-groups.md).ᵉ

## Definitions

### The predicate of being rigid

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ) (xᵉ : obj-Categoryᵉ Cᵉ)
  where

  is-rigid-obj-prop-Categoryᵉ : Propᵉ l2ᵉ
  is-rigid-obj-prop-Categoryᵉ =
    is-rigid-obj-prop-Precategoryᵉ (precategory-Categoryᵉ Cᵉ) xᵉ

  is-rigid-obj-Categoryᵉ : UUᵉ l2ᵉ
  is-rigid-obj-Categoryᵉ = type-Propᵉ is-rigid-obj-prop-Categoryᵉ

  is-prop-is-rigid-obj-Categoryᵉ : is-propᵉ is-rigid-obj-Categoryᵉ
  is-prop-is-rigid-obj-Categoryᵉ =
    is-prop-type-Propᵉ is-rigid-obj-prop-Categoryᵉ
```

### The type of rigid objects in a category

```agda
rigid-obj-Categoryᵉ : {l1ᵉ l2ᵉ : Level} (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
rigid-obj-Categoryᵉ Cᵉ =
    rigid-obj-Precategoryᵉ (precategory-Categoryᵉ Cᵉ)

module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  where

  obj-rigid-obj-Categoryᵉ : rigid-obj-Categoryᵉ Cᵉ → obj-Categoryᵉ Cᵉ
  obj-rigid-obj-Categoryᵉ = obj-rigid-obj-Precategoryᵉ (precategory-Categoryᵉ Cᵉ)

  is-rigid-rigid-obj-Categoryᵉ :
    (xᵉ : rigid-obj-Categoryᵉ Cᵉ) →
    is-rigid-obj-Categoryᵉ Cᵉ (obj-rigid-obj-Categoryᵉ xᵉ)
  is-rigid-rigid-obj-Categoryᵉ =
    is-rigid-rigid-obj-Precategoryᵉ (precategory-Categoryᵉ Cᵉ)
```

## See also

-ᵉ Everyᵉ objectᵉ in aᵉ categoryᵉ isᵉ rigidᵉ ifᵉ andᵉ onlyᵉ ifᵉ itᵉ isᵉ
  [gaunt](category-theory.gaunt-categories.md).ᵉ

## External links

-ᵉ [rigidᵉ object](https://ncatlab.org/nlab/show/rigid+objectᵉ) atᵉ $n$Labᵉ