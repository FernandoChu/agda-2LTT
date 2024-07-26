# Cores of categories

```agda
module category-theory.cores-categoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categoriesᵉ
open import category-theory.cores-precategoriesᵉ
open import category-theory.groupoidsᵉ
open import category-theory.isomorphisms-in-categoriesᵉ
open import category-theory.precategoriesᵉ
open import category-theory.pregroupoidsᵉ
open import category-theory.subcategoriesᵉ
open import category-theory.wide-subcategoriesᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Theᵉ **coreᵉ ofᵉ aᵉ [category](category-theory.categories.md)**ᵉ `C`ᵉ isᵉ theᵉ maximalᵉ
subgroupoidᵉ ofᵉ it.ᵉ Itᵉ consistsᵉ ofᵉ allᵉ objectsᵉ andᵉ
[isomorphisms](category-theory.isomorphisms-in-categories.mdᵉ) in `C`.ᵉ

## Definitions

### The core wide subcategory

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  where

  core-wide-subcategory-Categoryᵉ : Wide-Subcategoryᵉ l2ᵉ Cᵉ
  core-wide-subcategory-Categoryᵉ =
    core-wide-subprecategory-Precategoryᵉ (precategory-Categoryᵉ Cᵉ)
```

### The core subcategory

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  where

  core-subcategory-Categoryᵉ : Subcategoryᵉ lzero l2ᵉ Cᵉ
  core-subcategory-Categoryᵉ =
    core-subprecategory-Precategoryᵉ (precategory-Categoryᵉ Cᵉ)

  is-wide-core-Categoryᵉ : is-wide-Subcategoryᵉ Cᵉ core-subcategory-Categoryᵉ
  is-wide-core-Categoryᵉ = is-wide-core-Precategoryᵉ (precategory-Categoryᵉ Cᵉ)
```

### The core precategory

```agda
core-precategory-Categoryᵉ :
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ) → Precategoryᵉ l1ᵉ l2ᵉ
core-precategory-Categoryᵉ Cᵉ =
  core-precategory-Precategoryᵉ (precategory-Categoryᵉ Cᵉ)
```

### The core category

```agda
core-category-Categoryᵉ :
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ) → Categoryᵉ l1ᵉ l2ᵉ
pr1ᵉ (core-category-Categoryᵉ Cᵉ) = core-precategory-Categoryᵉ Cᵉ
pr2ᵉ (core-category-Categoryᵉ Cᵉ) =
  is-category-core-is-category-Precategoryᵉ
    ( precategory-Categoryᵉ Cᵉ)
    ( is-category-Categoryᵉ Cᵉ)
```

### The core pregroupoid

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  where

  is-pregroupoid-core-Categoryᵉ :
    is-pregroupoid-Precategoryᵉ (core-precategory-Categoryᵉ Cᵉ)
  is-pregroupoid-core-Categoryᵉ =
    is-pregroupoid-core-Precategoryᵉ (precategory-Categoryᵉ Cᵉ)

  core-pregroupoid-Categoryᵉ : Pregroupoidᵉ l1ᵉ l2ᵉ
  core-pregroupoid-Categoryᵉ =
    core-pregroupoid-Precategoryᵉ (precategory-Categoryᵉ Cᵉ)
```

### The core groupoid

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  where

  is-groupoid-core-Categoryᵉ : is-groupoid-Categoryᵉ (core-category-Categoryᵉ Cᵉ)
  is-groupoid-core-Categoryᵉ = is-pregroupoid-core-Categoryᵉ Cᵉ

  core-groupoid-Categoryᵉ : Groupoidᵉ l1ᵉ l2ᵉ
  pr1ᵉ core-groupoid-Categoryᵉ = core-category-Categoryᵉ Cᵉ
  pr2ᵉ core-groupoid-Categoryᵉ = is-groupoid-core-Categoryᵉ
```

## Properties

### Computing isomorphisms in the core

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ) {xᵉ yᵉ : obj-Categoryᵉ Cᵉ}
  where

  compute-iso-core-Categoryᵉ :
    iso-Categoryᵉ Cᵉ xᵉ yᵉ ≃ᵉ iso-Categoryᵉ (core-category-Categoryᵉ Cᵉ) xᵉ yᵉ
  compute-iso-core-Categoryᵉ =
    compute-iso-core-Precategoryᵉ (precategory-Categoryᵉ Cᵉ)

  inv-compute-iso-core-Categoryᵉ :
    iso-Categoryᵉ (core-category-Categoryᵉ Cᵉ) xᵉ yᵉ ≃ᵉ iso-Categoryᵉ Cᵉ xᵉ yᵉ
  inv-compute-iso-core-Categoryᵉ =
    inv-compute-iso-core-Precategoryᵉ (precategory-Categoryᵉ Cᵉ)
```

## See also

-ᵉ [Coresᵉ ofᵉ monoids](group-theory.cores-monoids.mdᵉ)
-ᵉ [Restrictionsᵉ ofᵉ functorsᵉ to coresᵉ ofᵉ precategories](category-theory.restrictions-functors-cores-precategories.mdᵉ)

## External links

-ᵉ [Theᵉ coreᵉ ofᵉ aᵉ category](https://1lab.dev/Cat.Instances.Core.htmlᵉ) atᵉ 1labᵉ
-ᵉ [coreᵉ groupoid](https://ncatlab.org/nlab/show/core+groupoidᵉ) atᵉ $n$Labᵉ