# Initial objects of large categories

```agda
module category-theory.initial-objects-large-categoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.initial-objects-large-precategoriesᵉ
open import category-theory.large-categoriesᵉ

open import foundation.universe-levelsᵉ
```

</details>

## Idea

Anᵉ **initialᵉ object**ᵉ in aᵉ [largeᵉ category](category-theory.large-categories.mdᵉ)
`C`ᵉ isᵉ anᵉ objectᵉ `X`ᵉ suchᵉ thatᵉ `homᵉ Xᵉ Y`ᵉ isᵉ
[contractible](foundation.contractible-types.mdᵉ) forᵉ anyᵉ objectᵉ `Y`.ᵉ

## Definitions

### Initial objects in large categories

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Cᵉ : Large-Categoryᵉ αᵉ βᵉ)
  {lᵉ : Level} (Xᵉ : obj-Large-Categoryᵉ Cᵉ lᵉ)
  where

  is-initial-obj-Large-Categoryᵉ : UUωᵉ
  is-initial-obj-Large-Categoryᵉ =
    is-initial-obj-Large-Precategoryᵉ (large-precategory-Large-Categoryᵉ Cᵉ) Xᵉ
```