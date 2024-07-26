# Large subcategories

```agda
module category-theory.large-subcategoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.large-categoriesᵉ
open import category-theory.large-subprecategoriesᵉ

open import foundation.universe-levelsᵉ
```

</details>

## Idea

Aᵉ **largeᵉ subcategory**ᵉ ofᵉ aᵉ
[largeᵉ category](category-theory.large-categories.mdᵉ) `C`ᵉ isᵉ aᵉ
[largeᵉ subprecategory](category-theory.large-subprecategories.mdᵉ) `P`ᵉ ofᵉ theᵉ
underlyingᵉ [largeᵉ precategory](category-theory.large-precategories.mdᵉ) ofᵉ `C`.ᵉ

## Definition

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (γᵉ : Level → Level) (δᵉ : Level → Level → Level)
  (Cᵉ : Large-Categoryᵉ αᵉ βᵉ)
  where

  Large-Subcategoryᵉ : UUωᵉ
  Large-Subcategoryᵉ =
    Large-Subprecategoryᵉ γᵉ δᵉ (large-precategory-Large-Categoryᵉ Cᵉ)
```