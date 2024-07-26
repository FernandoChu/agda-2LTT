# Equivalences between categories

```agda
module category-theory.equivalences-of-categoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categoriesᵉ
open import category-theory.equivalences-of-precategoriesᵉ
open import category-theory.functors-categoriesᵉ

open import foundation.universe-levelsᵉ
```

</details>

## Idea

Aᵉ [functor](category-theory.functors-categories.mdᵉ) `Fᵉ : Cᵉ → D`ᵉ onᵉ
[categories](category-theory.categories.mdᵉ) isᵉ anᵉ **equivalence**ᵉ ifᵉ itᵉ isᵉ anᵉ
[equivalenceᵉ onᵉ theᵉ underlyingᵉ precategories](category-theory.equivalences-of-precategories.md).ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Categoryᵉ l3ᵉ l4ᵉ)
  where

  is-equiv-functor-Categoryᵉ : functor-Categoryᵉ Cᵉ Dᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  is-equiv-functor-Categoryᵉ =
    is-equiv-functor-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( precategory-Categoryᵉ Dᵉ)

  equiv-Categoryᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  equiv-Categoryᵉ =
    equiv-Precategoryᵉ (precategory-Categoryᵉ Cᵉ) (precategory-Categoryᵉ Dᵉ)
```