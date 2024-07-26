# Endomorphisms in categories

```agda
module category-theory.endomorphisms-in-categoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categoriesᵉ
open import category-theory.endomorphisms-in-precategoriesᵉ

open import foundation.identity-typesᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.monoidsᵉ
open import group-theory.semigroupsᵉ
```

</details>

## Definition

### The monoid of endomorphisms on an object in a category

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ) (Xᵉ : obj-Categoryᵉ Cᵉ)
  where

  type-endo-Categoryᵉ : UUᵉ l2ᵉ
  type-endo-Categoryᵉ = type-endo-Precategoryᵉ (precategory-Categoryᵉ Cᵉ) Xᵉ

  comp-endo-Categoryᵉ :
    type-endo-Categoryᵉ → type-endo-Categoryᵉ → type-endo-Categoryᵉ
  comp-endo-Categoryᵉ = comp-endo-Precategoryᵉ (precategory-Categoryᵉ Cᵉ) Xᵉ

  id-endo-Categoryᵉ : type-endo-Categoryᵉ
  id-endo-Categoryᵉ = id-endo-Precategoryᵉ (precategory-Categoryᵉ Cᵉ) Xᵉ

  associative-comp-endo-Categoryᵉ :
    (hᵉ gᵉ fᵉ : type-endo-Categoryᵉ) →
    ( comp-endo-Categoryᵉ (comp-endo-Categoryᵉ hᵉ gᵉ) fᵉ) ＝ᵉ
    ( comp-endo-Categoryᵉ hᵉ (comp-endo-Categoryᵉ gᵉ fᵉ))
  associative-comp-endo-Categoryᵉ =
    associative-comp-endo-Precategoryᵉ (precategory-Categoryᵉ Cᵉ) Xᵉ

  left-unit-law-comp-endo-Categoryᵉ :
    (fᵉ : type-endo-Categoryᵉ) → comp-endo-Categoryᵉ id-endo-Categoryᵉ fᵉ ＝ᵉ fᵉ
  left-unit-law-comp-endo-Categoryᵉ =
    left-unit-law-comp-endo-Precategoryᵉ (precategory-Categoryᵉ Cᵉ) Xᵉ

  right-unit-law-comp-endo-Categoryᵉ :
    (fᵉ : type-endo-Categoryᵉ) → comp-endo-Categoryᵉ fᵉ id-endo-Categoryᵉ ＝ᵉ fᵉ
  right-unit-law-comp-endo-Categoryᵉ =
    right-unit-law-comp-endo-Precategoryᵉ (precategory-Categoryᵉ Cᵉ) Xᵉ

  set-endo-Categoryᵉ : Setᵉ l2ᵉ
  set-endo-Categoryᵉ = set-endo-Precategoryᵉ (precategory-Categoryᵉ Cᵉ) Xᵉ

  semigroup-endo-Categoryᵉ : Semigroupᵉ l2ᵉ
  semigroup-endo-Categoryᵉ =
    semigroup-endo-Precategoryᵉ (precategory-Categoryᵉ Cᵉ) Xᵉ

  monoid-endo-Categoryᵉ : Monoidᵉ l2ᵉ
  monoid-endo-Categoryᵉ = monoid-endo-Precategoryᵉ (precategory-Categoryᵉ Cᵉ) Xᵉ
```