# Constant functors

```agda
module category-theory.constant-functorsᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categoriesᵉ
open import category-theory.functors-categoriesᵉ
open import category-theory.functors-large-categoriesᵉ
open import category-theory.functors-large-precategoriesᵉ
open import category-theory.functors-precategoriesᵉ
open import category-theory.large-categoriesᵉ
open import category-theory.large-precategoriesᵉ
open import category-theory.precategoriesᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Aᵉ **constantᵉ functor**ᵉ isᵉ aᵉ [functor](category-theory.functors-categories.mdᵉ)
`Fᵉ : Cᵉ → D`ᵉ thatᵉ isᵉ constantᵉ atᵉ anᵉ objectᵉ `dᵉ ∈ᵉ D`ᵉ andᵉ theᵉ identityᵉ morphismᵉ atᵉ
thatᵉ object.ᵉ

## Definition

### Constant functors between precategories

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ) (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  (dᵉ : obj-Precategoryᵉ Dᵉ)
  where

  constant-functor-Precategoryᵉ : functor-Precategoryᵉ Cᵉ Dᵉ
  pr1ᵉ constant-functor-Precategoryᵉ _ = dᵉ
  pr1ᵉ (pr2ᵉ constant-functor-Precategoryᵉ) _ = id-hom-Precategoryᵉ Dᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ constant-functor-Precategoryᵉ)) _ _ =
    invᵉ (left-unit-law-comp-hom-Precategoryᵉ Dᵉ (id-hom-Precategoryᵉ Dᵉ))
  pr2ᵉ (pr2ᵉ (pr2ᵉ constant-functor-Precategoryᵉ)) = refl-htpyᵉ
```

### Constant functors between categories

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ) (Dᵉ : Categoryᵉ l3ᵉ l4ᵉ)
  (dᵉ : obj-Categoryᵉ Dᵉ)
  where

  constant-functor-Categoryᵉ : functor-Categoryᵉ Cᵉ Dᵉ
  constant-functor-Categoryᵉ =
    constant-functor-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( precategory-Categoryᵉ Dᵉ)
      ( dᵉ)
```

### Constant functors between large precategories

```agda
module _
  {αCᵉ αDᵉ : Level → Level} {βCᵉ βDᵉ : Level → Level → Level}
  (Cᵉ : Large-Precategoryᵉ αCᵉ βCᵉ) (Dᵉ : Large-Precategoryᵉ αDᵉ βDᵉ)
  {lᵉ : Level} (dᵉ : obj-Large-Precategoryᵉ Dᵉ lᵉ)
  where

  constant-functor-Large-Precategoryᵉ : functor-Large-Precategoryᵉ (λ _ → lᵉ) Cᵉ Dᵉ
  obj-functor-Large-Precategoryᵉ constant-functor-Large-Precategoryᵉ _ = dᵉ
  hom-functor-Large-Precategoryᵉ constant-functor-Large-Precategoryᵉ _ =
    id-hom-Large-Precategoryᵉ Dᵉ
  preserves-comp-functor-Large-Precategoryᵉ constant-functor-Large-Precategoryᵉ
    _ _ =
    invᵉ
      ( left-unit-law-comp-hom-Large-Precategoryᵉ Dᵉ (id-hom-Large-Precategoryᵉ Dᵉ))
  preserves-id-functor-Large-Precategoryᵉ constant-functor-Large-Precategoryᵉ =
    reflᵉ
```

### Constant functors between large categories

```agda
module _
  {αCᵉ αDᵉ : Level → Level} {βCᵉ βDᵉ : Level → Level → Level}
  (Cᵉ : Large-Categoryᵉ αCᵉ βCᵉ) (Dᵉ : Large-Categoryᵉ αDᵉ βDᵉ)
  {lᵉ : Level} (dᵉ : obj-Large-Categoryᵉ Dᵉ lᵉ)
  where

  constant-functor-Large-Categoryᵉ : functor-Large-Categoryᵉ (λ _ → lᵉ) Cᵉ Dᵉ
  constant-functor-Large-Categoryᵉ =
    constant-functor-Large-Precategoryᵉ
      ( large-precategory-Large-Categoryᵉ Cᵉ)
      ( large-precategory-Large-Categoryᵉ Dᵉ)
      ( dᵉ)
```

## External links

-ᵉ [constantᵉ functor](https://ncatlab.org/nlab/show/constant+functorᵉ) atᵉ $n$Labᵉ