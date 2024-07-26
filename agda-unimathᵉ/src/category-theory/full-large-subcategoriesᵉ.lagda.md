# Full large subcategories

```agda
module category-theory.full-large-subcategoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.full-large-subprecategoriesᵉ
open import category-theory.functors-large-categoriesᵉ
open import category-theory.large-categoriesᵉ
open import category-theory.large-precategoriesᵉ

open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.strictly-involutive-identity-typesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Aᵉ **fullᵉ largeᵉ subcategory**ᵉ ofᵉ aᵉ
[largeᵉ category](category-theory.large-categories.mdᵉ) `C`ᵉ consistsᵉ ofᵉ aᵉ
[subtype](foundation.subtypes.mdᵉ) ofᵉ theᵉ typeᵉ ofᵉ objectsᵉ ofᵉ eachᵉ universeᵉ level.ᵉ

### Full large subprecategories

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level} (γᵉ : Level → Level)
  (Cᵉ : Large-Categoryᵉ αᵉ βᵉ)
  where

  Full-Large-Subcategoryᵉ : UUωᵉ
  Full-Large-Subcategoryᵉ =
    Full-Large-Subprecategoryᵉ γᵉ (large-precategory-Large-Categoryᵉ Cᵉ)

module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level} {γᵉ : Level → Level}
  (Cᵉ : Large-Categoryᵉ αᵉ βᵉ)
  (Pᵉ : Full-Large-Subcategoryᵉ γᵉ Cᵉ)
  where

  large-precategory-Full-Large-Subcategoryᵉ :
    Large-Precategoryᵉ (λ lᵉ → αᵉ lᵉ ⊔ γᵉ lᵉ) βᵉ
  large-precategory-Full-Large-Subcategoryᵉ =
    large-precategory-Full-Large-Subprecategoryᵉ
      ( large-precategory-Large-Categoryᵉ Cᵉ)
      ( Pᵉ)

  is-in-obj-Full-Large-Subcategoryᵉ :
    {lᵉ : Level} (Xᵉ : obj-Large-Categoryᵉ Cᵉ lᵉ) → UUᵉ (γᵉ lᵉ)
  is-in-obj-Full-Large-Subcategoryᵉ =
    is-in-obj-Full-Large-Subprecategoryᵉ (large-precategory-Large-Categoryᵉ Cᵉ) Pᵉ

  is-prop-is-in-obj-Full-Large-Subcategoryᵉ :
    {lᵉ : Level} (Xᵉ : obj-Large-Categoryᵉ Cᵉ lᵉ) →
    is-propᵉ (is-in-obj-Full-Large-Subcategoryᵉ Xᵉ)
  is-prop-is-in-obj-Full-Large-Subcategoryᵉ =
    is-prop-is-in-obj-Full-Large-Subprecategoryᵉ
      ( large-precategory-Large-Categoryᵉ Cᵉ)
      ( Pᵉ)

  obj-Full-Large-Subcategoryᵉ : (lᵉ : Level) → UUᵉ (αᵉ lᵉ ⊔ γᵉ lᵉ)
  obj-Full-Large-Subcategoryᵉ =
    obj-Full-Large-Subprecategoryᵉ
      ( large-precategory-Large-Categoryᵉ Cᵉ)
      ( Pᵉ)

  hom-set-Full-Large-Subcategoryᵉ :
    {l1ᵉ l2ᵉ : Level}
    (Xᵉ : obj-Full-Large-Subcategoryᵉ l1ᵉ)
    (Yᵉ : obj-Full-Large-Subcategoryᵉ l2ᵉ) →
    Setᵉ (βᵉ l1ᵉ l2ᵉ)
  hom-set-Full-Large-Subcategoryᵉ =
    hom-set-Full-Large-Subprecategoryᵉ
      ( large-precategory-Large-Categoryᵉ Cᵉ)
      ( Pᵉ)

  hom-Full-Large-Subcategoryᵉ :
    {l1ᵉ l2ᵉ : Level}
    (Xᵉ : obj-Full-Large-Subcategoryᵉ l1ᵉ)
    (Yᵉ : obj-Full-Large-Subcategoryᵉ l2ᵉ) →
    UUᵉ (βᵉ l1ᵉ l2ᵉ)
  hom-Full-Large-Subcategoryᵉ =
    hom-Full-Large-Subprecategoryᵉ
      ( large-precategory-Large-Categoryᵉ Cᵉ)
      ( Pᵉ)

  comp-hom-Full-Large-Subcategoryᵉ :
    {l1ᵉ l2ᵉ l3ᵉ : Level}
    (Xᵉ : obj-Full-Large-Subcategoryᵉ l1ᵉ)
    (Yᵉ : obj-Full-Large-Subcategoryᵉ l2ᵉ)
    (Zᵉ : obj-Full-Large-Subcategoryᵉ l3ᵉ) →
    hom-Full-Large-Subcategoryᵉ Yᵉ Zᵉ → hom-Full-Large-Subcategoryᵉ Xᵉ Yᵉ →
    hom-Full-Large-Subcategoryᵉ Xᵉ Zᵉ
  comp-hom-Full-Large-Subcategoryᵉ =
    comp-hom-Full-Large-Subprecategoryᵉ
      ( large-precategory-Large-Categoryᵉ Cᵉ)
      ( Pᵉ)

  id-hom-Full-Large-Subcategoryᵉ :
    {l1ᵉ : Level} (Xᵉ : obj-Full-Large-Subcategoryᵉ l1ᵉ) →
    hom-Full-Large-Subcategoryᵉ Xᵉ Xᵉ
  id-hom-Full-Large-Subcategoryᵉ =
    id-hom-Full-Large-Subprecategoryᵉ
      ( large-precategory-Large-Categoryᵉ Cᵉ)
      ( Pᵉ)

  associative-comp-hom-Full-Large-Subcategoryᵉ :
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
    (Xᵉ : obj-Full-Large-Subcategoryᵉ l1ᵉ)
    (Yᵉ : obj-Full-Large-Subcategoryᵉ l2ᵉ)
    (Zᵉ : obj-Full-Large-Subcategoryᵉ l3ᵉ)
    (Wᵉ : obj-Full-Large-Subcategoryᵉ l4ᵉ)
    (hᵉ : hom-Full-Large-Subcategoryᵉ Zᵉ Wᵉ)
    (gᵉ : hom-Full-Large-Subcategoryᵉ Yᵉ Zᵉ)
    (fᵉ : hom-Full-Large-Subcategoryᵉ Xᵉ Yᵉ) →
    comp-hom-Full-Large-Subcategoryᵉ Xᵉ Yᵉ Wᵉ
      ( comp-hom-Full-Large-Subcategoryᵉ Yᵉ Zᵉ Wᵉ hᵉ gᵉ)
      ( fᵉ) ＝ᵉ
    comp-hom-Full-Large-Subcategoryᵉ Xᵉ Zᵉ Wᵉ
      ( hᵉ)
      ( comp-hom-Full-Large-Subcategoryᵉ Xᵉ Yᵉ Zᵉ gᵉ fᵉ)
  associative-comp-hom-Full-Large-Subcategoryᵉ =
    associative-comp-hom-Full-Large-Subprecategoryᵉ
      ( large-precategory-Large-Categoryᵉ Cᵉ)
      ( Pᵉ)

  involutive-eq-associative-comp-hom-Full-Large-Subcategoryᵉ :
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
    (Xᵉ : obj-Full-Large-Subcategoryᵉ l1ᵉ)
    (Yᵉ : obj-Full-Large-Subcategoryᵉ l2ᵉ)
    (Zᵉ : obj-Full-Large-Subcategoryᵉ l3ᵉ)
    (Wᵉ : obj-Full-Large-Subcategoryᵉ l4ᵉ)
    (hᵉ : hom-Full-Large-Subcategoryᵉ Zᵉ Wᵉ)
    (gᵉ : hom-Full-Large-Subcategoryᵉ Yᵉ Zᵉ)
    (fᵉ : hom-Full-Large-Subcategoryᵉ Xᵉ Yᵉ) →
    comp-hom-Full-Large-Subcategoryᵉ Xᵉ Yᵉ Wᵉ
      ( comp-hom-Full-Large-Subcategoryᵉ Yᵉ Zᵉ Wᵉ hᵉ gᵉ)
      ( fᵉ) ＝ⁱᵉ
    comp-hom-Full-Large-Subcategoryᵉ Xᵉ Zᵉ Wᵉ
      ( hᵉ)
      ( comp-hom-Full-Large-Subcategoryᵉ Xᵉ Yᵉ Zᵉ gᵉ fᵉ)
  involutive-eq-associative-comp-hom-Full-Large-Subcategoryᵉ =
    involutive-eq-associative-comp-hom-Full-Large-Subprecategoryᵉ
      ( large-precategory-Large-Categoryᵉ Cᵉ)
      ( Pᵉ)

  left-unit-law-comp-hom-Full-Large-Subcategoryᵉ :
    {l1ᵉ l2ᵉ : Level}
    (Xᵉ : obj-Full-Large-Subcategoryᵉ l1ᵉ)
    (Yᵉ : obj-Full-Large-Subcategoryᵉ l2ᵉ)
    (fᵉ : hom-Full-Large-Subcategoryᵉ Xᵉ Yᵉ) →
    comp-hom-Full-Large-Subcategoryᵉ Xᵉ Yᵉ Yᵉ
      ( id-hom-Full-Large-Subcategoryᵉ Yᵉ)
      ( fᵉ) ＝ᵉ
    fᵉ
  left-unit-law-comp-hom-Full-Large-Subcategoryᵉ =
    left-unit-law-comp-hom-Full-Large-Subprecategoryᵉ
      ( large-precategory-Large-Categoryᵉ Cᵉ)
      ( Pᵉ)

  right-unit-law-comp-hom-Full-Large-Subcategoryᵉ :
    {l1ᵉ l2ᵉ : Level}
    (Xᵉ : obj-Full-Large-Subcategoryᵉ l1ᵉ)
    (Yᵉ : obj-Full-Large-Subcategoryᵉ l2ᵉ)
    (fᵉ : hom-Full-Large-Subcategoryᵉ Xᵉ Yᵉ) →
    comp-hom-Full-Large-Subcategoryᵉ Xᵉ Xᵉ Yᵉ
      ( fᵉ)
      ( id-hom-Full-Large-Subcategoryᵉ Xᵉ) ＝ᵉ
    fᵉ
  right-unit-law-comp-hom-Full-Large-Subcategoryᵉ =
    right-unit-law-comp-hom-Full-Large-Subprecategoryᵉ
      ( large-precategory-Large-Categoryᵉ Cᵉ)
      ( Pᵉ)

  iso-Full-Large-Subcategoryᵉ :
    {l1ᵉ l2ᵉ : Level}
    (Xᵉ : obj-Full-Large-Subcategoryᵉ l1ᵉ)
    (Yᵉ : obj-Full-Large-Subcategoryᵉ l2ᵉ) →
    UUᵉ (βᵉ l1ᵉ l1ᵉ ⊔ βᵉ l1ᵉ l2ᵉ ⊔ βᵉ l2ᵉ l1ᵉ ⊔ βᵉ l2ᵉ l2ᵉ)
  iso-Full-Large-Subcategoryᵉ =
    iso-Full-Large-Subprecategoryᵉ
      ( large-precategory-Large-Categoryᵉ Cᵉ)
      ( Pᵉ)

  iso-eq-Full-Large-Subcategoryᵉ :
    {l1ᵉ : Level} (Xᵉ Yᵉ : obj-Full-Large-Subcategoryᵉ l1ᵉ) →
    (Xᵉ ＝ᵉ Yᵉ) → iso-Full-Large-Subcategoryᵉ Xᵉ Yᵉ
  iso-eq-Full-Large-Subcategoryᵉ =
    iso-eq-Full-Large-Subprecategoryᵉ
      ( large-precategory-Large-Categoryᵉ Cᵉ)
      ( Pᵉ)
```

### The underlying large category of a full large subcategory

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level} {γᵉ : Level → Level}
  (Cᵉ : Large-Categoryᵉ αᵉ βᵉ)
  (Pᵉ : Full-Large-Subcategoryᵉ γᵉ Cᵉ)
  where

  is-large-category-Full-Large-Subcategoryᵉ :
    is-large-category-Large-Precategoryᵉ
      ( large-precategory-Full-Large-Subcategoryᵉ Cᵉ Pᵉ)
  is-large-category-Full-Large-Subcategoryᵉ =
    is-large-category-large-precategory-is-large-category-Full-Large-Subprecategoryᵉ
      ( large-precategory-Large-Categoryᵉ Cᵉ)
      ( Pᵉ)
      ( is-large-category-Large-Categoryᵉ Cᵉ)

  large-category-Full-Large-Subcategoryᵉ :
    Large-Categoryᵉ (λ lᵉ → αᵉ lᵉ ⊔ γᵉ lᵉ) βᵉ
  large-precategory-Large-Categoryᵉ
    large-category-Full-Large-Subcategoryᵉ =
    large-precategory-Full-Large-Subcategoryᵉ Cᵉ Pᵉ
  is-large-category-Large-Categoryᵉ
    large-category-Full-Large-Subcategoryᵉ =
    is-large-category-Full-Large-Subcategoryᵉ
```

### The forgetful functor from a full large subcategory to the ambient large category

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level} {γᵉ : Level → Level}
  (Cᵉ : Large-Categoryᵉ αᵉ βᵉ)
  (Pᵉ : Full-Large-Subcategoryᵉ γᵉ Cᵉ)
  where

  forgetful-functor-Full-Large-Subcategoryᵉ :
    functor-Large-Categoryᵉ
      ( λ lᵉ → lᵉ)
      ( large-category-Full-Large-Subcategoryᵉ Cᵉ Pᵉ)
      ( Cᵉ)
  forgetful-functor-Full-Large-Subcategoryᵉ =
    forgetful-functor-Full-Large-Subprecategoryᵉ
      ( large-precategory-Large-Categoryᵉ Cᵉ)
      ( Pᵉ)
```