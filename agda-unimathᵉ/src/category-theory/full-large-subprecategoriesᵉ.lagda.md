# Full large subprecategories

```agda
module category-theory.full-large-subprecategoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.functors-large-precategoriesᵉ
open import category-theory.isomorphisms-in-large-categoriesᵉ
open import category-theory.isomorphisms-in-large-precategoriesᵉ
open import category-theory.large-categoriesᵉ
open import category-theory.large-precategoriesᵉ

open import foundation.function-typesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.strictly-involutive-identity-typesᵉ
open import foundation.subtype-identity-principleᵉ
open import foundation.subtypesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Aᵉ **fullᵉ largeᵉ subprecategory**ᵉ ofᵉ aᵉ
[largeᵉ precategory](category-theory.large-precategories.mdᵉ) `C`ᵉ consistsᵉ ofᵉ aᵉ
familyᵉ ofᵉ [subtypes](foundation.subtypes.mdᵉ) ofᵉ theᵉ typesᵉ
`obj-Large-Precategoryᵉ Cᵉ l`ᵉ forᵉ eachᵉ universeᵉ levelᵉ `l`.ᵉ

Alternatively,ᵉ weᵉ sayᵉ thatᵉ aᵉ
[largeᵉ subcategory](category-theory.large-subcategories.mdᵉ) **isᵉ full**ᵉ ifᵉ forᵉ
everyᵉ twoᵉ objectsᵉ `X`ᵉ andᵉ `Y`ᵉ in theᵉ subcategory,ᵉ theᵉ subtypeᵉ ofᵉ morphismsᵉ fromᵉ
`X`ᵉ to `Y`ᵉ in theᵉ subcategoryᵉ isᵉ [full](foundation.full-subtypes.md).ᵉ

Noteᵉ thatᵉ fullᵉ largeᵉ subprecategoriesᵉ areᵉ notᵉ assumedᵉ to beᵉ closedᵉ underᵉ
isomorphisms.ᵉ

## Definitions

### Full large subprecategories

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level} (γᵉ : Level → Level)
  (Cᵉ : Large-Precategoryᵉ αᵉ βᵉ)
  where

  Full-Large-Subprecategoryᵉ : UUωᵉ
  Full-Large-Subprecategoryᵉ =
    {lᵉ : Level} → subtypeᵉ (γᵉ lᵉ) (obj-Large-Precategoryᵉ Cᵉ lᵉ)

module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level} {γᵉ : Level → Level}
  (Cᵉ : Large-Precategoryᵉ αᵉ βᵉ)
  (Pᵉ : Full-Large-Subprecategoryᵉ γᵉ Cᵉ)
  where

  is-in-obj-Full-Large-Subprecategoryᵉ :
    {lᵉ : Level} (Xᵉ : obj-Large-Precategoryᵉ Cᵉ lᵉ) → UUᵉ (γᵉ lᵉ)
  is-in-obj-Full-Large-Subprecategoryᵉ Xᵉ = is-in-subtypeᵉ Pᵉ Xᵉ

  is-prop-is-in-obj-Full-Large-Subprecategoryᵉ :
    {lᵉ : Level} (Xᵉ : obj-Large-Precategoryᵉ Cᵉ lᵉ) →
    is-propᵉ (is-in-obj-Full-Large-Subprecategoryᵉ Xᵉ)
  is-prop-is-in-obj-Full-Large-Subprecategoryᵉ =
    is-prop-is-in-subtypeᵉ Pᵉ

  obj-Full-Large-Subprecategoryᵉ : (lᵉ : Level) → UUᵉ (αᵉ lᵉ ⊔ γᵉ lᵉ)
  obj-Full-Large-Subprecategoryᵉ lᵉ = type-subtypeᵉ (Pᵉ {lᵉ})

  hom-set-Full-Large-Subprecategoryᵉ :
    {l1ᵉ l2ᵉ : Level}
    (Xᵉ : obj-Full-Large-Subprecategoryᵉ l1ᵉ)
    (Yᵉ : obj-Full-Large-Subprecategoryᵉ l2ᵉ) →
    Setᵉ (βᵉ l1ᵉ l2ᵉ)
  hom-set-Full-Large-Subprecategoryᵉ Xᵉ Yᵉ =
    hom-set-Large-Precategoryᵉ Cᵉ
      ( inclusion-subtypeᵉ Pᵉ Xᵉ)
      ( inclusion-subtypeᵉ Pᵉ Yᵉ)

  hom-Full-Large-Subprecategoryᵉ :
    {l1ᵉ l2ᵉ : Level}
    (Xᵉ : obj-Full-Large-Subprecategoryᵉ l1ᵉ)
    (Yᵉ : obj-Full-Large-Subprecategoryᵉ l2ᵉ) →
    UUᵉ (βᵉ l1ᵉ l2ᵉ)
  hom-Full-Large-Subprecategoryᵉ Xᵉ Yᵉ =
    hom-Large-Precategoryᵉ Cᵉ
      ( inclusion-subtypeᵉ Pᵉ Xᵉ)
      ( inclusion-subtypeᵉ Pᵉ Yᵉ)

  comp-hom-Full-Large-Subprecategoryᵉ :
    {l1ᵉ l2ᵉ l3ᵉ : Level}
    (Xᵉ : obj-Full-Large-Subprecategoryᵉ l1ᵉ)
    (Yᵉ : obj-Full-Large-Subprecategoryᵉ l2ᵉ)
    (Zᵉ : obj-Full-Large-Subprecategoryᵉ l3ᵉ) →
    hom-Full-Large-Subprecategoryᵉ Yᵉ Zᵉ → hom-Full-Large-Subprecategoryᵉ Xᵉ Yᵉ →
    hom-Full-Large-Subprecategoryᵉ Xᵉ Zᵉ
  comp-hom-Full-Large-Subprecategoryᵉ Xᵉ Yᵉ Zᵉ =
    comp-hom-Large-Precategoryᵉ Cᵉ

  id-hom-Full-Large-Subprecategoryᵉ :
    {l1ᵉ : Level} (Xᵉ : obj-Full-Large-Subprecategoryᵉ l1ᵉ) →
    hom-Full-Large-Subprecategoryᵉ Xᵉ Xᵉ
  id-hom-Full-Large-Subprecategoryᵉ Xᵉ =
    id-hom-Large-Precategoryᵉ Cᵉ

  associative-comp-hom-Full-Large-Subprecategoryᵉ :
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
    (Xᵉ : obj-Full-Large-Subprecategoryᵉ l1ᵉ)
    (Yᵉ : obj-Full-Large-Subprecategoryᵉ l2ᵉ)
    (Zᵉ : obj-Full-Large-Subprecategoryᵉ l3ᵉ)
    (Wᵉ : obj-Full-Large-Subprecategoryᵉ l4ᵉ)
    (hᵉ : hom-Full-Large-Subprecategoryᵉ Zᵉ Wᵉ)
    (gᵉ : hom-Full-Large-Subprecategoryᵉ Yᵉ Zᵉ)
    (fᵉ : hom-Full-Large-Subprecategoryᵉ Xᵉ Yᵉ) →
    comp-hom-Full-Large-Subprecategoryᵉ Xᵉ Yᵉ Wᵉ
      ( comp-hom-Full-Large-Subprecategoryᵉ Yᵉ Zᵉ Wᵉ hᵉ gᵉ)
      ( fᵉ) ＝ᵉ
    comp-hom-Full-Large-Subprecategoryᵉ Xᵉ Zᵉ Wᵉ
      ( hᵉ)
      ( comp-hom-Full-Large-Subprecategoryᵉ Xᵉ Yᵉ Zᵉ gᵉ fᵉ)
  associative-comp-hom-Full-Large-Subprecategoryᵉ Xᵉ Yᵉ Zᵉ Wᵉ =
    associative-comp-hom-Large-Precategoryᵉ Cᵉ

  involutive-eq-associative-comp-hom-Full-Large-Subprecategoryᵉ :
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
    (Xᵉ : obj-Full-Large-Subprecategoryᵉ l1ᵉ)
    (Yᵉ : obj-Full-Large-Subprecategoryᵉ l2ᵉ)
    (Zᵉ : obj-Full-Large-Subprecategoryᵉ l3ᵉ)
    (Wᵉ : obj-Full-Large-Subprecategoryᵉ l4ᵉ)
    (hᵉ : hom-Full-Large-Subprecategoryᵉ Zᵉ Wᵉ)
    (gᵉ : hom-Full-Large-Subprecategoryᵉ Yᵉ Zᵉ)
    (fᵉ : hom-Full-Large-Subprecategoryᵉ Xᵉ Yᵉ) →
    comp-hom-Full-Large-Subprecategoryᵉ Xᵉ Yᵉ Wᵉ
      ( comp-hom-Full-Large-Subprecategoryᵉ Yᵉ Zᵉ Wᵉ hᵉ gᵉ)
      ( fᵉ) ＝ⁱᵉ
    comp-hom-Full-Large-Subprecategoryᵉ Xᵉ Zᵉ Wᵉ
      ( hᵉ)
      ( comp-hom-Full-Large-Subprecategoryᵉ Xᵉ Yᵉ Zᵉ gᵉ fᵉ)
  involutive-eq-associative-comp-hom-Full-Large-Subprecategoryᵉ Xᵉ Yᵉ Zᵉ Wᵉ =
    involutive-eq-associative-comp-hom-Large-Precategoryᵉ Cᵉ

  left-unit-law-comp-hom-Full-Large-Subprecategoryᵉ :
    {l1ᵉ l2ᵉ : Level}
    (Xᵉ : obj-Full-Large-Subprecategoryᵉ l1ᵉ)
    (Yᵉ : obj-Full-Large-Subprecategoryᵉ l2ᵉ)
    (fᵉ : hom-Full-Large-Subprecategoryᵉ Xᵉ Yᵉ) →
    comp-hom-Full-Large-Subprecategoryᵉ Xᵉ Yᵉ Yᵉ
      ( id-hom-Full-Large-Subprecategoryᵉ Yᵉ)
      ( fᵉ) ＝ᵉ
    fᵉ
  left-unit-law-comp-hom-Full-Large-Subprecategoryᵉ Xᵉ Yᵉ =
    left-unit-law-comp-hom-Large-Precategoryᵉ Cᵉ

  right-unit-law-comp-hom-Full-Large-Subprecategoryᵉ :
    {l1ᵉ l2ᵉ : Level}
    (Xᵉ : obj-Full-Large-Subprecategoryᵉ l1ᵉ)
    (Yᵉ : obj-Full-Large-Subprecategoryᵉ l2ᵉ)
    (fᵉ : hom-Full-Large-Subprecategoryᵉ Xᵉ Yᵉ) →
    comp-hom-Full-Large-Subprecategoryᵉ Xᵉ Xᵉ Yᵉ
      ( fᵉ)
      ( id-hom-Full-Large-Subprecategoryᵉ Xᵉ) ＝ᵉ
    fᵉ
  right-unit-law-comp-hom-Full-Large-Subprecategoryᵉ Xᵉ Yᵉ =
    right-unit-law-comp-hom-Large-Precategoryᵉ Cᵉ

  large-precategory-Full-Large-Subprecategoryᵉ :
    Large-Precategoryᵉ (λ lᵉ → αᵉ lᵉ ⊔ γᵉ lᵉ) βᵉ
  obj-Large-Precategoryᵉ
    large-precategory-Full-Large-Subprecategoryᵉ =
    obj-Full-Large-Subprecategoryᵉ
  hom-set-Large-Precategoryᵉ
    large-precategory-Full-Large-Subprecategoryᵉ =
    hom-set-Full-Large-Subprecategoryᵉ
  comp-hom-Large-Precategoryᵉ
    large-precategory-Full-Large-Subprecategoryᵉ
    {l1ᵉ} {l2ᵉ} {l3ᵉ} {Xᵉ} {Yᵉ} {Zᵉ} =
    comp-hom-Full-Large-Subprecategoryᵉ Xᵉ Yᵉ Zᵉ
  id-hom-Large-Precategoryᵉ
    large-precategory-Full-Large-Subprecategoryᵉ {l1ᵉ} {Xᵉ} =
    id-hom-Full-Large-Subprecategoryᵉ Xᵉ
  involutive-eq-associative-comp-hom-Large-Precategoryᵉ
    large-precategory-Full-Large-Subprecategoryᵉ
    {l1ᵉ} {l2ᵉ} {l3ᵉ} {l4ᵉ} {Xᵉ} {Yᵉ} {Zᵉ} {Wᵉ} =
    involutive-eq-associative-comp-hom-Full-Large-Subprecategoryᵉ Xᵉ Yᵉ Zᵉ Wᵉ
  left-unit-law-comp-hom-Large-Precategoryᵉ
    large-precategory-Full-Large-Subprecategoryᵉ {l1ᵉ} {l2ᵉ} {Xᵉ} {Yᵉ} =
    left-unit-law-comp-hom-Full-Large-Subprecategoryᵉ Xᵉ Yᵉ
  right-unit-law-comp-hom-Large-Precategoryᵉ
    large-precategory-Full-Large-Subprecategoryᵉ {l1ᵉ} {l2ᵉ} {Xᵉ} {Yᵉ} =
    right-unit-law-comp-hom-Full-Large-Subprecategoryᵉ Xᵉ Yᵉ

  iso-Full-Large-Subprecategoryᵉ :
    {l1ᵉ l2ᵉ : Level}
    (Xᵉ : obj-Full-Large-Subprecategoryᵉ l1ᵉ)
    (Yᵉ : obj-Full-Large-Subprecategoryᵉ l2ᵉ) →
    UUᵉ (βᵉ l1ᵉ l1ᵉ ⊔ βᵉ l1ᵉ l2ᵉ ⊔ βᵉ l2ᵉ l1ᵉ ⊔ βᵉ l2ᵉ l2ᵉ)
  iso-Full-Large-Subprecategoryᵉ Xᵉ Yᵉ =
    iso-Large-Precategoryᵉ Cᵉ (inclusion-subtypeᵉ Pᵉ Xᵉ) (inclusion-subtypeᵉ Pᵉ Yᵉ)

  iso-eq-Full-Large-Subprecategoryᵉ :
    {l1ᵉ : Level} (Xᵉ Yᵉ : obj-Full-Large-Subprecategoryᵉ l1ᵉ) →
    (Xᵉ ＝ᵉ Yᵉ) → iso-Full-Large-Subprecategoryᵉ Xᵉ Yᵉ
  iso-eq-Full-Large-Subprecategoryᵉ =
    iso-eq-Large-Precategoryᵉ large-precategory-Full-Large-Subprecategoryᵉ
```

### The forgetful functor from a full large subprecategory to the ambient large precategory

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level} {γᵉ : Level → Level}
  (Cᵉ : Large-Precategoryᵉ αᵉ βᵉ)
  (Pᵉ : Full-Large-Subprecategoryᵉ γᵉ Cᵉ)
  where

  forgetful-functor-Full-Large-Subprecategoryᵉ :
    functor-Large-Precategoryᵉ
      ( λ lᵉ → lᵉ)
      ( large-precategory-Full-Large-Subprecategoryᵉ Cᵉ Pᵉ)
      ( Cᵉ)
  obj-functor-Large-Precategoryᵉ
    forgetful-functor-Full-Large-Subprecategoryᵉ =
    inclusion-subtypeᵉ Pᵉ
  hom-functor-Large-Precategoryᵉ
    forgetful-functor-Full-Large-Subprecategoryᵉ =
    idᵉ
  preserves-comp-functor-Large-Precategoryᵉ
    forgetful-functor-Full-Large-Subprecategoryᵉ gᵉ fᵉ =
    reflᵉ
  preserves-id-functor-Large-Precategoryᵉ
    forgetful-functor-Full-Large-Subprecategoryᵉ =
    reflᵉ
```

## Properties

### A full large subprecategory of a large category is a large category

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level} {γᵉ : Level → Level}
  (Cᵉ : Large-Precategoryᵉ αᵉ βᵉ)
  (Pᵉ : Full-Large-Subprecategoryᵉ γᵉ Cᵉ)
  where

  is-large-category-large-precategory-is-large-category-Full-Large-Subprecategoryᵉ :
    is-large-category-Large-Precategoryᵉ Cᵉ →
    is-large-category-Large-Precategoryᵉ
      ( large-precategory-Full-Large-Subprecategoryᵉ Cᵉ Pᵉ)
  is-large-category-large-precategory-is-large-category-Full-Large-Subprecategoryᵉ
    is-large-category-Cᵉ Xᵉ =
    fundamental-theorem-idᵉ
      ( is-torsorial-Eq-subtypeᵉ
        ( is-torsorial-iso-Large-Categoryᵉ
          ( make-Large-Categoryᵉ Cᵉ is-large-category-Cᵉ)
          ( inclusion-subtypeᵉ Pᵉ Xᵉ))
        ( is-prop-is-in-subtypeᵉ Pᵉ)
        ( inclusion-subtypeᵉ Pᵉ Xᵉ)
        ( id-iso-Large-Precategoryᵉ Cᵉ)
        ( is-in-subtype-inclusion-subtypeᵉ Pᵉ Xᵉ))
      ( iso-eq-Full-Large-Subprecategoryᵉ Cᵉ Pᵉ Xᵉ)
```