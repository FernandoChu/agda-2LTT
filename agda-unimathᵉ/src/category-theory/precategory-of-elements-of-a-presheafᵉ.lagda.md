# Precategory of elements of a presheaf

```agda
module category-theory.precategory-of-elements-of-a-presheafᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.functors-precategoriesᵉ
open import category-theory.opposite-precategoriesᵉ
open import category-theory.precategoriesᵉ
open import category-theory.presheaf-categoriesᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.category-of-setsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.setsᵉ
open import foundation.subtypesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Letᵉ `Fᵉ : Cᵒᵖᵉ → Set`ᵉ beᵉ aᵉ [presheaf](category-theory.presheaf-categories.mdᵉ) onᵉ aᵉ
[precategory](category-theory.precategories.mdᵉ) `C`.ᵉ Theᵉ **precategoryᵉ ofᵉ
elements**ᵉ ofᵉ `F`ᵉ consistsᵉ ofᵉ:

-ᵉ Objectsᵉ areᵉ [pairs](foundation.dependent-pair-types.mdᵉ) `(Aᵉ ,ᵉ a)`ᵉ where `A`ᵉ isᵉ
  anᵉ objectᵉ in `C`ᵉ andᵉ `aᵉ : Fᵉ A`.ᵉ
-ᵉ Aᵉ morphismᵉ fromᵉ `(Aᵉ ,ᵉ a)`ᵉ to `(Bᵉ ,ᵉ b)`ᵉ isᵉ aᵉ morphismᵉ `fᵉ : homᵉ Aᵉ B`ᵉ in theᵉ
  precategoryᵉ `C`ᵉ equippedᵉ with anᵉ
  [identification](foundation-core.identity-types.mdᵉ) `aᵉ = Fᵉ fᵉ b`.ᵉ

## Definitions

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ} (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ) (Fᵉ : presheaf-Precategoryᵉ Cᵉ l3ᵉ)
  where

  obj-precategory-of-elements-presheaf-Precategoryᵉ : UUᵉ (l1ᵉ ⊔ l3ᵉ)
  obj-precategory-of-elements-presheaf-Precategoryᵉ =
    Σᵉ (obj-Precategoryᵉ Cᵉ) (element-presheaf-Precategoryᵉ Cᵉ Fᵉ)

  hom-set-precategory-of-elements-presheaf-Precategoryᵉ :
    (Aᵉ Bᵉ : obj-precategory-of-elements-presheaf-Precategoryᵉ) → Setᵉ (l2ᵉ ⊔ l3ᵉ)
  hom-set-precategory-of-elements-presheaf-Precategoryᵉ (Aᵉ ,ᵉ aᵉ) (Bᵉ ,ᵉ bᵉ) =
    set-subsetᵉ
      ( hom-set-Precategoryᵉ Cᵉ Aᵉ Bᵉ)
      ( λ fᵉ →
        Id-Propᵉ
          ( element-set-presheaf-Precategoryᵉ Cᵉ Fᵉ Aᵉ)
          ( aᵉ)
          ( action-presheaf-Precategoryᵉ Cᵉ Fᵉ fᵉ bᵉ))

  hom-precategory-of-elements-presheaf-Precategoryᵉ :
    (Aᵉ Bᵉ : obj-precategory-of-elements-presheaf-Precategoryᵉ) → UUᵉ (l2ᵉ ⊔ l3ᵉ)
  hom-precategory-of-elements-presheaf-Precategoryᵉ Aᵉ Bᵉ =
    type-Setᵉ (hom-set-precategory-of-elements-presheaf-Precategoryᵉ Aᵉ Bᵉ)

  eq-hom-precategory-of-elements-presheaf-Precategoryᵉ :
    {Xᵉ Yᵉ : obj-precategory-of-elements-presheaf-Precategoryᵉ}
    (fᵉ gᵉ : hom-precategory-of-elements-presheaf-Precategoryᵉ Xᵉ Yᵉ) →
    (pr1ᵉ fᵉ ＝ᵉ pr1ᵉ gᵉ) → fᵉ ＝ᵉ gᵉ
  eq-hom-precategory-of-elements-presheaf-Precategoryᵉ fᵉ gᵉ =
    eq-type-subtypeᵉ
      ( λ hᵉ →
        Id-Propᵉ
          ( element-set-presheaf-Precategoryᵉ Cᵉ Fᵉ _)
          ( _)
          ( action-presheaf-Precategoryᵉ Cᵉ Fᵉ hᵉ _))

  comp-hom-precategory-of-elements-presheaf-Precategoryᵉ :
    {Xᵉ Yᵉ Zᵉ : obj-precategory-of-elements-presheaf-Precategoryᵉ} →
    hom-precategory-of-elements-presheaf-Precategoryᵉ Yᵉ Zᵉ →
    hom-precategory-of-elements-presheaf-Precategoryᵉ Xᵉ Yᵉ →
    hom-precategory-of-elements-presheaf-Precategoryᵉ Xᵉ Zᵉ
  comp-hom-precategory-of-elements-presheaf-Precategoryᵉ
    ( gᵉ ,ᵉ qᵉ)
    ( fᵉ ,ᵉ pᵉ) =
    ( comp-hom-Precategoryᵉ Cᵉ gᵉ fᵉ ,ᵉ
      ( pᵉ) ∙ᵉ
      ( apᵉ (action-presheaf-Precategoryᵉ Cᵉ Fᵉ fᵉ) qᵉ) ∙ᵉ
      ( invᵉ (preserves-comp-action-presheaf-Precategoryᵉ Cᵉ Fᵉ gᵉ fᵉ _)))

  associative-comp-hom-precategory-of-elements-presheaf-Precategoryᵉ :
    {Xᵉ Yᵉ Zᵉ Wᵉ : obj-precategory-of-elements-presheaf-Precategoryᵉ} →
    (hᵉ : hom-precategory-of-elements-presheaf-Precategoryᵉ Zᵉ Wᵉ)
    (gᵉ : hom-precategory-of-elements-presheaf-Precategoryᵉ Yᵉ Zᵉ)
    (fᵉ : hom-precategory-of-elements-presheaf-Precategoryᵉ Xᵉ Yᵉ) →
    comp-hom-precategory-of-elements-presheaf-Precategoryᵉ
      ( comp-hom-precategory-of-elements-presheaf-Precategoryᵉ hᵉ gᵉ)
      ( fᵉ) ＝ᵉ
    comp-hom-precategory-of-elements-presheaf-Precategoryᵉ
      ( hᵉ)
      ( comp-hom-precategory-of-elements-presheaf-Precategoryᵉ gᵉ fᵉ)
  associative-comp-hom-precategory-of-elements-presheaf-Precategoryᵉ hᵉ gᵉ fᵉ =
    eq-hom-precategory-of-elements-presheaf-Precategoryᵉ
      ( comp-hom-precategory-of-elements-presheaf-Precategoryᵉ
        ( comp-hom-precategory-of-elements-presheaf-Precategoryᵉ hᵉ gᵉ)
        ( fᵉ))
      ( comp-hom-precategory-of-elements-presheaf-Precategoryᵉ
        ( hᵉ)
        ( comp-hom-precategory-of-elements-presheaf-Precategoryᵉ gᵉ fᵉ))
      ( associative-comp-hom-Precategoryᵉ Cᵉ (pr1ᵉ hᵉ) (pr1ᵉ gᵉ) (pr1ᵉ fᵉ))

  id-hom-precategory-of-elements-presheaf-Precategoryᵉ :
    {Xᵉ : obj-precategory-of-elements-presheaf-Precategoryᵉ} →
    hom-precategory-of-elements-presheaf-Precategoryᵉ Xᵉ Xᵉ
  pr1ᵉ id-hom-precategory-of-elements-presheaf-Precategoryᵉ =
    id-hom-Precategoryᵉ Cᵉ
  pr2ᵉ id-hom-precategory-of-elements-presheaf-Precategoryᵉ =
    invᵉ (preserves-id-action-presheaf-Precategoryᵉ Cᵉ Fᵉ _)

  left-unit-law-comp-hom-precategory-of-elements-presheaf-Precategoryᵉ :
    {Xᵉ Yᵉ : obj-precategory-of-elements-presheaf-Precategoryᵉ} →
    (fᵉ : hom-precategory-of-elements-presheaf-Precategoryᵉ Xᵉ Yᵉ) →
    comp-hom-precategory-of-elements-presheaf-Precategoryᵉ
      ( id-hom-precategory-of-elements-presheaf-Precategoryᵉ)
      ( fᵉ) ＝ᵉ
    fᵉ
  left-unit-law-comp-hom-precategory-of-elements-presheaf-Precategoryᵉ fᵉ =
    eq-hom-precategory-of-elements-presheaf-Precategoryᵉ
      ( comp-hom-precategory-of-elements-presheaf-Precategoryᵉ
        ( id-hom-precategory-of-elements-presheaf-Precategoryᵉ)
        ( fᵉ))
      ( fᵉ)
      ( left-unit-law-comp-hom-Precategoryᵉ Cᵉ (pr1ᵉ fᵉ))

  right-unit-law-comp-hom-precategory-of-elements-presheaf-Precategoryᵉ :
    {Xᵉ Yᵉ : obj-precategory-of-elements-presheaf-Precategoryᵉ} →
    (fᵉ : hom-precategory-of-elements-presheaf-Precategoryᵉ Xᵉ Yᵉ) →
    comp-hom-precategory-of-elements-presheaf-Precategoryᵉ
      ( fᵉ)
      ( id-hom-precategory-of-elements-presheaf-Precategoryᵉ) ＝ᵉ
    fᵉ
  right-unit-law-comp-hom-precategory-of-elements-presheaf-Precategoryᵉ fᵉ =
    eq-hom-precategory-of-elements-presheaf-Precategoryᵉ
      ( comp-hom-precategory-of-elements-presheaf-Precategoryᵉ
        ( fᵉ)
        ( id-hom-precategory-of-elements-presheaf-Precategoryᵉ))
      ( fᵉ)
      ( right-unit-law-comp-hom-Precategoryᵉ Cᵉ (pr1ᵉ fᵉ))

  precategory-of-elements-presheaf-Precategoryᵉ : Precategoryᵉ (l1ᵉ ⊔ l3ᵉ) (l2ᵉ ⊔ l3ᵉ)
  precategory-of-elements-presheaf-Precategoryᵉ =
    make-Precategoryᵉ
      ( obj-precategory-of-elements-presheaf-Precategoryᵉ)
      ( hom-set-precategory-of-elements-presheaf-Precategoryᵉ)
      ( comp-hom-precategory-of-elements-presheaf-Precategoryᵉ)
      ( λ Xᵉ → id-hom-precategory-of-elements-presheaf-Precategoryᵉ {Xᵉ})
      ( associative-comp-hom-precategory-of-elements-presheaf-Precategoryᵉ)
      ( left-unit-law-comp-hom-precategory-of-elements-presheaf-Precategoryᵉ)
      ( right-unit-law-comp-hom-precategory-of-elements-presheaf-Precategoryᵉ)
```

### The projection from the category of elements of a presheaf to the base category

```agda
module _ {l1ᵉ l2ᵉ l3ᵉ} (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Fᵉ : functor-Precategoryᵉ (opposite-Precategoryᵉ Cᵉ) (Set-Precategoryᵉ l3ᵉ))
  where

  proj-functor-precategory-of-elements-presheaf-Precategoryᵉ :
    functor-Precategoryᵉ (precategory-of-elements-presheaf-Precategoryᵉ Cᵉ Fᵉ) Cᵉ
  pr1ᵉ proj-functor-precategory-of-elements-presheaf-Precategoryᵉ Xᵉ =
    pr1ᵉ Xᵉ
  pr1ᵉ (pr2ᵉ proj-functor-precategory-of-elements-presheaf-Precategoryᵉ) fᵉ =
    pr1ᵉ fᵉ
  pr1ᵉ
    ( pr2ᵉ
      ( pr2ᵉ proj-functor-precategory-of-elements-presheaf-Precategoryᵉ)) gᵉ fᵉ =
    reflᵉ
  pr2ᵉ
    ( pr2ᵉ
      ( pr2ᵉ proj-functor-precategory-of-elements-presheaf-Precategoryᵉ)) xᵉ =
    reflᵉ
```