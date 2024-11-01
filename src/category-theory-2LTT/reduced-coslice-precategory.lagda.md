# Reduced coslice precategories

```agda
module category-theory-2LTT.reduced-coslice-precategory where
```

<details><summary>Imports</summary>

```agda
open import category-theory.coslice-precategoriesᵉ
open import category-theory.full-subprecategoriesᵉ
open import category-theory.functors-precategoriesᵉ
open import category-theory.precategoriesᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.negationᵉ
open import foundation.universe-levels
```

</details>

## Idea

The reduced coslice precategory of a precategory `C` under an object `X` of `C`
is the category of objects of `C` equipped with a morphism from `X`.

## Definitions

```agda
module _
  {l1 l2 : Level} (C : Precategoryᵉ l1 l2) (X : obj-Precategoryᵉ C)
  where

  Reduced-Coslice-Full-Subcategoryᵉ :
    Full-Subprecategoryᵉ (l1 ⊔ l2) (Coslice-Precategoryᵉ C X)
  pr1ᵉ (Reduced-Coslice-Full-Subcategoryᵉ (Y,f)) =
    ¬ᵉ ((Y,f) ＝ᵉ ((X ,ᵉ id-hom-Precategoryᵉ C)))
  pr2ᵉ (Reduced-Coslice-Full-Subcategoryᵉ (Y,f)) =
    is-prop-negᵉ

  Reduced-Coslice-Precategoryᵉ : Precategoryᵉ (l1 ⊔ l2) l2
  Reduced-Coslice-Precategoryᵉ =
    precategory-Full-Subprecategoryᵉ
      ( Coslice-Precategoryᵉ C X)
      ( Reduced-Coslice-Full-Subcategoryᵉ)

  cod-obj-Reduced-Coslice-Precategoryᵉ :
    (f : obj-Precategoryᵉ Reduced-Coslice-Precategoryᵉ) →
    obj-Precategoryᵉ C
  cod-obj-Reduced-Coslice-Precategoryᵉ f = pr1ᵉ (pr1ᵉ f)

  hom-obj-Reduced-Coslice-Precategoryᵉ :
    (f : obj-Precategoryᵉ Reduced-Coslice-Precategoryᵉ) →
    hom-Precategoryᵉ C X (cod-obj-Reduced-Coslice-Precategoryᵉ f)
  hom-obj-Reduced-Coslice-Precategoryᵉ f = pr2ᵉ (pr1ᵉ f)

  hom-hom-Reduced-Coslice-Precategoryᵉ :
    (f g : obj-Precategoryᵉ Reduced-Coslice-Precategoryᵉ)
    (h : hom-Precategoryᵉ Reduced-Coslice-Precategoryᵉ f g) →
    hom-Precategoryᵉ C
      (cod-obj-Reduced-Coslice-Precategoryᵉ f)
      (cod-obj-Reduced-Coslice-Precategoryᵉ g)
  hom-hom-Reduced-Coslice-Precategoryᵉ f g h = pr1ᵉ h

  triangle-hom-Reduced-Coslice-Precategoryᵉ :
    (f g : obj-Precategoryᵉ Reduced-Coslice-Precategoryᵉ)
    (h : hom-Precategoryᵉ Reduced-Coslice-Precategoryᵉ f g) →
    comp-hom-Precategoryᵉ C
      (hom-hom-Reduced-Coslice-Precategoryᵉ f g h)
      (hom-obj-Reduced-Coslice-Precategoryᵉ f) ＝ᵉ
    hom-obj-Reduced-Coslice-Precategoryᵉ g
  triangle-hom-Reduced-Coslice-Precategoryᵉ f g h = invᵉ (pr2ᵉ h)

  inclusion-functor-Reduced-Coslice-Precategory :
    functor-Precategoryᵉ Reduced-Coslice-Precategoryᵉ (Coslice-Precategoryᵉ C X)
  inclusion-functor-Reduced-Coslice-Precategory =
    inclusion-Full-Subprecategoryᵉ
      ( Coslice-Precategoryᵉ C X)
      ( Reduced-Coslice-Full-Subcategoryᵉ)

  forgetful-functor-Reduced-Coslice-Precategoryᵉ :
    functor-Precategoryᵉ Reduced-Coslice-Precategoryᵉ C
  forgetful-functor-Reduced-Coslice-Precategoryᵉ =
    comp-functor-Precategoryᵉ
      ( Reduced-Coslice-Precategoryᵉ)
      ( Coslice-Precategoryᵉ C X)
      ( C)
      ( forgetful-functor-Coslice-Precategoryᵉ C X)
      ( inclusion-functor-Reduced-Coslice-Precategory)
```
