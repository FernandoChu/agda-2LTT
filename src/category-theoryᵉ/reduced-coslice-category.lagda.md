# Reduced coslice precategories

```agda
module category-theoryᵉ.reduced-coslice-category where
```

<details><summary>Imports</summary>

```agda
open import category-theory.full-subprecategoriesᵉ
open import category-theory.functors-precategoriesᵉ
open import category-theory.coslice-precategoriesᵉ
open import category-theory.precategoriesᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.negationᵉ
open import foundation.universe-levels
```

</details>

## Idea

The reduced coslice precategory of a precategory `C` under an object `X` of `C` is the
category of objects of `C` equipped with a morphism from `X`.

## Definitions


```agda
module _
  {l1 l2 : Level} (C : Precategoryᵉ l1 l2) (X : obj-Precategoryᵉ C)
  where

  Reduced-Coslice-Full-Subprecategoryᵉ :
    Full-Subprecategoryᵉ (l1 ⊔ l2) (Coslice-Precategoryᵉ C X)
  pr1ᵉ (Reduced-Coslice-Full-Subprecategoryᵉ (Y,f)) =
    ¬ᵉ ((Y,f) ＝ᵉ ((X ,ᵉ id-hom-Precategoryᵉ C)))
  pr2ᵉ (Reduced-Coslice-Full-Subprecategoryᵉ (Y,f)) =
     is-prop-negᵉ

  Reduced-Coslice-Categoryᵉ : Precategoryᵉ (l1 ⊔ l2) l2
  Reduced-Coslice-Categoryᵉ =
    precategory-Full-Subprecategoryᵉ
      ( Coslice-Precategoryᵉ C X)
      ( Reduced-Coslice-Full-Subprecategoryᵉ)

  cod-obj-Reduced-Coslice-Categoryᵉ :
    (f : obj-Precategoryᵉ Reduced-Coslice-Categoryᵉ) →
    obj-Precategoryᵉ C
  cod-obj-Reduced-Coslice-Categoryᵉ f = pr1ᵉ (pr1ᵉ f)

  hom-obj-Reduced-Coslice-Categoryᵉ :
    (f : obj-Precategoryᵉ Reduced-Coslice-Categoryᵉ) →
    hom-Precategoryᵉ C X (cod-obj-Reduced-Coslice-Categoryᵉ f)
  hom-obj-Reduced-Coslice-Categoryᵉ f = pr2ᵉ (pr1ᵉ f)

  hom-hom-Reduced-Coslice-Categoryᵉ :
    (f g : obj-Precategoryᵉ Reduced-Coslice-Categoryᵉ)
    (h : hom-Precategoryᵉ Reduced-Coslice-Categoryᵉ f g) →
    hom-Precategoryᵉ C
      (cod-obj-Reduced-Coslice-Categoryᵉ f)
      (cod-obj-Reduced-Coslice-Categoryᵉ g)
  hom-hom-Reduced-Coslice-Categoryᵉ f g h = pr1ᵉ h

  triangle-hom-Reduced-Coslice-Categoryᵉ :
    (f g : obj-Precategoryᵉ Reduced-Coslice-Categoryᵉ)
    (h : hom-Precategoryᵉ Reduced-Coslice-Categoryᵉ f g) →
    comp-hom-Precategoryᵉ C
      (hom-hom-Reduced-Coslice-Categoryᵉ f g h)
      (hom-obj-Reduced-Coslice-Categoryᵉ f) ＝ᵉ
    hom-obj-Reduced-Coslice-Categoryᵉ g
  triangle-hom-Reduced-Coslice-Categoryᵉ f g h = invᵉ (pr2ᵉ h)

  inclusion-functor-Reduced-Coslice-Category :
    functor-Precategoryᵉ Reduced-Coslice-Categoryᵉ (Coslice-Precategoryᵉ C X)
  inclusion-functor-Reduced-Coslice-Category =
    inclusion-Full-Subprecategoryᵉ
      ( Coslice-Precategoryᵉ C X)
      ( Reduced-Coslice-Full-Subprecategoryᵉ)

  forgetful-functor-Reduced-Coslice-Categoryᵉ :
    functor-Precategoryᵉ Reduced-Coslice-Categoryᵉ C
  forgetful-functor-Reduced-Coslice-Categoryᵉ =
    comp-functor-Precategoryᵉ
      ( Reduced-Coslice-Categoryᵉ)
      ( Coslice-Precategoryᵉ C X)
      ( C)
      ( forgetful-functor-Coslice-Precategoryᵉ C X)
      ( inclusion-functor-Reduced-Coslice-Category)
```
