# Inverse categories

```agda
module category-theory.inverse-precategoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.functors-precategoriesᵉ
open import category-theory.precategoriesᵉ
open import category-theory.opposite-precategoriesᵉ
open import category-theory.isomorphisms-in-precategoriesᵉ

open import elementary-number-theory.inequality-natural-numbersᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

An inverse category is the categorification of the notion of
an inverted well order.

## Definitions

```agda
module _
  {l1 l2 l3 l4 : Level} (C : Precategoryᵉ l1 l2) (D : Precategoryᵉ l3 l4)
  (F : functor-Precategoryᵉ C D)
  where

  reflects-isos-functor-Precategoryᵉ : UUᵉ (l1 ⊔ l2 ⊔ l4)
  reflects-isos-functor-Precategoryᵉ =
    {x y : obj-Precategoryᵉ C} (f : hom-Precategoryᵉ C x y) →
    is-iso-Precategoryᵉ D (hom-functor-Precategoryᵉ C D F f) →
    is-iso-Precategoryᵉ C f

module _
  {l1 l2 : Level} (C : Precategoryᵉ l1 l2)
  where

  is-inverse-Precategoryᵉ : UUᵉ (l1 ⊔ l2)
  is-inverse-Precategoryᵉ =
    Σᵉ ( functor-Precategoryᵉ (opposite-Precategoryᵉ C) ℕ-Precategoryᵉ)
       ( λ F → reflects-isos-functor-Precategoryᵉ (opposite-Precategoryᵉ C) ℕ-Precategoryᵉ F)

inverse-Precategoryᵉ :
  (l1 l2 : Level) → UUᵉ (lsuc (l1 ⊔ l2))
inverse-Precategoryᵉ l1 l2 =
  Σᵉ ( Precategoryᵉ l1 l2)
     ( λ C → is-inverse-Precategoryᵉ C)

module _
  {l1 l2 : Level} (C : inverse-Precategoryᵉ l1 l2)
  where

  precategory-inverse-Precategoryᵉ : Precategoryᵉ l1 l2
  precategory-inverse-Precategoryᵉ = pr1ᵉ C

  is-inverse-inverse-Precategoryᵉ :
    is-inverse-Precategoryᵉ precategory-inverse-Precategoryᵉ
  is-inverse-inverse-Precategoryᵉ = pr2ᵉ C

  rank-functor-inverse-Precategoryᵉ :
    functor-Precategoryᵉ (opposite-Precategoryᵉ precategory-inverse-Precategoryᵉ) ℕ-Precategoryᵉ
  rank-functor-inverse-Precategoryᵉ = pr1ᵉ is-inverse-inverse-Precategoryᵉ

  reflects-isos-rank-functor-inverse-Precategoryᵉ :
    reflects-isos-functor-Precategoryᵉ
      (opposite-Precategoryᵉ precategory-inverse-Precategoryᵉ)
      ℕ-Precategoryᵉ
      rank-functor-inverse-Precategoryᵉ
  reflects-isos-rank-functor-inverse-Precategoryᵉ =
    pr2ᵉ is-inverse-inverse-Precategoryᵉ
```
