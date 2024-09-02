# Inverse categories

```agda
module category-theory.inverse-categoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.functors-precategoriesᵉ
open import category-theory.precategoriesᵉ
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

  reflects-isos-functor-Categoryᵉ : UUᵉ (l1 ⊔ l2 ⊔ l4)
  reflects-isos-functor-Categoryᵉ =
    {x y : obj-Precategoryᵉ C} (f : hom-Precategoryᵉ C x y) →
    is-iso-Precategoryᵉ D (hom-functor-Precategoryᵉ C D F f) →
    is-iso-Precategoryᵉ C f

module _
  {l1 l2 : Level} (C : Precategoryᵉ l1 l2)
  where

  is-inverse-Categoryᵉ : UUᵉ (l1 ⊔ l2)
  is-inverse-Categoryᵉ =
    Σᵉ ( functor-Precategoryᵉ C ℕ-Precategoryᵉ)
       ( λ F → reflects-isos-functor-Categoryᵉ C ℕ-Precategoryᵉ F)

Inverse-Categoryᵉ :
  (l1 l2 : Level) → UUᵉ (lsuc (l1 ⊔ l2))
Inverse-Categoryᵉ l1 l2 =
  Σᵉ ( Precategoryᵉ l1 l2)
     ( λ C → is-inverse-Categoryᵉ C)

module _
  {l1 l2 : Level} (C : Inverse-Categoryᵉ l1 l2)
  where

  category-Inverse-Categoryᵉ : Precategoryᵉ l1 l2
  category-Inverse-Categoryᵉ = pr1ᵉ C

  is-inverse-Inverse-Categoryᵉ : is-inverse-Categoryᵉ category-Inverse-Categoryᵉ
  is-inverse-Inverse-Categoryᵉ = pr2ᵉ C

  rank-functor-Inverse-Categoryᵉ :
    functor-Precategoryᵉ category-Inverse-Categoryᵉ ℕ-Precategoryᵉ
  rank-functor-Inverse-Categoryᵉ = pr1ᵉ is-inverse-Inverse-Categoryᵉ

  reflects-isos-rank-functor-Inverse-Categoryᵉ :
    reflects-isos-functor-Categoryᵉ
      category-Inverse-Categoryᵉ
      ℕ-Precategoryᵉ
      rank-functor-Inverse-Categoryᵉ
  reflects-isos-rank-functor-Inverse-Categoryᵉ =
    pr2ᵉ is-inverse-Inverse-Categoryᵉ
```
