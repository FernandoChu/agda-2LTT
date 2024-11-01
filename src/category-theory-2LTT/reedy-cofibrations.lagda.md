# Reedy cofibrations

```agda
module category-theory-2LTT.reedy-cofibrations where
```

<details><summary>Imports</summary>

```agda
open import category-theory.cones-precategoriesᵉ
open import category-theory.constant-functorsᵉ
open import category-theory.functors-precategoriesᵉ
open import category-theory.isomorphisms-in-precategoriesᵉ
open import category-theory.limits-precategoriesᵉ
open import category-theory.natural-transformations-functors-precategoriesᵉ
open import category-theory.precategoriesᵉ
open import category-theory.right-extensions-precategoriesᵉ
open import category-theory.right-kan-extensions-precategoriesᵉ

open import category-theory-2LTT.inverse-precategories
open import category-theory-2LTT.matching-objects
open import category-theory-2LTT.reduced-coslice-precategory
open import category-theory-2LTT.reedy-fibrations

open import elementary-number-theory.inequality-natural-numbersᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.category-of-setsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.empty-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.function-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.raising-universe-levelsᵉ
open import foundation.setsᵉ
open import foundation.standard-pullbacksᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import foundation-2LTT.fibrations
```

</details>

## Definitions

### Reedy fibration

```agda
module _
  {l1 l2 : Level} (C : Precategoryᵉ l1 l2)
  (Y : functor-Precategoryᵉ C (Set-Precategoryᵉ (l1 ⊔ l2)))
  (X : functor-Precategoryᵉ C (Set-Precategoryᵉ (l1 ⊔ l2)))
  (p : natural-transformation-Precategoryᵉ C (Set-Precategoryᵉ (l1 ⊔ l2)) Y X)
  where

  postulate
    is-reedy-cofibration : UUωᵉ
    is-trivial-reedy-cofibration : UUωᵉ

module _
  {l1 l2 : Level} (C : Precategoryᵉ l1 l2)
  where

  constant-functor-emptyᵉ :
    functor-Precategoryᵉ C (Set-Precategoryᵉ (l1 ⊔ l2))
  constant-functor-emptyᵉ =
    constant-functor-Precategoryᵉ
      ( C)
      ( Set-Precategoryᵉ (l1 ⊔ l2))
      ( raise-emptyᵉ (l1 ⊔ l2) ,ᵉ λ {(map-raiseᵉ ())})

  initial-natural-transformationᵉ :
    (X : functor-Precategoryᵉ C (Set-Precategoryᵉ (l1 ⊔ l2))) →
    natural-transformation-Precategoryᵉ C (Set-Precategoryᵉ (l1 ⊔ l2))
      constant-functor-emptyᵉ X
  pr1ᵉ (initial-natural-transformationᵉ X) x (map-raiseᵉ ())
  pr2ᵉ (initial-natural-transformationᵉ X) f = eq-htpyᵉ λ {(map-raiseᵉ ())}

  is-reedy-cofibrant :
    (X : functor-Precategoryᵉ C (Set-Precategoryᵉ (l1 ⊔ l2))) →
    UUωᵉ
  is-reedy-cofibrant X =
    is-reedy-cofibration C constant-functor-emptyᵉ X
      (initial-natural-transformationᵉ X)

  is-trivial-reedy-cofibrant :
    (X : functor-Precategoryᵉ C (Set-Precategoryᵉ (l1 ⊔ l2))) →
    UUωᵉ
  is-trivial-reedy-cofibrant X =
    is-trivial-reedy-cofibration C constant-functor-emptyᵉ X
      (initial-natural-transformationᵉ X)
```
