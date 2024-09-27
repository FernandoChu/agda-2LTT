# Reedy fibrations

```agda
module category-theory.reedy-fibrationsᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.cones-precategoriesᵉ
open import category-theory.constant-functorsᵉ
open import category-theory.functors-precategoriesᵉ
open import category-theory.precategoriesᵉ
open import category-theory.copresheaf-categoriesᵉ
open import category-theory.isomorphisms-in-precategoriesᵉ
open import category-theory.limits-precategoriesᵉ
open import category-theory.right-extensions-precategoriesᵉ
open import category-theory.right-kan-extensions-precategoriesᵉ
open import category-theory.terminal-categoryᵉ
open import category-theory.natural-transformations-functors-precategoriesᵉ
open import category-theory.inverse-precategoriesᵉ
open import category-theory.reduced-coslice-precategoryᵉ
open import category-theory.strict-simplex-precategoryᵉ
open import category-theory.matching-objectsᵉ

open import elementary-number-theory.inequality-natural-numbersᵉ

open import foundation.fibrationsᵉ
open import foundation.action-on-identifications-functionsᵉ
open import foundation.function-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.universe-levelsᵉ
open import foundation.category-of-setsᵉ
open import foundation.identity-typesᵉ
open import foundation.setsᵉ
open import foundation.unit-typeᵉ
open import foundation.standard-pullbacksᵉ
```

</details>

## Idea



## Definitions

### Reedy fibration

```agda
module _
  {l1 l2 : Level} (C : Precategoryᵉ l1 l2)
  (Y X : copresheaf-Precategoryᵉ C (l1 ⊔ l2))
  (p : hom-Precategoryᵉ (copresheaf-precategory-Precategoryᵉ C (l1 ⊔ l2)) Y X)
  where

  reedy-pullback :
    (z : obj-Precategoryᵉ C) →
    UUᵉ (l1 ⊔ l2)
  reedy-pullback z =
    standard-pullbackᵉ
      (hom-matching-functor C Y X p z)
      (hom-family-matching-natural-transformation C X z)

  reedy-map :
    (z : obj-Precategoryᵉ C) →
    type-Setᵉ
      ( obj-functor-Precategoryᵉ C (Set-Precategoryᵉ (l1 ⊔ l2)) Y z) →
    reedy-pullback z
  reedy-map z =
    gapᵉ
      ( hom-matching-functor C Y X p z)
      ( hom-family-matching-natural-transformation C X z)
      ( pairᵉ
        ( hom-family-matching-natural-transformation C Y z)
        ( pairᵉ
          ( pr1ᵉ p z)
          ( htpy-eqᵉ (pr2ᵉ (matching-natural-transformation C z) p))))

  is-reedy-fibration : UUᵉ (lsuc l1 ⊔ lsuc l2)
  is-reedy-fibration =
    (z : obj-Precategoryᵉ C) →
    is-fibration (reedy-map z)

  is-trivial-reedy-fibration : UUᵉ (lsuc l1 ⊔ lsuc l2)
  is-trivial-reedy-fibration =
    (z : obj-Precategoryᵉ C) →
    is-trivial-fibration (reedy-map z)
```

### Reedy fibrant diagrams

```agda
module _
  {l1 l2 : Level} (C : Precategoryᵉ l1 l2)
  where

  constant-functor-unit :
    copresheaf-Precategoryᵉ C (l1 ⊔ l2)
  constant-functor-unit =
    constant-functor-Precategoryᵉ
      C (Set-Precategoryᵉ (l1 ⊔ l2)) (raise-unit-Setᵉ (l1 ⊔ l2))

  terminal-natural-transformation :
    (X : copresheaf-Precategoryᵉ C (l1 ⊔ l2)) →
    natural-transformation-Precategoryᵉ C (Set-Precategoryᵉ (l1 ⊔ l2))
      X constant-functor-unit
  pr1ᵉ (terminal-natural-transformation X) c m = raise-starᵉ
  pr2ᵉ (terminal-natural-transformation X) f = reflᵉ

  is-reedy-fibrant :
    (X : copresheaf-Precategoryᵉ C (l1 ⊔ l2)) →
    UUᵉ (lsuc (l1 ⊔ l2))
  is-reedy-fibrant X =
    is-reedy-fibration C X
      constant-functor-unit (terminal-natural-transformation X)

  is-trivially-reedy-fibrant :
    (X : copresheaf-Precategoryᵉ C (l1 ⊔ l2)) →
    UUᵉ (lsuc (l1 ⊔ l2))
  is-trivially-reedy-fibrant X =
    is-trivial-reedy-fibration C X
      constant-functor-unit (terminal-natural-transformation X)
```

### Reedy semisimplicial types

```agda
Reedy-Fibrant-Semisimplicial-Type :
  UUᵉ (lsuc lzero)
Reedy-Fibrant-Semisimplicial-Type =
  Σᵉ (copresheaf-Precategoryᵉ op-strict-simplex-Precategoryᵉ lzero)
  (λ X → is-reedy-fibrant op-strict-simplex-Precategoryᵉ X)

module _
  (X : Reedy-Fibrant-Semisimplicial-Type)
  where

  diagram-Reedy-Fibrant-Semisimplicial-Type :
    copresheaf-Precategoryᵉ op-strict-simplex-Precategoryᵉ lzero
  diagram-Reedy-Fibrant-Semisimplicial-Type = pr1ᵉ X

  is-reedy-fibrant-Reedy-Fibrant-Semisimplicial-Type :
    is-reedy-fibrant
      op-strict-simplex-Precategoryᵉ
      diagram-Reedy-Fibrant-Semisimplicial-Type
  is-reedy-fibrant-Reedy-Fibrant-Semisimplicial-Type = pr2ᵉ X
```
