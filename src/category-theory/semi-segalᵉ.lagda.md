# Semi-Segal types

```agda
module category-theory.semi-segalᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.cones-precategoriesᵉ
open import category-theory.constant-functorsᵉ
open import category-theory.copresheaf-categoriesᵉ
open import category-theory.functors-precategoriesᵉ
open import category-theory.precategoriesᵉ
open import category-theory.isomorphisms-in-precategoriesᵉ
open import category-theory.limits-precategoriesᵉ
open import category-theory.right-extensions-precategoriesᵉ
open import category-theory.right-kan-extensions-precategoriesᵉ
open import category-theory.terminal-categoryᵉ
open import category-theory.natural-transformations-functors-precategoriesᵉ

open import category-theory.inverse-categoriesᵉ
open import category-theory.reduced-coslice-categoryᵉ
open import category-theory.strict-simplex-categoryᵉ

open import elementary-number-theory.inequality-natural-numbersᵉ


open import elementary-number-theory.natural-numbersᵉ

open import foundation.fibrationsᵉ
open import foundation.fibrant-typesᵉ
open import foundation.action-on-identifications-functionsᵉ
open import foundation.fibers-of-mapsᵉ
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
open import foundation.matching-objectsᵉ
open import foundation.reedy-fibrationsᵉ
```

</details>

## Idea


## Definitions

### Semi segal

```agda
module _
  (X : Reedy-Fibrant-Semisimplicial-Type)
  where

  is-semi-segal : UUᵉ (lsuc lzero)
  is-semi-segal =
    (k n : ℕᵉ) → lt-ℕᵉ 0ᵉ k → lt-ℕᵉ k n →
    is-trivial-fibration
      λ τ →
        comp-natural-transformation-Precategoryᵉ
          ( op-strict-simplex-Categoryᵉ)
          ( Set-Precategoryᵉ lzero)
          ( horn-strict-simplex k n)
          ( standard-strict-simplex n)
          ( diagram-Reedy-Fibrant-Semisimplicial-Type X)
          ( τ)
          ( horn-inclusion-strict-simplex k n)

Semi-Segal : UUᵉ (lsuc lzero)
Semi-Segal =
  Σᵉ Reedy-Fibrant-Semisimplicial-Type is-semi-segal

module _
  (X : Semi-Segal)
  where

  reedy-fibrant-semisimplicial-type-Semi-Segal :
    Reedy-Fibrant-Semisimplicial-Type
  reedy-fibrant-semisimplicial-type-Semi-Segal = pr1ᵉ X

  diagram-Semi-Segal :
    copresheaf-Precategoryᵉ op-strict-simplex-Categoryᵉ lzero
  diagram-Semi-Segal =
    diagram-Reedy-Fibrant-Semisimplicial-Type
      reedy-fibrant-semisimplicial-type-Semi-Segal

  is-reedy-fibrant-Semi-Segal :
    is-reedy-fibrant op-strict-simplex-Categoryᵉ diagram-Semi-Segal
  is-reedy-fibrant-Semi-Segal =
    is-reedy-fibrant-Reedy-Fibrant-Semisimplicial-Type
      reedy-fibrant-semisimplicial-type-Semi-Segal

  is-semi-segal-Semi-Segal :
    is-semi-segal reedy-fibrant-semisimplicial-type-Semi-Segal
  is-semi-segal-Semi-Segal = pr2ᵉ X

  horn-filler-Semi-Segal :
    (k n : ℕᵉ) → lt-ℕᵉ 0ᵉ k → lt-ℕᵉ k n →
    strict-simplicial-map
      (horn-strict-simplex k n)
      (diagram-Semi-Segal) →
    strict-simplicial-map
      (standard-strict-simplex n)
      (diagram-Semi-Segal)
  horn-filler-Semi-Segal k n 0<k k<n τ =
    pr1ᵉ (center-is-trivially-fibrant (is-semi-segal-Semi-Segal k n 0<k k<n τ))
```
