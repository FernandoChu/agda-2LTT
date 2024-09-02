# Cofibrations

```agda
module foundation.cofibrationsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.fibrationsᵉ
open import foundation.fibrant-typesᵉ
open import foundation.universe-levelsᵉ
open import foundation.function-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.cartesian-product-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.fibers-of-mapsᵉ
open import foundation.unit-typeᵉ
open import foundation.equivalencesᵉ
open import foundation.homotopiesᵉ
open import foundation.retractionsᵉ
open import foundation.sectionsᵉ

open import orthogonal-factorization-systems.pullback-homᵉ
```

## Idea

## Definition

```agda
module _
  {l1 l2 : Level} {A : UUᵉ l1} {B : UUᵉ l2} (f : A → B)
  where

  is-cofibration : UUωᵉ
  is-cofibration =
    {l3 l4 : Level} {X : UUᵉ l2} {Y : UUᵉ l4} (p : Y → X) →
    (is-fibration p → is-fibration (pullback-homᵉ f p)) ×ᵉ
    (is-trivial-fibration p → is-trivial-fibration (pullback-homᵉ f p))

  is-trivial-cofibration : UUωᵉ
  is-trivial-cofibration =
    {l3 l4 : Level} {X : UUᵉ l2} {Y : UUᵉ l4} (p : Y → X) →
    is-fibration p → is-trivial-fibration (pullback-homᵉ f p)
```
