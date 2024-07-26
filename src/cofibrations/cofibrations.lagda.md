# Cofibrations

```agda
module cofibrations.cofibrations where
```

<details><summary>Imports</summary>

```agda
open import fibrations.fibrations
open import fibrations.fibrant-types

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
```

## Idea

## Definition

```agda
module _
  {l1 l2 : Level} {A : UUᵉ l1} {B : UUᵉ l2} (f : A → B)
  where

  is-cofibration : UUᵉ (lsuc (l1 ⊔ l2))
  is-cofibration = (b : B) → is-fibrant (fiberᵉ f b)
```
