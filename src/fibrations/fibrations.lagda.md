# Fibrations

```agda
module fibrations.fibrations where
```

<details><summary>Imports</summary>

```agda
open import foundation.fibrant-exo-types
open import foundation.exo-universes
open import foundation.exo-function-types
open import foundation.exo-homotopies
open import foundation.exo-dependent-pair-types
open import foundation.exo-cartesian-product-types
open import foundation.exo-identity-types
open import foundation.exo-fibers-of-exo-maps

open import foundation.exo-isomorphisms
open import foundation.exo-homotopies
open import foundation.exo-retractions
open import foundation.exo-sections
```

## Idea

## Definition

```agda
module _
  {l1 l2 : Level} {A : UUᵉ l1} {B : UUᵉ l2} (f : A → B)
  where

  is-fibration : UUᵉ (lsuc (l1 ⊔ l2))
  is-fibration = (b : B) → is-fibrant (fiberᵉ f b)

  is-trivial-fibration : UUᵉ (lsuc (l1 ⊔ l2))
  is-trivial-fibration = (b : B) → is-trivially-fibrant (fiberᵉ f b)
```
