# Fibrations

```agda
module fibrations.fibrations where
```

<details><summary>Imports</summary>

```agda
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

open import fibrations.fibrant-types
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

```agda
module _
  {l1 : Level} {A : UUᵉ l1}
  where

  is-fibration-terminal-map-is-fibrant :
    is-fibration (terminal-mapᵉ A) → is-fibrant A
  is-fibration-terminal-map-is-fibrant is-fibration-! =
    is-fibrant-equivᵉ (is-fibration-! starᵉ) (equiv-fiber-terminal-mapᵉ starᵉ)

  is-fibrant-is-fibration-terminal-map :
    is-fibrant A → is-fibration (terminal-mapᵉ A)
  is-fibrant-is-fibration-terminal-map is-fibrant-A a =
    is-fibrant-equivᵉ is-fibrant-A (inv-equivᵉ (equiv-fiber-terminal-mapᵉ starᵉ))
```
