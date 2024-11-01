# Fibrations

```agda
module foundation-2LTT.fibrations where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.fibers-of-mapsᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.retractionsᵉ
open import foundation.sectionsᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import foundation-2LTT.fibrant-types
```

</details>

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
  {l1 l2 : Level} (A : UUᵉ l1) (B : UUᵉ l2)
  where

  Fibration : UUᵉ (lsuc (l1 ⊔ l2))
  Fibration = Σᵉ (A → B) (λ f → is-fibration f)

module _
  {l1 l2 : Level} {A : UUᵉ l1} {B : UUᵉ l2} (p : Fibration A B)
  where

  map-Fibration : A → B
  map-Fibration = pr1ᵉ p

  map-is-fibration-Fibration : is-fibration map-Fibration
  map-is-fibration-Fibration = pr2ᵉ p
```

```agda
module _
  {l1 l2 : Level} (A : UUᵉ l1) (B : UUᵉ l2)
  where

  Trivial-Fibration : UUᵉ (lsuc (l1 ⊔ l2))
  Trivial-Fibration = Σᵉ (A → B) (λ f → is-trivial-fibration f)

module _
  {l1 l2 : Level} {A : UUᵉ l1} {B : UUᵉ l2} (p : Trivial-Fibration A B)
  where

  map-Trivial-Fibration : A → B
  map-Trivial-Fibration = pr1ᵉ p

  map-is-trivial-fibration-Trivial-Fibration :
    is-trivial-fibration map-Trivial-Fibration
  map-is-trivial-fibration-Trivial-Fibration = pr2ᵉ p
```

## Properties

### Characterization of fibrant types as fibrations over 1

```agda
is-fibration-terminal-map-is-fibrant :
  {l1 : Level} {A : UUᵉ l1} →
  is-fibration (terminal-mapᵉ A) → is-fibrant A
is-fibration-terminal-map-is-fibrant is-fibration-! =
  is-fibrant-equivᵉ (is-fibration-! starᵉ) (equiv-fiber-terminal-mapᵉ starᵉ)

is-fibrant-is-fibration-terminal-map :
  {l1 : Level} {A : UUᵉ l1} →
  is-fibrant A → is-fibration (terminal-mapᵉ A)
is-fibrant-is-fibration-terminal-map is-fibrant-A a =
  is-fibrant-equivᵉ is-fibrant-A (inv-equivᵉ (equiv-fiber-terminal-mapᵉ starᵉ))
```
