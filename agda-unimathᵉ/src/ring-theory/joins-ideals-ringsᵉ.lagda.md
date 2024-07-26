# Joins of ideals of rings

```agda
module ring-theory.joins-ideals-ringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.unions-subtypesᵉ
open import foundation.universe-levelsᵉ

open import order-theory.large-suplatticesᵉ
open import order-theory.least-upper-bounds-large-posetsᵉ
open import order-theory.similarity-of-elements-large-posetsᵉ

open import ring-theory.ideals-generated-by-subsets-ringsᵉ
open import ring-theory.ideals-ringsᵉ
open import ring-theory.poset-of-ideals-ringsᵉ
open import ring-theory.ringsᵉ
open import ring-theory.subsets-ringsᵉ
```

</details>

## Idea

Theᵉ **join**ᵉ ofᵉ aᵉ familyᵉ ofᵉ [ideals](ring-theory.ideals-rings.mdᵉ) ofᵉ
[rings](ring-theory.rings.mdᵉ) isᵉ theᵉ leastᵉ idealᵉ containingᵉ allᵉ theᵉ idealsᵉ in
theᵉ familyᵉ ofᵉ ideals.ᵉ Inᵉ otherᵉ words,ᵉ theᵉ joinᵉ ofᵉ aᵉ familyᵉ ofᵉ idealsᵉ isᵉ theᵉ
[idealᵉ generatedᵉ by](ring-theory.ideals-generated-by-subsets-rings.mdᵉ) theᵉ unionᵉ
ofᵉ theᵉ underlyingᵉ subsetsᵉ ofᵉ theᵉ idealsᵉ in theᵉ familyᵉ ofᵉ ideals.ᵉ

## Definitions

### The predicate of being the join of a family of ideals

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ) {Uᵉ : UUᵉ l2ᵉ} (Iᵉ : Uᵉ → ideal-Ringᵉ l3ᵉ Rᵉ)
  where

  is-join-family-of-ideals-Ringᵉ :
    {l4ᵉ : Level} → ideal-Ringᵉ l4ᵉ Rᵉ → UUωᵉ
  is-join-family-of-ideals-Ringᵉ =
    is-least-upper-bound-family-of-elements-Large-Posetᵉ
      ( ideal-Ring-Large-Posetᵉ Rᵉ)
      ( Iᵉ)

  inclusion-is-join-family-of-ideals-Ringᵉ :
    {l4ᵉ l5ᵉ : Level} (Jᵉ : ideal-Ringᵉ l4ᵉ Rᵉ) →
    is-join-family-of-ideals-Ringᵉ Jᵉ →
    (Kᵉ : ideal-Ringᵉ l5ᵉ Rᵉ) → ((αᵉ : Uᵉ) → leq-ideal-Ringᵉ Rᵉ (Iᵉ αᵉ) Kᵉ) →
    leq-ideal-Ringᵉ Rᵉ Jᵉ Kᵉ
  inclusion-is-join-family-of-ideals-Ringᵉ Jᵉ Hᵉ Kᵉ =
    pr1ᵉ (Hᵉ Kᵉ)

  contains-ideal-is-join-family-of-ideals-Ringᵉ :
    {l4ᵉ : Level} (Jᵉ : ideal-Ringᵉ l4ᵉ Rᵉ) →
    is-join-family-of-ideals-Ringᵉ Jᵉ →
    {αᵉ : Uᵉ} → leq-ideal-Ringᵉ Rᵉ (Iᵉ αᵉ) Jᵉ
  contains-ideal-is-join-family-of-ideals-Ringᵉ Jᵉ Hᵉ {αᵉ} =
    pr2ᵉ (Hᵉ Jᵉ) (refl-leq-ideal-Ringᵉ Rᵉ Jᵉ) αᵉ
```

### The join of a family of ideals

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ) {Uᵉ : UUᵉ l2ᵉ} (Iᵉ : Uᵉ → ideal-Ringᵉ l3ᵉ Rᵉ)
  where

  generating-subset-join-family-of-ideals-Ringᵉ :
    subset-Ringᵉ (l2ᵉ ⊔ l3ᵉ) Rᵉ
  generating-subset-join-family-of-ideals-Ringᵉ =
    union-family-of-subtypesᵉ (λ αᵉ → subset-ideal-Ringᵉ Rᵉ (Iᵉ αᵉ))

  join-family-of-ideals-Ringᵉ :
    ideal-Ringᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ) Rᵉ
  join-family-of-ideals-Ringᵉ =
    ideal-family-of-subsets-Ringᵉ Rᵉ (λ αᵉ → subset-ideal-Ringᵉ Rᵉ (Iᵉ αᵉ))

  forward-inclusion-is-join-join-family-of-ideals-Ringᵉ :
    {l4ᵉ : Level} (Kᵉ : ideal-Ringᵉ l4ᵉ Rᵉ) →
    ((αᵉ : Uᵉ) → leq-ideal-Ringᵉ Rᵉ (Iᵉ αᵉ) Kᵉ) →
    leq-ideal-Ringᵉ Rᵉ join-family-of-ideals-Ringᵉ Kᵉ
  forward-inclusion-is-join-join-family-of-ideals-Ringᵉ Kᵉ Hᵉ =
    is-ideal-generated-by-family-of-subsets-ideal-family-of-subsets-Ringᵉ Rᵉ
      ( λ αᵉ → subset-ideal-Ringᵉ Rᵉ (Iᵉ αᵉ))
      ( Kᵉ)
      ( λ {αᵉ} xᵉ → Hᵉ αᵉ xᵉ)

  backward-inclusion-is-join-join-family-of-ideals-Ringᵉ :
    {l4ᵉ : Level} (Kᵉ : ideal-Ringᵉ l4ᵉ Rᵉ) →
    leq-ideal-Ringᵉ Rᵉ join-family-of-ideals-Ringᵉ Kᵉ →
    (αᵉ : Uᵉ) → leq-ideal-Ringᵉ Rᵉ (Iᵉ αᵉ) Kᵉ
  backward-inclusion-is-join-join-family-of-ideals-Ringᵉ Kᵉ Hᵉ _ xᵉ pᵉ =
    Hᵉ ( xᵉ)
      ( contains-subset-ideal-family-of-subsets-Ringᵉ Rᵉ
        ( λ αᵉ → subset-ideal-Ringᵉ Rᵉ (Iᵉ αᵉ))
        ( xᵉ)
        ( pᵉ))

  is-join-join-family-of-ideals-Ringᵉ :
    is-join-family-of-ideals-Ringᵉ Rᵉ Iᵉ join-family-of-ideals-Ringᵉ
  pr1ᵉ (is-join-join-family-of-ideals-Ringᵉ Kᵉ) =
    forward-inclusion-is-join-join-family-of-ideals-Ringᵉ Kᵉ
  pr2ᵉ (is-join-join-family-of-ideals-Ringᵉ Kᵉ) =
    backward-inclusion-is-join-join-family-of-ideals-Ringᵉ Kᵉ

  inclusion-join-family-of-ideals-Ringᵉ :
    {l4ᵉ : Level} (Jᵉ : ideal-Ringᵉ l4ᵉ Rᵉ) →
    ((αᵉ : Uᵉ) → leq-ideal-Ringᵉ Rᵉ (Iᵉ αᵉ) Jᵉ) →
    leq-ideal-Ringᵉ Rᵉ join-family-of-ideals-Ringᵉ Jᵉ
  inclusion-join-family-of-ideals-Ringᵉ =
    inclusion-is-join-family-of-ideals-Ringᵉ Rᵉ Iᵉ
      ( join-family-of-ideals-Ringᵉ)
      ( is-join-join-family-of-ideals-Ringᵉ)

  contains-ideal-join-family-of-ideals-Ringᵉ :
    {αᵉ : Uᵉ} → leq-ideal-Ringᵉ Rᵉ (Iᵉ αᵉ) join-family-of-ideals-Ringᵉ
  contains-ideal-join-family-of-ideals-Ringᵉ =
    contains-ideal-is-join-family-of-ideals-Ringᵉ Rᵉ Iᵉ
      ( join-family-of-ideals-Ringᵉ)
      ( is-join-join-family-of-ideals-Ringᵉ)
```

### The large suplattice of ideals in a ring

```agda
module _
  {l1ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ)
  where

  is-large-suplattice-ideal-Ring-Large-Posetᵉ :
    is-large-suplattice-Large-Posetᵉ l1ᵉ (ideal-Ring-Large-Posetᵉ Rᵉ)
  sup-has-least-upper-bound-family-of-elements-Large-Posetᵉ
    ( is-large-suplattice-ideal-Ring-Large-Posetᵉ Iᵉ) =
    join-family-of-ideals-Ringᵉ Rᵉ Iᵉ
  is-least-upper-bound-sup-has-least-upper-bound-family-of-elements-Large-Posetᵉ
    ( is-large-suplattice-ideal-Ring-Large-Posetᵉ Iᵉ) =
    is-join-join-family-of-ideals-Ringᵉ Rᵉ Iᵉ

  ideal-Ring-Large-Suplatticeᵉ :
    Large-Suplatticeᵉ (λ l2ᵉ → l1ᵉ ⊔ lsuc l2ᵉ) (λ l2ᵉ l3ᵉ → l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ) l1ᵉ
  large-poset-Large-Suplatticeᵉ
    ideal-Ring-Large-Suplatticeᵉ =
    ideal-Ring-Large-Posetᵉ Rᵉ
  is-large-suplattice-Large-Suplatticeᵉ
    ideal-Ring-Large-Suplatticeᵉ =
    is-large-suplattice-ideal-Ring-Large-Posetᵉ
```

## Properties

### If `I α ⊆ J α` for each `α`, then `⋁ I ⊆ ⋁ J`

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Aᵉ : Ringᵉ l1ᵉ)
  {Uᵉ : UUᵉ l2ᵉ}
  (Iᵉ : Uᵉ → ideal-Ringᵉ l3ᵉ Aᵉ)
  (Jᵉ : Uᵉ → ideal-Ringᵉ l4ᵉ Aᵉ)
  (Hᵉ : (αᵉ : Uᵉ) → leq-ideal-Ringᵉ Aᵉ (Iᵉ αᵉ) (Jᵉ αᵉ))
  where

  preserves-order-join-family-of-ideals-Ringᵉ :
    leq-ideal-Ringᵉ Aᵉ
      ( join-family-of-ideals-Ringᵉ Aᵉ Iᵉ)
      ( join-family-of-ideals-Ringᵉ Aᵉ Jᵉ)
  preserves-order-join-family-of-ideals-Ringᵉ =
    preserves-order-sup-Large-Suplatticeᵉ
      ( ideal-Ring-Large-Suplatticeᵉ Aᵉ)
      { xᵉ = Iᵉ}
      { yᵉ = Jᵉ}
      ( Hᵉ)
```

### The operation `S ↦ (S)` preserves joins

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ) {Uᵉ : UUᵉ l2ᵉ} (Sᵉ : Uᵉ → subset-Ringᵉ l3ᵉ Rᵉ)
  where

  is-least-upper-bound-join-ideal-subset-Ringᵉ :
    is-least-upper-bound-family-of-elements-Large-Posetᵉ
      ( ideal-Ring-Large-Posetᵉ Rᵉ)
      ( λ αᵉ → ideal-subset-Ringᵉ Rᵉ (Sᵉ αᵉ))
      ( ideal-subset-Ringᵉ Rᵉ (union-family-of-subtypesᵉ Sᵉ))
  is-least-upper-bound-join-ideal-subset-Ringᵉ =
    preserves-least-upper-bounds-ideal-subset-Ringᵉ Rᵉ Sᵉ
      ( union-family-of-subtypesᵉ Sᵉ)
      ( is-least-upper-bound-union-family-of-subtypesᵉ Sᵉ)

  sim-preserves-join-ideal-subset-Ringᵉ :
    sim-ideal-Ringᵉ Rᵉ
      ( ideal-subset-Ringᵉ Rᵉ (union-family-of-subtypesᵉ Sᵉ))
      ( join-family-of-ideals-Ringᵉ Rᵉ (λ αᵉ → ideal-subset-Ringᵉ Rᵉ (Sᵉ αᵉ)))
  sim-preserves-join-ideal-subset-Ringᵉ =
    sim-is-least-upper-bound-family-of-elements-Large-Posetᵉ
      ( ideal-Ring-Large-Posetᵉ Rᵉ)
      { xᵉ = λ αᵉ → ideal-subset-Ringᵉ Rᵉ (Sᵉ αᵉ)}
      { yᵉ = ideal-subset-Ringᵉ Rᵉ (union-family-of-subtypesᵉ Sᵉ)}
      { zᵉ = join-family-of-ideals-Ringᵉ Rᵉ (λ αᵉ → ideal-subset-Ringᵉ Rᵉ (Sᵉ αᵉ))}
      ( is-least-upper-bound-join-ideal-subset-Ringᵉ)
      ( is-join-join-family-of-ideals-Ringᵉ Rᵉ
        ( λ αᵉ → ideal-subset-Ringᵉ Rᵉ (Sᵉ αᵉ)))

  preserves-join-ideal-subset-Ringᵉ :
    ideal-subset-Ringᵉ Rᵉ (union-family-of-subtypesᵉ Sᵉ) ＝ᵉ
    join-family-of-ideals-Ringᵉ Rᵉ (λ αᵉ → ideal-subset-Ringᵉ Rᵉ (Sᵉ αᵉ))
  preserves-join-ideal-subset-Ringᵉ =
    eq-sim-Large-Posetᵉ
      ( ideal-Ring-Large-Posetᵉ Rᵉ)
      ( ideal-subset-Ringᵉ Rᵉ (union-family-of-subtypesᵉ Sᵉ))
      ( join-family-of-ideals-Ringᵉ Rᵉ (λ αᵉ → ideal-subset-Ringᵉ Rᵉ (Sᵉ αᵉ)))
      ( sim-preserves-join-ideal-subset-Ringᵉ)
```