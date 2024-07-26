# Joins of left ideals of rings

```agda
module ring-theory.joins-left-ideals-ringsᵉ where
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

open import ring-theory.left-ideals-generated-by-subsets-ringsᵉ
open import ring-theory.left-ideals-ringsᵉ
open import ring-theory.poset-of-left-ideals-ringsᵉ
open import ring-theory.ringsᵉ
open import ring-theory.subsets-ringsᵉ
```

</details>

## Idea

Theᵉ **join**ᵉ ofᵉ aᵉ familyᵉ ofᵉ [leftᵉ ideals](ring-theory.left-ideals-rings.mdᵉ) ofᵉ
[rings](ring-theory.rings.mdᵉ) isᵉ theᵉ leastᵉ leftᵉ idealᵉ containingᵉ allᵉ theᵉ leftᵉ
idealsᵉ in theᵉ familyᵉ ofᵉ leftᵉ ideals.ᵉ Inᵉ otherᵉ words,ᵉ theᵉ joinᵉ ofᵉ aᵉ familyᵉ ofᵉ
leftᵉ idealsᵉ isᵉ theᵉ
[leftᵉ idealᵉ generatedᵉ by](ring-theory.left-ideals-generated-by-subsets-rings.mdᵉ)
theᵉ unionᵉ ofᵉ theᵉ underlyingᵉ subsetsᵉ ofᵉ theᵉ leftᵉ idealsᵉ in theᵉ familyᵉ ofᵉ leftᵉ
ideals.ᵉ

## Definitions

### The predicate of being the join of a family of left ideals

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ) {Uᵉ : UUᵉ l2ᵉ} (Iᵉ : Uᵉ → left-ideal-Ringᵉ l3ᵉ Rᵉ)
  where

  is-join-family-of-left-ideals-Ringᵉ :
    {l4ᵉ : Level} → left-ideal-Ringᵉ l4ᵉ Rᵉ → UUωᵉ
  is-join-family-of-left-ideals-Ringᵉ =
    is-least-upper-bound-family-of-elements-Large-Posetᵉ
      ( left-ideal-Ring-Large-Posetᵉ Rᵉ)
      ( Iᵉ)

  inclusion-is-join-family-of-left-ideals-Ringᵉ :
    {l4ᵉ l5ᵉ : Level} (Jᵉ : left-ideal-Ringᵉ l4ᵉ Rᵉ) →
    is-join-family-of-left-ideals-Ringᵉ Jᵉ →
    (Kᵉ : left-ideal-Ringᵉ l5ᵉ Rᵉ) → ((αᵉ : Uᵉ) → leq-left-ideal-Ringᵉ Rᵉ (Iᵉ αᵉ) Kᵉ) →
    leq-left-ideal-Ringᵉ Rᵉ Jᵉ Kᵉ
  inclusion-is-join-family-of-left-ideals-Ringᵉ Jᵉ Hᵉ Kᵉ =
    pr1ᵉ (Hᵉ Kᵉ)

  contains-left-ideal-is-join-family-of-left-ideals-Ringᵉ :
    {l4ᵉ : Level} (Jᵉ : left-ideal-Ringᵉ l4ᵉ Rᵉ) →
    is-join-family-of-left-ideals-Ringᵉ Jᵉ →
    {αᵉ : Uᵉ} → leq-left-ideal-Ringᵉ Rᵉ (Iᵉ αᵉ) Jᵉ
  contains-left-ideal-is-join-family-of-left-ideals-Ringᵉ Jᵉ Hᵉ {αᵉ} =
    pr2ᵉ (Hᵉ Jᵉ) (refl-leq-left-ideal-Ringᵉ Rᵉ Jᵉ) αᵉ
```

### The join of a family of left ideals

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ) {Uᵉ : UUᵉ l2ᵉ} (Iᵉ : Uᵉ → left-ideal-Ringᵉ l3ᵉ Rᵉ)
  where

  generating-subset-join-family-of-left-ideals-Ringᵉ :
    subset-Ringᵉ (l2ᵉ ⊔ l3ᵉ) Rᵉ
  generating-subset-join-family-of-left-ideals-Ringᵉ =
    union-family-of-subtypesᵉ (λ αᵉ → subset-left-ideal-Ringᵉ Rᵉ (Iᵉ αᵉ))

  join-family-of-left-ideals-Ringᵉ :
    left-ideal-Ringᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ) Rᵉ
  join-family-of-left-ideals-Ringᵉ =
    left-ideal-family-of-subsets-Ringᵉ Rᵉ (λ αᵉ → subset-left-ideal-Ringᵉ Rᵉ (Iᵉ αᵉ))

  forward-inclusion-is-join-join-family-of-left-ideals-Ringᵉ :
    {l4ᵉ : Level} (Kᵉ : left-ideal-Ringᵉ l4ᵉ Rᵉ) →
    ((αᵉ : Uᵉ) → leq-left-ideal-Ringᵉ Rᵉ (Iᵉ αᵉ) Kᵉ) →
    leq-left-ideal-Ringᵉ Rᵉ join-family-of-left-ideals-Ringᵉ Kᵉ
  forward-inclusion-is-join-join-family-of-left-ideals-Ringᵉ Kᵉ Hᵉ =
    is-left-ideal-generated-by-family-of-subsets-left-ideal-family-of-subsets-Ringᵉ
      ( Rᵉ)
      ( λ αᵉ → subset-left-ideal-Ringᵉ Rᵉ (Iᵉ αᵉ))
      ( Kᵉ)
      ( λ αᵉ xᵉ → Hᵉ αᵉ xᵉ)

  backward-inclusion-is-join-join-family-of-left-ideals-Ringᵉ :
    {l4ᵉ : Level} (Kᵉ : left-ideal-Ringᵉ l4ᵉ Rᵉ) →
    leq-left-ideal-Ringᵉ Rᵉ join-family-of-left-ideals-Ringᵉ Kᵉ →
    (αᵉ : Uᵉ) → leq-left-ideal-Ringᵉ Rᵉ (Iᵉ αᵉ) Kᵉ
  backward-inclusion-is-join-join-family-of-left-ideals-Ringᵉ Kᵉ Hᵉ _ xᵉ pᵉ =
    Hᵉ ( xᵉ)
      ( contains-subset-left-ideal-family-of-subsets-Ringᵉ Rᵉ
        ( λ αᵉ → subset-left-ideal-Ringᵉ Rᵉ (Iᵉ αᵉ))
        ( xᵉ)
        ( pᵉ))

  is-join-join-family-of-left-ideals-Ringᵉ :
    is-join-family-of-left-ideals-Ringᵉ Rᵉ Iᵉ join-family-of-left-ideals-Ringᵉ
  pr1ᵉ (is-join-join-family-of-left-ideals-Ringᵉ Kᵉ) =
    forward-inclusion-is-join-join-family-of-left-ideals-Ringᵉ Kᵉ
  pr2ᵉ (is-join-join-family-of-left-ideals-Ringᵉ Kᵉ) =
    backward-inclusion-is-join-join-family-of-left-ideals-Ringᵉ Kᵉ

  inclusion-join-family-of-left-ideals-Ringᵉ :
    {l4ᵉ : Level} (Jᵉ : left-ideal-Ringᵉ l4ᵉ Rᵉ) →
    ((αᵉ : Uᵉ) → leq-left-ideal-Ringᵉ Rᵉ (Iᵉ αᵉ) Jᵉ) →
    leq-left-ideal-Ringᵉ Rᵉ join-family-of-left-ideals-Ringᵉ Jᵉ
  inclusion-join-family-of-left-ideals-Ringᵉ =
    inclusion-is-join-family-of-left-ideals-Ringᵉ Rᵉ Iᵉ
      ( join-family-of-left-ideals-Ringᵉ)
      ( is-join-join-family-of-left-ideals-Ringᵉ)

  contains-left-ideal-join-family-of-left-ideals-Ringᵉ :
    {αᵉ : Uᵉ} → leq-left-ideal-Ringᵉ Rᵉ (Iᵉ αᵉ) join-family-of-left-ideals-Ringᵉ
  contains-left-ideal-join-family-of-left-ideals-Ringᵉ =
    contains-left-ideal-is-join-family-of-left-ideals-Ringᵉ Rᵉ Iᵉ
      ( join-family-of-left-ideals-Ringᵉ)
      ( is-join-join-family-of-left-ideals-Ringᵉ)
```

### The large suplattice of left ideals in a ring

```agda
module _
  {l1ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ)
  where

  is-large-suplattice-left-ideal-Ring-Large-Posetᵉ :
    is-large-suplattice-Large-Posetᵉ l1ᵉ (left-ideal-Ring-Large-Posetᵉ Rᵉ)
  sup-has-least-upper-bound-family-of-elements-Large-Posetᵉ
    ( is-large-suplattice-left-ideal-Ring-Large-Posetᵉ Iᵉ) =
    join-family-of-left-ideals-Ringᵉ Rᵉ Iᵉ
  is-least-upper-bound-sup-has-least-upper-bound-family-of-elements-Large-Posetᵉ
    ( is-large-suplattice-left-ideal-Ring-Large-Posetᵉ Iᵉ) =
    is-join-join-family-of-left-ideals-Ringᵉ Rᵉ Iᵉ

  left-ideal-Ring-Large-Suplatticeᵉ :
    Large-Suplatticeᵉ (λ l2ᵉ → l1ᵉ ⊔ lsuc l2ᵉ) (λ l2ᵉ l3ᵉ → l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ) l1ᵉ
  large-poset-Large-Suplatticeᵉ
    left-ideal-Ring-Large-Suplatticeᵉ =
    left-ideal-Ring-Large-Posetᵉ Rᵉ
  is-large-suplattice-Large-Suplatticeᵉ
    left-ideal-Ring-Large-Suplatticeᵉ =
    is-large-suplattice-left-ideal-Ring-Large-Posetᵉ
```

## Properties

### If `I α ⊆ J α` for each `α`, then `⋁ I ⊆ ⋁ J`

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Aᵉ : Ringᵉ l1ᵉ)
  {Uᵉ : UUᵉ l2ᵉ}
  (Iᵉ : Uᵉ → left-ideal-Ringᵉ l3ᵉ Aᵉ)
  (Jᵉ : Uᵉ → left-ideal-Ringᵉ l4ᵉ Aᵉ)
  (Hᵉ : (αᵉ : Uᵉ) → leq-left-ideal-Ringᵉ Aᵉ (Iᵉ αᵉ) (Jᵉ αᵉ))
  where

  preserves-order-join-family-of-left-ideals-Ringᵉ :
    leq-left-ideal-Ringᵉ Aᵉ
      ( join-family-of-left-ideals-Ringᵉ Aᵉ Iᵉ)
      ( join-family-of-left-ideals-Ringᵉ Aᵉ Jᵉ)
  preserves-order-join-family-of-left-ideals-Ringᵉ =
    preserves-order-sup-Large-Suplatticeᵉ
      ( left-ideal-Ring-Large-Suplatticeᵉ Aᵉ)
      { xᵉ = Iᵉ}
      { yᵉ = Jᵉ}
      ( Hᵉ)
```

### The operation `S ↦ (S)` preserves joins

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ) {Uᵉ : UUᵉ l2ᵉ} (Sᵉ : Uᵉ → subset-Ringᵉ l3ᵉ Rᵉ)
  where

  is-least-upper-bound-join-left-ideal-subset-Ringᵉ :
    is-least-upper-bound-family-of-elements-Large-Posetᵉ
      ( left-ideal-Ring-Large-Posetᵉ Rᵉ)
      ( λ αᵉ → left-ideal-subset-Ringᵉ Rᵉ (Sᵉ αᵉ))
      ( left-ideal-subset-Ringᵉ Rᵉ (union-family-of-subtypesᵉ Sᵉ))
  is-least-upper-bound-join-left-ideal-subset-Ringᵉ =
    preserves-least-upper-bounds-left-ideal-subset-Ringᵉ Rᵉ Sᵉ
      ( union-family-of-subtypesᵉ Sᵉ)
      ( is-least-upper-bound-union-family-of-subtypesᵉ Sᵉ)

  sim-preserves-join-left-ideal-subset-Ringᵉ :
    sim-left-ideal-Ringᵉ Rᵉ
      ( left-ideal-subset-Ringᵉ Rᵉ (union-family-of-subtypesᵉ Sᵉ))
      ( join-family-of-left-ideals-Ringᵉ Rᵉ
        ( λ αᵉ → left-ideal-subset-Ringᵉ Rᵉ (Sᵉ αᵉ)))
  sim-preserves-join-left-ideal-subset-Ringᵉ =
    sim-is-least-upper-bound-family-of-elements-Large-Posetᵉ
      ( left-ideal-Ring-Large-Posetᵉ Rᵉ)
      { xᵉ = λ αᵉ → left-ideal-subset-Ringᵉ Rᵉ (Sᵉ αᵉ)}
      { yᵉ = left-ideal-subset-Ringᵉ Rᵉ (union-family-of-subtypesᵉ Sᵉ)}
      { zᵉ =
        join-family-of-left-ideals-Ringᵉ Rᵉ
          ( λ αᵉ → left-ideal-subset-Ringᵉ Rᵉ (Sᵉ αᵉ))}
      ( is-least-upper-bound-join-left-ideal-subset-Ringᵉ)
      ( is-join-join-family-of-left-ideals-Ringᵉ Rᵉ
        ( λ αᵉ → left-ideal-subset-Ringᵉ Rᵉ (Sᵉ αᵉ)))

  preserves-join-left-ideal-subset-Ringᵉ :
    left-ideal-subset-Ringᵉ Rᵉ (union-family-of-subtypesᵉ Sᵉ) ＝ᵉ
    join-family-of-left-ideals-Ringᵉ Rᵉ (λ αᵉ → left-ideal-subset-Ringᵉ Rᵉ (Sᵉ αᵉ))
  preserves-join-left-ideal-subset-Ringᵉ =
    eq-sim-Large-Posetᵉ
      ( left-ideal-Ring-Large-Posetᵉ Rᵉ)
      ( left-ideal-subset-Ringᵉ Rᵉ (union-family-of-subtypesᵉ Sᵉ))
      ( join-family-of-left-ideals-Ringᵉ Rᵉ
        ( λ αᵉ → left-ideal-subset-Ringᵉ Rᵉ (Sᵉ αᵉ)))
      ( sim-preserves-join-left-ideal-subset-Ringᵉ)
```