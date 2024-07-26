# Joins of right ideals of rings

```agda
module ring-theory.joins-right-ideals-ringsᵉ where
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

open import ring-theory.poset-of-right-ideals-ringsᵉ
open import ring-theory.right-ideals-generated-by-subsets-ringsᵉ
open import ring-theory.right-ideals-ringsᵉ
open import ring-theory.ringsᵉ
open import ring-theory.subsets-ringsᵉ
```

</details>

## Idea

Theᵉ **join**ᵉ ofᵉ aᵉ familyᵉ ofᵉ [rightᵉ ideals](ring-theory.right-ideals-rings.mdᵉ) ofᵉ
[rings](ring-theory.rings.mdᵉ) isᵉ theᵉ leastᵉ rightᵉ idealᵉ containingᵉ allᵉ theᵉ rightᵉ
idealsᵉ in theᵉ familyᵉ ofᵉ rightᵉ ideals.ᵉ Inᵉ otherᵉ words,ᵉ theᵉ joinᵉ ofᵉ aᵉ familyᵉ ofᵉ
rightᵉ idealsᵉ isᵉ theᵉ
[rightᵉ idealᵉ generatedᵉ by](ring-theory.right-ideals-generated-by-subsets-rings.mdᵉ)
theᵉ unionᵉ ofᵉ theᵉ underlyingᵉ subsetsᵉ ofᵉ theᵉ rightᵉ idealsᵉ in theᵉ familyᵉ ofᵉ rightᵉ
ideals.ᵉ

## Definitions

### The predicate of being the join of a family of right ideals

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ) {Uᵉ : UUᵉ l2ᵉ} (Iᵉ : Uᵉ → right-ideal-Ringᵉ l3ᵉ Rᵉ)
  where

  is-join-family-of-right-ideals-Ringᵉ :
    {l4ᵉ : Level} → right-ideal-Ringᵉ l4ᵉ Rᵉ → UUωᵉ
  is-join-family-of-right-ideals-Ringᵉ =
    is-least-upper-bound-family-of-elements-Large-Posetᵉ
      ( right-ideal-Ring-Large-Posetᵉ Rᵉ)
      ( Iᵉ)

  inclusion-is-join-family-of-right-ideals-Ringᵉ :
    {l4ᵉ l5ᵉ : Level} (Jᵉ : right-ideal-Ringᵉ l4ᵉ Rᵉ) →
    is-join-family-of-right-ideals-Ringᵉ Jᵉ →
    (Kᵉ : right-ideal-Ringᵉ l5ᵉ Rᵉ) → ((αᵉ : Uᵉ) → leq-right-ideal-Ringᵉ Rᵉ (Iᵉ αᵉ) Kᵉ) →
    leq-right-ideal-Ringᵉ Rᵉ Jᵉ Kᵉ
  inclusion-is-join-family-of-right-ideals-Ringᵉ Jᵉ Hᵉ Kᵉ =
    pr1ᵉ (Hᵉ Kᵉ)

  contains-right-ideal-is-join-family-of-right-ideals-Ringᵉ :
    {l4ᵉ : Level} (Jᵉ : right-ideal-Ringᵉ l4ᵉ Rᵉ) →
    is-join-family-of-right-ideals-Ringᵉ Jᵉ →
    {αᵉ : Uᵉ} → leq-right-ideal-Ringᵉ Rᵉ (Iᵉ αᵉ) Jᵉ
  contains-right-ideal-is-join-family-of-right-ideals-Ringᵉ Jᵉ Hᵉ {αᵉ} =
    pr2ᵉ (Hᵉ Jᵉ) (refl-leq-right-ideal-Ringᵉ Rᵉ Jᵉ) αᵉ
```

### The join of a family of right ideals

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ) {Uᵉ : UUᵉ l2ᵉ} (Iᵉ : Uᵉ → right-ideal-Ringᵉ l3ᵉ Rᵉ)
  where

  generating-subset-join-family-of-right-ideals-Ringᵉ :
    subset-Ringᵉ (l2ᵉ ⊔ l3ᵉ) Rᵉ
  generating-subset-join-family-of-right-ideals-Ringᵉ =
    union-family-of-subtypesᵉ (λ αᵉ → subset-right-ideal-Ringᵉ Rᵉ (Iᵉ αᵉ))

  join-family-of-right-ideals-Ringᵉ :
    right-ideal-Ringᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ) Rᵉ
  join-family-of-right-ideals-Ringᵉ =
    right-ideal-family-of-subsets-Ringᵉ Rᵉ (λ αᵉ → subset-right-ideal-Ringᵉ Rᵉ (Iᵉ αᵉ))

  forward-inclusion-is-join-join-family-of-right-ideals-Ringᵉ :
    {l4ᵉ : Level} (Kᵉ : right-ideal-Ringᵉ l4ᵉ Rᵉ) →
    ((αᵉ : Uᵉ) → leq-right-ideal-Ringᵉ Rᵉ (Iᵉ αᵉ) Kᵉ) →
    leq-right-ideal-Ringᵉ Rᵉ join-family-of-right-ideals-Ringᵉ Kᵉ
  forward-inclusion-is-join-join-family-of-right-ideals-Ringᵉ Kᵉ Hᵉ =
    is-right-ideal-generated-by-family-of-subsets-right-ideal-family-of-subsets-Ringᵉ
      ( Rᵉ)
      ( λ αᵉ → subset-right-ideal-Ringᵉ Rᵉ (Iᵉ αᵉ))
      ( Kᵉ)
      ( λ αᵉ xᵉ → Hᵉ αᵉ xᵉ)

  backward-inclusion-is-join-join-family-of-right-ideals-Ringᵉ :
    {l4ᵉ : Level} (Kᵉ : right-ideal-Ringᵉ l4ᵉ Rᵉ) →
    leq-right-ideal-Ringᵉ Rᵉ join-family-of-right-ideals-Ringᵉ Kᵉ →
    (αᵉ : Uᵉ) → leq-right-ideal-Ringᵉ Rᵉ (Iᵉ αᵉ) Kᵉ
  backward-inclusion-is-join-join-family-of-right-ideals-Ringᵉ Kᵉ Hᵉ _ xᵉ pᵉ =
    Hᵉ ( xᵉ)
      ( contains-subset-right-ideal-family-of-subsets-Ringᵉ Rᵉ
        ( λ αᵉ → subset-right-ideal-Ringᵉ Rᵉ (Iᵉ αᵉ))
        ( xᵉ)
        ( pᵉ))

  is-join-join-family-of-right-ideals-Ringᵉ :
    is-join-family-of-right-ideals-Ringᵉ Rᵉ Iᵉ join-family-of-right-ideals-Ringᵉ
  pr1ᵉ (is-join-join-family-of-right-ideals-Ringᵉ Kᵉ) =
    forward-inclusion-is-join-join-family-of-right-ideals-Ringᵉ Kᵉ
  pr2ᵉ (is-join-join-family-of-right-ideals-Ringᵉ Kᵉ) =
    backward-inclusion-is-join-join-family-of-right-ideals-Ringᵉ Kᵉ

  inclusion-join-family-of-right-ideals-Ringᵉ :
    {l4ᵉ : Level} (Jᵉ : right-ideal-Ringᵉ l4ᵉ Rᵉ) →
    ((αᵉ : Uᵉ) → leq-right-ideal-Ringᵉ Rᵉ (Iᵉ αᵉ) Jᵉ) →
    leq-right-ideal-Ringᵉ Rᵉ join-family-of-right-ideals-Ringᵉ Jᵉ
  inclusion-join-family-of-right-ideals-Ringᵉ =
    inclusion-is-join-family-of-right-ideals-Ringᵉ Rᵉ Iᵉ
      ( join-family-of-right-ideals-Ringᵉ)
      ( is-join-join-family-of-right-ideals-Ringᵉ)

  contains-right-ideal-join-family-of-right-ideals-Ringᵉ :
    {αᵉ : Uᵉ} → leq-right-ideal-Ringᵉ Rᵉ (Iᵉ αᵉ) join-family-of-right-ideals-Ringᵉ
  contains-right-ideal-join-family-of-right-ideals-Ringᵉ =
    contains-right-ideal-is-join-family-of-right-ideals-Ringᵉ Rᵉ Iᵉ
      ( join-family-of-right-ideals-Ringᵉ)
      ( is-join-join-family-of-right-ideals-Ringᵉ)
```

### The large suplattice of right ideals in a ring

```agda
module _
  {l1ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ)
  where

  is-large-suplattice-right-ideal-Ring-Large-Posetᵉ :
    is-large-suplattice-Large-Posetᵉ l1ᵉ (right-ideal-Ring-Large-Posetᵉ Rᵉ)
  sup-has-least-upper-bound-family-of-elements-Large-Posetᵉ
    ( is-large-suplattice-right-ideal-Ring-Large-Posetᵉ Iᵉ) =
    join-family-of-right-ideals-Ringᵉ Rᵉ Iᵉ
  is-least-upper-bound-sup-has-least-upper-bound-family-of-elements-Large-Posetᵉ
    ( is-large-suplattice-right-ideal-Ring-Large-Posetᵉ Iᵉ) =
    is-join-join-family-of-right-ideals-Ringᵉ Rᵉ Iᵉ

  right-ideal-Ring-Large-Suplatticeᵉ :
    Large-Suplatticeᵉ (λ l2ᵉ → l1ᵉ ⊔ lsuc l2ᵉ) (λ l2ᵉ l3ᵉ → l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ) l1ᵉ
  large-poset-Large-Suplatticeᵉ
    right-ideal-Ring-Large-Suplatticeᵉ =
    right-ideal-Ring-Large-Posetᵉ Rᵉ
  is-large-suplattice-Large-Suplatticeᵉ
    right-ideal-Ring-Large-Suplatticeᵉ =
    is-large-suplattice-right-ideal-Ring-Large-Posetᵉ
```

## Properties

### If `I α ⊆ J α` for each `α`, then `⋁ I ⊆ ⋁ J`

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Aᵉ : Ringᵉ l1ᵉ)
  {Uᵉ : UUᵉ l2ᵉ}
  (Iᵉ : Uᵉ → right-ideal-Ringᵉ l3ᵉ Aᵉ)
  (Jᵉ : Uᵉ → right-ideal-Ringᵉ l4ᵉ Aᵉ)
  (Hᵉ : (αᵉ : Uᵉ) → leq-right-ideal-Ringᵉ Aᵉ (Iᵉ αᵉ) (Jᵉ αᵉ))
  where

  preserves-order-join-family-of-right-ideals-Ringᵉ :
    leq-right-ideal-Ringᵉ Aᵉ
      ( join-family-of-right-ideals-Ringᵉ Aᵉ Iᵉ)
      ( join-family-of-right-ideals-Ringᵉ Aᵉ Jᵉ)
  preserves-order-join-family-of-right-ideals-Ringᵉ =
    preserves-order-sup-Large-Suplatticeᵉ
      ( right-ideal-Ring-Large-Suplatticeᵉ Aᵉ)
      { xᵉ = Iᵉ}
      { yᵉ = Jᵉ}
      ( Hᵉ)
```

### The operation `S ↦ (S)` preserves joins

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ) {Uᵉ : UUᵉ l2ᵉ} (Sᵉ : Uᵉ → subset-Ringᵉ l3ᵉ Rᵉ)
  where

  is-least-upper-bound-join-right-ideal-subset-Ringᵉ :
    is-least-upper-bound-family-of-elements-Large-Posetᵉ
      ( right-ideal-Ring-Large-Posetᵉ Rᵉ)
      ( λ αᵉ → right-ideal-subset-Ringᵉ Rᵉ (Sᵉ αᵉ))
      ( right-ideal-subset-Ringᵉ Rᵉ (union-family-of-subtypesᵉ Sᵉ))
  is-least-upper-bound-join-right-ideal-subset-Ringᵉ =
    preserves-least-upper-bounds-right-ideal-subset-Ringᵉ Rᵉ Sᵉ
      ( union-family-of-subtypesᵉ Sᵉ)
      ( is-least-upper-bound-union-family-of-subtypesᵉ Sᵉ)

  sim-preserves-join-right-ideal-subset-Ringᵉ :
    sim-right-ideal-Ringᵉ Rᵉ
      ( right-ideal-subset-Ringᵉ Rᵉ (union-family-of-subtypesᵉ Sᵉ))
      ( join-family-of-right-ideals-Ringᵉ Rᵉ
        ( λ αᵉ → right-ideal-subset-Ringᵉ Rᵉ (Sᵉ αᵉ)))
  sim-preserves-join-right-ideal-subset-Ringᵉ =
    sim-is-least-upper-bound-family-of-elements-Large-Posetᵉ
      ( right-ideal-Ring-Large-Posetᵉ Rᵉ)
      { xᵉ = λ αᵉ → right-ideal-subset-Ringᵉ Rᵉ (Sᵉ αᵉ)}
      { yᵉ = right-ideal-subset-Ringᵉ Rᵉ (union-family-of-subtypesᵉ Sᵉ)}
      { zᵉ =
        join-family-of-right-ideals-Ringᵉ Rᵉ
          ( λ αᵉ → right-ideal-subset-Ringᵉ Rᵉ (Sᵉ αᵉ))}
      ( is-least-upper-bound-join-right-ideal-subset-Ringᵉ)
      ( is-join-join-family-of-right-ideals-Ringᵉ Rᵉ
        ( λ αᵉ → right-ideal-subset-Ringᵉ Rᵉ (Sᵉ αᵉ)))

  preserves-join-right-ideal-subset-Ringᵉ :
    right-ideal-subset-Ringᵉ Rᵉ (union-family-of-subtypesᵉ Sᵉ) ＝ᵉ
    join-family-of-right-ideals-Ringᵉ Rᵉ (λ αᵉ → right-ideal-subset-Ringᵉ Rᵉ (Sᵉ αᵉ))
  preserves-join-right-ideal-subset-Ringᵉ =
    eq-sim-Large-Posetᵉ
      ( right-ideal-Ring-Large-Posetᵉ Rᵉ)
      ( right-ideal-subset-Ringᵉ Rᵉ (union-family-of-subtypesᵉ Sᵉ))
      ( join-family-of-right-ideals-Ringᵉ Rᵉ
        ( λ αᵉ → right-ideal-subset-Ringᵉ Rᵉ (Sᵉ αᵉ)))
      ( sim-preserves-join-right-ideal-subset-Ringᵉ)
```