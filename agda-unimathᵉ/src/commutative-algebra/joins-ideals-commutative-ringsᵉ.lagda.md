# Joins of ideals of commutative rings

```agda
module commutative-algebra.joins-ideals-commutative-ringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-ringsᵉ
open import commutative-algebra.ideals-commutative-ringsᵉ
open import commutative-algebra.ideals-generated-by-subsets-commutative-ringsᵉ
open import commutative-algebra.poset-of-ideals-commutative-ringsᵉ
open import commutative-algebra.products-ideals-commutative-ringsᵉ
open import commutative-algebra.products-subsets-commutative-ringsᵉ
open import commutative-algebra.subsets-commutative-ringsᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.subtypesᵉ
open import foundation.unions-subtypesᵉ
open import foundation.universe-levelsᵉ

open import ring-theory.joins-ideals-ringsᵉ
```

</details>

## Idea

Theᵉ **join**ᵉ ofᵉ aᵉ familyᵉ ofᵉ
[ideals](commutative-algebra.ideals-commutative-rings.mdᵉ) `iᵉ ↦ᵉ Jᵉ i`ᵉ in aᵉ
[commutativeᵉ ring](commutative-algebra.commutative-rings.mdᵉ) isᵉ theᵉ leastᵉ idealᵉ
containingᵉ eachᵉ `Jᵉ i`.ᵉ

## Definition

### The universal property of the join of a family of ideals

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Aᵉ : Commutative-Ringᵉ l1ᵉ)
  {Uᵉ : UUᵉ l2ᵉ} (Iᵉ : Uᵉ → ideal-Commutative-Ringᵉ l3ᵉ Aᵉ)
  where

  is-join-family-of-ideals-Commutative-Ringᵉ :
    {l4ᵉ : Level} (Kᵉ : ideal-Commutative-Ringᵉ l4ᵉ Aᵉ) → UUωᵉ
  is-join-family-of-ideals-Commutative-Ringᵉ =
    is-join-family-of-ideals-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ) Iᵉ

  inclusion-is-join-family-of-ideals-Commutative-Ringᵉ :
    {l4ᵉ l5ᵉ : Level} (Jᵉ : ideal-Commutative-Ringᵉ l4ᵉ Aᵉ) →
    is-join-family-of-ideals-Commutative-Ringᵉ Jᵉ →
    (Kᵉ : ideal-Commutative-Ringᵉ l5ᵉ Aᵉ) →
    ((αᵉ : Uᵉ) → leq-ideal-Commutative-Ringᵉ Aᵉ (Iᵉ αᵉ) Kᵉ) →
    leq-ideal-Commutative-Ringᵉ Aᵉ Jᵉ Kᵉ
  inclusion-is-join-family-of-ideals-Commutative-Ringᵉ =
    inclusion-is-join-family-of-ideals-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ) Iᵉ

  contains-ideal-is-join-family-of-ideals-Commutative-Ringᵉ :
    {l4ᵉ : Level} (Jᵉ : ideal-Commutative-Ringᵉ l4ᵉ Aᵉ) →
    is-join-family-of-ideals-Commutative-Ringᵉ Jᵉ →
    {αᵉ : Uᵉ} → leq-ideal-Commutative-Ringᵉ Aᵉ (Iᵉ αᵉ) Jᵉ
  contains-ideal-is-join-family-of-ideals-Commutative-Ringᵉ =
    contains-ideal-is-join-family-of-ideals-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ) Iᵉ
```

### The join of a family of ideals

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Aᵉ : Commutative-Ringᵉ l1ᵉ)
  {Uᵉ : UUᵉ l2ᵉ} (Iᵉ : Uᵉ → ideal-Commutative-Ringᵉ l3ᵉ Aᵉ)
  where

  generating-subset-join-family-of-ideals-Commutative-Ringᵉ :
    subset-Commutative-Ringᵉ (l2ᵉ ⊔ l3ᵉ) Aᵉ
  generating-subset-join-family-of-ideals-Commutative-Ringᵉ =
    generating-subset-join-family-of-ideals-Ringᵉ
      ( ring-Commutative-Ringᵉ Aᵉ)
      ( Iᵉ)

  join-family-of-ideals-Commutative-Ringᵉ :
    ideal-Commutative-Ringᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ) Aᵉ
  join-family-of-ideals-Commutative-Ringᵉ =
    join-family-of-ideals-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ) Iᵉ

  forward-inclusion-is-join-join-family-of-ideals-Commutative-Ringᵉ :
    {l4ᵉ : Level} (Kᵉ : ideal-Commutative-Ringᵉ l4ᵉ Aᵉ) →
    ((αᵉ : Uᵉ) → leq-ideal-Commutative-Ringᵉ Aᵉ (Iᵉ αᵉ) Kᵉ) →
    leq-ideal-Commutative-Ringᵉ Aᵉ join-family-of-ideals-Commutative-Ringᵉ Kᵉ
  forward-inclusion-is-join-join-family-of-ideals-Commutative-Ringᵉ =
    forward-inclusion-is-join-join-family-of-ideals-Ringᵉ
      ( ring-Commutative-Ringᵉ Aᵉ)
      ( Iᵉ)

  backward-inclusion-is-join-join-family-of-ideals-Commutative-Ringᵉ :
    {l4ᵉ : Level} (Kᵉ : ideal-Commutative-Ringᵉ l4ᵉ Aᵉ) →
    leq-ideal-Commutative-Ringᵉ Aᵉ join-family-of-ideals-Commutative-Ringᵉ Kᵉ →
    (αᵉ : Uᵉ) → leq-ideal-Commutative-Ringᵉ Aᵉ (Iᵉ αᵉ) Kᵉ
  backward-inclusion-is-join-join-family-of-ideals-Commutative-Ringᵉ =
    backward-inclusion-is-join-join-family-of-ideals-Ringᵉ
      ( ring-Commutative-Ringᵉ Aᵉ)
      ( Iᵉ)

  is-join-join-family-of-ideals-Commutative-Ringᵉ :
    is-join-family-of-ideals-Commutative-Ringᵉ Aᵉ Iᵉ
      join-family-of-ideals-Commutative-Ringᵉ
  is-join-join-family-of-ideals-Commutative-Ringᵉ =
    is-join-join-family-of-ideals-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ) Iᵉ

  inclusion-join-family-of-ideals-Commutative-Ringᵉ :
    {l4ᵉ : Level} (Jᵉ : ideal-Commutative-Ringᵉ l4ᵉ Aᵉ) →
    ((αᵉ : Uᵉ) → leq-ideal-Commutative-Ringᵉ Aᵉ (Iᵉ αᵉ) Jᵉ) →
    leq-ideal-Commutative-Ringᵉ Aᵉ join-family-of-ideals-Commutative-Ringᵉ Jᵉ
  inclusion-join-family-of-ideals-Commutative-Ringᵉ =
    inclusion-join-family-of-ideals-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ) Iᵉ

  contains-ideal-join-family-of-ideals-Commutative-Ringᵉ :
    {αᵉ : Uᵉ} →
    leq-ideal-Commutative-Ringᵉ Aᵉ (Iᵉ αᵉ) join-family-of-ideals-Commutative-Ringᵉ
  contains-ideal-join-family-of-ideals-Commutative-Ringᵉ =
    contains-ideal-join-family-of-ideals-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ) Iᵉ
```

## Properties

### If `I α ⊆ J α` for each `α`, then `⋁ I ⊆ ⋁ J`

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Aᵉ : Commutative-Ringᵉ l1ᵉ)
  {Uᵉ : UUᵉ l2ᵉ}
  (Iᵉ : Uᵉ → ideal-Commutative-Ringᵉ l3ᵉ Aᵉ)
  (Jᵉ : Uᵉ → ideal-Commutative-Ringᵉ l4ᵉ Aᵉ)
  (Hᵉ : (αᵉ : Uᵉ) → leq-ideal-Commutative-Ringᵉ Aᵉ (Iᵉ αᵉ) (Jᵉ αᵉ))
  where

  preserves-order-join-family-of-ideals-Commutative-Ringᵉ :
    leq-ideal-Commutative-Ringᵉ Aᵉ
      ( join-family-of-ideals-Commutative-Ringᵉ Aᵉ Iᵉ)
      ( join-family-of-ideals-Commutative-Ringᵉ Aᵉ Jᵉ)
  preserves-order-join-family-of-ideals-Commutative-Ringᵉ =
    preserves-order-join-family-of-ideals-Ringᵉ
      ( ring-Commutative-Ringᵉ Aᵉ)
      ( Iᵉ)
      ( Jᵉ)
      ( Hᵉ)
```

### Products distribute over joins of families of ideals

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Aᵉ : Commutative-Ringᵉ l1ᵉ)
  (Iᵉ : ideal-Commutative-Ringᵉ l2ᵉ Aᵉ)
  {Uᵉ : UUᵉ l3ᵉ} (Jᵉ : Uᵉ → ideal-Commutative-Ringᵉ l4ᵉ Aᵉ)
  where

  forward-inclusion-distributive-product-join-family-of-ideals-Commutative-Ringᵉ :
    leq-ideal-Commutative-Ringᵉ Aᵉ
      ( product-ideal-Commutative-Ringᵉ Aᵉ
        ( Iᵉ)
        ( join-family-of-ideals-Commutative-Ringᵉ Aᵉ Jᵉ))
      ( join-family-of-ideals-Commutative-Ringᵉ Aᵉ
        ( λ αᵉ →
          product-ideal-Commutative-Ringᵉ Aᵉ Iᵉ (Jᵉ αᵉ)))
  forward-inclusion-distributive-product-join-family-of-ideals-Commutative-Ringᵉ
    xᵉ pᵉ =
    preserves-order-ideal-subset-Commutative-Ringᵉ Aᵉ
      ( product-subset-Commutative-Ringᵉ Aᵉ
        ( subset-ideal-Commutative-Ringᵉ Aᵉ Iᵉ)
        ( union-family-of-subtypesᵉ
          ( λ αᵉ → subset-ideal-Commutative-Ringᵉ Aᵉ (Jᵉ αᵉ))))
      ( generating-subset-join-family-of-ideals-Commutative-Ringᵉ Aᵉ
        ( λ αᵉ → product-ideal-Commutative-Ringᵉ Aᵉ Iᵉ (Jᵉ αᵉ)))
      ( transitive-leq-subtypeᵉ
        ( product-subset-Commutative-Ringᵉ Aᵉ
          ( subset-ideal-Commutative-Ringᵉ Aᵉ Iᵉ)
          ( union-family-of-subtypesᵉ
            ( λ αᵉ → subset-ideal-Commutative-Ringᵉ Aᵉ (Jᵉ αᵉ))))
        ( union-family-of-subtypesᵉ
          ( λ αᵉ →
            generating-subset-product-ideal-Commutative-Ringᵉ Aᵉ Iᵉ (Jᵉ αᵉ)))
        ( generating-subset-join-family-of-ideals-Commutative-Ringᵉ Aᵉ
          ( λ αᵉ → product-ideal-Commutative-Ringᵉ Aᵉ Iᵉ (Jᵉ αᵉ)))
        ( preserves-order-union-family-of-subtypesᵉ
          ( λ αᵉ → generating-subset-product-ideal-Commutative-Ringᵉ Aᵉ Iᵉ (Jᵉ αᵉ))
          ( λ αᵉ → subset-product-ideal-Commutative-Ringᵉ Aᵉ Iᵉ (Jᵉ αᵉ))
          ( λ αᵉ →
            contains-subset-ideal-subset-Commutative-Ringᵉ Aᵉ
              ( generating-subset-product-ideal-Commutative-Ringᵉ Aᵉ Iᵉ (Jᵉ αᵉ))))
        ( forward-inclusion-distributive-product-union-family-of-subsets-Commutative-Ringᵉ
          ( Aᵉ)
          ( subset-ideal-Commutative-Ringᵉ Aᵉ Iᵉ)
          ( λ αᵉ → subset-ideal-Commutative-Ringᵉ Aᵉ (Jᵉ αᵉ))))
      ( xᵉ)
      ( backward-inclusion-right-preserves-product-ideal-subset-Commutative-Ringᵉ
        ( Aᵉ)
        ( Iᵉ)
        ( generating-subset-join-family-of-ideals-Commutative-Ringᵉ Aᵉ Jᵉ)
        ( xᵉ)
        ( pᵉ))

  backward-inclusion-distributive-product-join-family-of-ideals-Commutative-Ringᵉ :
    leq-ideal-Commutative-Ringᵉ Aᵉ
      ( join-family-of-ideals-Commutative-Ringᵉ Aᵉ
        ( λ αᵉ →
          product-ideal-Commutative-Ringᵉ Aᵉ Iᵉ (Jᵉ αᵉ)))
      ( product-ideal-Commutative-Ringᵉ Aᵉ
        ( Iᵉ)
        ( join-family-of-ideals-Commutative-Ringᵉ Aᵉ Jᵉ))
  backward-inclusion-distributive-product-join-family-of-ideals-Commutative-Ringᵉ
    =
    forward-implicationᵉ
      ( is-join-join-family-of-ideals-Commutative-Ringᵉ Aᵉ
        ( λ αᵉ → product-ideal-Commutative-Ringᵉ Aᵉ Iᵉ (Jᵉ αᵉ))
        ( product-ideal-Commutative-Ringᵉ Aᵉ Iᵉ
          ( join-family-of-ideals-Commutative-Ringᵉ Aᵉ Jᵉ)))
      ( λ αᵉ →
        preserves-order-right-product-ideal-Commutative-Ringᵉ Aᵉ Iᵉ
          ( Jᵉ αᵉ)
          ( join-family-of-ideals-Commutative-Ringᵉ Aᵉ Jᵉ)
          ( contains-ideal-join-family-of-ideals-Commutative-Ringᵉ Aᵉ Jᵉ))

  sim-distributive-product-join-family-of-ideals-Commutative-Ringᵉ :
    sim-ideal-Commutative-Ringᵉ Aᵉ
      ( product-ideal-Commutative-Ringᵉ Aᵉ Iᵉ
        ( join-family-of-ideals-Commutative-Ringᵉ Aᵉ Jᵉ))
      ( join-family-of-ideals-Commutative-Ringᵉ Aᵉ
        ( λ αᵉ → product-ideal-Commutative-Ringᵉ Aᵉ Iᵉ (Jᵉ αᵉ)))
  pr1ᵉ sim-distributive-product-join-family-of-ideals-Commutative-Ringᵉ =
    forward-inclusion-distributive-product-join-family-of-ideals-Commutative-Ringᵉ
  pr2ᵉ sim-distributive-product-join-family-of-ideals-Commutative-Ringᵉ =
    backward-inclusion-distributive-product-join-family-of-ideals-Commutative-Ringᵉ

  distributive-product-join-family-of-ideals-Commutative-Ringᵉ :
    product-ideal-Commutative-Ringᵉ Aᵉ Iᵉ
      ( join-family-of-ideals-Commutative-Ringᵉ Aᵉ Jᵉ) ＝ᵉ
    join-family-of-ideals-Commutative-Ringᵉ Aᵉ
      ( λ αᵉ → product-ideal-Commutative-Ringᵉ Aᵉ Iᵉ (Jᵉ αᵉ))
  distributive-product-join-family-of-ideals-Commutative-Ringᵉ =
    eq-sim-ideal-Commutative-Ringᵉ Aᵉ
      ( product-ideal-Commutative-Ringᵉ Aᵉ Iᵉ
        ( join-family-of-ideals-Commutative-Ringᵉ Aᵉ Jᵉ))
      ( join-family-of-ideals-Commutative-Ringᵉ Aᵉ
        ( λ αᵉ → product-ideal-Commutative-Ringᵉ Aᵉ Iᵉ (Jᵉ αᵉ)))
      ( sim-distributive-product-join-family-of-ideals-Commutative-Ringᵉ)
```