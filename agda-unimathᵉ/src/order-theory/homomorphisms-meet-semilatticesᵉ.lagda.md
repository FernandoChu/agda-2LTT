# Homomorphisms of meet-semilattices

```agda
module order-theory.homomorphisms-meet-semilatticesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.subtypesᵉ
open import foundation.universe-levelsᵉ

open import group-theory.homomorphisms-semigroupsᵉ

open import order-theory.greatest-lower-bounds-posetsᵉ
open import order-theory.meet-semilatticesᵉ
open import order-theory.order-preserving-maps-posetsᵉ
```

</details>

## Idea

Aᵉ **homomorphismᵉ ofᵉ meet-semilattice**ᵉ isᵉ aᵉ mapᵉ thatᵉ preservesᵉ meets.ᵉ Itᵉ followsᵉ
thatᵉ homomorphismsᵉ ofᵉ meet-semilatticesᵉ areᵉ orderᵉ preserving.ᵉ

## Definitions

### Homomorphisms of algebraic meet-semilattices

```agda
module _
  {l1ᵉ l2ᵉ : Level}
  (Aᵉ : Meet-Semilatticeᵉ l1ᵉ) (Bᵉ : Meet-Semilatticeᵉ l2ᵉ)
  where

  preserves-meet-Propᵉ :
    (type-Meet-Semilatticeᵉ Aᵉ → type-Meet-Semilatticeᵉ Bᵉ) → Propᵉ (l1ᵉ ⊔ l2ᵉ)
  preserves-meet-Propᵉ =
    preserves-mul-prop-Semigroupᵉ
      ( semigroup-Meet-Semilatticeᵉ Aᵉ)
      ( semigroup-Meet-Semilatticeᵉ Bᵉ)

  preserves-meetᵉ :
    (type-Meet-Semilatticeᵉ Aᵉ → type-Meet-Semilatticeᵉ Bᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  preserves-meetᵉ =
    preserves-mul-Semigroupᵉ
      ( semigroup-Meet-Semilatticeᵉ Aᵉ)
      ( semigroup-Meet-Semilatticeᵉ Bᵉ)

  is-prop-preserves-meetᵉ :
    (fᵉ : type-Meet-Semilatticeᵉ Aᵉ → type-Meet-Semilatticeᵉ Bᵉ) →
    is-propᵉ (preserves-meetᵉ fᵉ)
  is-prop-preserves-meetᵉ =
    is-prop-preserves-mul-Semigroupᵉ
      ( semigroup-Meet-Semilatticeᵉ Aᵉ)
      ( semigroup-Meet-Semilatticeᵉ Bᵉ)

  hom-set-Meet-Semilatticeᵉ : Setᵉ (l1ᵉ ⊔ l2ᵉ)
  hom-set-Meet-Semilatticeᵉ =
    hom-set-Semigroupᵉ
      ( semigroup-Meet-Semilatticeᵉ Aᵉ)
      ( semigroup-Meet-Semilatticeᵉ Bᵉ)

  hom-Meet-Semilatticeᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  hom-Meet-Semilatticeᵉ = type-Setᵉ hom-set-Meet-Semilatticeᵉ

  is-set-hom-Meet-Semilatticeᵉ : is-setᵉ hom-Meet-Semilatticeᵉ
  is-set-hom-Meet-Semilatticeᵉ = is-set-type-Setᵉ hom-set-Meet-Semilatticeᵉ

  module _
    (fᵉ : hom-Meet-Semilatticeᵉ)
    where

    map-hom-Meet-Semilatticeᵉ :
      type-Meet-Semilatticeᵉ Aᵉ → type-Meet-Semilatticeᵉ Bᵉ
    map-hom-Meet-Semilatticeᵉ = pr1ᵉ fᵉ

    preserves-meet-hom-Meet-Semilatticeᵉ :
      preserves-meetᵉ map-hom-Meet-Semilatticeᵉ
    preserves-meet-hom-Meet-Semilatticeᵉ = pr2ᵉ fᵉ

    preserves-order-hom-Meet-Semilatticeᵉ :
      preserves-order-Posetᵉ
        ( poset-Meet-Semilatticeᵉ Aᵉ)
        ( poset-Meet-Semilatticeᵉ Bᵉ)
        ( map-hom-Meet-Semilatticeᵉ)
    preserves-order-hom-Meet-Semilatticeᵉ xᵉ yᵉ Hᵉ =
      ( invᵉ preserves-meet-hom-Meet-Semilatticeᵉ) ∙ᵉ
      ( apᵉ map-hom-Meet-Semilatticeᵉ Hᵉ)

    hom-poset-hom-Meet-Semilatticeᵉ :
      hom-Posetᵉ (poset-Meet-Semilatticeᵉ Aᵉ) (poset-Meet-Semilatticeᵉ Bᵉ)
    pr1ᵉ hom-poset-hom-Meet-Semilatticeᵉ = map-hom-Meet-Semilatticeᵉ
    pr2ᵉ hom-poset-hom-Meet-Semilatticeᵉ = preserves-order-hom-Meet-Semilatticeᵉ
```

### Homomorphisms of order-theoretic meet-semilattices

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Aᵉ : Order-Theoretic-Meet-Semilatticeᵉ l1ᵉ l2ᵉ)
  (Bᵉ : Order-Theoretic-Meet-Semilatticeᵉ l3ᵉ l4ᵉ)
  where

  preserves-meet-hom-Poset-Propᵉ :
    hom-Posetᵉ
      ( poset-Order-Theoretic-Meet-Semilatticeᵉ Aᵉ)
      ( poset-Order-Theoretic-Meet-Semilatticeᵉ Bᵉ) → Propᵉ (l1ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  preserves-meet-hom-Poset-Propᵉ (fᵉ ,ᵉ Hᵉ) =
    Π-Propᵉ
      ( type-Order-Theoretic-Meet-Semilatticeᵉ Aᵉ)
      ( λ xᵉ →
        Π-Propᵉ
          ( type-Order-Theoretic-Meet-Semilatticeᵉ Aᵉ)
          ( λ yᵉ →
            is-greatest-binary-lower-bound-Poset-Propᵉ
              ( poset-Order-Theoretic-Meet-Semilatticeᵉ Bᵉ)
              ( fᵉ xᵉ)
              ( fᵉ yᵉ)
              ( fᵉ (meet-Order-Theoretic-Meet-Semilatticeᵉ Aᵉ xᵉ yᵉ))))

  preserves-meet-hom-Posetᵉ :
    hom-Posetᵉ
      ( poset-Order-Theoretic-Meet-Semilatticeᵉ Aᵉ)
      ( poset-Order-Theoretic-Meet-Semilatticeᵉ Bᵉ) → UUᵉ (l1ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  preserves-meet-hom-Posetᵉ fᵉ =
    type-Propᵉ (preserves-meet-hom-Poset-Propᵉ fᵉ)

  is-prop-preserves-meet-hom-Propᵉ :
    ( fᵉ :
      hom-Posetᵉ
        ( poset-Order-Theoretic-Meet-Semilatticeᵉ Aᵉ)
        ( poset-Order-Theoretic-Meet-Semilatticeᵉ Bᵉ)) →
    is-propᵉ (preserves-meet-hom-Posetᵉ fᵉ)
  is-prop-preserves-meet-hom-Propᵉ fᵉ =
    is-prop-type-Propᵉ (preserves-meet-hom-Poset-Propᵉ fᵉ)

  hom-set-Order-Theoretic-Meet-Semilatticeᵉ : Setᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  hom-set-Order-Theoretic-Meet-Semilatticeᵉ =
    set-subsetᵉ
      ( hom-set-Posetᵉ
        ( poset-Order-Theoretic-Meet-Semilatticeᵉ Aᵉ)
        ( poset-Order-Theoretic-Meet-Semilatticeᵉ Bᵉ))
      ( preserves-meet-hom-Poset-Propᵉ)
```