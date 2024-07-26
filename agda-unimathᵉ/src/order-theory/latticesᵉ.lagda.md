# Lattices

```agda
module order-theory.latticesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relationsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ

open import order-theory.join-semilatticesᵉ
open import order-theory.meet-semilatticesᵉ
open import order-theory.posetsᵉ
```

</details>

## Idea

Aᵉ **lattice**ᵉ isᵉ aᵉ posetᵉ in whichᵉ everyᵉ pairᵉ ofᵉ elementsᵉ hasᵉ aᵉ meetᵉ (aᵉ greatestᵉ
lowerᵉ boundᵉ) andᵉ aᵉ joinᵉ (aᵉ leastᵉ upperᵉ bound).ᵉ

Noteᵉ thatᵉ weᵉ don'tᵉ requireᵉ thatᵉ meetsᵉ distributeᵉ overᵉ joins.ᵉ Suchᵉ latticesᵉ areᵉ
calledᵉ [distributiveᵉ lattices](order-theory.distributive-lattices.md).ᵉ

## Definitions

### Order theoretic lattices

```agda
is-lattice-Poset-Propᵉ :
  {l1ᵉ l2ᵉ : Level} (Pᵉ : Posetᵉ l1ᵉ l2ᵉ) → Propᵉ (l1ᵉ ⊔ l2ᵉ)
is-lattice-Poset-Propᵉ Pᵉ =
  product-Propᵉ
    ( is-meet-semilattice-Poset-Propᵉ Pᵉ)
    ( is-join-semilattice-Poset-Propᵉ Pᵉ)

is-lattice-Posetᵉ : {l1ᵉ l2ᵉ : Level} → Posetᵉ l1ᵉ l2ᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
is-lattice-Posetᵉ Pᵉ = type-Propᵉ (is-lattice-Poset-Propᵉ Pᵉ)

is-prop-is-lattice-Posetᵉ :
  {l1ᵉ l2ᵉ : Level} (Pᵉ : Posetᵉ l1ᵉ l2ᵉ) → is-propᵉ (is-lattice-Posetᵉ Pᵉ)
is-prop-is-lattice-Posetᵉ Pᵉ = is-prop-type-Propᵉ (is-lattice-Poset-Propᵉ Pᵉ)

Latticeᵉ : (l1ᵉ l2ᵉ : Level) → UUᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ)
Latticeᵉ l1ᵉ l2ᵉ = Σᵉ (Posetᵉ l1ᵉ l2ᵉ) is-lattice-Posetᵉ

module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Latticeᵉ l1ᵉ l2ᵉ)
  where

  poset-Latticeᵉ : Posetᵉ l1ᵉ l2ᵉ
  poset-Latticeᵉ = pr1ᵉ Aᵉ

  type-Latticeᵉ : UUᵉ l1ᵉ
  type-Latticeᵉ = type-Posetᵉ poset-Latticeᵉ

  leq-lattice-Propᵉ : (xᵉ yᵉ : type-Latticeᵉ) → Propᵉ l2ᵉ
  leq-lattice-Propᵉ = leq-Poset-Propᵉ poset-Latticeᵉ

  leq-Latticeᵉ : (xᵉ yᵉ : type-Latticeᵉ) → UUᵉ l2ᵉ
  leq-Latticeᵉ = leq-Posetᵉ poset-Latticeᵉ

  is-prop-leq-Latticeᵉ : (xᵉ yᵉ : type-Latticeᵉ) → is-propᵉ (leq-Latticeᵉ xᵉ yᵉ)
  is-prop-leq-Latticeᵉ = is-prop-leq-Posetᵉ poset-Latticeᵉ

  refl-leq-Latticeᵉ : is-reflexiveᵉ leq-Latticeᵉ
  refl-leq-Latticeᵉ = refl-leq-Posetᵉ poset-Latticeᵉ

  antisymmetric-leq-Latticeᵉ : is-antisymmetricᵉ leq-Latticeᵉ
  antisymmetric-leq-Latticeᵉ = antisymmetric-leq-Posetᵉ poset-Latticeᵉ

  transitive-leq-Latticeᵉ : is-transitiveᵉ leq-Latticeᵉ
  transitive-leq-Latticeᵉ = transitive-leq-Posetᵉ poset-Latticeᵉ

  is-set-type-Latticeᵉ : is-setᵉ type-Latticeᵉ
  is-set-type-Latticeᵉ = is-set-type-Posetᵉ poset-Latticeᵉ

  set-Latticeᵉ : Setᵉ l1ᵉ
  set-Latticeᵉ = set-Posetᵉ poset-Latticeᵉ

  is-lattice-Latticeᵉ : is-lattice-Posetᵉ poset-Latticeᵉ
  is-lattice-Latticeᵉ = pr2ᵉ Aᵉ

  is-meet-semilattice-Latticeᵉ : is-meet-semilattice-Posetᵉ poset-Latticeᵉ
  is-meet-semilattice-Latticeᵉ = pr1ᵉ is-lattice-Latticeᵉ

  meet-semilattice-Latticeᵉ : Meet-Semilatticeᵉ l1ᵉ
  meet-semilattice-Latticeᵉ =
    meet-semilattice-Order-Theoretic-Meet-Semilatticeᵉ
      ( poset-Latticeᵉ ,ᵉ
        is-meet-semilattice-Latticeᵉ)

  meet-Latticeᵉ : (xᵉ yᵉ : type-Latticeᵉ) → type-Latticeᵉ
  meet-Latticeᵉ xᵉ yᵉ = pr1ᵉ (is-meet-semilattice-Latticeᵉ xᵉ yᵉ)

  is-join-semilattice-Latticeᵉ : is-join-semilattice-Posetᵉ poset-Latticeᵉ
  is-join-semilattice-Latticeᵉ = pr2ᵉ is-lattice-Latticeᵉ

  join-semilattice-Latticeᵉ : Join-Semilatticeᵉ l1ᵉ
  join-semilattice-Latticeᵉ =
    join-semilattice-Order-Theoretic-Join-Semilatticeᵉ
      ( poset-Latticeᵉ ,ᵉ
        is-join-semilattice-Latticeᵉ)

  join-Latticeᵉ : (xᵉ yᵉ : type-Latticeᵉ) → type-Latticeᵉ
  join-Latticeᵉ xᵉ yᵉ = pr1ᵉ (is-join-semilattice-Latticeᵉ xᵉ yᵉ)
```