# Distributive lattices

```agda
module order-theory.distributive-latticesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relationsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ

open import order-theory.join-semilatticesᵉ
open import order-theory.latticesᵉ
open import order-theory.meet-semilatticesᵉ
open import order-theory.posetsᵉ
```

</details>

## Idea

Aᵉ **distributiveᵉ lattice**ᵉ isᵉ aᵉ latticeᵉ in whichᵉ meetsᵉ distributeᵉ overᵉ joins.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Lᵉ : Latticeᵉ l1ᵉ l2ᵉ)
  where

  is-distributive-lattice-Propᵉ : Propᵉ l1ᵉ
  is-distributive-lattice-Propᵉ =
    Π-Propᵉ
      ( type-Latticeᵉ Lᵉ)
      ( λ xᵉ →
        Π-Propᵉ
          ( type-Latticeᵉ Lᵉ)
          ( λ yᵉ →
            Π-Propᵉ
              ( type-Latticeᵉ Lᵉ)
              ( λ zᵉ →
                Id-Propᵉ
                  ( set-Latticeᵉ Lᵉ)
                  ( meet-Latticeᵉ Lᵉ xᵉ (join-Latticeᵉ Lᵉ yᵉ zᵉ))
                  ( join-Latticeᵉ Lᵉ (meet-Latticeᵉ Lᵉ xᵉ yᵉ) (meet-Latticeᵉ Lᵉ xᵉ zᵉ)))))

  is-distributive-Latticeᵉ : UUᵉ l1ᵉ
  is-distributive-Latticeᵉ = type-Propᵉ is-distributive-lattice-Propᵉ

  is-prop-is-distributive-Latticeᵉ : is-propᵉ is-distributive-Latticeᵉ
  is-prop-is-distributive-Latticeᵉ =
    is-prop-type-Propᵉ is-distributive-lattice-Propᵉ

Distributive-Latticeᵉ : (l1ᵉ l2ᵉ : Level) → UUᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ)
Distributive-Latticeᵉ l1ᵉ l2ᵉ = Σᵉ (Latticeᵉ l1ᵉ l2ᵉ) is-distributive-Latticeᵉ

module _
  {l1ᵉ l2ᵉ : Level} (Lᵉ : Distributive-Latticeᵉ l1ᵉ l2ᵉ)
  where

  lattice-Distributive-Latticeᵉ : Latticeᵉ l1ᵉ l2ᵉ
  lattice-Distributive-Latticeᵉ = pr1ᵉ Lᵉ

  poset-Distributive-Latticeᵉ : Posetᵉ l1ᵉ l2ᵉ
  poset-Distributive-Latticeᵉ = poset-Latticeᵉ lattice-Distributive-Latticeᵉ

  type-Distributive-Latticeᵉ : UUᵉ l1ᵉ
  type-Distributive-Latticeᵉ = type-Latticeᵉ lattice-Distributive-Latticeᵉ

  leq-Distributive-Lattice-Propᵉ : (xᵉ yᵉ : type-Distributive-Latticeᵉ) → Propᵉ l2ᵉ
  leq-Distributive-Lattice-Propᵉ = leq-lattice-Propᵉ lattice-Distributive-Latticeᵉ

  leq-Distributive-Latticeᵉ : (xᵉ yᵉ : type-Distributive-Latticeᵉ) → UUᵉ l2ᵉ
  leq-Distributive-Latticeᵉ = leq-Latticeᵉ lattice-Distributive-Latticeᵉ

  is-prop-leq-Distributive-Latticeᵉ :
    (xᵉ yᵉ : type-Distributive-Latticeᵉ) → is-propᵉ (leq-Distributive-Latticeᵉ xᵉ yᵉ)
  is-prop-leq-Distributive-Latticeᵉ =
    is-prop-leq-Latticeᵉ lattice-Distributive-Latticeᵉ

  refl-leq-Distributive-Latticeᵉ : is-reflexiveᵉ leq-Distributive-Latticeᵉ
  refl-leq-Distributive-Latticeᵉ =
    refl-leq-Latticeᵉ lattice-Distributive-Latticeᵉ

  antisymmetric-leq-Distributive-Latticeᵉ :
    is-antisymmetricᵉ leq-Distributive-Latticeᵉ
  antisymmetric-leq-Distributive-Latticeᵉ =
    antisymmetric-leq-Latticeᵉ lattice-Distributive-Latticeᵉ

  transitive-leq-Distributive-Latticeᵉ : is-transitiveᵉ leq-Distributive-Latticeᵉ
  transitive-leq-Distributive-Latticeᵉ =
    transitive-leq-Latticeᵉ lattice-Distributive-Latticeᵉ

  is-set-type-Distributive-Latticeᵉ : is-setᵉ type-Distributive-Latticeᵉ
  is-set-type-Distributive-Latticeᵉ =
    is-set-type-Latticeᵉ lattice-Distributive-Latticeᵉ

  set-Distributive-Latticeᵉ : Setᵉ l1ᵉ
  set-Distributive-Latticeᵉ = set-Latticeᵉ lattice-Distributive-Latticeᵉ

  is-lattice-Distributive-Latticeᵉ :
    is-lattice-Posetᵉ poset-Distributive-Latticeᵉ
  is-lattice-Distributive-Latticeᵉ =
    is-lattice-Latticeᵉ lattice-Distributive-Latticeᵉ

  is-meet-semilattice-Distributive-Latticeᵉ :
    is-meet-semilattice-Posetᵉ poset-Distributive-Latticeᵉ
  is-meet-semilattice-Distributive-Latticeᵉ =
    is-meet-semilattice-Latticeᵉ lattice-Distributive-Latticeᵉ

  meet-semilattice-Distributive-Latticeᵉ : Meet-Semilatticeᵉ l1ᵉ
  meet-semilattice-Distributive-Latticeᵉ =
    meet-semilattice-Latticeᵉ lattice-Distributive-Latticeᵉ

  meet-Distributive-Latticeᵉ :
    (xᵉ yᵉ : type-Distributive-Latticeᵉ) → type-Distributive-Latticeᵉ
  meet-Distributive-Latticeᵉ =
    meet-Latticeᵉ lattice-Distributive-Latticeᵉ

  is-join-semilattice-Distributive-Latticeᵉ :
    is-join-semilattice-Posetᵉ poset-Distributive-Latticeᵉ
  is-join-semilattice-Distributive-Latticeᵉ =
    is-join-semilattice-Latticeᵉ lattice-Distributive-Latticeᵉ

  join-semilattice-Distributive-Latticeᵉ : Join-Semilatticeᵉ l1ᵉ
  join-semilattice-Distributive-Latticeᵉ =
    join-semilattice-Latticeᵉ lattice-Distributive-Latticeᵉ

  join-Distributive-Latticeᵉ :
    (xᵉ yᵉ : type-Distributive-Latticeᵉ) → type-Distributive-Latticeᵉ
  join-Distributive-Latticeᵉ =
    join-Latticeᵉ lattice-Distributive-Latticeᵉ

  distributive-meet-join-Distributive-Latticeᵉ :
    (xᵉ yᵉ zᵉ : type-Distributive-Latticeᵉ) →
    meet-Distributive-Latticeᵉ xᵉ (join-Distributive-Latticeᵉ yᵉ zᵉ) ＝ᵉ
    join-Distributive-Latticeᵉ
      ( meet-Distributive-Latticeᵉ xᵉ yᵉ)
      ( meet-Distributive-Latticeᵉ xᵉ zᵉ)
  distributive-meet-join-Distributive-Latticeᵉ = pr2ᵉ Lᵉ
```