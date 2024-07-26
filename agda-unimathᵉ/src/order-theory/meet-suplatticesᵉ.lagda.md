# Meet-suplattices

```agda
module order-theory.meet-suplatticesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relationsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ

open import order-theory.meet-semilatticesᵉ
open import order-theory.posetsᵉ
open import order-theory.suplatticesᵉ
```

</details>

## Idea

Anᵉ **`l`-meet-suplattice**ᵉ isᵉ aᵉ meet-semilatticeᵉ `L`ᵉ whichᵉ hasᵉ leastᵉ upperᵉ
boundsᵉ forᵉ allᵉ familiesᵉ ofᵉ elementsᵉ `xᵉ : Iᵉ → L`ᵉ indexedᵉ byᵉ aᵉ typeᵉ `Iᵉ : UUᵉ l`.ᵉ

Noteᵉ thatᵉ meet-suplatticesᵉ areᵉ notᵉ requiredᵉ to satisfyᵉ aᵉ distributiveᵉ law.ᵉ Suchᵉ
meet-suplatticesᵉ areᵉ calledᵉ [frames](order-theory.frames.md).ᵉ

## Definitions

### The predicate on meet-semilattices of being a meet-suplattice

```agda
module _
  {l1ᵉ : Level} (l2ᵉ : Level) (Xᵉ : Meet-Semilatticeᵉ l1ᵉ)
  where

  is-meet-suplattice-Meet-Semilattice-Propᵉ : Propᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
  is-meet-suplattice-Meet-Semilattice-Propᵉ =
    is-suplattice-Poset-Propᵉ l2ᵉ (poset-Meet-Semilatticeᵉ Xᵉ)

  is-meet-suplattice-Meet-Semilatticeᵉ : UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
  is-meet-suplattice-Meet-Semilatticeᵉ =
    type-Propᵉ is-meet-suplattice-Meet-Semilattice-Propᵉ

  is-prop-is-meet-suplattice-Meet-Semilatticeᵉ :
    is-propᵉ is-meet-suplattice-Meet-Semilatticeᵉ
  is-prop-is-meet-suplattice-Meet-Semilatticeᵉ =
    is-prop-type-Propᵉ is-meet-suplattice-Meet-Semilattice-Propᵉ
```

### Meet-suplattices

```agda
Meet-Suplatticeᵉ : (l1ᵉ l2ᵉ : Level) → UUᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ)
Meet-Suplatticeᵉ l1ᵉ l2ᵉ =
  Σᵉ (Meet-Semilatticeᵉ l1ᵉ) (is-meet-suplattice-Meet-Semilatticeᵉ l2ᵉ)

module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Meet-Suplatticeᵉ l1ᵉ l2ᵉ)
  where

  meet-semilattice-Meet-Suplatticeᵉ : Meet-Semilatticeᵉ l1ᵉ
  meet-semilattice-Meet-Suplatticeᵉ = pr1ᵉ Aᵉ

  poset-Meet-Suplatticeᵉ : Posetᵉ l1ᵉ l1ᵉ
  poset-Meet-Suplatticeᵉ =
    poset-Meet-Semilatticeᵉ meet-semilattice-Meet-Suplatticeᵉ

  type-Meet-Suplatticeᵉ : UUᵉ l1ᵉ
  type-Meet-Suplatticeᵉ =
    type-Posetᵉ poset-Meet-Suplatticeᵉ

  leq-meet-suplattice-Propᵉ : (xᵉ yᵉ : type-Meet-Suplatticeᵉ) → Propᵉ l1ᵉ
  leq-meet-suplattice-Propᵉ = leq-Poset-Propᵉ poset-Meet-Suplatticeᵉ

  leq-Meet-Suplatticeᵉ : (xᵉ yᵉ : type-Meet-Suplatticeᵉ) → UUᵉ l1ᵉ
  leq-Meet-Suplatticeᵉ = leq-Posetᵉ poset-Meet-Suplatticeᵉ

  is-prop-leq-Meet-Suplatticeᵉ :
    (xᵉ yᵉ : type-Meet-Suplatticeᵉ) → is-propᵉ (leq-Meet-Suplatticeᵉ xᵉ yᵉ)
  is-prop-leq-Meet-Suplatticeᵉ = is-prop-leq-Posetᵉ poset-Meet-Suplatticeᵉ

  refl-leq-Meet-Suplatticeᵉ : is-reflexiveᵉ leq-Meet-Suplatticeᵉ
  refl-leq-Meet-Suplatticeᵉ = refl-leq-Posetᵉ poset-Meet-Suplatticeᵉ

  antisymmetric-leq-Meet-Suplatticeᵉ : is-antisymmetricᵉ leq-Meet-Suplatticeᵉ
  antisymmetric-leq-Meet-Suplatticeᵉ =
    antisymmetric-leq-Posetᵉ poset-Meet-Suplatticeᵉ

  transitive-leq-Meet-Suplatticeᵉ : is-transitiveᵉ leq-Meet-Suplatticeᵉ
  transitive-leq-Meet-Suplatticeᵉ = transitive-leq-Posetᵉ poset-Meet-Suplatticeᵉ

  is-set-type-Meet-Suplatticeᵉ : is-setᵉ type-Meet-Suplatticeᵉ
  is-set-type-Meet-Suplatticeᵉ = is-set-type-Posetᵉ poset-Meet-Suplatticeᵉ

  set-Meet-Suplatticeᵉ : Setᵉ l1ᵉ
  set-Meet-Suplatticeᵉ = set-Posetᵉ poset-Meet-Suplatticeᵉ

  is-suplattice-Meet-Suplatticeᵉ :
    is-suplattice-Posetᵉ l2ᵉ poset-Meet-Suplatticeᵉ
  is-suplattice-Meet-Suplatticeᵉ = pr2ᵉ Aᵉ

  suplattice-Meet-Suplatticeᵉ : Suplatticeᵉ l1ᵉ l1ᵉ l2ᵉ
  suplattice-Meet-Suplatticeᵉ =
    ( poset-Meet-Suplatticeᵉ ,ᵉ is-suplattice-Meet-Suplatticeᵉ)

  meet-Meet-Suplatticeᵉ :
    (xᵉ yᵉ : type-Meet-Suplatticeᵉ) →
    type-Meet-Suplatticeᵉ
  meet-Meet-Suplatticeᵉ =
    meet-Meet-Semilatticeᵉ meet-semilattice-Meet-Suplatticeᵉ

  sup-Meet-Suplatticeᵉ :
    {Iᵉ : UUᵉ l2ᵉ} → (Iᵉ → type-Meet-Suplatticeᵉ) →
    type-Meet-Suplatticeᵉ
  sup-Meet-Suplatticeᵉ {Iᵉ} fᵉ = pr1ᵉ (is-suplattice-Meet-Suplatticeᵉ Iᵉ fᵉ)
```