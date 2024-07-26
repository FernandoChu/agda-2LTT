# Suplattices

```agda
module order-theory.suplatticesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relationsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ

open import order-theory.least-upper-bounds-posetsᵉ
open import order-theory.posetsᵉ
```

</details>

## Idea

Anᵉ **`l`-suplattice**ᵉ isᵉ aᵉ posetᵉ whichᵉ hasᵉ allᵉ leastᵉ upperᵉ boundsᵉ ofᵉ familiesᵉ ofᵉ
elementsᵉ indexedᵉ byᵉ aᵉ typeᵉ ofᵉ universeᵉ levelᵉ `l`.ᵉ

## Definitions

### The predicate on posets of being an `l`-suplattice

```agda
module _
  {l1ᵉ l2ᵉ : Level} (l3ᵉ : Level) (Pᵉ : Posetᵉ l1ᵉ l2ᵉ)
  where

  is-suplattice-Poset-Propᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ lsuc l3ᵉ)
  is-suplattice-Poset-Propᵉ =
    Π-Propᵉ
      (UUᵉ l3ᵉ)
      (λ Iᵉ →
        Π-Propᵉ
          ( Iᵉ → type-Posetᵉ Pᵉ)
          ( λ fᵉ → has-least-upper-bound-family-of-elements-Poset-Propᵉ Pᵉ fᵉ))

  is-suplattice-Posetᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ lsuc l3ᵉ)
  is-suplattice-Posetᵉ = type-Propᵉ is-suplattice-Poset-Propᵉ

  is-prop-suplattice-Posetᵉ : is-propᵉ is-suplattice-Posetᵉ
  is-prop-suplattice-Posetᵉ = is-prop-type-Propᵉ is-suplattice-Poset-Propᵉ

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Pᵉ : Posetᵉ l1ᵉ l2ᵉ) (Hᵉ : is-suplattice-Posetᵉ l3ᵉ Pᵉ)
  where

  sup-is-suplattice-Posetᵉ :
    {Iᵉ : UUᵉ l3ᵉ} → (Iᵉ → type-Posetᵉ Pᵉ) → type-Posetᵉ Pᵉ
  sup-is-suplattice-Posetᵉ {Iᵉ} xᵉ = pr1ᵉ (Hᵉ Iᵉ xᵉ)

  is-least-upper-bound-sup-is-suplattice-Posetᵉ :
    {Iᵉ : UUᵉ l3ᵉ} (xᵉ : Iᵉ → type-Posetᵉ Pᵉ) →
    is-least-upper-bound-family-of-elements-Posetᵉ Pᵉ xᵉ
      ( sup-is-suplattice-Posetᵉ xᵉ)
  is-least-upper-bound-sup-is-suplattice-Posetᵉ {Iᵉ} xᵉ = pr2ᵉ (Hᵉ Iᵉ xᵉ)
```

### `l`-Suplattices

```agda
Suplatticeᵉ : (l1ᵉ l2ᵉ l3ᵉ : Level) → UUᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ ⊔ lsuc l3ᵉ)
Suplatticeᵉ l1ᵉ l2ᵉ l3ᵉ = Σᵉ (Posetᵉ l1ᵉ l2ᵉ) (λ Pᵉ → is-suplattice-Posetᵉ l3ᵉ Pᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Aᵉ : Suplatticeᵉ l1ᵉ l2ᵉ l3ᵉ)
  where

  poset-Suplatticeᵉ : Posetᵉ l1ᵉ l2ᵉ
  poset-Suplatticeᵉ = pr1ᵉ Aᵉ

  type-Suplatticeᵉ : UUᵉ l1ᵉ
  type-Suplatticeᵉ = type-Posetᵉ poset-Suplatticeᵉ

  leq-Suplattice-Propᵉ : (xᵉ yᵉ : type-Suplatticeᵉ) → Propᵉ l2ᵉ
  leq-Suplattice-Propᵉ = leq-Poset-Propᵉ poset-Suplatticeᵉ

  leq-Suplatticeᵉ : (xᵉ yᵉ : type-Suplatticeᵉ) → UUᵉ l2ᵉ
  leq-Suplatticeᵉ = leq-Posetᵉ poset-Suplatticeᵉ

  is-prop-leq-Suplatticeᵉ :
    (xᵉ yᵉ : type-Suplatticeᵉ) → is-propᵉ (leq-Suplatticeᵉ xᵉ yᵉ)
  is-prop-leq-Suplatticeᵉ = is-prop-leq-Posetᵉ poset-Suplatticeᵉ

  refl-leq-Suplatticeᵉ :
    (xᵉ : type-Suplatticeᵉ) → leq-Suplatticeᵉ xᵉ xᵉ
  refl-leq-Suplatticeᵉ = refl-leq-Posetᵉ poset-Suplatticeᵉ

  antisymmetric-leq-Suplatticeᵉ : is-antisymmetricᵉ leq-Suplatticeᵉ
  antisymmetric-leq-Suplatticeᵉ =
    antisymmetric-leq-Posetᵉ poset-Suplatticeᵉ

  transitive-leq-Suplatticeᵉ : is-transitiveᵉ leq-Suplatticeᵉ
  transitive-leq-Suplatticeᵉ = transitive-leq-Posetᵉ poset-Suplatticeᵉ

  is-set-type-Suplatticeᵉ : is-setᵉ type-Suplatticeᵉ
  is-set-type-Suplatticeᵉ = is-set-type-Posetᵉ poset-Suplatticeᵉ

  set-Suplatticeᵉ : Setᵉ l1ᵉ
  set-Suplatticeᵉ = set-Posetᵉ poset-Suplatticeᵉ

  is-suplattice-Suplatticeᵉ :
    is-suplattice-Posetᵉ l3ᵉ poset-Suplatticeᵉ
  is-suplattice-Suplatticeᵉ = pr2ᵉ Aᵉ

  sup-Suplatticeᵉ :
    {Iᵉ : UUᵉ l3ᵉ} → (Iᵉ → type-Suplatticeᵉ) → type-Suplatticeᵉ
  sup-Suplatticeᵉ =
    sup-is-suplattice-Posetᵉ
      ( poset-Suplatticeᵉ)
      ( is-suplattice-Suplatticeᵉ)

  is-least-upper-bound-sup-Suplatticeᵉ :
    {Iᵉ : UUᵉ l3ᵉ} (xᵉ : Iᵉ → type-Suplatticeᵉ) →
    is-least-upper-bound-family-of-elements-Posetᵉ poset-Suplatticeᵉ xᵉ
      ( sup-Suplatticeᵉ xᵉ)
  is-least-upper-bound-sup-Suplatticeᵉ =
    is-least-upper-bound-sup-is-suplattice-Posetᵉ
      ( poset-Suplatticeᵉ)
      ( is-suplattice-Suplatticeᵉ)
```