# Large suplattices

```agda
module order-theory.large-suplatticesᵉ where
```

<detail><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.large-binary-relationsᵉ

open import foundation.binary-relationsᵉ

open import foundation.identity-typesᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ

open import order-theory.large-posetsᵉ
open import order-theory.posetsᵉ
open import order-theory.suplatticesᵉ
open import order-theory.least-upper-bounds-large-posetsᵉ
open import order-theory.upper-bounds-large-posetsᵉ
```

</details>

## Idea

Aᵉ **largeᵉ suplattice**ᵉ isᵉ aᵉ [largeᵉ poset](order-theory.large-posets.mdᵉ) `P`ᵉ suchᵉ
thatᵉ forᵉ everyᵉ familyᵉ

```text
  xᵉ : Iᵉ → type-Large-Posetᵉ Pᵉ l1ᵉ
```

indexedᵉ byᵉ `Iᵉ : UUᵉ l2`ᵉ thereᵉ isᵉ anᵉ elementᵉ `⋁ᵉ xᵉ : type-Large-Posetᵉ Pᵉ (l1ᵉ ⊔ l2)`ᵉ
suchᵉ thatᵉ theᵉ logicalᵉ equivalenceᵉ

```text
  (∀ᵢᵉ xᵢᵉ ≤ᵉ yᵉ) ↔ᵉ ((⋁ᵉ xᵉ) ≤ᵉ yᵉ)
```

holdsᵉ forᵉ everyᵉ elementᵉ `yᵉ : type-Large-Posetᵉ Pᵉ l3`.ᵉ

## Definitions

### The predicate on large posets of having least upper bounds of families of elements

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level} (γᵉ : Level)
  (Pᵉ : Large-Posetᵉ αᵉ βᵉ)
  where

  is-large-suplattice-Large-Posetᵉ : UUωᵉ
  is-large-suplattice-Large-Posetᵉ =
    {l1ᵉ l2ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ} (xᵉ : Iᵉ → type-Large-Posetᵉ Pᵉ l2ᵉ) →
    has-least-upper-bound-family-of-elements-Large-Posetᵉ γᵉ Pᵉ xᵉ

  module _
    (Hᵉ : is-large-suplattice-Large-Posetᵉ)
    {l1ᵉ l2ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ} (xᵉ : Iᵉ → type-Large-Posetᵉ Pᵉ l2ᵉ)
    where

    sup-is-large-suplattice-Large-Posetᵉ : type-Large-Posetᵉ Pᵉ (γᵉ ⊔ l1ᵉ ⊔ l2ᵉ)
    sup-is-large-suplattice-Large-Posetᵉ =
      sup-has-least-upper-bound-family-of-elements-Large-Posetᵉ (Hᵉ xᵉ)

    is-least-upper-bound-sup-is-large-suplattice-Large-Posetᵉ :
      is-least-upper-bound-family-of-elements-Large-Posetᵉ Pᵉ xᵉ
        sup-is-large-suplattice-Large-Posetᵉ
    is-least-upper-bound-sup-is-large-suplattice-Large-Posetᵉ =
      is-least-upper-bound-sup-has-least-upper-bound-family-of-elements-Large-Posetᵉ
        ( Hᵉ xᵉ)
```

### Large suplattices

```agda
record
  Large-Suplatticeᵉ
    (αᵉ : Level → Level) (βᵉ : Level → Level → Level) (γᵉ : Level) : UUωᵉ
  where
  constructor
    make-Large-Suplatticeᵉ
  field
    large-poset-Large-Suplatticeᵉ : Large-Posetᵉ αᵉ βᵉ
    is-large-suplattice-Large-Suplatticeᵉ :
      is-large-suplattice-Large-Posetᵉ γᵉ large-poset-Large-Suplatticeᵉ

open Large-Suplatticeᵉ public

module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level} {γᵉ : Level}
  (Lᵉ : Large-Suplatticeᵉ αᵉ βᵉ γᵉ)
  where

  set-Large-Suplatticeᵉ : (lᵉ : Level) → Setᵉ (αᵉ lᵉ)
  set-Large-Suplatticeᵉ = set-Large-Posetᵉ (large-poset-Large-Suplatticeᵉ Lᵉ)

  type-Large-Suplatticeᵉ : (lᵉ : Level) → UUᵉ (αᵉ lᵉ)
  type-Large-Suplatticeᵉ = type-Large-Posetᵉ (large-poset-Large-Suplatticeᵉ Lᵉ)

  is-set-type-Large-Suplatticeᵉ : {lᵉ : Level} → is-setᵉ (type-Large-Suplatticeᵉ lᵉ)
  is-set-type-Large-Suplatticeᵉ =
    is-set-type-Large-Posetᵉ (large-poset-Large-Suplatticeᵉ Lᵉ)

  leq-prop-Large-Suplatticeᵉ :
    Large-Relation-Propᵉ βᵉ type-Large-Suplatticeᵉ
  leq-prop-Large-Suplatticeᵉ =
    leq-prop-Large-Posetᵉ (large-poset-Large-Suplatticeᵉ Lᵉ)

  leq-Large-Suplatticeᵉ :
    Large-Relationᵉ βᵉ type-Large-Suplatticeᵉ
  leq-Large-Suplatticeᵉ = leq-Large-Posetᵉ (large-poset-Large-Suplatticeᵉ Lᵉ)

  is-prop-leq-Large-Suplatticeᵉ :
    is-prop-Large-Relationᵉ type-Large-Suplatticeᵉ leq-Large-Suplatticeᵉ
  is-prop-leq-Large-Suplatticeᵉ =
    is-prop-leq-Large-Posetᵉ (large-poset-Large-Suplatticeᵉ Lᵉ)

  refl-leq-Large-Suplatticeᵉ :
    is-reflexive-Large-Relationᵉ type-Large-Suplatticeᵉ leq-Large-Suplatticeᵉ
  refl-leq-Large-Suplatticeᵉ =
    refl-leq-Large-Posetᵉ (large-poset-Large-Suplatticeᵉ Lᵉ)

  antisymmetric-leq-Large-Suplatticeᵉ :
    is-antisymmetric-Large-Relationᵉ type-Large-Suplatticeᵉ leq-Large-Suplatticeᵉ
  antisymmetric-leq-Large-Suplatticeᵉ =
    antisymmetric-leq-Large-Posetᵉ (large-poset-Large-Suplatticeᵉ Lᵉ)

  transitive-leq-Large-Suplatticeᵉ :
    is-transitive-Large-Relationᵉ type-Large-Suplatticeᵉ leq-Large-Suplatticeᵉ
  transitive-leq-Large-Suplatticeᵉ =
    transitive-leq-Large-Posetᵉ (large-poset-Large-Suplatticeᵉ Lᵉ)

  sup-Large-Suplatticeᵉ :
    {l1ᵉ l2ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ} (xᵉ : Iᵉ → type-Large-Suplatticeᵉ l2ᵉ) →
    type-Large-Suplatticeᵉ (γᵉ ⊔ l1ᵉ ⊔ l2ᵉ)
  sup-Large-Suplatticeᵉ xᵉ =
    sup-has-least-upper-bound-family-of-elements-Large-Posetᵉ
      ( is-large-suplattice-Large-Suplatticeᵉ Lᵉ xᵉ)

  is-upper-bound-family-of-elements-Large-Suplatticeᵉ :
    {l1ᵉ l2ᵉ l3ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ} (xᵉ : Iᵉ → type-Large-Suplatticeᵉ l2ᵉ)
    (yᵉ : type-Large-Suplatticeᵉ l3ᵉ) → UUᵉ (βᵉ l2ᵉ l3ᵉ ⊔ l1ᵉ)
  is-upper-bound-family-of-elements-Large-Suplatticeᵉ xᵉ yᵉ =
    is-upper-bound-family-of-elements-Large-Posetᵉ
      ( large-poset-Large-Suplatticeᵉ Lᵉ)
      ( xᵉ)
      ( yᵉ)

  is-least-upper-bound-family-of-elements-Large-Suplatticeᵉ :
    {l1ᵉ l2ᵉ l3ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ} (xᵉ : Iᵉ → type-Large-Suplatticeᵉ l2ᵉ) →
    type-Large-Suplatticeᵉ l3ᵉ → UUωᵉ
  is-least-upper-bound-family-of-elements-Large-Suplatticeᵉ =
    is-least-upper-bound-family-of-elements-Large-Posetᵉ
      ( large-poset-Large-Suplatticeᵉ Lᵉ)

  is-least-upper-bound-sup-Large-Suplatticeᵉ :
    {l1ᵉ l2ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ} (xᵉ : Iᵉ → type-Large-Suplatticeᵉ l2ᵉ) →
    is-least-upper-bound-family-of-elements-Large-Suplatticeᵉ xᵉ
      ( sup-Large-Suplatticeᵉ xᵉ)
  is-least-upper-bound-sup-Large-Suplatticeᵉ xᵉ =
    is-least-upper-bound-sup-has-least-upper-bound-family-of-elements-Large-Posetᵉ
      ( is-large-suplattice-Large-Suplatticeᵉ Lᵉ xᵉ)

  is-upper-bound-sup-Large-Suplatticeᵉ :
    {l1ᵉ l2ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ} (xᵉ : Iᵉ → type-Large-Suplatticeᵉ l2ᵉ) →
    is-upper-bound-family-of-elements-Large-Suplatticeᵉ xᵉ
      ( sup-Large-Suplatticeᵉ xᵉ)
  is-upper-bound-sup-Large-Suplatticeᵉ xᵉ =
    backward-implicationᵉ
      ( is-least-upper-bound-sup-Large-Suplatticeᵉ xᵉ (sup-Large-Suplatticeᵉ xᵉ))
      ( refl-leq-Large-Suplatticeᵉ (sup-Large-Suplatticeᵉ xᵉ))
```

## Properties

### The operation `sup` is order preserving

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level} {γᵉ : Level}
  (Lᵉ : Large-Suplatticeᵉ αᵉ βᵉ γᵉ)
  where

  preserves-order-sup-Large-Suplatticeᵉ :
    {l1ᵉ l2ᵉ l3ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ}
    {xᵉ : Iᵉ → type-Large-Suplatticeᵉ Lᵉ l2ᵉ}
    {yᵉ : Iᵉ → type-Large-Suplatticeᵉ Lᵉ l3ᵉ} →
    ((iᵉ : Iᵉ) → leq-Large-Suplatticeᵉ Lᵉ (xᵉ iᵉ) (yᵉ iᵉ)) →
    leq-Large-Suplatticeᵉ Lᵉ
      ( sup-Large-Suplatticeᵉ Lᵉ xᵉ)
      ( sup-Large-Suplatticeᵉ Lᵉ yᵉ)
  preserves-order-sup-Large-Suplatticeᵉ {xᵉ = xᵉ} {yᵉ} Hᵉ =
    forward-implicationᵉ
      ( is-least-upper-bound-sup-Large-Suplatticeᵉ Lᵉ xᵉ
        ( sup-Large-Suplatticeᵉ Lᵉ yᵉ))
      ( λ iᵉ →
        transitive-leq-Large-Suplatticeᵉ Lᵉ
          ( xᵉ iᵉ)
          ( yᵉ iᵉ)
          ( sup-Large-Suplatticeᵉ Lᵉ yᵉ)
          ( is-upper-bound-sup-Large-Suplatticeᵉ Lᵉ yᵉ iᵉ)
          ( Hᵉ iᵉ))
```

### Small suplattices from large suplattices

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level} {γᵉ : Level}
  (Lᵉ : Large-Suplatticeᵉ αᵉ βᵉ γᵉ)
  where

  poset-Large-Suplatticeᵉ : (lᵉ : Level) → Posetᵉ (αᵉ lᵉ) (βᵉ lᵉ lᵉ)
  poset-Large-Suplatticeᵉ = poset-Large-Posetᵉ (large-poset-Large-Suplatticeᵉ Lᵉ)

  is-suplattice-poset-Large-Suplatticeᵉ :
    (l1ᵉ l2ᵉ : Level) →
    is-suplattice-Posetᵉ l1ᵉ (poset-Large-Suplatticeᵉ (γᵉ ⊔ l1ᵉ ⊔ l2ᵉ))
  pr1ᵉ (is-suplattice-poset-Large-Suplatticeᵉ l1ᵉ l2ᵉ Iᵉ fᵉ) =
    sup-Large-Suplatticeᵉ Lᵉ fᵉ
  pr2ᵉ (is-suplattice-poset-Large-Suplatticeᵉ l1ᵉ l2ᵉ Iᵉ fᵉ) =
    is-least-upper-bound-sup-Large-Suplatticeᵉ Lᵉ fᵉ

  suplattice-Large-Suplatticeᵉ :
    (l1ᵉ l2ᵉ : Level) →
    Suplatticeᵉ (αᵉ (γᵉ ⊔ l1ᵉ ⊔ l2ᵉ)) (βᵉ (γᵉ ⊔ l1ᵉ ⊔ l2ᵉ) (γᵉ ⊔ l1ᵉ ⊔ l2ᵉ)) (l1ᵉ)
  pr1ᵉ (suplattice-Large-Suplatticeᵉ l1ᵉ l2ᵉ) =
    poset-Large-Suplatticeᵉ (γᵉ ⊔ l1ᵉ ⊔ l2ᵉ)
  pr2ᵉ (suplattice-Large-Suplatticeᵉ l1ᵉ l2ᵉ) =
    is-suplattice-poset-Large-Suplatticeᵉ l1ᵉ l2ᵉ
```