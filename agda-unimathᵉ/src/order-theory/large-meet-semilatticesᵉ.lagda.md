# Large meet-semilattices

```agda
module order-theory.large-meet-semilatticesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.large-binary-relationsᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ

open import order-theory.greatest-lower-bounds-large-posetsᵉ
open import order-theory.large-posetsᵉ
open import order-theory.meet-semilatticesᵉ
open import order-theory.posetsᵉ
open import order-theory.top-elements-large-posetsᵉ
```

</details>

## Idea

Aᵉ **largeᵉ meet-semilattice**ᵉ isᵉ aᵉ
[largeᵉ semigroup](group-theory.large-semigroups.mdᵉ) whichᵉ isᵉ commutativeᵉ andᵉ
idempotent.ᵉ

## Definition

### The predicate that a large poset has meets

```agda
record
  has-meets-Large-Posetᵉ
    { αᵉ : Level → Level}
    { βᵉ : Level → Level → Level}
    ( Pᵉ : Large-Posetᵉ αᵉ βᵉ) :
    UUωᵉ
  where
  constructor
    make-has-meets-Large-Posetᵉ
  field
    meet-has-meets-Large-Posetᵉ :
      {l1ᵉ l2ᵉ : Level}
      (xᵉ : type-Large-Posetᵉ Pᵉ l1ᵉ) (yᵉ : type-Large-Posetᵉ Pᵉ l2ᵉ) →
      type-Large-Posetᵉ Pᵉ (l1ᵉ ⊔ l2ᵉ)
    is-greatest-binary-lower-bound-meet-has-meets-Large-Posetᵉ :
      {l1ᵉ l2ᵉ : Level}
      (xᵉ : type-Large-Posetᵉ Pᵉ l1ᵉ) (yᵉ : type-Large-Posetᵉ Pᵉ l2ᵉ) →
      is-greatest-binary-lower-bound-Large-Posetᵉ Pᵉ xᵉ yᵉ
        ( meet-has-meets-Large-Posetᵉ xᵉ yᵉ)

open has-meets-Large-Posetᵉ public
```

### The predicate of being a large meet-semilattice

```agda
record
  is-large-meet-semilattice-Large-Posetᵉ
    { αᵉ : Level → Level}
    { βᵉ : Level → Level → Level}
    ( Pᵉ : Large-Posetᵉ αᵉ βᵉ) :
    UUωᵉ
  where
  field
    has-meets-is-large-meet-semilattice-Large-Posetᵉ :
      has-meets-Large-Posetᵉ Pᵉ
    has-top-element-is-large-meet-semilattice-Large-Posetᵉ :
      has-top-element-Large-Posetᵉ Pᵉ

open is-large-meet-semilattice-Large-Posetᵉ public

module _
  {αᵉ : Level → Level}
  {βᵉ : Level → Level → Level}
  (Pᵉ : Large-Posetᵉ αᵉ βᵉ)
  (Hᵉ : is-large-meet-semilattice-Large-Posetᵉ Pᵉ)
  where

  meet-is-large-meet-semilattice-Large-Posetᵉ :
    {l1ᵉ l2ᵉ : Level} (xᵉ : type-Large-Posetᵉ Pᵉ l1ᵉ) (yᵉ : type-Large-Posetᵉ Pᵉ l2ᵉ) →
    type-Large-Posetᵉ Pᵉ (l1ᵉ ⊔ l2ᵉ)
  meet-is-large-meet-semilattice-Large-Posetᵉ =
    meet-has-meets-Large-Posetᵉ
      ( has-meets-is-large-meet-semilattice-Large-Posetᵉ Hᵉ)

  is-greatest-binary-lower-bound-meet-is-large-meet-semilattice-Large-Posetᵉ :
    {l1ᵉ l2ᵉ : Level} (xᵉ : type-Large-Posetᵉ Pᵉ l1ᵉ) (yᵉ : type-Large-Posetᵉ Pᵉ l2ᵉ) →
    is-greatest-binary-lower-bound-Large-Posetᵉ Pᵉ xᵉ yᵉ
      ( meet-is-large-meet-semilattice-Large-Posetᵉ xᵉ yᵉ)
  is-greatest-binary-lower-bound-meet-is-large-meet-semilattice-Large-Posetᵉ =
    is-greatest-binary-lower-bound-meet-has-meets-Large-Posetᵉ
      ( has-meets-is-large-meet-semilattice-Large-Posetᵉ Hᵉ)

  top-is-large-meet-semilattice-Large-Posetᵉ :
    type-Large-Posetᵉ Pᵉ lzero
  top-is-large-meet-semilattice-Large-Posetᵉ =
    top-has-top-element-Large-Posetᵉ
      ( has-top-element-is-large-meet-semilattice-Large-Posetᵉ Hᵉ)

  is-top-element-top-is-large-meet-semilattice-Large-Posetᵉ :
    {l1ᵉ : Level} (xᵉ : type-Large-Posetᵉ Pᵉ l1ᵉ) →
    leq-Large-Posetᵉ Pᵉ xᵉ top-is-large-meet-semilattice-Large-Posetᵉ
  is-top-element-top-is-large-meet-semilattice-Large-Posetᵉ =
    is-top-element-top-has-top-element-Large-Posetᵉ
      ( has-top-element-is-large-meet-semilattice-Large-Posetᵉ Hᵉ)
```

### Large meet-semilattices

```agda
record
  Large-Meet-Semilatticeᵉ
    ( αᵉ : Level → Level)
    ( βᵉ : Level → Level → Level) :
    UUωᵉ
  where
  constructor
    make-Large-Meet-Semilatticeᵉ
  field
    large-poset-Large-Meet-Semilatticeᵉ :
      Large-Posetᵉ αᵉ βᵉ
    is-large-meet-semilattice-Large-Meet-Semilatticeᵉ :
      is-large-meet-semilattice-Large-Posetᵉ
        large-poset-Large-Meet-Semilatticeᵉ

open Large-Meet-Semilatticeᵉ public

module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Lᵉ : Large-Meet-Semilatticeᵉ αᵉ βᵉ)
  where

  type-Large-Meet-Semilatticeᵉ : (lᵉ : Level) → UUᵉ (αᵉ lᵉ)
  type-Large-Meet-Semilatticeᵉ =
    type-Large-Posetᵉ (large-poset-Large-Meet-Semilatticeᵉ Lᵉ)

  set-Large-Meet-Semilatticeᵉ : (lᵉ : Level) → Setᵉ (αᵉ lᵉ)
  set-Large-Meet-Semilatticeᵉ =
    set-Large-Posetᵉ (large-poset-Large-Meet-Semilatticeᵉ Lᵉ)

  is-set-type-Large-Meet-Semilatticeᵉ :
    {lᵉ : Level} → is-setᵉ (type-Large-Meet-Semilatticeᵉ lᵉ)
  is-set-type-Large-Meet-Semilatticeᵉ =
    is-set-type-Large-Posetᵉ (large-poset-Large-Meet-Semilatticeᵉ Lᵉ)

  leq-Large-Meet-Semilatticeᵉ : Large-Relationᵉ βᵉ type-Large-Meet-Semilatticeᵉ
  leq-Large-Meet-Semilatticeᵉ =
    leq-Large-Posetᵉ (large-poset-Large-Meet-Semilatticeᵉ Lᵉ)

  refl-leq-Large-Meet-Semilatticeᵉ :
    is-reflexive-Large-Relationᵉ
      ( type-Large-Meet-Semilatticeᵉ)
      ( leq-Large-Meet-Semilatticeᵉ)
  refl-leq-Large-Meet-Semilatticeᵉ =
    refl-leq-Large-Posetᵉ (large-poset-Large-Meet-Semilatticeᵉ Lᵉ)

  antisymmetric-leq-Large-Meet-Semilatticeᵉ :
    is-antisymmetric-Large-Relationᵉ
      ( type-Large-Meet-Semilatticeᵉ)
      ( leq-Large-Meet-Semilatticeᵉ)
  antisymmetric-leq-Large-Meet-Semilatticeᵉ =
    antisymmetric-leq-Large-Posetᵉ (large-poset-Large-Meet-Semilatticeᵉ Lᵉ)

  transitive-leq-Large-Meet-Semilatticeᵉ :
    is-transitive-Large-Relationᵉ
      ( type-Large-Meet-Semilatticeᵉ)
      ( leq-Large-Meet-Semilatticeᵉ)
  transitive-leq-Large-Meet-Semilatticeᵉ =
    transitive-leq-Large-Posetᵉ (large-poset-Large-Meet-Semilatticeᵉ Lᵉ)

  has-meets-Large-Meet-Semilatticeᵉ :
    has-meets-Large-Posetᵉ (large-poset-Large-Meet-Semilatticeᵉ Lᵉ)
  has-meets-Large-Meet-Semilatticeᵉ =
    has-meets-is-large-meet-semilattice-Large-Posetᵉ
      ( is-large-meet-semilattice-Large-Meet-Semilatticeᵉ Lᵉ)

  meet-Large-Meet-Semilatticeᵉ :
    {l1ᵉ l2ᵉ : Level}
    (xᵉ : type-Large-Meet-Semilatticeᵉ l1ᵉ)
    (yᵉ : type-Large-Meet-Semilatticeᵉ l2ᵉ) →
    type-Large-Meet-Semilatticeᵉ (l1ᵉ ⊔ l2ᵉ)
  meet-Large-Meet-Semilatticeᵉ =
    meet-is-large-meet-semilattice-Large-Posetᵉ
      ( large-poset-Large-Meet-Semilatticeᵉ Lᵉ)
      ( is-large-meet-semilattice-Large-Meet-Semilatticeᵉ Lᵉ)

  is-greatest-binary-lower-bound-meet-Large-Meet-Semilatticeᵉ :
    {l1ᵉ l2ᵉ : Level}
    (xᵉ : type-Large-Meet-Semilatticeᵉ l1ᵉ)
    (yᵉ : type-Large-Meet-Semilatticeᵉ l2ᵉ) →
    is-greatest-binary-lower-bound-Large-Posetᵉ
      ( large-poset-Large-Meet-Semilatticeᵉ Lᵉ)
      ( xᵉ)
      ( yᵉ)
      ( meet-Large-Meet-Semilatticeᵉ xᵉ yᵉ)
  is-greatest-binary-lower-bound-meet-Large-Meet-Semilatticeᵉ =
    is-greatest-binary-lower-bound-meet-is-large-meet-semilattice-Large-Posetᵉ
      ( large-poset-Large-Meet-Semilatticeᵉ Lᵉ)
      ( is-large-meet-semilattice-Large-Meet-Semilatticeᵉ Lᵉ)

  ap-meet-Large-Meet-Semilatticeᵉ :
    {l1ᵉ l2ᵉ : Level}
    {xᵉ x'ᵉ : type-Large-Meet-Semilatticeᵉ l1ᵉ}
    {yᵉ y'ᵉ : type-Large-Meet-Semilatticeᵉ l2ᵉ} →
    (xᵉ ＝ᵉ x'ᵉ) → (yᵉ ＝ᵉ y'ᵉ) →
    meet-Large-Meet-Semilatticeᵉ xᵉ yᵉ ＝ᵉ meet-Large-Meet-Semilatticeᵉ x'ᵉ y'ᵉ
  ap-meet-Large-Meet-Semilatticeᵉ pᵉ qᵉ =
    ap-binaryᵉ meet-Large-Meet-Semilatticeᵉ pᵉ qᵉ

  has-top-element-Large-Meet-Semilatticeᵉ :
    has-top-element-Large-Posetᵉ (large-poset-Large-Meet-Semilatticeᵉ Lᵉ)
  has-top-element-Large-Meet-Semilatticeᵉ =
    has-top-element-is-large-meet-semilattice-Large-Posetᵉ
      ( is-large-meet-semilattice-Large-Meet-Semilatticeᵉ Lᵉ)

  top-Large-Meet-Semilatticeᵉ :
    type-Large-Meet-Semilatticeᵉ lzero
  top-Large-Meet-Semilatticeᵉ =
    top-is-large-meet-semilattice-Large-Posetᵉ
      ( large-poset-Large-Meet-Semilatticeᵉ Lᵉ)
      ( is-large-meet-semilattice-Large-Meet-Semilatticeᵉ Lᵉ)

  is-top-element-top-Large-Meet-Semilatticeᵉ :
    {l1ᵉ : Level} (xᵉ : type-Large-Meet-Semilatticeᵉ l1ᵉ) →
    leq-Large-Meet-Semilatticeᵉ xᵉ top-Large-Meet-Semilatticeᵉ
  is-top-element-top-Large-Meet-Semilatticeᵉ =
    is-top-element-top-is-large-meet-semilattice-Large-Posetᵉ
      ( large-poset-Large-Meet-Semilatticeᵉ Lᵉ)
      ( is-large-meet-semilattice-Large-Meet-Semilatticeᵉ Lᵉ)
```

### Small meet semilattices from large meet semilattices

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Lᵉ : Large-Meet-Semilatticeᵉ αᵉ βᵉ)
  where

  poset-Large-Meet-Semilatticeᵉ : (lᵉ : Level) → Posetᵉ (αᵉ lᵉ) (βᵉ lᵉ lᵉ)
  poset-Large-Meet-Semilatticeᵉ =
    poset-Large-Posetᵉ (large-poset-Large-Meet-Semilatticeᵉ Lᵉ)

  is-meet-semilattice-poset-Large-Meet-Semilatticeᵉ :
    {lᵉ : Level} → is-meet-semilattice-Posetᵉ (poset-Large-Meet-Semilatticeᵉ lᵉ)
  pr1ᵉ (is-meet-semilattice-poset-Large-Meet-Semilatticeᵉ xᵉ yᵉ) =
    meet-Large-Meet-Semilatticeᵉ Lᵉ xᵉ yᵉ
  pr2ᵉ (is-meet-semilattice-poset-Large-Meet-Semilatticeᵉ xᵉ yᵉ) =
    is-greatest-binary-lower-bound-meet-Large-Meet-Semilatticeᵉ Lᵉ xᵉ yᵉ

  order-theoretic-meet-semilattice-Large-Meet-Semilatticeᵉ :
    (lᵉ : Level) → Order-Theoretic-Meet-Semilatticeᵉ (αᵉ lᵉ) (βᵉ lᵉ lᵉ)
  pr1ᵉ (order-theoretic-meet-semilattice-Large-Meet-Semilatticeᵉ lᵉ) =
    poset-Large-Meet-Semilatticeᵉ lᵉ
  pr2ᵉ (order-theoretic-meet-semilattice-Large-Meet-Semilatticeᵉ lᵉ) =
    is-meet-semilattice-poset-Large-Meet-Semilatticeᵉ

  meet-semilattice-Large-Meet-Semilatticeᵉ :
    (lᵉ : Level) → Meet-Semilatticeᵉ (αᵉ lᵉ)
  meet-semilattice-Large-Meet-Semilatticeᵉ lᵉ =
    meet-semilattice-Order-Theoretic-Meet-Semilatticeᵉ
      ( order-theoretic-meet-semilattice-Large-Meet-Semilatticeᵉ lᵉ)
```