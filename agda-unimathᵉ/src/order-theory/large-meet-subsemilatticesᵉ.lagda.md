# Large meet-subsemilattices

```agda
module order-theory.large-meet-subsemilatticesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.large-binary-relationsᵉ
open import foundation.universe-levelsᵉ

open import order-theory.greatest-lower-bounds-large-posetsᵉ
open import order-theory.large-meet-semilatticesᵉ
open import order-theory.large-posetsᵉ
open import order-theory.large-preordersᵉ
open import order-theory.large-subposetsᵉ
open import order-theory.top-elements-large-posetsᵉ
```

</details>

## Idea

Aᵉ **largeᵉ meet-subsemilattice**ᵉ ofᵉ aᵉ
[largeᵉ meet-semilattice](order-theory.large-meet-semilattices.mdᵉ) `L`ᵉ isᵉ aᵉ
[largeᵉ subposet](order-theory.large-subposets.mdᵉ) `S`ᵉ ofᵉ `L`ᵉ thatᵉ isᵉ closedᵉ
underᵉ meetsᵉ andᵉ containsᵉ theᵉ topᵉ element.ᵉ

## Definitions

### The predicate that a large subposet is closed under meets

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level} {γᵉ : Level → Level}
  (Lᵉ : Large-Meet-Semilatticeᵉ αᵉ βᵉ)
  (Sᵉ : Large-Subposetᵉ γᵉ (large-poset-Large-Meet-Semilatticeᵉ Lᵉ))
  where

  is-closed-under-meets-Large-Subposetᵉ : UUωᵉ
  is-closed-under-meets-Large-Subposetᵉ =
    {l1ᵉ l2ᵉ : Level}
    (xᵉ : type-Large-Meet-Semilatticeᵉ Lᵉ l1ᵉ)
    (yᵉ : type-Large-Meet-Semilatticeᵉ Lᵉ l2ᵉ) →
    is-in-Large-Subposetᵉ (large-poset-Large-Meet-Semilatticeᵉ Lᵉ) Sᵉ xᵉ →
    is-in-Large-Subposetᵉ (large-poset-Large-Meet-Semilatticeᵉ Lᵉ) Sᵉ yᵉ →
    is-in-Large-Subposetᵉ
      ( large-poset-Large-Meet-Semilatticeᵉ Lᵉ)
      ( Sᵉ)
      ( meet-Large-Meet-Semilatticeᵉ Lᵉ xᵉ yᵉ)
```

### The predicate that a large subposet contains the top element

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level} {γᵉ : Level → Level}
  (Lᵉ : Large-Meet-Semilatticeᵉ αᵉ βᵉ)
  (Sᵉ : Large-Subposetᵉ γᵉ (large-poset-Large-Meet-Semilatticeᵉ Lᵉ))
  where

  contains-top-Large-Subposetᵉ : UUᵉ (γᵉ lzero)
  contains-top-Large-Subposetᵉ =
    is-in-Large-Subposetᵉ
      ( large-poset-Large-Meet-Semilatticeᵉ Lᵉ)
      ( Sᵉ)
      ( top-Large-Meet-Semilatticeᵉ Lᵉ)
```

### The predicate that a large subposet is a large meet-subsemilattice

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level} {γᵉ : Level → Level}
  (Lᵉ : Large-Meet-Semilatticeᵉ αᵉ βᵉ)
  (Sᵉ : Large-Subposetᵉ γᵉ (large-poset-Large-Meet-Semilatticeᵉ Lᵉ))
  where

  record
    is-large-meet-subsemilattice-Large-Subposetᵉ : UUωᵉ
    where
    field
      is-closed-under-meets-is-large-meet-subsemilattice-Large-Subposetᵉ :
        is-closed-under-meets-Large-Subposetᵉ Lᵉ Sᵉ
      contains-top-is-large-meet-subsemilattice-Large-Posetᵉ :
        contains-top-Large-Subposetᵉ Lᵉ Sᵉ

  open is-large-meet-subsemilattice-Large-Subposetᵉ public
```

### Large meet-subsemilattices

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level} (γᵉ : Level → Level)
  (Lᵉ : Large-Meet-Semilatticeᵉ αᵉ βᵉ)
  where

  record
    Large-Meet-Subsemilatticeᵉ : UUωᵉ
    where
    field
      large-subposet-Large-Meet-Subsemilatticeᵉ :
        Large-Subposetᵉ γᵉ (large-poset-Large-Meet-Semilatticeᵉ Lᵉ)
      is-closed-under-meets-Large-Meet-Subsemilatticeᵉ :
        is-closed-under-meets-Large-Subposetᵉ Lᵉ
          ( large-subposet-Large-Meet-Subsemilatticeᵉ)
      contains-top-Large-Meet-Subsemilatticeᵉ :
        contains-top-Large-Subposetᵉ Lᵉ
          ( large-subposet-Large-Meet-Subsemilatticeᵉ)

  open Large-Meet-Subsemilatticeᵉ public

module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level} {γᵉ : Level → Level}
  (Lᵉ : Large-Meet-Semilatticeᵉ αᵉ βᵉ)
  (Sᵉ : Large-Meet-Subsemilatticeᵉ γᵉ Lᵉ)
  where

  large-poset-Large-Meet-Subsemilatticeᵉ :
    Large-Posetᵉ (λ lᵉ → αᵉ lᵉ ⊔ γᵉ lᵉ) βᵉ
  large-poset-Large-Meet-Subsemilatticeᵉ =
    large-poset-Large-Subposetᵉ
      ( large-poset-Large-Meet-Semilatticeᵉ Lᵉ)
      ( large-subposet-Large-Meet-Subsemilatticeᵉ Sᵉ)

  large-preorder-Large-Meet-Subsemilatticeᵉ :
    Large-Preorderᵉ (λ lᵉ → αᵉ lᵉ ⊔ γᵉ lᵉ) (λ l1ᵉ l2ᵉ → βᵉ l1ᵉ l2ᵉ)
  large-preorder-Large-Meet-Subsemilatticeᵉ =
    large-preorder-Large-Subposetᵉ
      ( large-poset-Large-Meet-Semilatticeᵉ Lᵉ)
      ( large-subposet-Large-Meet-Subsemilatticeᵉ Sᵉ)

  is-in-Large-Meet-Subsemilatticeᵉ :
    {l1ᵉ : Level} → type-Large-Meet-Semilatticeᵉ Lᵉ l1ᵉ → UUᵉ (γᵉ l1ᵉ)
  is-in-Large-Meet-Subsemilatticeᵉ =
    is-in-Large-Subposetᵉ
      ( large-poset-Large-Meet-Semilatticeᵉ Lᵉ)
      ( large-subposet-Large-Meet-Subsemilatticeᵉ Sᵉ)

  type-Large-Meet-Subsemilatticeᵉ : (l1ᵉ : Level) → UUᵉ (αᵉ l1ᵉ ⊔ γᵉ l1ᵉ)
  type-Large-Meet-Subsemilatticeᵉ =
    type-Large-Subposetᵉ
      ( large-poset-Large-Meet-Semilatticeᵉ Lᵉ)
      ( large-subposet-Large-Meet-Subsemilatticeᵉ Sᵉ)

  leq-prop-Large-Meet-Subsemilatticeᵉ :
    Large-Relation-Propᵉ βᵉ type-Large-Meet-Subsemilatticeᵉ
  leq-prop-Large-Meet-Subsemilatticeᵉ =
    leq-prop-Large-Subposetᵉ
      ( large-poset-Large-Meet-Semilatticeᵉ Lᵉ)
      ( large-subposet-Large-Meet-Subsemilatticeᵉ Sᵉ)

  leq-Large-Meet-Subsemilatticeᵉ :
    Large-Relationᵉ βᵉ type-Large-Meet-Subsemilatticeᵉ
  leq-Large-Meet-Subsemilatticeᵉ =
    leq-Large-Subposetᵉ
      ( large-poset-Large-Meet-Semilatticeᵉ Lᵉ)
      ( large-subposet-Large-Meet-Subsemilatticeᵉ Sᵉ)

  is-prop-leq-Large-Meet-Subsemilatticeᵉ :
    is-prop-Large-Relationᵉ
      ( type-Large-Meet-Subsemilatticeᵉ)
      ( leq-Large-Meet-Subsemilatticeᵉ)
  is-prop-leq-Large-Meet-Subsemilatticeᵉ =
    is-prop-leq-Large-Subposetᵉ
      ( large-poset-Large-Meet-Semilatticeᵉ Lᵉ)
      ( large-subposet-Large-Meet-Subsemilatticeᵉ Sᵉ)

  refl-leq-Large-Meet-Subsemilatticeᵉ :
    is-reflexive-Large-Relationᵉ
      ( type-Large-Meet-Subsemilatticeᵉ)
      ( leq-Large-Meet-Subsemilatticeᵉ)
  refl-leq-Large-Meet-Subsemilatticeᵉ =
    refl-leq-Large-Subposetᵉ
      ( large-poset-Large-Meet-Semilatticeᵉ Lᵉ)
      ( large-subposet-Large-Meet-Subsemilatticeᵉ Sᵉ)

  transitive-leq-Large-Meet-Subsemilatticeᵉ :
    is-transitive-Large-Relationᵉ
      ( type-Large-Meet-Subsemilatticeᵉ)
      ( leq-Large-Meet-Subsemilatticeᵉ)
  transitive-leq-Large-Meet-Subsemilatticeᵉ =
    transitive-leq-Large-Subposetᵉ
      ( large-poset-Large-Meet-Semilatticeᵉ Lᵉ)
      ( large-subposet-Large-Meet-Subsemilatticeᵉ Sᵉ)

  antisymmetric-leq-Large-Meet-Subsemilatticeᵉ :
    is-antisymmetric-Large-Relationᵉ
      ( type-Large-Meet-Subsemilatticeᵉ)
      ( leq-Large-Meet-Subsemilatticeᵉ)
  antisymmetric-leq-Large-Meet-Subsemilatticeᵉ =
    antisymmetric-leq-Large-Subposetᵉ
      ( large-poset-Large-Meet-Semilatticeᵉ Lᵉ)
      ( large-subposet-Large-Meet-Subsemilatticeᵉ Sᵉ)

  is-closed-under-sim-Large-Meet-Subsemilatticeᵉ :
    {l1ᵉ l2ᵉ : Level}
    (xᵉ : type-Large-Meet-Semilatticeᵉ Lᵉ l1ᵉ)
    (yᵉ : type-Large-Meet-Semilatticeᵉ Lᵉ l2ᵉ) →
    leq-Large-Meet-Semilatticeᵉ Lᵉ xᵉ yᵉ →
    leq-Large-Meet-Semilatticeᵉ Lᵉ yᵉ xᵉ →
    is-in-Large-Meet-Subsemilatticeᵉ xᵉ →
    is-in-Large-Meet-Subsemilatticeᵉ yᵉ
  is-closed-under-sim-Large-Meet-Subsemilatticeᵉ =
    is-closed-under-sim-Large-Subposetᵉ
      ( large-subposet-Large-Meet-Subsemilatticeᵉ Sᵉ)

  meet-Large-Meet-Subsemilatticeᵉ :
    {l1ᵉ l2ᵉ : Level}
    (xᵉ : type-Large-Meet-Subsemilatticeᵉ l1ᵉ)
    (yᵉ : type-Large-Meet-Subsemilatticeᵉ l2ᵉ) →
    type-Large-Meet-Subsemilatticeᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ (meet-Large-Meet-Subsemilatticeᵉ (xᵉ ,ᵉ pᵉ) (yᵉ ,ᵉ qᵉ)) =
    meet-Large-Meet-Semilatticeᵉ Lᵉ xᵉ yᵉ
  pr2ᵉ (meet-Large-Meet-Subsemilatticeᵉ (xᵉ ,ᵉ pᵉ) (yᵉ ,ᵉ qᵉ)) =
    is-closed-under-meets-Large-Meet-Subsemilatticeᵉ Sᵉ xᵉ yᵉ pᵉ qᵉ

  is-greatest-binary-lower-bound-meet-Large-Meet-Subsemilatticeᵉ :
    {l1ᵉ l2ᵉ : Level}
    (xᵉ : type-Large-Meet-Subsemilatticeᵉ l1ᵉ)
    (yᵉ : type-Large-Meet-Subsemilatticeᵉ l2ᵉ) →
    is-greatest-binary-lower-bound-Large-Posetᵉ
      ( large-poset-Large-Meet-Subsemilatticeᵉ)
      ( xᵉ)
      ( yᵉ)
      ( meet-Large-Meet-Subsemilatticeᵉ xᵉ yᵉ)
  is-greatest-binary-lower-bound-meet-Large-Meet-Subsemilatticeᵉ
    (xᵉ ,ᵉ pᵉ) (yᵉ ,ᵉ qᵉ) (zᵉ ,ᵉ rᵉ) =
    is-greatest-binary-lower-bound-meet-Large-Meet-Semilatticeᵉ Lᵉ xᵉ yᵉ zᵉ

  has-meets-Large-Meet-Subsemilatticeᵉ :
    has-meets-Large-Posetᵉ
      ( large-poset-Large-Meet-Subsemilatticeᵉ)
  meet-has-meets-Large-Posetᵉ
    has-meets-Large-Meet-Subsemilatticeᵉ =
    meet-Large-Meet-Subsemilatticeᵉ
  is-greatest-binary-lower-bound-meet-has-meets-Large-Posetᵉ
    has-meets-Large-Meet-Subsemilatticeᵉ =
    is-greatest-binary-lower-bound-meet-Large-Meet-Subsemilatticeᵉ

  top-Large-Meet-Subsemilatticeᵉ :
    type-Large-Meet-Subsemilatticeᵉ lzero
  pr1ᵉ top-Large-Meet-Subsemilatticeᵉ = top-Large-Meet-Semilatticeᵉ Lᵉ
  pr2ᵉ top-Large-Meet-Subsemilatticeᵉ = contains-top-Large-Meet-Subsemilatticeᵉ Sᵉ

  is-top-element-top-Large-Meet-Subsemilatticeᵉ :
    {l1ᵉ : Level} (xᵉ : type-Large-Meet-Subsemilatticeᵉ l1ᵉ) →
    leq-Large-Meet-Subsemilatticeᵉ xᵉ top-Large-Meet-Subsemilatticeᵉ
  is-top-element-top-Large-Meet-Subsemilatticeᵉ (xᵉ ,ᵉ pᵉ) =
    is-top-element-top-Large-Meet-Semilatticeᵉ Lᵉ xᵉ

  has-top-element-Large-Meet-Subsemilatticeᵉ :
    has-top-element-Large-Posetᵉ
      ( large-poset-Large-Meet-Subsemilatticeᵉ)
  top-has-top-element-Large-Posetᵉ
    has-top-element-Large-Meet-Subsemilatticeᵉ =
    top-Large-Meet-Subsemilatticeᵉ
  is-top-element-top-has-top-element-Large-Posetᵉ
    has-top-element-Large-Meet-Subsemilatticeᵉ =
    is-top-element-top-Large-Meet-Subsemilatticeᵉ

  is-large-meet-semilattice-Large-Meet-Subsemilatticeᵉ :
    is-large-meet-semilattice-Large-Posetᵉ
      ( large-poset-Large-Meet-Subsemilatticeᵉ)
  has-meets-is-large-meet-semilattice-Large-Posetᵉ
    is-large-meet-semilattice-Large-Meet-Subsemilatticeᵉ =
    has-meets-Large-Meet-Subsemilatticeᵉ
  has-top-element-is-large-meet-semilattice-Large-Posetᵉ
    is-large-meet-semilattice-Large-Meet-Subsemilatticeᵉ =
    has-top-element-Large-Meet-Subsemilatticeᵉ

  large-meet-semilattice-Large-Meet-Subsemilatticeᵉ :
    Large-Meet-Semilatticeᵉ (λ lᵉ → αᵉ lᵉ ⊔ γᵉ lᵉ) βᵉ
  large-poset-Large-Meet-Semilatticeᵉ
    large-meet-semilattice-Large-Meet-Subsemilatticeᵉ =
    large-poset-Large-Meet-Subsemilatticeᵉ
  is-large-meet-semilattice-Large-Meet-Semilatticeᵉ
    large-meet-semilattice-Large-Meet-Subsemilatticeᵉ =
    is-large-meet-semilattice-Large-Meet-Subsemilatticeᵉ
```