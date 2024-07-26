# Dependent products of large meet-semilattices

```agda
module order-theory.dependent-products-large-meet-semilatticesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.large-binary-relationsᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ

open import order-theory.dependent-products-large-posetsᵉ
open import order-theory.greatest-lower-bounds-large-posetsᵉ
open import order-theory.large-meet-semilatticesᵉ
open import order-theory.large-posetsᵉ
open import order-theory.top-elements-large-posetsᵉ
```

</details>

## Idea

Meetsᵉ in dependentᵉ productsᵉ ofᵉ largeᵉ posetsᵉ areᵉ computedᵉ pointwise.ᵉ Thisᵉ impliesᵉ
thatᵉ theᵉ dependentᵉ productᵉ ofᵉ aᵉ largeᵉ meet-semilatticeᵉ isᵉ againᵉ aᵉ largeᵉ
meet-semilattice.ᵉ

## Definitions

### Meets in dependent products of large posets that have meets

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  {lᵉ : Level} {Iᵉ : UUᵉ lᵉ} (Pᵉ : Iᵉ → Large-Posetᵉ αᵉ βᵉ)
  where

  has-meets-Π-Large-Posetᵉ :
    ((iᵉ : Iᵉ) → has-meets-Large-Posetᵉ (Pᵉ iᵉ)) →
    has-meets-Large-Posetᵉ (Π-Large-Posetᵉ Pᵉ)
  meet-has-meets-Large-Posetᵉ (has-meets-Π-Large-Posetᵉ Hᵉ) xᵉ yᵉ iᵉ =
    meet-has-meets-Large-Posetᵉ (Hᵉ iᵉ) (xᵉ iᵉ) (yᵉ iᵉ)
  is-greatest-binary-lower-bound-meet-has-meets-Large-Posetᵉ
    ( has-meets-Π-Large-Posetᵉ Hᵉ) xᵉ yᵉ =
    is-greatest-binary-lower-bound-Π-Large-Posetᵉ Pᵉ xᵉ yᵉ
      ( λ iᵉ → meet-has-meets-Large-Posetᵉ (Hᵉ iᵉ) (xᵉ iᵉ) (yᵉ iᵉ))
      ( λ iᵉ →
        is-greatest-binary-lower-bound-meet-has-meets-Large-Posetᵉ
          ( Hᵉ iᵉ)
          ( xᵉ iᵉ)
          ( yᵉ iᵉ))
```

### Large meet-semilattices

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  {lᵉ : Level} {Iᵉ : UUᵉ lᵉ} (Lᵉ : Iᵉ → Large-Meet-Semilatticeᵉ αᵉ βᵉ)
  where

  large-poset-Π-Large-Meet-Semilatticeᵉ :
    Large-Posetᵉ (λ l1ᵉ → αᵉ l1ᵉ ⊔ lᵉ) (λ l1ᵉ l2ᵉ → βᵉ l1ᵉ l2ᵉ ⊔ lᵉ)
  large-poset-Π-Large-Meet-Semilatticeᵉ =
    Π-Large-Posetᵉ (λ iᵉ → large-poset-Large-Meet-Semilatticeᵉ (Lᵉ iᵉ))

  has-meets-Π-Large-Meet-Semilatticeᵉ :
    has-meets-Large-Posetᵉ large-poset-Π-Large-Meet-Semilatticeᵉ
  has-meets-Π-Large-Meet-Semilatticeᵉ =
    has-meets-Π-Large-Posetᵉ
      ( λ iᵉ → large-poset-Large-Meet-Semilatticeᵉ (Lᵉ iᵉ))
      ( λ iᵉ → has-meets-Large-Meet-Semilatticeᵉ (Lᵉ iᵉ))

  has-top-element-Π-Large-Meet-Semilatticeᵉ :
    has-top-element-Large-Posetᵉ large-poset-Π-Large-Meet-Semilatticeᵉ
  has-top-element-Π-Large-Meet-Semilatticeᵉ =
    has-top-element-Π-Large-Posetᵉ
      ( λ iᵉ → large-poset-Large-Meet-Semilatticeᵉ (Lᵉ iᵉ))
      ( λ iᵉ → has-top-element-Large-Meet-Semilatticeᵉ (Lᵉ iᵉ))

  is-large-meet-semilattice-Π-Large-Meet-Semilatticeᵉ :
    is-large-meet-semilattice-Large-Posetᵉ
      large-poset-Π-Large-Meet-Semilatticeᵉ
  has-meets-is-large-meet-semilattice-Large-Posetᵉ
    is-large-meet-semilattice-Π-Large-Meet-Semilatticeᵉ =
    has-meets-Π-Large-Meet-Semilatticeᵉ
  has-top-element-is-large-meet-semilattice-Large-Posetᵉ
    is-large-meet-semilattice-Π-Large-Meet-Semilatticeᵉ =
    has-top-element-Π-Large-Meet-Semilatticeᵉ

  Π-Large-Meet-Semilatticeᵉ :
    Large-Meet-Semilatticeᵉ (λ l1ᵉ → αᵉ l1ᵉ ⊔ lᵉ) (λ l1ᵉ l2ᵉ → βᵉ l1ᵉ l2ᵉ ⊔ lᵉ)
  large-poset-Large-Meet-Semilatticeᵉ Π-Large-Meet-Semilatticeᵉ =
    large-poset-Π-Large-Meet-Semilatticeᵉ
  is-large-meet-semilattice-Large-Meet-Semilatticeᵉ Π-Large-Meet-Semilatticeᵉ =
    is-large-meet-semilattice-Π-Large-Meet-Semilatticeᵉ

  type-Π-Large-Meet-Semilatticeᵉ : (l1ᵉ : Level) → UUᵉ (αᵉ l1ᵉ ⊔ lᵉ)
  type-Π-Large-Meet-Semilatticeᵉ =
    type-Large-Meet-Semilatticeᵉ Π-Large-Meet-Semilatticeᵉ

  set-Π-Large-Meet-Semilatticeᵉ : (l1ᵉ : Level) → Setᵉ (αᵉ l1ᵉ ⊔ lᵉ)
  set-Π-Large-Meet-Semilatticeᵉ =
    set-Large-Meet-Semilatticeᵉ Π-Large-Meet-Semilatticeᵉ

  is-set-type-Π-Large-Meet-Semilatticeᵉ :
    {lᵉ : Level} → is-setᵉ (type-Π-Large-Meet-Semilatticeᵉ lᵉ)
  is-set-type-Π-Large-Meet-Semilatticeᵉ =
    is-set-type-Large-Meet-Semilatticeᵉ Π-Large-Meet-Semilatticeᵉ

  leq-Π-Large-Meet-Semilatticeᵉ :
    Large-Relationᵉ
      ( λ l1ᵉ l2ᵉ → βᵉ l1ᵉ l2ᵉ ⊔ lᵉ)
      ( type-Π-Large-Meet-Semilatticeᵉ)
  leq-Π-Large-Meet-Semilatticeᵉ =
    leq-Large-Meet-Semilatticeᵉ Π-Large-Meet-Semilatticeᵉ

  refl-leq-Π-Large-Meet-Semilatticeᵉ :
    is-reflexive-Large-Relationᵉ
      ( type-Π-Large-Meet-Semilatticeᵉ)
      ( leq-Π-Large-Meet-Semilatticeᵉ)
  refl-leq-Π-Large-Meet-Semilatticeᵉ =
    refl-leq-Large-Meet-Semilatticeᵉ Π-Large-Meet-Semilatticeᵉ

  antisymmetric-leq-Π-Large-Meet-Semilatticeᵉ :
    is-antisymmetric-Large-Relationᵉ
      ( type-Π-Large-Meet-Semilatticeᵉ)
      ( leq-Π-Large-Meet-Semilatticeᵉ)
  antisymmetric-leq-Π-Large-Meet-Semilatticeᵉ =
    antisymmetric-leq-Large-Meet-Semilatticeᵉ Π-Large-Meet-Semilatticeᵉ

  transitive-leq-Π-Large-Meet-Semilatticeᵉ :
    is-transitive-Large-Relationᵉ
      ( type-Π-Large-Meet-Semilatticeᵉ)
      ( leq-Π-Large-Meet-Semilatticeᵉ)
  transitive-leq-Π-Large-Meet-Semilatticeᵉ =
    transitive-leq-Large-Meet-Semilatticeᵉ Π-Large-Meet-Semilatticeᵉ

  meet-Π-Large-Meet-Semilatticeᵉ :
    {l1ᵉ l2ᵉ : Level}
    (xᵉ : type-Π-Large-Meet-Semilatticeᵉ l1ᵉ)
    (yᵉ : type-Π-Large-Meet-Semilatticeᵉ l2ᵉ) →
    type-Π-Large-Meet-Semilatticeᵉ (l1ᵉ ⊔ l2ᵉ)
  meet-Π-Large-Meet-Semilatticeᵉ =
    meet-Large-Meet-Semilatticeᵉ Π-Large-Meet-Semilatticeᵉ

  is-greatest-binary-lower-bound-meet-Π-Large-Meet-Semilatticeᵉ :
    {l1ᵉ l2ᵉ : Level}
    (xᵉ : type-Π-Large-Meet-Semilatticeᵉ l1ᵉ)
    (yᵉ : type-Π-Large-Meet-Semilatticeᵉ l2ᵉ) →
    is-greatest-binary-lower-bound-Large-Posetᵉ
      ( large-poset-Π-Large-Meet-Semilatticeᵉ)
      ( xᵉ)
      ( yᵉ)
      ( meet-Π-Large-Meet-Semilatticeᵉ xᵉ yᵉ)
  is-greatest-binary-lower-bound-meet-Π-Large-Meet-Semilatticeᵉ =
    is-greatest-binary-lower-bound-meet-Large-Meet-Semilatticeᵉ
      Π-Large-Meet-Semilatticeᵉ

  top-Π-Large-Meet-Semilatticeᵉ :
    type-Π-Large-Meet-Semilatticeᵉ lzero
  top-Π-Large-Meet-Semilatticeᵉ =
    top-has-top-element-Large-Posetᵉ
      has-top-element-Π-Large-Meet-Semilatticeᵉ

  is-top-element-top-Π-Large-Meet-Semilatticeᵉ :
    {l1ᵉ : Level} (xᵉ : type-Π-Large-Meet-Semilatticeᵉ l1ᵉ) →
    leq-Π-Large-Meet-Semilatticeᵉ xᵉ top-Π-Large-Meet-Semilatticeᵉ
  is-top-element-top-Π-Large-Meet-Semilatticeᵉ =
    is-top-element-top-has-top-element-Large-Posetᵉ
      has-top-element-Π-Large-Meet-Semilatticeᵉ
```