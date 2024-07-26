# Frames

```agda
module order-theory.framesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relationsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ

open import order-theory.greatest-lower-bounds-posetsᵉ
open import order-theory.least-upper-bounds-posetsᵉ
open import order-theory.meet-semilatticesᵉ
open import order-theory.meet-suplatticesᵉ
open import order-theory.posetsᵉ
open import order-theory.suplatticesᵉ
```

</details>

## Idea

Aᵉ **frame**ᵉ isᵉ aᵉ [meet-suplattice](order-theory.meet-suplattices.mdᵉ) with
arbitraryᵉ joinsᵉ in whichᵉ meetsᵉ distributeᵉ overᵉ suprema.ᵉ Theᵉ **distributiveᵉ lawᵉ
forᵉ meetsᵉ overᵉ suprema**ᵉ statesᵉ thatᵉ in anyᵉ
[meet-suplattice](order-theory.meet-suplattices.mdᵉ) `A`,ᵉ weᵉ haveᵉ

```text
  xᵉ ∧ᵉ (⋁ᵢᵉ yᵢᵉ) ＝ᵉ ⋁ᵢᵉ (xᵉ ∧ᵉ yᵢᵉ)
```

forᵉ everyᵉ elementᵉ `xᵉ : A`ᵉ andᵉ anyᵉ familyᵉ `yᵉ : Iᵉ → A`.ᵉ

## Definitions

### Statement of (instances of) the infinite distributive law

#### In posets

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Pᵉ : Posetᵉ l1ᵉ l2ᵉ)
  where

  module _
    {Iᵉ : UUᵉ l3ᵉ} {xᵉ : type-Posetᵉ Pᵉ} {yᵉ : Iᵉ → type-Posetᵉ Pᵉ}
    (Hᵉ : has-least-upper-bound-family-of-elements-Posetᵉ Pᵉ yᵉ)
    (Kᵉ : has-greatest-binary-lower-bound-Posetᵉ Pᵉ xᵉ (pr1ᵉ Hᵉ))
    (Lᵉ : (iᵉ : Iᵉ) → has-greatest-binary-lower-bound-Posetᵉ Pᵉ xᵉ (yᵉ iᵉ))
    (Mᵉ : has-least-upper-bound-family-of-elements-Posetᵉ Pᵉ (λ iᵉ → (pr1ᵉ (Lᵉ iᵉ))))
    where

    instance-distributive-law-meet-sup-Poset-Propᵉ : Propᵉ l1ᵉ
    instance-distributive-law-meet-sup-Poset-Propᵉ =
      Id-Propᵉ (set-Posetᵉ Pᵉ) (pr1ᵉ Kᵉ) (pr1ᵉ Mᵉ)

    instance-distributive-law-meet-sup-Posetᵉ : UUᵉ l1ᵉ
    instance-distributive-law-meet-sup-Posetᵉ =
      type-Propᵉ instance-distributive-law-meet-sup-Poset-Propᵉ

    is-prop-instance-distributive-law-meet-sup-Posetᵉ :
      is-propᵉ instance-distributive-law-meet-sup-Posetᵉ
    is-prop-instance-distributive-law-meet-sup-Posetᵉ =
      is-prop-type-Propᵉ instance-distributive-law-meet-sup-Poset-Propᵉ

  module _
    ( Hᵉ : is-meet-semilattice-Posetᵉ Pᵉ)
    ( Kᵉ : is-suplattice-Posetᵉ l3ᵉ Pᵉ)
    where

    distributive-law-meet-sup-Poset-Propᵉ : Propᵉ (l1ᵉ ⊔ lsuc l3ᵉ)
    distributive-law-meet-sup-Poset-Propᵉ =
      Π-Propᵉ
        ( type-Posetᵉ Pᵉ)
        ( λ xᵉ →
          implicit-Π-Propᵉ
            ( UUᵉ l3ᵉ)
            ( λ Iᵉ →
              Π-Propᵉ
                ( Iᵉ → type-Posetᵉ Pᵉ)
                ( λ yᵉ →
                  instance-distributive-law-meet-sup-Poset-Propᵉ {Iᵉ} {xᵉ} {yᵉ}
                    ( Kᵉ Iᵉ yᵉ)
                    ( Hᵉ xᵉ (pr1ᵉ (Kᵉ Iᵉ yᵉ)))
                    ( λ iᵉ → Hᵉ xᵉ (yᵉ iᵉ))
                    ( Kᵉ Iᵉ (λ iᵉ → pr1ᵉ (Hᵉ xᵉ (yᵉ iᵉ)))))))

    distributive-law-meet-sup-Posetᵉ : UUᵉ (l1ᵉ ⊔ lsuc l3ᵉ)
    distributive-law-meet-sup-Posetᵉ =
      type-Propᵉ distributive-law-meet-sup-Poset-Propᵉ

    is-prop-distributive-law-meet-sup-Posetᵉ :
      is-propᵉ distributive-law-meet-sup-Posetᵉ
    is-prop-distributive-law-meet-sup-Posetᵉ =
      is-prop-type-Propᵉ distributive-law-meet-sup-Poset-Propᵉ
```

#### In meet-semilattices

```agda
instance-distributive-law-meet-sup-Meet-Semilatticeᵉ :
  {l1ᵉ l2ᵉ : Level} (Lᵉ : Meet-Semilatticeᵉ l1ᵉ) {Iᵉ : UUᵉ l2ᵉ}
  ( xᵉ : type-Meet-Semilatticeᵉ Lᵉ)
  { yᵉ : Iᵉ → type-Meet-Semilatticeᵉ Lᵉ} →
  ( Hᵉ :
    has-least-upper-bound-family-of-elements-Posetᵉ
      ( poset-Meet-Semilatticeᵉ Lᵉ)
      ( yᵉ))
  ( Kᵉ :
    has-least-upper-bound-family-of-elements-Posetᵉ
      ( poset-Meet-Semilatticeᵉ Lᵉ)
      ( λ iᵉ → meet-Meet-Semilatticeᵉ Lᵉ xᵉ (yᵉ iᵉ))) →
  UUᵉ l1ᵉ
instance-distributive-law-meet-sup-Meet-Semilatticeᵉ Lᵉ xᵉ {yᵉ} Hᵉ =
  instance-distributive-law-meet-sup-Posetᵉ
    ( poset-Meet-Semilatticeᵉ Lᵉ)
    ( Hᵉ)
    ( has-greatest-binary-lower-bound-Meet-Semilatticeᵉ Lᵉ xᵉ (pr1ᵉ Hᵉ))
    ( λ iᵉ → has-greatest-binary-lower-bound-Meet-Semilatticeᵉ Lᵉ xᵉ (yᵉ iᵉ))
```

#### Statement of the distributive law in meet-suplattices

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Lᵉ : Meet-Suplatticeᵉ l1ᵉ l2ᵉ)
  where

  private
    _∧ᵉ_ = meet-Meet-Suplatticeᵉ Lᵉ
    ⋁ᵉ_ = sup-Meet-Suplatticeᵉ Lᵉ

  distributive-law-Meet-Suplattice-Propᵉ : Propᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
  distributive-law-Meet-Suplattice-Propᵉ =
    Π-Propᵉ
      ( type-Meet-Suplatticeᵉ Lᵉ)
      ( λ xᵉ →
        implicit-Π-Propᵉ
          ( UUᵉ l2ᵉ)
          ( λ Iᵉ →
            Π-Propᵉ
              ( Iᵉ → type-Meet-Suplatticeᵉ Lᵉ)
              ( λ yᵉ →
                Id-Propᵉ
                  ( set-Meet-Suplatticeᵉ Lᵉ)
                  ( xᵉ ∧ᵉ (⋁ᵉ yᵉ))
                  ( ⋁ᵉ (λ iᵉ → (xᵉ ∧ᵉ (yᵉ iᵉ)))))))

  distributive-law-Meet-Suplatticeᵉ : UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
  distributive-law-Meet-Suplatticeᵉ =
    type-Propᵉ distributive-law-Meet-Suplattice-Propᵉ

  is-prop-distributive-law-Meet-Suplatticeᵉ :
    is-propᵉ distributive-law-Meet-Suplatticeᵉ
  is-prop-distributive-law-Meet-Suplatticeᵉ =
    is-prop-type-Propᵉ distributive-law-Meet-Suplattice-Propᵉ
```

### The predicate on meet-suplattices to be a frame

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Lᵉ : Meet-Suplatticeᵉ l1ᵉ l2ᵉ)
  where

  is-frame-Meet-Suplattice-Propᵉ : Propᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
  is-frame-Meet-Suplattice-Propᵉ = distributive-law-Meet-Suplattice-Propᵉ Lᵉ

  is-frame-Meet-Suplatticeᵉ : UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
  is-frame-Meet-Suplatticeᵉ = type-Propᵉ is-frame-Meet-Suplattice-Propᵉ

  is-prop-is-frame-Meet-Suplatticeᵉ : is-propᵉ is-frame-Meet-Suplatticeᵉ
  is-prop-is-frame-Meet-Suplatticeᵉ =
    is-prop-type-Propᵉ is-frame-Meet-Suplattice-Propᵉ
```

### Frames

```agda
Frameᵉ : (l1ᵉ l2ᵉ : Level) → UUᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ)
Frameᵉ l1ᵉ l2ᵉ = Σᵉ (Meet-Suplatticeᵉ l1ᵉ l2ᵉ) is-frame-Meet-Suplatticeᵉ

module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Frameᵉ l1ᵉ l2ᵉ)
  where

  meet-suplattice-Frameᵉ : Meet-Suplatticeᵉ l1ᵉ l2ᵉ
  meet-suplattice-Frameᵉ = pr1ᵉ Aᵉ

  meet-semilattice-Frameᵉ : Meet-Semilatticeᵉ l1ᵉ
  meet-semilattice-Frameᵉ =
    meet-semilattice-Meet-Suplatticeᵉ meet-suplattice-Frameᵉ

  suplattice-Frameᵉ : Suplatticeᵉ l1ᵉ l1ᵉ l2ᵉ
  suplattice-Frameᵉ = suplattice-Meet-Suplatticeᵉ meet-suplattice-Frameᵉ

  poset-Frameᵉ : Posetᵉ l1ᵉ l1ᵉ
  poset-Frameᵉ = poset-Meet-Suplatticeᵉ meet-suplattice-Frameᵉ

  set-Frameᵉ : Setᵉ l1ᵉ
  set-Frameᵉ = set-Posetᵉ poset-Frameᵉ

  type-Frameᵉ : UUᵉ l1ᵉ
  type-Frameᵉ = type-Posetᵉ poset-Frameᵉ

  is-set-type-Frameᵉ : is-setᵉ type-Frameᵉ
  is-set-type-Frameᵉ = is-set-type-Posetᵉ poset-Frameᵉ

  leq-Frame-Propᵉ : (xᵉ yᵉ : type-Frameᵉ) → Propᵉ l1ᵉ
  leq-Frame-Propᵉ = leq-Poset-Propᵉ poset-Frameᵉ

  leq-Frameᵉ : (xᵉ yᵉ : type-Frameᵉ) → UUᵉ l1ᵉ
  leq-Frameᵉ = leq-Posetᵉ poset-Frameᵉ

  is-prop-leq-Frameᵉ : (xᵉ yᵉ : type-Frameᵉ) → is-propᵉ (leq-Frameᵉ xᵉ yᵉ)
  is-prop-leq-Frameᵉ = is-prop-leq-Posetᵉ poset-Frameᵉ

  refl-leq-Frameᵉ : is-reflexiveᵉ leq-Frameᵉ
  refl-leq-Frameᵉ = refl-leq-Posetᵉ poset-Frameᵉ

  antisymmetric-leq-Frameᵉ : is-antisymmetricᵉ leq-Frameᵉ
  antisymmetric-leq-Frameᵉ = antisymmetric-leq-Posetᵉ poset-Frameᵉ

  transitive-leq-Frameᵉ : is-transitiveᵉ leq-Frameᵉ
  transitive-leq-Frameᵉ = transitive-leq-Posetᵉ poset-Frameᵉ

  meet-Frameᵉ : type-Frameᵉ → type-Frameᵉ → type-Frameᵉ
  meet-Frameᵉ = meet-Meet-Semilatticeᵉ meet-semilattice-Frameᵉ

  is-greatest-binary-lower-bound-meet-Frameᵉ :
    (xᵉ yᵉ : type-Frameᵉ) →
    is-greatest-binary-lower-bound-Posetᵉ poset-Frameᵉ xᵉ yᵉ (meet-Frameᵉ xᵉ yᵉ)
  is-greatest-binary-lower-bound-meet-Frameᵉ =
    is-greatest-binary-lower-bound-meet-Meet-Semilatticeᵉ meet-semilattice-Frameᵉ

  associative-meet-Frameᵉ :
    (xᵉ yᵉ zᵉ : type-Frameᵉ) →
    meet-Frameᵉ (meet-Frameᵉ xᵉ yᵉ) zᵉ ＝ᵉ meet-Frameᵉ xᵉ (meet-Frameᵉ yᵉ zᵉ)
  associative-meet-Frameᵉ =
    associative-meet-Meet-Semilatticeᵉ meet-semilattice-Frameᵉ

  commutative-meet-Frameᵉ :
    (xᵉ yᵉ : type-Frameᵉ) → meet-Frameᵉ xᵉ yᵉ ＝ᵉ meet-Frameᵉ yᵉ xᵉ
  commutative-meet-Frameᵉ =
    commutative-meet-Meet-Semilatticeᵉ meet-semilattice-Frameᵉ

  idempotent-meet-Frameᵉ :
    (xᵉ : type-Frameᵉ) → meet-Frameᵉ xᵉ xᵉ ＝ᵉ xᵉ
  idempotent-meet-Frameᵉ =
    idempotent-meet-Meet-Semilatticeᵉ meet-semilattice-Frameᵉ

  is-suplattice-Frameᵉ :
    is-suplattice-Posetᵉ l2ᵉ poset-Frameᵉ
  is-suplattice-Frameᵉ = is-suplattice-Suplatticeᵉ suplattice-Frameᵉ

  sup-Frameᵉ : {Iᵉ : UUᵉ l2ᵉ} → (Iᵉ → type-Frameᵉ) → type-Frameᵉ
  sup-Frameᵉ = sup-Suplatticeᵉ suplattice-Frameᵉ

  is-least-upper-bound-sup-Frameᵉ :
    {Iᵉ : UUᵉ l2ᵉ} (xᵉ : Iᵉ → type-Frameᵉ) →
    is-least-upper-bound-family-of-elements-Posetᵉ poset-Frameᵉ xᵉ (sup-Frameᵉ xᵉ)
  is-least-upper-bound-sup-Frameᵉ =
    is-least-upper-bound-sup-Suplatticeᵉ suplattice-Frameᵉ

  distributive-meet-sup-Frameᵉ :
    distributive-law-Meet-Suplatticeᵉ meet-suplattice-Frameᵉ
  distributive-meet-sup-Frameᵉ = pr2ᵉ Aᵉ
```