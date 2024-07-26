# Large frames

```agda
module order-theory.large-framesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.large-binary-relationsᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ

open import order-theory.greatest-lower-bounds-large-posetsᵉ
open import order-theory.large-meet-semilatticesᵉ
open import order-theory.large-posetsᵉ
open import order-theory.large-preordersᵉ
open import order-theory.large-suplatticesᵉ
open import order-theory.least-upper-bounds-large-posetsᵉ
open import order-theory.meet-semilatticesᵉ
open import order-theory.posetsᵉ
open import order-theory.preordersᵉ
open import order-theory.suplatticesᵉ
open import order-theory.top-elements-large-posetsᵉ
open import order-theory.upper-bounds-large-posetsᵉ
```

</details>

## Idea

Aᵉ **largeᵉ frame**ᵉ isᵉ aᵉ largeᵉ [meet-suplattice](order-theory.meet-suplattices.mdᵉ)
satisfyingᵉ theᵉ distributiveᵉ lawᵉ forᵉ meetsᵉ overᵉ suprema.ᵉ

## Definitions

### Large frames

```agda
record
  Large-Frameᵉ (αᵉ : Level → Level) (βᵉ : Level → Level → Level) (γᵉ : Level) : UUωᵉ
  where
  constructor
    make-Large-Frameᵉ
  field
    large-poset-Large-Frameᵉ :
      Large-Posetᵉ αᵉ βᵉ
    is-large-meet-semilattice-Large-Frameᵉ :
      is-large-meet-semilattice-Large-Posetᵉ large-poset-Large-Frameᵉ
    is-large-suplattice-Large-Frameᵉ :
      is-large-suplattice-Large-Posetᵉ γᵉ large-poset-Large-Frameᵉ
    distributive-meet-sup-Large-Frameᵉ :
      {l1ᵉ l2ᵉ l3ᵉ : Level}
      (xᵉ : type-Large-Posetᵉ large-poset-Large-Frameᵉ l1ᵉ)
      {Iᵉ : UUᵉ l2ᵉ} (yᵉ : Iᵉ → type-Large-Posetᵉ large-poset-Large-Frameᵉ l3ᵉ) →
      meet-is-large-meet-semilattice-Large-Posetᵉ
        ( large-poset-Large-Frameᵉ)
        ( is-large-meet-semilattice-Large-Frameᵉ)
        ( xᵉ)
        ( sup-has-least-upper-bound-family-of-elements-Large-Posetᵉ
          ( is-large-suplattice-Large-Frameᵉ yᵉ)) ＝ᵉ
      sup-has-least-upper-bound-family-of-elements-Large-Posetᵉ
        ( is-large-suplattice-Large-Frameᵉ
          ( λ iᵉ →
            meet-is-large-meet-semilattice-Large-Posetᵉ
              ( large-poset-Large-Frameᵉ)
              ( is-large-meet-semilattice-Large-Frameᵉ)
              ( xᵉ)
              ( yᵉ iᵉ)))

open Large-Frameᵉ public

module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level} {γᵉ : Level}
  (Lᵉ : Large-Frameᵉ αᵉ βᵉ γᵉ)
  where

  large-preorder-Large-Frameᵉ : Large-Preorderᵉ αᵉ βᵉ
  large-preorder-Large-Frameᵉ =
    large-preorder-Large-Posetᵉ (large-poset-Large-Frameᵉ Lᵉ)

  set-Large-Frameᵉ : (lᵉ : Level) → Setᵉ (αᵉ lᵉ)
  set-Large-Frameᵉ = set-Large-Posetᵉ (large-poset-Large-Frameᵉ Lᵉ)

  type-Large-Frameᵉ : (lᵉ : Level) → UUᵉ (αᵉ lᵉ)
  type-Large-Frameᵉ = type-Large-Posetᵉ (large-poset-Large-Frameᵉ Lᵉ)

  is-set-type-Large-Frameᵉ : {lᵉ : Level} → is-setᵉ (type-Large-Frameᵉ lᵉ)
  is-set-type-Large-Frameᵉ =
    is-set-type-Large-Posetᵉ (large-poset-Large-Frameᵉ Lᵉ)

  leq-prop-Large-Frameᵉ : Large-Relation-Propᵉ βᵉ type-Large-Frameᵉ
  leq-prop-Large-Frameᵉ = leq-prop-Large-Posetᵉ (large-poset-Large-Frameᵉ Lᵉ)

  leq-Large-Frameᵉ : Large-Relationᵉ βᵉ type-Large-Frameᵉ
  leq-Large-Frameᵉ = leq-Large-Posetᵉ (large-poset-Large-Frameᵉ Lᵉ)

  is-prop-leq-Large-Frameᵉ :
    is-prop-Large-Relationᵉ type-Large-Frameᵉ leq-Large-Frameᵉ
  is-prop-leq-Large-Frameᵉ =
    is-prop-leq-Large-Posetᵉ (large-poset-Large-Frameᵉ Lᵉ)

  leq-eq-Large-Frameᵉ :
    {l1ᵉ : Level} {xᵉ yᵉ : type-Large-Frameᵉ l1ᵉ} →
    (xᵉ ＝ᵉ yᵉ) → leq-Large-Frameᵉ xᵉ yᵉ
  leq-eq-Large-Frameᵉ =
    leq-eq-Large-Posetᵉ (large-poset-Large-Frameᵉ Lᵉ)

  refl-leq-Large-Frameᵉ :
    is-reflexive-Large-Relationᵉ type-Large-Frameᵉ leq-Large-Frameᵉ
  refl-leq-Large-Frameᵉ = refl-leq-Large-Posetᵉ (large-poset-Large-Frameᵉ Lᵉ)

  antisymmetric-leq-Large-Frameᵉ :
    is-antisymmetric-Large-Relationᵉ type-Large-Frameᵉ leq-Large-Frameᵉ
  antisymmetric-leq-Large-Frameᵉ =
    antisymmetric-leq-Large-Posetᵉ (large-poset-Large-Frameᵉ Lᵉ)

  transitive-leq-Large-Frameᵉ :
    is-transitive-Large-Relationᵉ type-Large-Frameᵉ leq-Large-Frameᵉ
  transitive-leq-Large-Frameᵉ =
    transitive-leq-Large-Posetᵉ (large-poset-Large-Frameᵉ Lᵉ)

  large-meet-semilattice-Large-Frameᵉ :
    Large-Meet-Semilatticeᵉ αᵉ βᵉ
  large-poset-Large-Meet-Semilatticeᵉ large-meet-semilattice-Large-Frameᵉ =
    large-poset-Large-Frameᵉ Lᵉ
  is-large-meet-semilattice-Large-Meet-Semilatticeᵉ
    large-meet-semilattice-Large-Frameᵉ =
    is-large-meet-semilattice-Large-Frameᵉ Lᵉ

  has-meets-Large-Frameᵉ :
    has-meets-Large-Posetᵉ (large-poset-Large-Frameᵉ Lᵉ)
  has-meets-Large-Frameᵉ =
    has-meets-Large-Meet-Semilatticeᵉ large-meet-semilattice-Large-Frameᵉ

  meet-Large-Frameᵉ :
    {l1ᵉ l2ᵉ : Level} →
    type-Large-Frameᵉ l1ᵉ → type-Large-Frameᵉ l2ᵉ → type-Large-Frameᵉ (l1ᵉ ⊔ l2ᵉ)
  meet-Large-Frameᵉ =
    meet-is-large-meet-semilattice-Large-Posetᵉ
      ( large-poset-Large-Frameᵉ Lᵉ)
      ( is-large-meet-semilattice-Large-Frameᵉ Lᵉ)

  is-greatest-binary-lower-bound-meet-Large-Frameᵉ :
    {l1ᵉ l2ᵉ : Level} →
    (xᵉ : type-Large-Frameᵉ l1ᵉ) (yᵉ : type-Large-Frameᵉ l2ᵉ) →
    is-greatest-binary-lower-bound-Large-Posetᵉ
      ( large-poset-Large-Frameᵉ Lᵉ)
      ( xᵉ)
      ( yᵉ)
      ( meet-Large-Frameᵉ xᵉ yᵉ)
  is-greatest-binary-lower-bound-meet-Large-Frameᵉ =
    is-greatest-binary-lower-bound-meet-is-large-meet-semilattice-Large-Posetᵉ
      ( large-poset-Large-Frameᵉ Lᵉ)
      ( is-large-meet-semilattice-Large-Frameᵉ Lᵉ)

  ap-meet-Large-Frameᵉ :
    {l1ᵉ l2ᵉ : Level}
    {xᵉ x'ᵉ : type-Large-Frameᵉ l1ᵉ} {yᵉ y'ᵉ : type-Large-Frameᵉ l2ᵉ} →
    (xᵉ ＝ᵉ x'ᵉ) → (yᵉ ＝ᵉ y'ᵉ) → (meet-Large-Frameᵉ xᵉ yᵉ ＝ᵉ meet-Large-Frameᵉ x'ᵉ y'ᵉ)
  ap-meet-Large-Frameᵉ =
    ap-meet-Large-Meet-Semilatticeᵉ large-meet-semilattice-Large-Frameᵉ

  has-top-element-Large-Frameᵉ :
    has-top-element-Large-Posetᵉ (large-poset-Large-Frameᵉ Lᵉ)
  has-top-element-Large-Frameᵉ =
    has-top-element-Large-Meet-Semilatticeᵉ
      large-meet-semilattice-Large-Frameᵉ

  top-Large-Frameᵉ : type-Large-Frameᵉ lzero
  top-Large-Frameᵉ =
    top-Large-Meet-Semilatticeᵉ large-meet-semilattice-Large-Frameᵉ

  is-top-element-top-Large-Frameᵉ :
    {l1ᵉ : Level} (xᵉ : type-Large-Frameᵉ l1ᵉ) →
    leq-Large-Frameᵉ xᵉ top-Large-Frameᵉ
  is-top-element-top-Large-Frameᵉ =
    is-top-element-top-Large-Meet-Semilatticeᵉ
      large-meet-semilattice-Large-Frameᵉ

  sup-Large-Frameᵉ :
    {l1ᵉ l2ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ} →
    (Iᵉ → type-Large-Frameᵉ l2ᵉ) → type-Large-Frameᵉ (γᵉ ⊔ l1ᵉ ⊔ l2ᵉ)
  sup-Large-Frameᵉ =
    sup-is-large-suplattice-Large-Posetᵉ γᵉ
      ( large-poset-Large-Frameᵉ Lᵉ)
      ( is-large-suplattice-Large-Frameᵉ Lᵉ)

  is-least-upper-bound-sup-Large-Frameᵉ :
    {l1ᵉ l2ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ} (xᵉ : Iᵉ → type-Large-Frameᵉ l2ᵉ) →
    is-least-upper-bound-family-of-elements-Large-Posetᵉ
      ( large-poset-Large-Frameᵉ Lᵉ)
      ( xᵉ)
      ( sup-Large-Frameᵉ xᵉ)
  is-least-upper-bound-sup-Large-Frameᵉ =
    is-least-upper-bound-sup-is-large-suplattice-Large-Posetᵉ γᵉ
      ( large-poset-Large-Frameᵉ Lᵉ)
      ( is-large-suplattice-Large-Frameᵉ Lᵉ)

  large-suplattice-Large-Frameᵉ : Large-Suplatticeᵉ αᵉ βᵉ γᵉ
  large-poset-Large-Suplatticeᵉ large-suplattice-Large-Frameᵉ =
    large-poset-Large-Frameᵉ Lᵉ
  is-large-suplattice-Large-Suplatticeᵉ large-suplattice-Large-Frameᵉ =
    is-large-suplattice-Large-Frameᵉ Lᵉ

  is-upper-bound-sup-Large-Frameᵉ :
    {l1ᵉ l2ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ} (xᵉ : Iᵉ → type-Large-Frameᵉ l2ᵉ) →
    is-upper-bound-family-of-elements-Large-Posetᵉ
      ( large-poset-Large-Frameᵉ Lᵉ)
      ( xᵉ)
      ( sup-Large-Frameᵉ xᵉ)
  is-upper-bound-sup-Large-Frameᵉ =
    is-upper-bound-sup-Large-Suplatticeᵉ large-suplattice-Large-Frameᵉ
```

## Properties

### Small constructions from large frames

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level} {γᵉ : Level}
  (Lᵉ : Large-Frameᵉ αᵉ βᵉ γᵉ)
  where

  preorder-Large-Frameᵉ : (lᵉ : Level) → Preorderᵉ (αᵉ lᵉ) (βᵉ lᵉ lᵉ)
  preorder-Large-Frameᵉ = preorder-Large-Preorderᵉ (large-preorder-Large-Frameᵉ Lᵉ)

  poset-Large-Frameᵉ : (lᵉ : Level) → Posetᵉ (αᵉ lᵉ) (βᵉ lᵉ lᵉ)
  poset-Large-Frameᵉ = poset-Large-Posetᵉ (large-poset-Large-Frameᵉ Lᵉ)

  is-suplattice-poset-Large-Frameᵉ :
    (l1ᵉ l2ᵉ : Level) → is-suplattice-Posetᵉ l1ᵉ (poset-Large-Frameᵉ (γᵉ ⊔ l1ᵉ ⊔ l2ᵉ))
  pr1ᵉ (is-suplattice-poset-Large-Frameᵉ l1ᵉ l2ᵉ Iᵉ yᵉ) =
    sup-Large-Frameᵉ Lᵉ yᵉ
  pr2ᵉ (is-suplattice-poset-Large-Frameᵉ l1ᵉ l2ᵉ Iᵉ yᵉ) =
    is-least-upper-bound-sup-Large-Frameᵉ Lᵉ yᵉ

  suplattice-Large-Frameᵉ :
    (l1ᵉ l2ᵉ : Level) →
    Suplatticeᵉ (αᵉ (γᵉ ⊔ l1ᵉ ⊔ l2ᵉ)) (βᵉ (γᵉ ⊔ l1ᵉ ⊔ l2ᵉ) (γᵉ ⊔ l1ᵉ ⊔ l2ᵉ)) l1ᵉ
  pr1ᵉ (suplattice-Large-Frameᵉ l1ᵉ l2ᵉ) = poset-Large-Frameᵉ (γᵉ ⊔ l1ᵉ ⊔ l2ᵉ)
  pr2ᵉ (suplattice-Large-Frameᵉ l1ᵉ l2ᵉ) = is-suplattice-poset-Large-Frameᵉ l1ᵉ l2ᵉ

  is-meet-semilattice-poset-Large-Frameᵉ :
    (lᵉ : Level) → is-meet-semilattice-Posetᵉ (poset-Large-Frameᵉ lᵉ)
  pr1ᵉ (is-meet-semilattice-poset-Large-Frameᵉ lᵉ xᵉ yᵉ) =
    meet-Large-Frameᵉ Lᵉ xᵉ yᵉ
  pr2ᵉ (is-meet-semilattice-poset-Large-Frameᵉ lᵉ xᵉ yᵉ) =
    is-greatest-binary-lower-bound-meet-Large-Frameᵉ Lᵉ xᵉ yᵉ

  order-theoretic-meet-semilattice-Large-Frameᵉ :
    (lᵉ : Level) → Order-Theoretic-Meet-Semilatticeᵉ (αᵉ lᵉ) (βᵉ lᵉ lᵉ)
  pr1ᵉ (order-theoretic-meet-semilattice-Large-Frameᵉ lᵉ) =
    poset-Large-Frameᵉ lᵉ
  pr2ᵉ (order-theoretic-meet-semilattice-Large-Frameᵉ lᵉ) =
    is-meet-semilattice-poset-Large-Frameᵉ lᵉ

  meet-semilattice-Large-Frameᵉ : (lᵉ : Level) → Meet-Semilatticeᵉ (αᵉ lᵉ)
  meet-semilattice-Large-Frameᵉ =
    meet-semilattice-Large-Meet-Semilatticeᵉ
      ( large-meet-semilattice-Large-Frameᵉ Lᵉ)
```