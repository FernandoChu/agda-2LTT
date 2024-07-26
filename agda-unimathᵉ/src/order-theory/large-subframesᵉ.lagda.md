# Large subframes

```agda
module order-theory.large-subframesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.function-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.large-binary-relationsᵉ
open import foundation.subtypesᵉ
open import foundation.universe-levelsᵉ

open import order-theory.greatest-lower-bounds-large-posetsᵉ
open import order-theory.large-framesᵉ
open import order-theory.large-meet-semilatticesᵉ
open import order-theory.large-meet-subsemilatticesᵉ
open import order-theory.large-posetsᵉ
open import order-theory.large-preordersᵉ
open import order-theory.large-subposetsᵉ
open import order-theory.large-subpreordersᵉ
open import order-theory.large-subsuplatticesᵉ
open import order-theory.large-suplatticesᵉ
open import order-theory.least-upper-bounds-large-posetsᵉ
open import order-theory.top-elements-large-posetsᵉ
```

</details>

## Idea

Aᵉ **largeᵉ subframe**ᵉ ofᵉ aᵉ [largeᵉ frame](order-theory.large-frames.mdᵉ) isᵉ aᵉ
[largeᵉ subposet](order-theory.large-subposets.mdᵉ) whichᵉ isᵉ closedᵉ underᵉ meets,ᵉ
containsᵉ theᵉ topᵉ element,ᵉ andᵉ isᵉ closedᵉ underᵉ suprema.ᵉ

## Definition

```agda
record
  Large-Subframeᵉ
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level} {γᵉ : Level}
  (δᵉ : Level → Level) (Fᵉ : Large-Frameᵉ αᵉ βᵉ γᵉ) :
  UUωᵉ
  where
  field
    large-subposet-Large-Subframeᵉ :
      Large-Subposetᵉ δᵉ (large-poset-Large-Frameᵉ Fᵉ)
    is-closed-under-meets-Large-Subframeᵉ :
      is-closed-under-meets-Large-Subposetᵉ
        ( large-meet-semilattice-Large-Frameᵉ Fᵉ)
        ( large-subposet-Large-Subframeᵉ)
    contains-top-Large-Subframeᵉ :
      contains-top-Large-Subposetᵉ
        ( large-meet-semilattice-Large-Frameᵉ Fᵉ)
        ( large-subposet-Large-Subframeᵉ)
    is-closed-under-sup-Large-Subframeᵉ :
      is-closed-under-sup-Large-Subposetᵉ
        ( large-suplattice-Large-Frameᵉ Fᵉ)
        ( large-subposet-Large-Subframeᵉ)

open Large-Subframeᵉ public

module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level} {γᵉ : Level}
  {δᵉ : Level → Level} (Fᵉ : Large-Frameᵉ αᵉ βᵉ γᵉ) (Sᵉ : Large-Subframeᵉ δᵉ Fᵉ)
  where

  large-poset-Large-Subframeᵉ :
    Large-Posetᵉ (λ lᵉ → αᵉ lᵉ ⊔ δᵉ lᵉ) βᵉ
  large-poset-Large-Subframeᵉ =
    large-poset-Large-Subposetᵉ
      ( large-poset-Large-Frameᵉ Fᵉ)
      ( large-subposet-Large-Subframeᵉ Sᵉ)

  large-subpreorder-Large-Subframeᵉ :
    Large-Subpreorderᵉ δᵉ (large-preorder-Large-Frameᵉ Fᵉ)
  large-subpreorder-Large-Subframeᵉ =
    large-subpreorder-Large-Subposetᵉ (large-subposet-Large-Subframeᵉ Sᵉ)

  large-preorder-Large-Subframeᵉ :
    Large-Preorderᵉ (λ lᵉ → αᵉ lᵉ ⊔ δᵉ lᵉ) (λ l1ᵉ l2ᵉ → βᵉ l1ᵉ l2ᵉ)
  large-preorder-Large-Subframeᵉ =
    large-preorder-Large-Subposetᵉ
      ( large-poset-Large-Frameᵉ Fᵉ)
      ( large-subposet-Large-Subframeᵉ Sᵉ)

  is-in-Large-Subframeᵉ :
    {l1ᵉ : Level} → type-Large-Frameᵉ Fᵉ l1ᵉ → UUᵉ (δᵉ l1ᵉ)
  is-in-Large-Subframeᵉ =
    is-in-Large-Subposetᵉ
      ( large-poset-Large-Frameᵉ Fᵉ)
      ( large-subposet-Large-Subframeᵉ Sᵉ)

  type-Large-Subframeᵉ : (l1ᵉ : Level) → UUᵉ (αᵉ l1ᵉ ⊔ δᵉ l1ᵉ)
  type-Large-Subframeᵉ =
    type-Large-Subposetᵉ
      ( large-poset-Large-Frameᵉ Fᵉ)
      ( large-subposet-Large-Subframeᵉ Sᵉ)

  leq-prop-Large-Subframeᵉ :
    Large-Relation-Propᵉ βᵉ type-Large-Subframeᵉ
  leq-prop-Large-Subframeᵉ =
    leq-prop-Large-Subposetᵉ
      ( large-poset-Large-Frameᵉ Fᵉ)
      ( large-subposet-Large-Subframeᵉ Sᵉ)

  leq-Large-Subframeᵉ :
    Large-Relationᵉ βᵉ type-Large-Subframeᵉ
  leq-Large-Subframeᵉ =
    leq-Large-Subposetᵉ
      ( large-poset-Large-Frameᵉ Fᵉ)
      ( large-subposet-Large-Subframeᵉ Sᵉ)

  is-prop-leq-Large-Subframeᵉ :
    is-prop-Large-Relationᵉ type-Large-Subframeᵉ leq-Large-Subframeᵉ
  is-prop-leq-Large-Subframeᵉ =
    is-prop-leq-Large-Subposetᵉ
      ( large-poset-Large-Frameᵉ Fᵉ)
      ( large-subposet-Large-Subframeᵉ Sᵉ)

  refl-leq-Large-Subframeᵉ :
    is-reflexive-Large-Relationᵉ type-Large-Subframeᵉ leq-Large-Subframeᵉ
  refl-leq-Large-Subframeᵉ =
    refl-leq-Large-Subposetᵉ
      ( large-poset-Large-Frameᵉ Fᵉ)
      ( large-subposet-Large-Subframeᵉ Sᵉ)

  transitive-leq-Large-Subframeᵉ :
    is-transitive-Large-Relationᵉ type-Large-Subframeᵉ leq-Large-Subframeᵉ
  transitive-leq-Large-Subframeᵉ =
    transitive-leq-Large-Subposetᵉ
      ( large-poset-Large-Frameᵉ Fᵉ)
      ( large-subposet-Large-Subframeᵉ Sᵉ)

  antisymmetric-leq-Large-Subframeᵉ :
    is-antisymmetric-Large-Relationᵉ type-Large-Subframeᵉ leq-Large-Subframeᵉ
  antisymmetric-leq-Large-Subframeᵉ =
    antisymmetric-leq-Large-Subposetᵉ
      ( large-poset-Large-Frameᵉ Fᵉ)
      ( large-subposet-Large-Subframeᵉ Sᵉ)

  is-closed-under-sim-Large-Subframeᵉ :
    {l1ᵉ l2ᵉ : Level}
    (xᵉ : type-Large-Frameᵉ Fᵉ l1ᵉ)
    (yᵉ : type-Large-Frameᵉ Fᵉ l2ᵉ) →
    leq-Large-Frameᵉ Fᵉ xᵉ yᵉ →
    leq-Large-Frameᵉ Fᵉ yᵉ xᵉ →
    is-in-Large-Subframeᵉ xᵉ →
    is-in-Large-Subframeᵉ yᵉ
  is-closed-under-sim-Large-Subframeᵉ =
    is-closed-under-sim-Large-Subposetᵉ
      ( large-subposet-Large-Subframeᵉ Sᵉ)

  meet-Large-Subframeᵉ :
    {l1ᵉ l2ᵉ : Level}
    (xᵉ : type-Large-Subframeᵉ l1ᵉ)
    (yᵉ : type-Large-Subframeᵉ l2ᵉ) →
    type-Large-Subframeᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ (meet-Large-Subframeᵉ (xᵉ ,ᵉ pᵉ) (yᵉ ,ᵉ qᵉ)) =
    meet-Large-Frameᵉ Fᵉ xᵉ yᵉ
  pr2ᵉ (meet-Large-Subframeᵉ (xᵉ ,ᵉ pᵉ) (yᵉ ,ᵉ qᵉ)) =
    is-closed-under-meets-Large-Subframeᵉ Sᵉ xᵉ yᵉ pᵉ qᵉ

  is-greatest-binary-lower-bound-meet-Large-Subframeᵉ :
    {l1ᵉ l2ᵉ : Level}
    (xᵉ : type-Large-Subframeᵉ l1ᵉ)
    (yᵉ : type-Large-Subframeᵉ l2ᵉ) →
    is-greatest-binary-lower-bound-Large-Posetᵉ
      ( large-poset-Large-Subframeᵉ)
      ( xᵉ)
      ( yᵉ)
      ( meet-Large-Subframeᵉ xᵉ yᵉ)
  is-greatest-binary-lower-bound-meet-Large-Subframeᵉ
    (xᵉ ,ᵉ pᵉ) (yᵉ ,ᵉ qᵉ) (zᵉ ,ᵉ rᵉ) =
    is-greatest-binary-lower-bound-meet-Large-Frameᵉ Fᵉ xᵉ yᵉ zᵉ

  has-meets-Large-Subframeᵉ :
    has-meets-Large-Posetᵉ
      ( large-poset-Large-Subframeᵉ)
  meet-has-meets-Large-Posetᵉ
    has-meets-Large-Subframeᵉ =
    meet-Large-Subframeᵉ
  is-greatest-binary-lower-bound-meet-has-meets-Large-Posetᵉ
    has-meets-Large-Subframeᵉ =
    is-greatest-binary-lower-bound-meet-Large-Subframeᵉ

  top-Large-Subframeᵉ :
    type-Large-Subframeᵉ lzero
  pr1ᵉ top-Large-Subframeᵉ = top-Large-Frameᵉ Fᵉ
  pr2ᵉ top-Large-Subframeᵉ = contains-top-Large-Subframeᵉ Sᵉ

  is-top-element-top-Large-Subframeᵉ :
    {l1ᵉ : Level} (xᵉ : type-Large-Subframeᵉ l1ᵉ) →
    leq-Large-Subframeᵉ xᵉ top-Large-Subframeᵉ
  is-top-element-top-Large-Subframeᵉ (xᵉ ,ᵉ pᵉ) =
    is-top-element-top-Large-Frameᵉ Fᵉ xᵉ

  has-top-element-Large-Subframeᵉ :
    has-top-element-Large-Posetᵉ
      ( large-poset-Large-Subframeᵉ)
  top-has-top-element-Large-Posetᵉ
    has-top-element-Large-Subframeᵉ =
    top-Large-Subframeᵉ
  is-top-element-top-has-top-element-Large-Posetᵉ
    has-top-element-Large-Subframeᵉ =
    is-top-element-top-Large-Subframeᵉ

  is-large-meet-semilattice-Large-Subframeᵉ :
    is-large-meet-semilattice-Large-Posetᵉ
      ( large-poset-Large-Subframeᵉ)
  has-meets-is-large-meet-semilattice-Large-Posetᵉ
    is-large-meet-semilattice-Large-Subframeᵉ =
    has-meets-Large-Subframeᵉ
  has-top-element-is-large-meet-semilattice-Large-Posetᵉ
    is-large-meet-semilattice-Large-Subframeᵉ =
    has-top-element-Large-Subframeᵉ

  large-meet-semilattice-Large-Subframeᵉ :
    Large-Meet-Semilatticeᵉ (λ lᵉ → αᵉ lᵉ ⊔ δᵉ lᵉ) βᵉ
  large-poset-Large-Meet-Semilatticeᵉ
    large-meet-semilattice-Large-Subframeᵉ =
    large-poset-Large-Subframeᵉ
  is-large-meet-semilattice-Large-Meet-Semilatticeᵉ
    large-meet-semilattice-Large-Subframeᵉ =
    is-large-meet-semilattice-Large-Subframeᵉ

  sup-Large-Subframeᵉ :
    {l1ᵉ l2ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ} (xᵉ : Iᵉ → type-Large-Subframeᵉ l2ᵉ) →
    type-Large-Subframeᵉ (γᵉ ⊔ l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ (sup-Large-Subframeᵉ xᵉ) = sup-Large-Frameᵉ Fᵉ (pr1ᵉ ∘ᵉ xᵉ)
  pr2ᵉ (sup-Large-Subframeᵉ xᵉ) =
    is-closed-under-sup-Large-Subframeᵉ Sᵉ
      ( pr1ᵉ ∘ᵉ xᵉ)
      ( pr2ᵉ ∘ᵉ xᵉ)

  is-least-upper-bound-sup-Large-Subframeᵉ :
    {l1ᵉ l2ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ} (xᵉ : Iᵉ → type-Large-Subframeᵉ l2ᵉ) →
    is-least-upper-bound-family-of-elements-Large-Posetᵉ
      ( large-poset-Large-Subframeᵉ)
      ( xᵉ)
      ( sup-Large-Subframeᵉ xᵉ)
  is-least-upper-bound-sup-Large-Subframeᵉ xᵉ yᵉ =
    is-least-upper-bound-sup-Large-Frameᵉ Fᵉ (pr1ᵉ ∘ᵉ xᵉ) (pr1ᵉ yᵉ)

  is-large-suplattice-Large-Subframeᵉ :
    is-large-suplattice-Large-Posetᵉ γᵉ (large-poset-Large-Subframeᵉ)
  sup-has-least-upper-bound-family-of-elements-Large-Posetᵉ
    ( is-large-suplattice-Large-Subframeᵉ xᵉ) =
    sup-Large-Subframeᵉ xᵉ
  is-least-upper-bound-sup-has-least-upper-bound-family-of-elements-Large-Posetᵉ
    ( is-large-suplattice-Large-Subframeᵉ xᵉ) =
    is-least-upper-bound-sup-Large-Subframeᵉ xᵉ

  large-suplattice-Large-Subframeᵉ :
    Large-Suplatticeᵉ (λ lᵉ → αᵉ lᵉ ⊔ δᵉ lᵉ) βᵉ γᵉ
  large-poset-Large-Suplatticeᵉ
    large-suplattice-Large-Subframeᵉ =
    large-poset-Large-Subframeᵉ
  is-large-suplattice-Large-Suplatticeᵉ
    large-suplattice-Large-Subframeᵉ =
    is-large-suplattice-Large-Subframeᵉ

  distributive-meet-sup-Large-Subframeᵉ :
    {l1ᵉ l2ᵉ l3ᵉ : Level} (xᵉ : type-Large-Subframeᵉ l1ᵉ)
    {Iᵉ : UUᵉ l2ᵉ} (yᵉ : Iᵉ → type-Large-Subframeᵉ l3ᵉ) →
    meet-Large-Subframeᵉ xᵉ (sup-Large-Subframeᵉ yᵉ) ＝ᵉ
    sup-Large-Subframeᵉ (λ iᵉ → meet-Large-Subframeᵉ xᵉ (yᵉ iᵉ))
  distributive-meet-sup-Large-Subframeᵉ xᵉ yᵉ =
    eq-type-subtypeᵉ
      ( large-subpreorder-Large-Subframeᵉ)
      ( distributive-meet-sup-Large-Frameᵉ Fᵉ (pr1ᵉ xᵉ) (pr1ᵉ ∘ᵉ yᵉ))

  large-frame-Large-Subframeᵉ :
    Large-Frameᵉ (λ lᵉ → αᵉ lᵉ ⊔ δᵉ lᵉ) βᵉ γᵉ
  large-poset-Large-Frameᵉ
    large-frame-Large-Subframeᵉ =
    large-poset-Large-Subframeᵉ
  is-large-meet-semilattice-Large-Frameᵉ
    large-frame-Large-Subframeᵉ =
    is-large-meet-semilattice-Large-Subframeᵉ
  is-large-suplattice-Large-Frameᵉ
    large-frame-Large-Subframeᵉ =
    is-large-suplattice-Large-Subframeᵉ
  distributive-meet-sup-Large-Frameᵉ
    large-frame-Large-Subframeᵉ =
    distributive-meet-sup-Large-Subframeᵉ
```