# Large quotient locales

```agda
module order-theory.large-quotient-localesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.identity-typesᵉ
open import foundation.large-binary-relationsᵉ
open import foundation.universe-levelsᵉ

open import order-theory.greatest-lower-bounds-large-posetsᵉ
open import order-theory.large-localesᵉ
open import order-theory.large-meet-semilatticesᵉ
open import order-theory.large-meet-subsemilatticesᵉ
open import order-theory.large-posetsᵉ
open import order-theory.large-preordersᵉ
open import order-theory.large-subframesᵉ
open import order-theory.large-subposetsᵉ
open import order-theory.large-subpreordersᵉ
open import order-theory.large-subsuplatticesᵉ
open import order-theory.large-suplatticesᵉ
open import order-theory.least-upper-bounds-large-posetsᵉ
open import order-theory.top-elements-large-posetsᵉ
```

</details>

## Idea

Aᵉ **largeᵉ quotientᵉ locale**ᵉ ofᵉ aᵉ [largeᵉ locale](order-theory.large-locales.mdᵉ)
`L`ᵉ isᵉ byᵉ dualityᵉ justᵉ aᵉ [largeᵉ subframe](order-theory.large-subframes.mdᵉ) ofᵉ
`L`.ᵉ

## Definition

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level} {γᵉ : Level}
  (δᵉ : Level → Level)
  (Lᵉ : Large-Localeᵉ αᵉ βᵉ γᵉ)
  where

  Large-Quotient-Localeᵉ : UUωᵉ
  Large-Quotient-Localeᵉ = Large-Subframeᵉ δᵉ Lᵉ

module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level} {γᵉ : Level}
  {δᵉ : Level → Level}
  (Lᵉ : Large-Localeᵉ αᵉ βᵉ γᵉ) (Qᵉ : Large-Quotient-Localeᵉ δᵉ Lᵉ)
  where

  large-subposet-Large-Quotient-Localeᵉ :
    Large-Subposetᵉ δᵉ (large-poset-Large-Localeᵉ Lᵉ)
  large-subposet-Large-Quotient-Localeᵉ =
    large-subposet-Large-Subframeᵉ Qᵉ

  is-closed-under-meets-Large-Quotient-Localeᵉ :
    is-closed-under-meets-Large-Subposetᵉ
      ( large-meet-semilattice-Large-Localeᵉ Lᵉ)
      ( large-subposet-Large-Quotient-Localeᵉ)
  is-closed-under-meets-Large-Quotient-Localeᵉ =
    is-closed-under-meets-Large-Subframeᵉ Qᵉ

  contains-top-Large-Quotient-Localeᵉ :
    contains-top-Large-Subposetᵉ
      ( large-meet-semilattice-Large-Localeᵉ Lᵉ)
      ( large-subposet-Large-Quotient-Localeᵉ)
  contains-top-Large-Quotient-Localeᵉ =
    contains-top-Large-Subframeᵉ Qᵉ

  is-closed-under-sup-Large-Quotient-Localeᵉ :
    is-closed-under-sup-Large-Subposetᵉ
      ( large-suplattice-Large-Localeᵉ Lᵉ)
      ( large-subposet-Large-Quotient-Localeᵉ)
  is-closed-under-sup-Large-Quotient-Localeᵉ =
    is-closed-under-sup-Large-Subframeᵉ Qᵉ

  large-poset-Large-Quotient-Localeᵉ :
    Large-Posetᵉ (λ lᵉ → αᵉ lᵉ ⊔ δᵉ lᵉ) βᵉ
  large-poset-Large-Quotient-Localeᵉ =
    large-poset-Large-Subframeᵉ Lᵉ Qᵉ

  large-subpreorder-Large-Quotient-Localeᵉ :
    Large-Subpreorderᵉ δᵉ (large-preorder-Large-Localeᵉ Lᵉ)
  large-subpreorder-Large-Quotient-Localeᵉ =
    large-subpreorder-Large-Subframeᵉ Lᵉ Qᵉ

  large-preorder-Large-Quotient-Localeᵉ :
    Large-Preorderᵉ (λ lᵉ → αᵉ lᵉ ⊔ δᵉ lᵉ) (λ l1ᵉ l2ᵉ → βᵉ l1ᵉ l2ᵉ)
  large-preorder-Large-Quotient-Localeᵉ =
    large-preorder-Large-Subframeᵉ Lᵉ Qᵉ

  is-in-Large-Quotient-Localeᵉ :
    {l1ᵉ : Level} → type-Large-Localeᵉ Lᵉ l1ᵉ → UUᵉ (δᵉ l1ᵉ)
  is-in-Large-Quotient-Localeᵉ =
    is-in-Large-Subframeᵉ Lᵉ Qᵉ

  type-Large-Quotient-Localeᵉ : (l1ᵉ : Level) → UUᵉ (αᵉ l1ᵉ ⊔ δᵉ l1ᵉ)
  type-Large-Quotient-Localeᵉ =
    type-Large-Subframeᵉ Lᵉ Qᵉ

  leq-prop-Large-Quotient-Localeᵉ :
    Large-Relation-Propᵉ βᵉ type-Large-Quotient-Localeᵉ
  leq-prop-Large-Quotient-Localeᵉ =
    leq-prop-Large-Subframeᵉ Lᵉ Qᵉ

  leq-Large-Quotient-Localeᵉ :
    Large-Relationᵉ βᵉ type-Large-Quotient-Localeᵉ
  leq-Large-Quotient-Localeᵉ =
    leq-Large-Subframeᵉ Lᵉ Qᵉ

  is-prop-leq-Large-Quotient-Localeᵉ :
    is-prop-Large-Relationᵉ type-Large-Quotient-Localeᵉ leq-Large-Quotient-Localeᵉ
  is-prop-leq-Large-Quotient-Localeᵉ =
    is-prop-leq-Large-Subframeᵉ Lᵉ Qᵉ

  refl-leq-Large-Quotient-Localeᵉ :
    is-reflexive-Large-Relationᵉ
      ( type-Large-Quotient-Localeᵉ)
      ( leq-Large-Quotient-Localeᵉ)
  refl-leq-Large-Quotient-Localeᵉ =
    refl-leq-Large-Subframeᵉ Lᵉ Qᵉ

  transitive-leq-Large-Quotient-Localeᵉ :
    is-transitive-Large-Relationᵉ
      ( type-Large-Quotient-Localeᵉ)
      ( leq-Large-Quotient-Localeᵉ)
  transitive-leq-Large-Quotient-Localeᵉ =
    transitive-leq-Large-Subframeᵉ Lᵉ Qᵉ

  antisymmetric-leq-Large-Quotient-Localeᵉ :
    is-antisymmetric-Large-Relationᵉ
      ( type-Large-Quotient-Localeᵉ)
      ( leq-Large-Quotient-Localeᵉ)
  antisymmetric-leq-Large-Quotient-Localeᵉ =
    antisymmetric-leq-Large-Subframeᵉ Lᵉ Qᵉ

  is-closed-under-sim-Large-Quotient-Localeᵉ :
    {l1ᵉ l2ᵉ : Level}
    (xᵉ : type-Large-Localeᵉ Lᵉ l1ᵉ)
    (yᵉ : type-Large-Localeᵉ Lᵉ l2ᵉ) →
    leq-Large-Localeᵉ Lᵉ xᵉ yᵉ →
    leq-Large-Localeᵉ Lᵉ yᵉ xᵉ →
    is-in-Large-Quotient-Localeᵉ xᵉ →
    is-in-Large-Quotient-Localeᵉ yᵉ
  is-closed-under-sim-Large-Quotient-Localeᵉ =
    is-closed-under-sim-Large-Subframeᵉ Lᵉ Qᵉ

  meet-Large-Quotient-Localeᵉ :
    {l1ᵉ l2ᵉ : Level}
    (xᵉ : type-Large-Quotient-Localeᵉ l1ᵉ)
    (yᵉ : type-Large-Quotient-Localeᵉ l2ᵉ) →
    type-Large-Quotient-Localeᵉ (l1ᵉ ⊔ l2ᵉ)
  meet-Large-Quotient-Localeᵉ =
    meet-Large-Subframeᵉ Lᵉ Qᵉ

  is-greatest-binary-lower-bound-meet-Large-Quotient-Localeᵉ :
    {l1ᵉ l2ᵉ : Level}
    (xᵉ : type-Large-Quotient-Localeᵉ l1ᵉ)
    (yᵉ : type-Large-Quotient-Localeᵉ l2ᵉ) →
    is-greatest-binary-lower-bound-Large-Posetᵉ
      ( large-poset-Large-Quotient-Localeᵉ)
      ( xᵉ)
      ( yᵉ)
      ( meet-Large-Quotient-Localeᵉ xᵉ yᵉ)
  is-greatest-binary-lower-bound-meet-Large-Quotient-Localeᵉ =
    is-greatest-binary-lower-bound-meet-Large-Subframeᵉ Lᵉ Qᵉ

  has-meets-Large-Quotient-Localeᵉ :
    has-meets-Large-Posetᵉ
      ( large-poset-Large-Quotient-Localeᵉ)
  has-meets-Large-Quotient-Localeᵉ =
    has-meets-Large-Subframeᵉ Lᵉ Qᵉ

  top-Large-Quotient-Localeᵉ :
    type-Large-Quotient-Localeᵉ lzero
  top-Large-Quotient-Localeᵉ =
    top-Large-Subframeᵉ Lᵉ Qᵉ

  is-top-element-top-Large-Quotient-Localeᵉ :
    {l1ᵉ : Level} (xᵉ : type-Large-Quotient-Localeᵉ l1ᵉ) →
    leq-Large-Quotient-Localeᵉ xᵉ top-Large-Quotient-Localeᵉ
  is-top-element-top-Large-Quotient-Localeᵉ =
    is-top-element-top-Large-Subframeᵉ Lᵉ Qᵉ

  has-top-element-Large-Quotient-Localeᵉ :
    has-top-element-Large-Posetᵉ
      ( large-poset-Large-Quotient-Localeᵉ)
  has-top-element-Large-Quotient-Localeᵉ =
    has-top-element-Large-Subframeᵉ Lᵉ Qᵉ

  is-large-meet-semilattice-Large-Quotient-Localeᵉ :
    is-large-meet-semilattice-Large-Posetᵉ
      ( large-poset-Large-Quotient-Localeᵉ)
  is-large-meet-semilattice-Large-Quotient-Localeᵉ =
    is-large-meet-semilattice-Large-Subframeᵉ Lᵉ Qᵉ

  large-meet-semilattice-Large-Quotient-Localeᵉ :
    Large-Meet-Semilatticeᵉ (λ lᵉ → αᵉ lᵉ ⊔ δᵉ lᵉ) βᵉ
  large-meet-semilattice-Large-Quotient-Localeᵉ =
    large-meet-semilattice-Large-Subframeᵉ Lᵉ Qᵉ

  sup-Large-Quotient-Localeᵉ :
    {l1ᵉ l2ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ} (xᵉ : Iᵉ → type-Large-Quotient-Localeᵉ l2ᵉ) →
    type-Large-Quotient-Localeᵉ (γᵉ ⊔ l1ᵉ ⊔ l2ᵉ)
  sup-Large-Quotient-Localeᵉ =
    sup-Large-Subframeᵉ Lᵉ Qᵉ

  is-least-upper-bound-sup-Large-Quotient-Localeᵉ :
    {l1ᵉ l2ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ} (xᵉ : Iᵉ → type-Large-Quotient-Localeᵉ l2ᵉ) →
    is-least-upper-bound-family-of-elements-Large-Posetᵉ
      ( large-poset-Large-Quotient-Localeᵉ)
      ( xᵉ)
      ( sup-Large-Quotient-Localeᵉ xᵉ)
  is-least-upper-bound-sup-Large-Quotient-Localeᵉ =
    is-least-upper-bound-sup-Large-Subframeᵉ Lᵉ Qᵉ

  is-large-suplattice-Large-Quotient-Localeᵉ :
    is-large-suplattice-Large-Posetᵉ γᵉ (large-poset-Large-Quotient-Localeᵉ)
  is-large-suplattice-Large-Quotient-Localeᵉ =
    is-large-suplattice-Large-Subframeᵉ Lᵉ Qᵉ

  large-suplattice-Large-Quotient-Localeᵉ :
    Large-Suplatticeᵉ (λ lᵉ → αᵉ lᵉ ⊔ δᵉ lᵉ) βᵉ γᵉ
  large-suplattice-Large-Quotient-Localeᵉ =
    large-suplattice-Large-Subframeᵉ Lᵉ Qᵉ

  distributive-meet-sup-Large-Quotient-Localeᵉ :
    {l1ᵉ l2ᵉ l3ᵉ : Level} (xᵉ : type-Large-Quotient-Localeᵉ l1ᵉ)
    {Iᵉ : UUᵉ l2ᵉ} (yᵉ : Iᵉ → type-Large-Quotient-Localeᵉ l3ᵉ) →
    meet-Large-Quotient-Localeᵉ xᵉ (sup-Large-Quotient-Localeᵉ yᵉ) ＝ᵉ
    sup-Large-Quotient-Localeᵉ (λ iᵉ → meet-Large-Quotient-Localeᵉ xᵉ (yᵉ iᵉ))
  distributive-meet-sup-Large-Quotient-Localeᵉ =
    distributive-meet-sup-Large-Subframeᵉ Lᵉ Qᵉ

  large-locale-Large-Quotient-Localeᵉ :
    Large-Localeᵉ (λ lᵉ → αᵉ lᵉ ⊔ δᵉ lᵉ) βᵉ γᵉ
  large-locale-Large-Quotient-Localeᵉ =
    large-frame-Large-Subframeᵉ Lᵉ Qᵉ
```