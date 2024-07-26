# Powers of large locales

```agda
module order-theory.powers-of-large-localesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.identity-typesᵉ
open import foundation.large-binary-relationsᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ

open import order-theory.dependent-products-large-localesᵉ
open import order-theory.greatest-lower-bounds-large-posetsᵉ
open import order-theory.large-localesᵉ
open import order-theory.large-meet-semilatticesᵉ
open import order-theory.large-posetsᵉ
open import order-theory.large-suplatticesᵉ
open import order-theory.least-upper-bounds-large-posetsᵉ
open import order-theory.top-elements-large-posetsᵉ
```

</details>

## Idea

Givenᵉ aᵉ largeᵉ localeᵉ `L`ᵉ andᵉ aᵉ typeᵉ `Xᵉ : UUᵉ l`,ᵉ theᵉ **largeᵉ powerᵉ locale**ᵉ isᵉ
theᵉ localeᵉ `Xᵉ → L`ᵉ ofᵉ functionsᵉ fromᵉ `X`ᵉ to `L`.ᵉ

## Definitions

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level} {γᵉ : Level} {l1ᵉ : Level}
  (Xᵉ : UUᵉ l1ᵉ) (Lᵉ : Large-Localeᵉ αᵉ βᵉ γᵉ)
  where

  power-Large-Localeᵉ :
    Large-Localeᵉ (λ l2ᵉ → αᵉ l2ᵉ ⊔ l1ᵉ) (λ l2ᵉ l3ᵉ → βᵉ l2ᵉ l3ᵉ ⊔ l1ᵉ) γᵉ
  power-Large-Localeᵉ = Π-Large-Localeᵉ (λ (xᵉ : Xᵉ) → Lᵉ)

  large-poset-power-Large-Localeᵉ :
    Large-Posetᵉ (λ l2ᵉ → αᵉ l2ᵉ ⊔ l1ᵉ) (λ l2ᵉ l3ᵉ → βᵉ l2ᵉ l3ᵉ ⊔ l1ᵉ)
  large-poset-power-Large-Localeᵉ =
    large-poset-Large-Localeᵉ power-Large-Localeᵉ

  set-power-Large-Localeᵉ : (lᵉ : Level) → Setᵉ (αᵉ lᵉ ⊔ l1ᵉ)
  set-power-Large-Localeᵉ =
    set-Large-Localeᵉ power-Large-Localeᵉ

  type-power-Large-Localeᵉ : (lᵉ : Level) → UUᵉ (αᵉ lᵉ ⊔ l1ᵉ)
  type-power-Large-Localeᵉ =
    type-Large-Localeᵉ power-Large-Localeᵉ

  is-set-type-power-Large-Localeᵉ :
    {lᵉ : Level} → is-setᵉ (type-power-Large-Localeᵉ lᵉ)
  is-set-type-power-Large-Localeᵉ =
    is-set-type-Large-Localeᵉ power-Large-Localeᵉ

  leq-prop-power-Large-Localeᵉ :
    Large-Relation-Propᵉ
      ( λ l2ᵉ l3ᵉ → βᵉ l2ᵉ l3ᵉ ⊔ l1ᵉ)
      ( type-power-Large-Localeᵉ)
  leq-prop-power-Large-Localeᵉ =
    leq-prop-Large-Localeᵉ power-Large-Localeᵉ

  leq-power-Large-Localeᵉ :
    Large-Relationᵉ
      ( λ l2ᵉ l3ᵉ → βᵉ l2ᵉ l3ᵉ ⊔ l1ᵉ)
      ( type-power-Large-Localeᵉ)
  leq-power-Large-Localeᵉ =
    leq-Large-Localeᵉ power-Large-Localeᵉ

  is-prop-leq-power-Large-Localeᵉ :
    is-prop-Large-Relationᵉ (type-power-Large-Localeᵉ) (leq-power-Large-Localeᵉ)
  is-prop-leq-power-Large-Localeᵉ =
    is-prop-leq-Large-Localeᵉ power-Large-Localeᵉ

  refl-leq-power-Large-Localeᵉ :
    is-reflexive-Large-Relationᵉ type-power-Large-Localeᵉ leq-power-Large-Localeᵉ
  refl-leq-power-Large-Localeᵉ =
    refl-leq-Large-Localeᵉ power-Large-Localeᵉ

  antisymmetric-leq-power-Large-Localeᵉ :
    is-antisymmetric-Large-Relationᵉ
      ( type-power-Large-Localeᵉ)
      ( leq-power-Large-Localeᵉ)
  antisymmetric-leq-power-Large-Localeᵉ =
    antisymmetric-leq-Large-Localeᵉ power-Large-Localeᵉ

  transitive-leq-power-Large-Localeᵉ :
    is-transitive-Large-Relationᵉ type-power-Large-Localeᵉ leq-power-Large-Localeᵉ
  transitive-leq-power-Large-Localeᵉ =
    transitive-leq-Large-Localeᵉ power-Large-Localeᵉ

  large-meet-semilattice-power-Large-Localeᵉ :
    Large-Meet-Semilatticeᵉ (λ l2ᵉ → αᵉ l2ᵉ ⊔ l1ᵉ) (λ l2ᵉ l3ᵉ → βᵉ l2ᵉ l3ᵉ ⊔ l1ᵉ)
  large-meet-semilattice-power-Large-Localeᵉ =
    large-meet-semilattice-Large-Localeᵉ power-Large-Localeᵉ

  has-meets-power-Large-Localeᵉ :
    has-meets-Large-Posetᵉ large-poset-power-Large-Localeᵉ
  has-meets-power-Large-Localeᵉ =
    has-meets-Large-Localeᵉ power-Large-Localeᵉ

  meet-power-Large-Localeᵉ :
    {l2ᵉ l3ᵉ : Level} →
    type-power-Large-Localeᵉ l2ᵉ → type-power-Large-Localeᵉ l3ᵉ →
    type-power-Large-Localeᵉ (l2ᵉ ⊔ l3ᵉ)
  meet-power-Large-Localeᵉ =
    meet-Large-Localeᵉ power-Large-Localeᵉ

  is-greatest-binary-lower-bound-meet-power-Large-Localeᵉ :
    {l2ᵉ l3ᵉ : Level}
    (xᵉ : type-power-Large-Localeᵉ l2ᵉ)
    (yᵉ : type-power-Large-Localeᵉ l3ᵉ) →
    is-greatest-binary-lower-bound-Large-Posetᵉ
      ( large-poset-power-Large-Localeᵉ)
      ( xᵉ)
      ( yᵉ)
      ( meet-power-Large-Localeᵉ xᵉ yᵉ)
  is-greatest-binary-lower-bound-meet-power-Large-Localeᵉ =
    is-greatest-binary-lower-bound-meet-Large-Localeᵉ power-Large-Localeᵉ

  has-top-element-power-Large-Localeᵉ :
    has-top-element-Large-Posetᵉ large-poset-power-Large-Localeᵉ
  has-top-element-power-Large-Localeᵉ =
    has-top-element-Large-Localeᵉ power-Large-Localeᵉ

  top-power-Large-Localeᵉ : type-power-Large-Localeᵉ lzero
  top-power-Large-Localeᵉ = top-Large-Localeᵉ power-Large-Localeᵉ

  is-top-element-top-power-Large-Localeᵉ :
    {l1ᵉ : Level} (xᵉ : type-power-Large-Localeᵉ l1ᵉ) →
    leq-power-Large-Localeᵉ xᵉ top-power-Large-Localeᵉ
  is-top-element-top-power-Large-Localeᵉ =
    is-top-element-top-Large-Localeᵉ power-Large-Localeᵉ

  large-suplattice-power-Large-Localeᵉ :
    Large-Suplatticeᵉ (λ l2ᵉ → αᵉ l2ᵉ ⊔ l1ᵉ) (λ l2ᵉ l3ᵉ → βᵉ l2ᵉ l3ᵉ ⊔ l1ᵉ) γᵉ
  large-suplattice-power-Large-Localeᵉ =
    large-suplattice-Large-Localeᵉ power-Large-Localeᵉ

  is-large-suplattice-power-Large-Localeᵉ :
    is-large-suplattice-Large-Posetᵉ γᵉ large-poset-power-Large-Localeᵉ
  is-large-suplattice-power-Large-Localeᵉ =
    is-large-suplattice-Large-Localeᵉ power-Large-Localeᵉ

  sup-power-Large-Localeᵉ :
    {l2ᵉ l3ᵉ : Level} {Jᵉ : UUᵉ l2ᵉ} (xᵉ : Jᵉ → type-power-Large-Localeᵉ l3ᵉ) →
    type-power-Large-Localeᵉ (γᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  sup-power-Large-Localeᵉ =
    sup-Large-Localeᵉ power-Large-Localeᵉ

  is-least-upper-bound-sup-power-Large-Localeᵉ :
    {l2ᵉ l3ᵉ : Level} {Jᵉ : UUᵉ l2ᵉ} (xᵉ : Jᵉ → type-power-Large-Localeᵉ l3ᵉ) →
    is-least-upper-bound-family-of-elements-Large-Posetᵉ
      ( large-poset-power-Large-Localeᵉ)
      ( xᵉ)
      ( sup-power-Large-Localeᵉ xᵉ)
  is-least-upper-bound-sup-power-Large-Localeᵉ =
    is-least-upper-bound-sup-Large-Localeᵉ power-Large-Localeᵉ

  distributive-meet-sup-power-Large-Localeᵉ :
    {l2ᵉ l3ᵉ l4ᵉ : Level}
    (xᵉ : type-power-Large-Localeᵉ l2ᵉ)
    {Jᵉ : UUᵉ l3ᵉ} (yᵉ : Jᵉ → type-power-Large-Localeᵉ l4ᵉ) →
    meet-power-Large-Localeᵉ xᵉ (sup-power-Large-Localeᵉ yᵉ) ＝ᵉ
    sup-power-Large-Localeᵉ (λ jᵉ → meet-power-Large-Localeᵉ xᵉ (yᵉ jᵉ))
  distributive-meet-sup-power-Large-Localeᵉ =
    distributive-meet-sup-Large-Localeᵉ power-Large-Localeᵉ
```