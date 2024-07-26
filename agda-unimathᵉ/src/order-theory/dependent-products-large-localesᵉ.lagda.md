# Dependent products of large locales

```agda
module order-theory.dependent-products-large-localesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.identity-typesᵉ
open import foundation.large-binary-relationsᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ

open import order-theory.dependent-products-large-framesᵉ
open import order-theory.greatest-lower-bounds-large-posetsᵉ
open import order-theory.large-localesᵉ
open import order-theory.large-meet-semilatticesᵉ
open import order-theory.large-posetsᵉ
open import order-theory.large-suplatticesᵉ
open import order-theory.least-upper-bounds-large-posetsᵉ
open import order-theory.top-elements-large-posetsᵉ
```

</details>

Givenᵉ aᵉ familyᵉ `Lᵉ : Iᵉ → Large-Localeᵉ αᵉ β`ᵉ ofᵉ largeᵉ localesᵉ indexedᵉ byᵉ aᵉ typeᵉ
`Iᵉ : UUᵉ l`,ᵉ theᵉ productᵉ ofᵉ theᵉ largeᵉ localesᵉ `Lᵉ i`ᵉ isᵉ againᵉ aᵉ largeᵉ locale.ᵉ

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level} {γᵉ : Level}
  {l1ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ} (Lᵉ : Iᵉ → Large-Localeᵉ αᵉ βᵉ γᵉ)
  where

  Π-Large-Localeᵉ : Large-Localeᵉ (λ l2ᵉ → αᵉ l2ᵉ ⊔ l1ᵉ) (λ l2ᵉ l3ᵉ → βᵉ l2ᵉ l3ᵉ ⊔ l1ᵉ) γᵉ
  Π-Large-Localeᵉ = Π-Large-Frameᵉ Lᵉ

  large-poset-Π-Large-Localeᵉ :
    Large-Posetᵉ (λ l2ᵉ → αᵉ l2ᵉ ⊔ l1ᵉ) (λ l2ᵉ l3ᵉ → βᵉ l2ᵉ l3ᵉ ⊔ l1ᵉ)
  large-poset-Π-Large-Localeᵉ = large-poset-Π-Large-Frameᵉ Lᵉ

  large-meet-semilattice-Π-Large-Localeᵉ :
    Large-Meet-Semilatticeᵉ (λ l2ᵉ → αᵉ l2ᵉ ⊔ l1ᵉ) (λ l2ᵉ l3ᵉ → βᵉ l2ᵉ l3ᵉ ⊔ l1ᵉ)
  large-meet-semilattice-Π-Large-Localeᵉ =
    large-meet-semilattice-Π-Large-Frameᵉ Lᵉ

  has-meets-Π-Large-Localeᵉ :
    has-meets-Large-Posetᵉ large-poset-Π-Large-Localeᵉ
  has-meets-Π-Large-Localeᵉ = has-meets-Π-Large-Frameᵉ Lᵉ

  large-suplattice-Π-Large-Localeᵉ :
    Large-Suplatticeᵉ (λ l2ᵉ → αᵉ l2ᵉ ⊔ l1ᵉ) (λ l2ᵉ l3ᵉ → βᵉ l2ᵉ l3ᵉ ⊔ l1ᵉ) γᵉ
  large-suplattice-Π-Large-Localeᵉ = large-suplattice-Π-Large-Frameᵉ Lᵉ

  is-large-suplattice-Π-Large-Localeᵉ :
    is-large-suplattice-Large-Posetᵉ γᵉ large-poset-Π-Large-Localeᵉ
  is-large-suplattice-Π-Large-Localeᵉ =
    is-large-suplattice-Π-Large-Frameᵉ Lᵉ

  set-Π-Large-Localeᵉ : (lᵉ : Level) → Setᵉ (αᵉ lᵉ ⊔ l1ᵉ)
  set-Π-Large-Localeᵉ = set-Π-Large-Frameᵉ Lᵉ

  type-Π-Large-Localeᵉ : (lᵉ : Level) → UUᵉ (αᵉ lᵉ ⊔ l1ᵉ)
  type-Π-Large-Localeᵉ = type-Π-Large-Frameᵉ Lᵉ

  is-set-type-Π-Large-Localeᵉ : {lᵉ : Level} → is-setᵉ (type-Π-Large-Localeᵉ lᵉ)
  is-set-type-Π-Large-Localeᵉ = is-set-type-Π-Large-Frameᵉ Lᵉ

  leq-prop-Π-Large-Localeᵉ :
    Large-Relation-Propᵉ
      ( λ l2ᵉ l3ᵉ → βᵉ l2ᵉ l3ᵉ ⊔ l1ᵉ)
      ( type-Π-Large-Localeᵉ)
  leq-prop-Π-Large-Localeᵉ = leq-prop-Π-Large-Frameᵉ Lᵉ

  leq-Π-Large-Localeᵉ :
    Large-Relationᵉ
      ( λ l2ᵉ l3ᵉ → βᵉ l2ᵉ l3ᵉ ⊔ l1ᵉ)
      ( type-Π-Large-Localeᵉ)
  leq-Π-Large-Localeᵉ = leq-Π-Large-Frameᵉ Lᵉ

  is-prop-leq-Π-Large-Localeᵉ :
    is-prop-Large-Relationᵉ type-Π-Large-Localeᵉ leq-Π-Large-Localeᵉ
  is-prop-leq-Π-Large-Localeᵉ = is-prop-leq-Π-Large-Frameᵉ Lᵉ

  refl-leq-Π-Large-Localeᵉ :
    is-reflexive-Large-Relationᵉ type-Π-Large-Localeᵉ leq-Π-Large-Localeᵉ
  refl-leq-Π-Large-Localeᵉ = refl-leq-Π-Large-Frameᵉ Lᵉ

  antisymmetric-leq-Π-Large-Localeᵉ :
    is-antisymmetric-Large-Relationᵉ type-Π-Large-Localeᵉ leq-Π-Large-Localeᵉ
  antisymmetric-leq-Π-Large-Localeᵉ = antisymmetric-leq-Π-Large-Frameᵉ Lᵉ

  transitive-leq-Π-Large-Localeᵉ :
    is-transitive-Large-Relationᵉ type-Π-Large-Localeᵉ leq-Π-Large-Localeᵉ
  transitive-leq-Π-Large-Localeᵉ = transitive-leq-Π-Large-Frameᵉ Lᵉ

  meet-Π-Large-Localeᵉ :
    {l2ᵉ l3ᵉ : Level} →
    type-Π-Large-Localeᵉ l2ᵉ → type-Π-Large-Localeᵉ l3ᵉ →
    type-Π-Large-Localeᵉ (l2ᵉ ⊔ l3ᵉ)
  meet-Π-Large-Localeᵉ = meet-Π-Large-Frameᵉ Lᵉ

  is-greatest-binary-lower-bound-meet-Π-Large-Localeᵉ :
    {l2ᵉ l3ᵉ : Level}
    (xᵉ : type-Π-Large-Localeᵉ l2ᵉ)
    (yᵉ : type-Π-Large-Localeᵉ l3ᵉ) →
    is-greatest-binary-lower-bound-Large-Posetᵉ
      ( large-poset-Π-Large-Localeᵉ)
      ( xᵉ)
      ( yᵉ)
      ( meet-Π-Large-Localeᵉ xᵉ yᵉ)
  is-greatest-binary-lower-bound-meet-Π-Large-Localeᵉ =
    is-greatest-binary-lower-bound-meet-Π-Large-Frameᵉ Lᵉ

  top-Π-Large-Localeᵉ : type-Π-Large-Localeᵉ lzero
  top-Π-Large-Localeᵉ = top-Π-Large-Frameᵉ Lᵉ

  is-top-element-top-Π-Large-Localeᵉ :
    {l1ᵉ : Level} (xᵉ : type-Π-Large-Localeᵉ l1ᵉ) →
    leq-Π-Large-Localeᵉ xᵉ top-Π-Large-Localeᵉ
  is-top-element-top-Π-Large-Localeᵉ =
    is-top-element-top-Π-Large-Frameᵉ Lᵉ

  has-top-element-Π-Large-Localeᵉ :
    has-top-element-Large-Posetᵉ large-poset-Π-Large-Localeᵉ
  has-top-element-Π-Large-Localeᵉ =
    has-top-element-Π-Large-Frameᵉ Lᵉ

  is-large-meet-semilattice-Π-Large-Localeᵉ :
    is-large-meet-semilattice-Large-Posetᵉ large-poset-Π-Large-Localeᵉ
  is-large-meet-semilattice-Π-Large-Localeᵉ =
    is-large-meet-semilattice-Π-Large-Frameᵉ Lᵉ

  sup-Π-Large-Localeᵉ :
    {l2ᵉ l3ᵉ : Level} {Jᵉ : UUᵉ l2ᵉ} (xᵉ : Jᵉ → type-Π-Large-Localeᵉ l3ᵉ) →
    type-Π-Large-Localeᵉ (γᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  sup-Π-Large-Localeᵉ = sup-Π-Large-Frameᵉ Lᵉ

  is-least-upper-bound-sup-Π-Large-Localeᵉ :
    {l2ᵉ l3ᵉ : Level} {Jᵉ : UUᵉ l2ᵉ} (xᵉ : Jᵉ → type-Π-Large-Localeᵉ l3ᵉ) →
    is-least-upper-bound-family-of-elements-Large-Posetᵉ
      ( large-poset-Π-Large-Localeᵉ)
      ( xᵉ)
      ( sup-Π-Large-Localeᵉ xᵉ)
  is-least-upper-bound-sup-Π-Large-Localeᵉ =
    is-least-upper-bound-sup-Π-Large-Frameᵉ Lᵉ

  distributive-meet-sup-Π-Large-Localeᵉ :
    {l2ᵉ l3ᵉ l4ᵉ : Level}
    (xᵉ : type-Π-Large-Localeᵉ l2ᵉ)
    {Jᵉ : UUᵉ l3ᵉ} (yᵉ : Jᵉ → type-Π-Large-Localeᵉ l4ᵉ) →
    meet-Π-Large-Localeᵉ xᵉ (sup-Π-Large-Localeᵉ yᵉ) ＝ᵉ
    sup-Π-Large-Localeᵉ (λ jᵉ → meet-Π-Large-Localeᵉ xᵉ (yᵉ jᵉ))
  distributive-meet-sup-Π-Large-Localeᵉ =
    distributive-meet-sup-Π-Large-Frameᵉ Lᵉ
```