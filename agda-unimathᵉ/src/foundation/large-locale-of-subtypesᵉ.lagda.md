# The large locale of subtypes

```agda
module foundation.large-locale-of-subtypesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.large-binary-relationsᵉ
open import foundation.large-locale-of-propositionsᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.identity-typesᵉ
open import foundation-core.setsᵉ

open import order-theory.greatest-lower-bounds-large-posetsᵉ
open import order-theory.large-localesᵉ
open import order-theory.large-meet-semilatticesᵉ
open import order-theory.large-posetsᵉ
open import order-theory.large-suplatticesᵉ
open import order-theory.least-upper-bounds-large-posetsᵉ
open import order-theory.powers-of-large-localesᵉ
```

</details>

## Idea

Theᵉ **largeᵉ localeᵉ ofᵉ subtypes**ᵉ ofᵉ aᵉ typeᵉ `A`ᵉ isᵉ theᵉ
[powerᵉ locale](order-theory.powers-of-large-locales.mdᵉ) `Aᵉ → Prop-Large-Locale`.ᵉ

## Definition

```agda
module _
  {l1ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ)
  where

  powerset-Large-Localeᵉ :
    Large-Localeᵉ (λ l2ᵉ → l1ᵉ ⊔ lsuc l2ᵉ) (λ l2ᵉ l3ᵉ → l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ) lzero
  powerset-Large-Localeᵉ = power-Large-Localeᵉ Aᵉ Prop-Large-Localeᵉ

  large-poset-powerset-Large-Localeᵉ :
    Large-Posetᵉ (λ l2ᵉ → l1ᵉ ⊔ lsuc l2ᵉ) (λ l2ᵉ l3ᵉ → l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  large-poset-powerset-Large-Localeᵉ =
    large-poset-Large-Localeᵉ powerset-Large-Localeᵉ

  set-powerset-Large-Localeᵉ : (lᵉ : Level) → Setᵉ (l1ᵉ ⊔ lsuc lᵉ)
  set-powerset-Large-Localeᵉ =
    set-Large-Localeᵉ powerset-Large-Localeᵉ

  type-powerset-Large-Localeᵉ : (lᵉ : Level) → UUᵉ (l1ᵉ ⊔ lsuc lᵉ)
  type-powerset-Large-Localeᵉ =
    type-Large-Localeᵉ powerset-Large-Localeᵉ

  is-set-type-powerset-Large-Localeᵉ :
    {lᵉ : Level} → is-setᵉ (type-powerset-Large-Localeᵉ lᵉ)
  is-set-type-powerset-Large-Localeᵉ =
    is-set-type-Large-Localeᵉ powerset-Large-Localeᵉ

  large-meet-semilattice-powerset-Large-Localeᵉ :
    Large-Meet-Semilatticeᵉ (λ l2ᵉ → l1ᵉ ⊔ lsuc l2ᵉ) (λ l2ᵉ l3ᵉ → l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  large-meet-semilattice-powerset-Large-Localeᵉ =
    large-meet-semilattice-Large-Localeᵉ powerset-Large-Localeᵉ

  large-suplattice-powerset-Large-Localeᵉ :
    Large-Suplatticeᵉ (λ l2ᵉ → l1ᵉ ⊔ lsuc l2ᵉ) (λ l2ᵉ l3ᵉ → l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ) lzero
  large-suplattice-powerset-Large-Localeᵉ =
    large-suplattice-Large-Localeᵉ powerset-Large-Localeᵉ

module _
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  where

  leq-prop-powerset-Large-Localeᵉ :
    Large-Relation-Propᵉ
      ( λ l2ᵉ l3ᵉ → l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
      ( type-powerset-Large-Localeᵉ Aᵉ)
  leq-prop-powerset-Large-Localeᵉ =
    leq-prop-Large-Localeᵉ (powerset-Large-Localeᵉ Aᵉ)

  leq-powerset-Large-Localeᵉ :
    Large-Relationᵉ
      ( λ l2ᵉ l3ᵉ → l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
      ( type-powerset-Large-Localeᵉ Aᵉ)
  leq-powerset-Large-Localeᵉ =
    leq-Large-Localeᵉ (powerset-Large-Localeᵉ Aᵉ)

  is-prop-leq-powerset-Large-Localeᵉ :
    is-prop-Large-Relationᵉ
      ( type-powerset-Large-Localeᵉ Aᵉ)
      ( leq-powerset-Large-Localeᵉ)
  is-prop-leq-powerset-Large-Localeᵉ =
    is-prop-leq-Large-Localeᵉ (powerset-Large-Localeᵉ Aᵉ)

  refl-leq-powerset-Large-Localeᵉ :
    is-reflexive-Large-Relationᵉ
      ( type-powerset-Large-Localeᵉ Aᵉ)
      ( leq-powerset-Large-Localeᵉ)
  refl-leq-powerset-Large-Localeᵉ =
    refl-leq-Large-Localeᵉ (powerset-Large-Localeᵉ Aᵉ)

  antisymmetric-leq-powerset-Large-Localeᵉ :
    is-antisymmetric-Large-Relationᵉ
      ( type-powerset-Large-Localeᵉ Aᵉ)
      ( leq-powerset-Large-Localeᵉ)
  antisymmetric-leq-powerset-Large-Localeᵉ =
    antisymmetric-leq-Large-Localeᵉ (powerset-Large-Localeᵉ Aᵉ)

  transitive-leq-powerset-Large-Localeᵉ :
    is-transitive-Large-Relationᵉ
      ( type-powerset-Large-Localeᵉ Aᵉ)
      ( leq-powerset-Large-Localeᵉ)
  transitive-leq-powerset-Large-Localeᵉ =
    transitive-leq-Large-Localeᵉ (powerset-Large-Localeᵉ Aᵉ)

  has-meets-powerset-Large-Localeᵉ :
    has-meets-Large-Posetᵉ (large-poset-powerset-Large-Localeᵉ Aᵉ)
  has-meets-powerset-Large-Localeᵉ =
    has-meets-Large-Localeᵉ (powerset-Large-Localeᵉ Aᵉ)

  meet-powerset-Large-Localeᵉ :
    {l2ᵉ l3ᵉ : Level} →
    type-powerset-Large-Localeᵉ Aᵉ l2ᵉ →
    type-powerset-Large-Localeᵉ Aᵉ l3ᵉ →
    type-powerset-Large-Localeᵉ Aᵉ (l2ᵉ ⊔ l3ᵉ)
  meet-powerset-Large-Localeᵉ =
    meet-Large-Localeᵉ (powerset-Large-Localeᵉ Aᵉ)

  is-greatest-binary-lower-bound-meet-powerset-Large-Localeᵉ :
    {l2ᵉ l3ᵉ : Level}
    (xᵉ : type-powerset-Large-Localeᵉ Aᵉ l2ᵉ)
    (yᵉ : type-powerset-Large-Localeᵉ Aᵉ l3ᵉ) →
    is-greatest-binary-lower-bound-Large-Posetᵉ
      ( large-poset-powerset-Large-Localeᵉ Aᵉ)
      ( xᵉ)
      ( yᵉ)
      ( meet-powerset-Large-Localeᵉ xᵉ yᵉ)
  is-greatest-binary-lower-bound-meet-powerset-Large-Localeᵉ =
    is-greatest-binary-lower-bound-meet-Large-Localeᵉ (powerset-Large-Localeᵉ Aᵉ)

  is-large-suplattice-powerset-Large-Localeᵉ :
    is-large-suplattice-Large-Posetᵉ lzero (large-poset-powerset-Large-Localeᵉ Aᵉ)
  is-large-suplattice-powerset-Large-Localeᵉ =
    is-large-suplattice-Large-Localeᵉ (powerset-Large-Localeᵉ Aᵉ)

  sup-powerset-Large-Localeᵉ :
    {l2ᵉ l3ᵉ : Level} {Jᵉ : UUᵉ l2ᵉ} (xᵉ : Jᵉ → type-powerset-Large-Localeᵉ Aᵉ l3ᵉ) →
    type-powerset-Large-Localeᵉ Aᵉ (l2ᵉ ⊔ l3ᵉ)
  sup-powerset-Large-Localeᵉ =
    sup-Large-Localeᵉ (powerset-Large-Localeᵉ Aᵉ)

  is-least-upper-bound-sup-powerset-Large-Localeᵉ :
    {l2ᵉ l3ᵉ : Level} {Jᵉ : UUᵉ l2ᵉ} (xᵉ : Jᵉ → type-powerset-Large-Localeᵉ Aᵉ l3ᵉ) →
    is-least-upper-bound-family-of-elements-Large-Posetᵉ
      ( large-poset-powerset-Large-Localeᵉ Aᵉ)
      ( xᵉ)
      ( sup-powerset-Large-Localeᵉ xᵉ)
  is-least-upper-bound-sup-powerset-Large-Localeᵉ =
    is-least-upper-bound-sup-Large-Localeᵉ (powerset-Large-Localeᵉ Aᵉ)

  distributive-meet-sup-powerset-Large-Localeᵉ :
    {l2ᵉ l3ᵉ l4ᵉ : Level}
    (xᵉ : type-powerset-Large-Localeᵉ Aᵉ l2ᵉ)
    {Jᵉ : UUᵉ l3ᵉ} (yᵉ : Jᵉ → type-powerset-Large-Localeᵉ Aᵉ l4ᵉ) →
    meet-powerset-Large-Localeᵉ xᵉ (sup-powerset-Large-Localeᵉ yᵉ) ＝ᵉ
    sup-powerset-Large-Localeᵉ (λ jᵉ → meet-powerset-Large-Localeᵉ xᵉ (yᵉ jᵉ))
  distributive-meet-sup-powerset-Large-Localeᵉ =
    distributive-meet-sup-Large-Localeᵉ (powerset-Large-Localeᵉ Aᵉ)
```