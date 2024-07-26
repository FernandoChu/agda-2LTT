# Large locales

```agda
module order-theory.large-localesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.identity-typesᵉ
open import foundation.large-binary-relationsᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ

open import order-theory.greatest-lower-bounds-large-posetsᵉ
open import order-theory.large-framesᵉ
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

Aᵉ **largeᵉ locale**ᵉ isᵉ aᵉ largeᵉ
[meet-suplattice](order-theory.meet-suplattices.mdᵉ) satisfyingᵉ theᵉ distributiveᵉ
lawᵉ forᵉ meetsᵉ overᵉ suprema.ᵉ

## Definitions

### Large locales

```agda
Large-Localeᵉ :
  (αᵉ : Level → Level) (βᵉ : Level → Level → Level) (γᵉ : Level) → UUωᵉ
Large-Localeᵉ = Large-Frameᵉ

module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level} {γᵉ : Level}
  (Lᵉ : Large-Localeᵉ αᵉ βᵉ γᵉ)
  where

  large-poset-Large-Localeᵉ : Large-Posetᵉ αᵉ βᵉ
  large-poset-Large-Localeᵉ = large-poset-Large-Frameᵉ Lᵉ

  large-preorder-Large-Localeᵉ : Large-Preorderᵉ αᵉ βᵉ
  large-preorder-Large-Localeᵉ =
    large-preorder-Large-Posetᵉ large-poset-Large-Localeᵉ

  set-Large-Localeᵉ : (lᵉ : Level) → Setᵉ (αᵉ lᵉ)
  set-Large-Localeᵉ = set-Large-Frameᵉ Lᵉ

  type-Large-Localeᵉ : (lᵉ : Level) → UUᵉ (αᵉ lᵉ)
  type-Large-Localeᵉ = type-Large-Frameᵉ Lᵉ

  is-set-type-Large-Localeᵉ : {lᵉ : Level} → is-setᵉ (type-Large-Localeᵉ lᵉ)
  is-set-type-Large-Localeᵉ = is-set-type-Large-Frameᵉ Lᵉ

  leq-prop-Large-Localeᵉ : Large-Relation-Propᵉ βᵉ type-Large-Localeᵉ
  leq-prop-Large-Localeᵉ = leq-prop-Large-Frameᵉ Lᵉ

  leq-Large-Localeᵉ : Large-Relationᵉ βᵉ type-Large-Localeᵉ
  leq-Large-Localeᵉ = leq-Large-Frameᵉ Lᵉ

  is-prop-leq-Large-Localeᵉ :
    is-prop-Large-Relationᵉ type-Large-Localeᵉ leq-Large-Localeᵉ
  is-prop-leq-Large-Localeᵉ = is-prop-leq-Large-Frameᵉ Lᵉ

  leq-eq-Large-Localeᵉ :
    {l1ᵉ : Level} {xᵉ yᵉ : type-Large-Localeᵉ l1ᵉ} →
    (xᵉ ＝ᵉ yᵉ) → leq-Large-Localeᵉ xᵉ yᵉ
  leq-eq-Large-Localeᵉ = leq-eq-Large-Frameᵉ Lᵉ

  refl-leq-Large-Localeᵉ :
    is-reflexive-Large-Relationᵉ type-Large-Localeᵉ leq-Large-Localeᵉ
  refl-leq-Large-Localeᵉ = refl-leq-Large-Frameᵉ Lᵉ

  antisymmetric-leq-Large-Localeᵉ :
    is-antisymmetric-Large-Relationᵉ type-Large-Localeᵉ leq-Large-Localeᵉ
  antisymmetric-leq-Large-Localeᵉ =
    antisymmetric-leq-Large-Frameᵉ Lᵉ

  transitive-leq-Large-Localeᵉ :
    is-transitive-Large-Relationᵉ type-Large-Localeᵉ leq-Large-Localeᵉ
  transitive-leq-Large-Localeᵉ =
    transitive-leq-Large-Frameᵉ Lᵉ

  is-large-meet-semilattice-Large-Localeᵉ :
    is-large-meet-semilattice-Large-Posetᵉ large-poset-Large-Localeᵉ
  is-large-meet-semilattice-Large-Localeᵉ =
    is-large-meet-semilattice-Large-Frameᵉ Lᵉ

  large-meet-semilattice-Large-Localeᵉ : Large-Meet-Semilatticeᵉ αᵉ βᵉ
  large-meet-semilattice-Large-Localeᵉ =
    large-meet-semilattice-Large-Frameᵉ Lᵉ

  has-meets-Large-Localeᵉ : has-meets-Large-Posetᵉ large-poset-Large-Localeᵉ
  has-meets-Large-Localeᵉ =
    has-meets-Large-Meet-Semilatticeᵉ large-meet-semilattice-Large-Localeᵉ

  meet-Large-Localeᵉ :
    {l1ᵉ l2ᵉ : Level} →
    type-Large-Localeᵉ l1ᵉ → type-Large-Localeᵉ l2ᵉ → type-Large-Localeᵉ (l1ᵉ ⊔ l2ᵉ)
  meet-Large-Localeᵉ = meet-Large-Frameᵉ Lᵉ

  is-greatest-binary-lower-bound-meet-Large-Localeᵉ :
    {l1ᵉ l2ᵉ : Level} →
    (xᵉ : type-Large-Localeᵉ l1ᵉ) (yᵉ : type-Large-Localeᵉ l2ᵉ) →
    is-greatest-binary-lower-bound-Large-Posetᵉ
      ( large-poset-Large-Localeᵉ)
      ( xᵉ)
      ( yᵉ)
      ( meet-Large-Localeᵉ xᵉ yᵉ)
  is-greatest-binary-lower-bound-meet-Large-Localeᵉ =
    is-greatest-binary-lower-bound-meet-Large-Frameᵉ Lᵉ

  ap-meet-Large-Localeᵉ :
    {l1ᵉ l2ᵉ : Level} →
    {xᵉ x'ᵉ : type-Large-Localeᵉ l1ᵉ} {yᵉ y'ᵉ : type-Large-Localeᵉ l2ᵉ} →
    (xᵉ ＝ᵉ x'ᵉ) → (yᵉ ＝ᵉ y'ᵉ) → (meet-Large-Localeᵉ xᵉ yᵉ ＝ᵉ meet-Large-Localeᵉ x'ᵉ y'ᵉ)
  ap-meet-Large-Localeᵉ = ap-meet-Large-Frameᵉ Lᵉ

  has-top-element-Large-Localeᵉ :
    has-top-element-Large-Posetᵉ large-poset-Large-Localeᵉ
  has-top-element-Large-Localeᵉ =
    has-top-element-Large-Frameᵉ Lᵉ

  top-Large-Localeᵉ : type-Large-Localeᵉ lzero
  top-Large-Localeᵉ = top-Large-Frameᵉ Lᵉ

  is-top-element-top-Large-Localeᵉ :
    {l1ᵉ : Level} (xᵉ : type-Large-Localeᵉ l1ᵉ) →
    leq-Large-Localeᵉ xᵉ top-Large-Localeᵉ
  is-top-element-top-Large-Localeᵉ =
    is-top-element-top-Large-Frameᵉ Lᵉ

  large-suplattice-Large-Localeᵉ : Large-Suplatticeᵉ αᵉ βᵉ γᵉ
  large-suplattice-Large-Localeᵉ = large-suplattice-Large-Frameᵉ Lᵉ

  is-large-suplattice-Large-Localeᵉ :
    is-large-suplattice-Large-Posetᵉ γᵉ large-poset-Large-Localeᵉ
  is-large-suplattice-Large-Localeᵉ = is-large-suplattice-Large-Frameᵉ Lᵉ

  sup-Large-Localeᵉ :
    {l1ᵉ l2ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ} →
    (Iᵉ → type-Large-Localeᵉ l2ᵉ) → type-Large-Localeᵉ (γᵉ ⊔ l1ᵉ ⊔ l2ᵉ)
  sup-Large-Localeᵉ = sup-Large-Frameᵉ Lᵉ

  is-least-upper-bound-sup-Large-Localeᵉ :
    {l1ᵉ l2ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ} (xᵉ : Iᵉ → type-Large-Localeᵉ l2ᵉ) →
    is-least-upper-bound-family-of-elements-Large-Posetᵉ
      ( large-poset-Large-Localeᵉ)
      ( xᵉ)
      ( sup-Large-Localeᵉ xᵉ)
  is-least-upper-bound-sup-Large-Localeᵉ =
    is-least-upper-bound-sup-Large-Frameᵉ Lᵉ

  is-upper-bound-sup-Large-Localeᵉ :
    {l1ᵉ l2ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ} (xᵉ : Iᵉ → type-Large-Localeᵉ l2ᵉ) →
    is-upper-bound-family-of-elements-Large-Posetᵉ
      ( large-poset-Large-Localeᵉ)
      ( xᵉ)
      ( sup-Large-Localeᵉ xᵉ)
  is-upper-bound-sup-Large-Localeᵉ =
    is-upper-bound-sup-Large-Frameᵉ Lᵉ

  distributive-meet-sup-Large-Localeᵉ :
    {l1ᵉ l2ᵉ l3ᵉ : Level}
    (xᵉ : type-Large-Posetᵉ large-poset-Large-Localeᵉ l1ᵉ)
    {Iᵉ : UUᵉ l2ᵉ} (yᵉ : Iᵉ → type-Large-Posetᵉ large-poset-Large-Localeᵉ l3ᵉ) →
    meet-Large-Localeᵉ xᵉ (sup-Large-Localeᵉ yᵉ) ＝ᵉ
    sup-Large-Localeᵉ (λ iᵉ → meet-Large-Localeᵉ xᵉ (yᵉ iᵉ))
  distributive-meet-sup-Large-Localeᵉ =
    distributive-meet-sup-Large-Frameᵉ Lᵉ
```

## Properties

### Small constructions from large locales

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level} {γᵉ : Level}
  (Lᵉ : Large-Localeᵉ αᵉ βᵉ γᵉ)
  where

  preorder-Large-Localeᵉ : (lᵉ : Level) → Preorderᵉ (αᵉ lᵉ) (βᵉ lᵉ lᵉ)
  preorder-Large-Localeᵉ = preorder-Large-Frameᵉ Lᵉ

  poset-Large-Localeᵉ : (lᵉ : Level) → Posetᵉ (αᵉ lᵉ) (βᵉ lᵉ lᵉ)
  poset-Large-Localeᵉ = poset-Large-Frameᵉ Lᵉ

  is-suplattice-poset-Large-Localeᵉ :
    (l1ᵉ l2ᵉ : Level) → is-suplattice-Posetᵉ l1ᵉ (poset-Large-Localeᵉ (γᵉ ⊔ l1ᵉ ⊔ l2ᵉ))
  is-suplattice-poset-Large-Localeᵉ = is-suplattice-poset-Large-Frameᵉ Lᵉ

  suplattice-Large-Localeᵉ :
    (l1ᵉ l2ᵉ : Level) →
    Suplatticeᵉ (αᵉ (γᵉ ⊔ l1ᵉ ⊔ l2ᵉ)) (βᵉ (γᵉ ⊔ l1ᵉ ⊔ l2ᵉ) (γᵉ ⊔ l1ᵉ ⊔ l2ᵉ)) l1ᵉ
  suplattice-Large-Localeᵉ = suplattice-Large-Frameᵉ Lᵉ

  is-meet-semilattice-poset-Large-Localeᵉ :
    (lᵉ : Level) → is-meet-semilattice-Posetᵉ (poset-Large-Localeᵉ lᵉ)
  is-meet-semilattice-poset-Large-Localeᵉ =
    is-meet-semilattice-poset-Large-Frameᵉ Lᵉ

  order-theoretic-meet-semilattice-Large-Localeᵉ :
    (lᵉ : Level) → Order-Theoretic-Meet-Semilatticeᵉ (αᵉ lᵉ) (βᵉ lᵉ lᵉ)
  order-theoretic-meet-semilattice-Large-Localeᵉ =
    order-theoretic-meet-semilattice-Large-Frameᵉ Lᵉ

  meet-semilattice-Large-Localeᵉ : (lᵉ : Level) → Meet-Semilatticeᵉ (αᵉ lᵉ)
  meet-semilattice-Large-Localeᵉ = meet-semilattice-Large-Frameᵉ Lᵉ
```