# Dependent products of large frames

```agda
module order-theory.dependent-products-large-framesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.function-extensionalityᵉ
open import foundation.identity-typesᵉ
open import foundation.large-binary-relationsᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ

open import order-theory.dependent-products-large-meet-semilatticesᵉ
open import order-theory.dependent-products-large-posetsᵉ
open import order-theory.dependent-products-large-suplatticesᵉ
open import order-theory.greatest-lower-bounds-large-posetsᵉ
open import order-theory.large-framesᵉ
open import order-theory.large-meet-semilatticesᵉ
open import order-theory.large-posetsᵉ
open import order-theory.large-suplatticesᵉ
open import order-theory.least-upper-bounds-large-posetsᵉ
open import order-theory.top-elements-large-posetsᵉ
```

</details>

Givenᵉ aᵉ familyᵉ `Lᵉ : Iᵉ → Large-Frameᵉ αᵉ β`ᵉ ofᵉ largeᵉ framesᵉ indexedᵉ byᵉ aᵉ typeᵉ
`Iᵉ : UUᵉ l`,ᵉ theᵉ productᵉ ofᵉ theᵉ largeᵉ frameᵉ `Lᵉ i`ᵉ isᵉ againᵉ aᵉ largeᵉ frame.ᵉ

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level} {γᵉ : Level}
  {l1ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ} (Lᵉ : Iᵉ → Large-Frameᵉ αᵉ βᵉ γᵉ)
  where

  large-poset-Π-Large-Frameᵉ :
    Large-Posetᵉ (λ l2ᵉ → αᵉ l2ᵉ ⊔ l1ᵉ) (λ l2ᵉ l3ᵉ → βᵉ l2ᵉ l3ᵉ ⊔ l1ᵉ)
  large-poset-Π-Large-Frameᵉ =
    Π-Large-Posetᵉ (λ iᵉ → large-poset-Large-Frameᵉ (Lᵉ iᵉ))

  large-meet-semilattice-Π-Large-Frameᵉ :
    Large-Meet-Semilatticeᵉ (λ l2ᵉ → αᵉ l2ᵉ ⊔ l1ᵉ) (λ l2ᵉ l3ᵉ → βᵉ l2ᵉ l3ᵉ ⊔ l1ᵉ)
  large-meet-semilattice-Π-Large-Frameᵉ =
    Π-Large-Meet-Semilatticeᵉ (λ iᵉ → large-meet-semilattice-Large-Frameᵉ (Lᵉ iᵉ))

  has-meets-Π-Large-Frameᵉ :
    has-meets-Large-Posetᵉ large-poset-Π-Large-Frameᵉ
  has-meets-Π-Large-Frameᵉ =
    has-meets-Π-Large-Posetᵉ
      ( λ iᵉ → large-poset-Large-Frameᵉ (Lᵉ iᵉ))
      ( λ iᵉ → has-meets-Large-Frameᵉ (Lᵉ iᵉ))

  large-suplattice-Π-Large-Frameᵉ :
    Large-Suplatticeᵉ (λ l2ᵉ → αᵉ l2ᵉ ⊔ l1ᵉ) (λ l2ᵉ l3ᵉ → βᵉ l2ᵉ l3ᵉ ⊔ l1ᵉ) γᵉ
  large-suplattice-Π-Large-Frameᵉ =
    Π-Large-Suplatticeᵉ (λ iᵉ → large-suplattice-Large-Frameᵉ (Lᵉ iᵉ))

  is-large-suplattice-Π-Large-Frameᵉ :
    is-large-suplattice-Large-Posetᵉ γᵉ large-poset-Π-Large-Frameᵉ
  is-large-suplattice-Π-Large-Frameᵉ =
    is-large-suplattice-Π-Large-Suplatticeᵉ
      ( λ iᵉ → large-suplattice-Large-Frameᵉ (Lᵉ iᵉ))

  set-Π-Large-Frameᵉ : (lᵉ : Level) → Setᵉ (αᵉ lᵉ ⊔ l1ᵉ)
  set-Π-Large-Frameᵉ = set-Large-Posetᵉ large-poset-Π-Large-Frameᵉ

  type-Π-Large-Frameᵉ : (lᵉ : Level) → UUᵉ (αᵉ lᵉ ⊔ l1ᵉ)
  type-Π-Large-Frameᵉ = type-Large-Posetᵉ large-poset-Π-Large-Frameᵉ

  is-set-type-Π-Large-Frameᵉ : {lᵉ : Level} → is-setᵉ (type-Π-Large-Frameᵉ lᵉ)
  is-set-type-Π-Large-Frameᵉ =
    is-set-type-Large-Posetᵉ large-poset-Π-Large-Frameᵉ

  leq-prop-Π-Large-Frameᵉ :
    Large-Relation-Propᵉ
      ( λ l2ᵉ l3ᵉ → βᵉ l2ᵉ l3ᵉ ⊔ l1ᵉ)
      ( type-Π-Large-Frameᵉ)
  leq-prop-Π-Large-Frameᵉ =
    leq-prop-Large-Posetᵉ large-poset-Π-Large-Frameᵉ

  leq-Π-Large-Frameᵉ :
    Large-Relationᵉ
      ( λ l2ᵉ l3ᵉ → βᵉ l2ᵉ l3ᵉ ⊔ l1ᵉ)
      ( type-Π-Large-Frameᵉ)
  leq-Π-Large-Frameᵉ = leq-Large-Posetᵉ large-poset-Π-Large-Frameᵉ

  is-prop-leq-Π-Large-Frameᵉ :
    is-prop-Large-Relationᵉ type-Π-Large-Frameᵉ leq-Π-Large-Frameᵉ
  is-prop-leq-Π-Large-Frameᵉ =
    is-prop-leq-Large-Posetᵉ large-poset-Π-Large-Frameᵉ

  refl-leq-Π-Large-Frameᵉ :
    is-reflexive-Large-Relationᵉ type-Π-Large-Frameᵉ leq-Π-Large-Frameᵉ
  refl-leq-Π-Large-Frameᵉ = refl-leq-Large-Posetᵉ large-poset-Π-Large-Frameᵉ

  antisymmetric-leq-Π-Large-Frameᵉ :
    is-antisymmetric-Large-Relationᵉ type-Π-Large-Frameᵉ leq-Π-Large-Frameᵉ
  antisymmetric-leq-Π-Large-Frameᵉ =
    antisymmetric-leq-Large-Posetᵉ large-poset-Π-Large-Frameᵉ

  transitive-leq-Π-Large-Frameᵉ :
    is-transitive-Large-Relationᵉ type-Π-Large-Frameᵉ leq-Π-Large-Frameᵉ
  transitive-leq-Π-Large-Frameᵉ =
    transitive-leq-Large-Posetᵉ large-poset-Π-Large-Frameᵉ

  meet-Π-Large-Frameᵉ :
    {l2ᵉ l3ᵉ : Level} →
    type-Π-Large-Frameᵉ l2ᵉ →
    type-Π-Large-Frameᵉ l3ᵉ →
    type-Π-Large-Frameᵉ (l2ᵉ ⊔ l3ᵉ)
  meet-Π-Large-Frameᵉ =
    meet-has-meets-Large-Posetᵉ has-meets-Π-Large-Frameᵉ

  is-greatest-binary-lower-bound-meet-Π-Large-Frameᵉ :
    {l2ᵉ l3ᵉ : Level}
    (xᵉ : type-Π-Large-Frameᵉ l2ᵉ)
    (yᵉ : type-Π-Large-Frameᵉ l3ᵉ) →
    is-greatest-binary-lower-bound-Large-Posetᵉ
      ( large-poset-Π-Large-Frameᵉ)
      ( xᵉ)
      ( yᵉ)
      ( meet-Π-Large-Frameᵉ xᵉ yᵉ)
  is-greatest-binary-lower-bound-meet-Π-Large-Frameᵉ =
    is-greatest-binary-lower-bound-meet-has-meets-Large-Posetᵉ
      has-meets-Π-Large-Frameᵉ

  top-Π-Large-Frameᵉ : type-Π-Large-Frameᵉ lzero
  top-Π-Large-Frameᵉ =
    top-Large-Meet-Semilatticeᵉ large-meet-semilattice-Π-Large-Frameᵉ

  is-top-element-top-Π-Large-Frameᵉ :
    {l1ᵉ : Level} (xᵉ : type-Π-Large-Frameᵉ l1ᵉ) →
    leq-Π-Large-Frameᵉ xᵉ top-Π-Large-Frameᵉ
  is-top-element-top-Π-Large-Frameᵉ =
    is-top-element-top-Large-Meet-Semilatticeᵉ
      large-meet-semilattice-Π-Large-Frameᵉ

  has-top-element-Π-Large-Frameᵉ :
    has-top-element-Large-Posetᵉ large-poset-Π-Large-Frameᵉ
  has-top-element-Π-Large-Frameᵉ =
    has-top-element-Large-Meet-Semilatticeᵉ
      large-meet-semilattice-Π-Large-Frameᵉ

  is-large-meet-semilattice-Π-Large-Frameᵉ :
    is-large-meet-semilattice-Large-Posetᵉ large-poset-Π-Large-Frameᵉ
  is-large-meet-semilattice-Π-Large-Frameᵉ =
    is-large-meet-semilattice-Large-Meet-Semilatticeᵉ
      large-meet-semilattice-Π-Large-Frameᵉ

  sup-Π-Large-Frameᵉ :
    {l2ᵉ l3ᵉ : Level} {Jᵉ : UUᵉ l2ᵉ} (xᵉ : Jᵉ → type-Π-Large-Frameᵉ l3ᵉ) →
    type-Π-Large-Frameᵉ (γᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  sup-Π-Large-Frameᵉ =
    sup-is-large-suplattice-Large-Posetᵉ γᵉ
      ( large-poset-Π-Large-Frameᵉ)
      ( is-large-suplattice-Π-Large-Frameᵉ)

  is-least-upper-bound-sup-Π-Large-Frameᵉ :
    {l2ᵉ l3ᵉ : Level} {Jᵉ : UUᵉ l2ᵉ} (xᵉ : Jᵉ → type-Π-Large-Frameᵉ l3ᵉ) →
    is-least-upper-bound-family-of-elements-Large-Posetᵉ
      ( large-poset-Π-Large-Frameᵉ)
      ( xᵉ)
      ( sup-Π-Large-Frameᵉ xᵉ)
  is-least-upper-bound-sup-Π-Large-Frameᵉ =
    is-least-upper-bound-sup-is-large-suplattice-Large-Posetᵉ γᵉ
      ( large-poset-Π-Large-Frameᵉ)
      ( is-large-suplattice-Π-Large-Frameᵉ)

  distributive-meet-sup-Π-Large-Frameᵉ :
    {l2ᵉ l3ᵉ l4ᵉ : Level}
    (xᵉ : type-Π-Large-Frameᵉ l2ᵉ)
    {Jᵉ : UUᵉ l3ᵉ} (yᵉ : Jᵉ → type-Π-Large-Frameᵉ l4ᵉ) →
    meet-Π-Large-Frameᵉ xᵉ (sup-Π-Large-Frameᵉ yᵉ) ＝ᵉ
    sup-Π-Large-Frameᵉ (λ jᵉ → meet-Π-Large-Frameᵉ xᵉ (yᵉ jᵉ))
  distributive-meet-sup-Π-Large-Frameᵉ xᵉ yᵉ =
    eq-htpyᵉ
      ( λ iᵉ → distributive-meet-sup-Large-Frameᵉ (Lᵉ iᵉ) (xᵉ iᵉ) (λ jᵉ → yᵉ jᵉ iᵉ))

  Π-Large-Frameᵉ : Large-Frameᵉ (λ l2ᵉ → αᵉ l2ᵉ ⊔ l1ᵉ) (λ l2ᵉ l3ᵉ → βᵉ l2ᵉ l3ᵉ ⊔ l1ᵉ) γᵉ
  large-poset-Large-Frameᵉ Π-Large-Frameᵉ =
    large-poset-Π-Large-Frameᵉ
  is-large-meet-semilattice-Large-Frameᵉ Π-Large-Frameᵉ =
    is-large-meet-semilattice-Π-Large-Frameᵉ
  is-large-suplattice-Large-Frameᵉ Π-Large-Frameᵉ =
    is-large-suplattice-Π-Large-Frameᵉ
  distributive-meet-sup-Large-Frameᵉ Π-Large-Frameᵉ =
    distributive-meet-sup-Π-Large-Frameᵉ
```