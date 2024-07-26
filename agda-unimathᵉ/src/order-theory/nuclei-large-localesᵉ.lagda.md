# Nuclei on large locales

```agda
module order-theory.nuclei-large-localesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.function-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.large-binary-relationsᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.subtypesᵉ
open import foundation.universe-levelsᵉ

open import order-theory.homomorphisms-large-meet-semilatticesᵉ
open import order-theory.large-framesᵉ
open import order-theory.large-localesᵉ
open import order-theory.large-meet-semilatticesᵉ
open import order-theory.large-meet-subsemilatticesᵉ
open import order-theory.large-posetsᵉ
open import order-theory.large-subposetsᵉ
open import order-theory.large-subpreordersᵉ
open import order-theory.large-suplatticesᵉ
open import order-theory.least-upper-bounds-large-posetsᵉ
```

</details>

## Idea

Aᵉ **nucleus**ᵉ onᵉ aᵉ [largeᵉ locale](order-theory.large-locales.mdᵉ) `L`ᵉ isᵉ anᵉ orderᵉ
preservingᵉ mapᵉ `jᵉ : hom-Large-Posetᵉ (λ lᵉ → lᵉ) Lᵉ L`ᵉ suchᵉ thatᵉ `j`ᵉ preservesᵉ meetsᵉ
andᵉ isᵉ inflationaryᵉ andᵉ idempotent.ᵉ

## Definitions

### Nuclei on large locales

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level} {γᵉ : Level}
  (Lᵉ : Large-Localeᵉ αᵉ βᵉ γᵉ)
  where

  record
    nucleus-Large-Localeᵉ : UUωᵉ
    where
    field
      hom-large-meet-semilattice-nucleus-Large-Localeᵉ :
        hom-Large-Meet-Semilatticeᵉ
          ( large-meet-semilattice-Large-Localeᵉ Lᵉ)
          ( large-meet-semilattice-Large-Localeᵉ Lᵉ)
      is-inflationary-nucleus-Large-Localeᵉ :
        {l1ᵉ : Level} (xᵉ : type-Large-Localeᵉ Lᵉ l1ᵉ) →
        leq-Large-Localeᵉ Lᵉ xᵉ
          ( map-hom-Large-Meet-Semilatticeᵉ
            ( large-meet-semilattice-Large-Localeᵉ Lᵉ)
            ( large-meet-semilattice-Large-Localeᵉ Lᵉ)
            ( hom-large-meet-semilattice-nucleus-Large-Localeᵉ)
            ( xᵉ))
      is-idempotent-nucleus-Large-Localeᵉ :
        {l1ᵉ : Level} (xᵉ : type-Large-Localeᵉ Lᵉ l1ᵉ) →
        map-hom-Large-Meet-Semilatticeᵉ
          ( large-meet-semilattice-Large-Localeᵉ Lᵉ)
          ( large-meet-semilattice-Large-Localeᵉ Lᵉ)
          ( hom-large-meet-semilattice-nucleus-Large-Localeᵉ)
          ( map-hom-Large-Meet-Semilatticeᵉ
            ( large-meet-semilattice-Large-Localeᵉ Lᵉ)
            ( large-meet-semilattice-Large-Localeᵉ Lᵉ)
            ( hom-large-meet-semilattice-nucleus-Large-Localeᵉ)
            ( xᵉ)) ＝ᵉ
        map-hom-Large-Meet-Semilatticeᵉ
          ( large-meet-semilattice-Large-Localeᵉ Lᵉ)
          ( large-meet-semilattice-Large-Localeᵉ Lᵉ)
          ( hom-large-meet-semilattice-nucleus-Large-Localeᵉ)
          ( xᵉ)

  open nucleus-Large-Localeᵉ public

  module _
    (jᵉ : nucleus-Large-Localeᵉ)
    where

    map-nucleus-Large-Localeᵉ :
      {l1ᵉ : Level} → type-Large-Localeᵉ Lᵉ l1ᵉ → type-Large-Localeᵉ Lᵉ l1ᵉ
    map-nucleus-Large-Localeᵉ =
      map-hom-Large-Meet-Semilatticeᵉ
        ( large-meet-semilattice-Large-Localeᵉ Lᵉ)
        ( large-meet-semilattice-Large-Localeᵉ Lᵉ)
        ( hom-large-meet-semilattice-nucleus-Large-Localeᵉ jᵉ)

    preserves-order-nucleus-Large-Localeᵉ :
      {l1ᵉ l2ᵉ : Level}
      (xᵉ : type-Large-Localeᵉ Lᵉ l1ᵉ)
      (yᵉ : type-Large-Localeᵉ Lᵉ l2ᵉ) →
      leq-Large-Localeᵉ Lᵉ xᵉ yᵉ →
      leq-Large-Localeᵉ Lᵉ
        ( map-nucleus-Large-Localeᵉ xᵉ)
        ( map-nucleus-Large-Localeᵉ yᵉ)
    preserves-order-nucleus-Large-Localeᵉ =
      preserves-order-hom-Large-Meet-Semilatticeᵉ
        ( large-meet-semilattice-Large-Localeᵉ Lᵉ)
        ( large-meet-semilattice-Large-Localeᵉ Lᵉ)
        ( hom-large-meet-semilattice-nucleus-Large-Localeᵉ jᵉ)

    preserves-meets-nucleus-Large-Localeᵉ :
      {l1ᵉ l2ᵉ : Level}
      (xᵉ : type-Large-Localeᵉ Lᵉ l1ᵉ)
      (yᵉ : type-Large-Localeᵉ Lᵉ l2ᵉ) →
      map-nucleus-Large-Localeᵉ (meet-Large-Localeᵉ Lᵉ xᵉ yᵉ) ＝ᵉ
      meet-Large-Localeᵉ Lᵉ
        ( map-nucleus-Large-Localeᵉ xᵉ)
        ( map-nucleus-Large-Localeᵉ yᵉ)
    preserves-meets-nucleus-Large-Localeᵉ =
      preserves-meets-hom-Large-Meet-Semilatticeᵉ
        ( hom-large-meet-semilattice-nucleus-Large-Localeᵉ jᵉ)

    preserves-top-nucleus-Large-Localeᵉ :
      map-nucleus-Large-Localeᵉ (top-Large-Localeᵉ Lᵉ) ＝ᵉ top-Large-Localeᵉ Lᵉ
    preserves-top-nucleus-Large-Localeᵉ =
      preserves-top-hom-Large-Meet-Semilatticeᵉ
        ( hom-large-meet-semilattice-nucleus-Large-Localeᵉ jᵉ)
```

### The large locale of `j`-closed elements of a nucleus

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level} {γᵉ : Level}
  (Lᵉ : Large-Localeᵉ αᵉ βᵉ γᵉ) (jᵉ : nucleus-Large-Localeᵉ Lᵉ)
  where

  large-subpreorder-nucleus-Large-Localeᵉ :
    Large-Subpreorderᵉ αᵉ (large-preorder-Large-Localeᵉ Lᵉ)
  large-subpreorder-nucleus-Large-Localeᵉ {l1ᵉ} xᵉ =
    Id-Propᵉ (set-Large-Localeᵉ Lᵉ l1ᵉ) (map-nucleus-Large-Localeᵉ Lᵉ jᵉ xᵉ) xᵉ

  is-closed-element-nucleus-Large-Localeᵉ :
    {l1ᵉ : Level} → type-Large-Localeᵉ Lᵉ l1ᵉ → UUᵉ (αᵉ l1ᵉ)
  is-closed-element-nucleus-Large-Localeᵉ =
    is-in-Large-Subpreorderᵉ
      ( large-preorder-Large-Localeᵉ Lᵉ)
      ( large-subpreorder-nucleus-Large-Localeᵉ)

  is-prop-is-closed-element-nucleus-Large-Localeᵉ :
    {l1ᵉ : Level} (xᵉ : type-Large-Localeᵉ Lᵉ l1ᵉ) →
    is-propᵉ (is-closed-element-nucleus-Large-Localeᵉ xᵉ)
  is-prop-is-closed-element-nucleus-Large-Localeᵉ =
    is-prop-is-in-Large-Subpreorderᵉ
      ( large-preorder-Large-Localeᵉ Lᵉ)
      ( large-subpreorder-nucleus-Large-Localeᵉ)

  is-closed-element-leq-nucleus-Large-Localeᵉ :
    {l1ᵉ : Level} (xᵉ : type-Large-Localeᵉ Lᵉ l1ᵉ) →
    leq-Large-Localeᵉ Lᵉ (map-nucleus-Large-Localeᵉ Lᵉ jᵉ xᵉ) xᵉ →
    is-closed-element-nucleus-Large-Localeᵉ xᵉ
  is-closed-element-leq-nucleus-Large-Localeᵉ xᵉ Hᵉ =
    antisymmetric-leq-Large-Localeᵉ Lᵉ
      ( map-nucleus-Large-Localeᵉ Lᵉ jᵉ xᵉ)
      ( xᵉ)
      ( Hᵉ)
      (is-inflationary-nucleus-Large-Localeᵉ jᵉ xᵉ)

  closed-element-nucleus-Large-Localeᵉ :
    (l1ᵉ : Level) → UUᵉ (αᵉ l1ᵉ)
  closed-element-nucleus-Large-Localeᵉ =
    type-Large-Subpreorderᵉ
      ( large-preorder-Large-Localeᵉ Lᵉ)
      ( large-subpreorder-nucleus-Large-Localeᵉ)

  is-closed-under-sim-nucleus-Large-Localeᵉ :
    {l1ᵉ l2ᵉ : Level}
    (xᵉ : type-Large-Localeᵉ Lᵉ l1ᵉ)
    (yᵉ : type-Large-Localeᵉ Lᵉ l2ᵉ) →
    leq-Large-Localeᵉ Lᵉ xᵉ yᵉ → leq-Large-Localeᵉ Lᵉ yᵉ xᵉ →
    is-closed-element-nucleus-Large-Localeᵉ xᵉ →
    is-closed-element-nucleus-Large-Localeᵉ yᵉ
  is-closed-under-sim-nucleus-Large-Localeᵉ xᵉ yᵉ Hᵉ Kᵉ cᵉ =
    is-closed-element-leq-nucleus-Large-Localeᵉ yᵉ
      ( transitive-leq-Large-Localeᵉ Lᵉ
        ( map-nucleus-Large-Localeᵉ Lᵉ jᵉ yᵉ)
        ( map-nucleus-Large-Localeᵉ Lᵉ jᵉ xᵉ)
        ( yᵉ)
        ( transitive-leq-Large-Localeᵉ Lᵉ
          ( map-nucleus-Large-Localeᵉ Lᵉ jᵉ xᵉ)
          ( xᵉ)
          ( yᵉ)
          ( Hᵉ)
          ( leq-eq-Large-Localeᵉ Lᵉ cᵉ))
        ( preserves-order-nucleus-Large-Localeᵉ Lᵉ jᵉ yᵉ xᵉ Kᵉ))

  large-subposet-nucleus-Large-Localeᵉ :
    Large-Subposetᵉ αᵉ (large-poset-Large-Localeᵉ Lᵉ)
  large-subpreorder-Large-Subposetᵉ
    large-subposet-nucleus-Large-Localeᵉ =
    large-subpreorder-nucleus-Large-Localeᵉ
  is-closed-under-sim-Large-Subposetᵉ
    large-subposet-nucleus-Large-Localeᵉ =
    is-closed-under-sim-nucleus-Large-Localeᵉ

  large-poset-nucleus-Large-Localeᵉ :
    Large-Posetᵉ αᵉ βᵉ
  large-poset-nucleus-Large-Localeᵉ =
    large-poset-Large-Subposetᵉ
      ( large-poset-Large-Localeᵉ Lᵉ)
      ( large-subposet-nucleus-Large-Localeᵉ)

  leq-prop-closed-element-nucleus-Large-Localeᵉ :
    Large-Relation-Propᵉ βᵉ closed-element-nucleus-Large-Localeᵉ
  leq-prop-closed-element-nucleus-Large-Localeᵉ =
    leq-prop-Large-Subposetᵉ
      ( large-poset-Large-Localeᵉ Lᵉ)
      ( large-subposet-nucleus-Large-Localeᵉ)

  leq-closed-element-nucleus-Large-Localeᵉ :
    Large-Relationᵉ βᵉ closed-element-nucleus-Large-Localeᵉ
  leq-closed-element-nucleus-Large-Localeᵉ =
    leq-Large-Subposetᵉ
      ( large-poset-Large-Localeᵉ Lᵉ)
      ( large-subposet-nucleus-Large-Localeᵉ)

  is-prop-leq-closed-element-nucleus-Large-Localeᵉ :
    is-prop-Large-Relationᵉ
      ( closed-element-nucleus-Large-Localeᵉ)
      ( leq-closed-element-nucleus-Large-Localeᵉ)
  is-prop-leq-closed-element-nucleus-Large-Localeᵉ =
    is-prop-leq-Large-Subposetᵉ
      ( large-poset-Large-Localeᵉ Lᵉ)
      ( large-subposet-nucleus-Large-Localeᵉ)

  refl-leq-closed-element-nucleus-Large-Localeᵉ :
    is-reflexive-Large-Relationᵉ
      ( closed-element-nucleus-Large-Localeᵉ)
      ( leq-closed-element-nucleus-Large-Localeᵉ)
  refl-leq-closed-element-nucleus-Large-Localeᵉ =
    refl-leq-Large-Subposetᵉ
      ( large-poset-Large-Localeᵉ Lᵉ)
      ( large-subposet-nucleus-Large-Localeᵉ)

  antisymmetric-leq-closed-element-nucleus-Large-Localeᵉ :
    is-antisymmetric-Large-Relationᵉ
      ( closed-element-nucleus-Large-Localeᵉ)
      ( leq-closed-element-nucleus-Large-Localeᵉ)
  antisymmetric-leq-closed-element-nucleus-Large-Localeᵉ =
    antisymmetric-leq-Large-Subposetᵉ
      ( large-poset-Large-Localeᵉ Lᵉ)
      ( large-subposet-nucleus-Large-Localeᵉ)

  transitive-leq-closed-element-nucleus-Large-Localeᵉ :
    is-transitive-Large-Relationᵉ
      ( closed-element-nucleus-Large-Localeᵉ)
      ( leq-closed-element-nucleus-Large-Localeᵉ)
  transitive-leq-closed-element-nucleus-Large-Localeᵉ =
    transitive-leq-Large-Subposetᵉ
      ( large-poset-Large-Localeᵉ Lᵉ)
      ( large-subposet-nucleus-Large-Localeᵉ)

  is-closed-under-meets-large-subposet-nucleus-Large-Localeᵉ :
    is-closed-under-meets-Large-Subposetᵉ
      ( large-meet-semilattice-Large-Localeᵉ Lᵉ)
      ( large-subposet-nucleus-Large-Localeᵉ)
  is-closed-under-meets-large-subposet-nucleus-Large-Localeᵉ xᵉ yᵉ pᵉ qᵉ =
    ( preserves-meets-nucleus-Large-Localeᵉ Lᵉ jᵉ xᵉ yᵉ) ∙ᵉ
    ( ap-meet-Large-Localeᵉ Lᵉ pᵉ qᵉ)

  contains-top-large-subposet-nucleus-Large-Localeᵉ :
    contains-top-Large-Subposetᵉ
      ( large-meet-semilattice-Large-Localeᵉ Lᵉ)
      ( large-subposet-nucleus-Large-Localeᵉ)
  contains-top-large-subposet-nucleus-Large-Localeᵉ =
    is-closed-element-leq-nucleus-Large-Localeᵉ
      ( top-Large-Localeᵉ Lᵉ)
      ( is-top-element-top-Large-Localeᵉ Lᵉ
        ( map-nucleus-Large-Localeᵉ Lᵉ jᵉ (top-Large-Localeᵉ Lᵉ)))

  large-meet-subsemilattice-nucleus-Large-Localeᵉ :
    Large-Meet-Subsemilatticeᵉ αᵉ (large-meet-semilattice-Large-Localeᵉ Lᵉ)
  large-subposet-Large-Meet-Subsemilatticeᵉ
    large-meet-subsemilattice-nucleus-Large-Localeᵉ =
    large-subposet-nucleus-Large-Localeᵉ
  is-closed-under-meets-Large-Meet-Subsemilatticeᵉ
    large-meet-subsemilattice-nucleus-Large-Localeᵉ =
    is-closed-under-meets-large-subposet-nucleus-Large-Localeᵉ
  contains-top-Large-Meet-Subsemilatticeᵉ
    large-meet-subsemilattice-nucleus-Large-Localeᵉ =
    contains-top-large-subposet-nucleus-Large-Localeᵉ

  is-large-meet-semilattice-nucleus-Large-Localeᵉ :
    is-large-meet-semilattice-Large-Posetᵉ
      ( large-poset-nucleus-Large-Localeᵉ)
  is-large-meet-semilattice-nucleus-Large-Localeᵉ =
    is-large-meet-semilattice-Large-Meet-Subsemilatticeᵉ
      ( large-meet-semilattice-Large-Localeᵉ Lᵉ)
      ( large-meet-subsemilattice-nucleus-Large-Localeᵉ)

  large-meet-semilattice-nucleus-Large-Localeᵉ :
    Large-Meet-Semilatticeᵉ αᵉ βᵉ
  large-meet-semilattice-nucleus-Large-Localeᵉ =
    large-meet-semilattice-Large-Meet-Subsemilatticeᵉ
      ( large-meet-semilattice-Large-Localeᵉ Lᵉ)
      ( large-meet-subsemilattice-nucleus-Large-Localeᵉ)

  meet-closed-element-nucleus-Large-Localeᵉ :
    {l1ᵉ l2ᵉ : Level} →
    closed-element-nucleus-Large-Localeᵉ l1ᵉ →
    closed-element-nucleus-Large-Localeᵉ l2ᵉ →
    closed-element-nucleus-Large-Localeᵉ (l1ᵉ ⊔ l2ᵉ)
  meet-closed-element-nucleus-Large-Localeᵉ =
    meet-Large-Meet-Semilatticeᵉ large-meet-semilattice-nucleus-Large-Localeᵉ

  forward-implication-adjoint-relation-nucleus-Large-Localeᵉ :
    {l1ᵉ l2ᵉ : Level}
    {xᵉ : type-Large-Localeᵉ Lᵉ l1ᵉ}
    {yᵉ : type-Large-Localeᵉ Lᵉ l2ᵉ} →
    is-closed-element-nucleus-Large-Localeᵉ yᵉ →
    leq-Large-Localeᵉ Lᵉ xᵉ yᵉ →
    leq-Large-Localeᵉ Lᵉ (map-nucleus-Large-Localeᵉ Lᵉ jᵉ xᵉ) yᵉ
  forward-implication-adjoint-relation-nucleus-Large-Localeᵉ {xᵉ = xᵉ} {yᵉ} Hᵉ Kᵉ =
    transitive-leq-Large-Localeᵉ Lᵉ
      ( map-nucleus-Large-Localeᵉ Lᵉ jᵉ xᵉ)
      ( map-nucleus-Large-Localeᵉ Lᵉ jᵉ yᵉ)
      ( yᵉ)
      ( leq-eq-Large-Localeᵉ Lᵉ Hᵉ)
      ( preserves-order-nucleus-Large-Localeᵉ Lᵉ jᵉ
        ( xᵉ)
        ( yᵉ)
        ( Kᵉ))

  backward-implication-adjoint-relation-nucleus-Large-Localeᵉ :
    {l1ᵉ l2ᵉ : Level}
    {xᵉ : type-Large-Localeᵉ Lᵉ l1ᵉ}
    {yᵉ : type-Large-Localeᵉ Lᵉ l2ᵉ} →
    leq-Large-Localeᵉ Lᵉ (map-nucleus-Large-Localeᵉ Lᵉ jᵉ xᵉ) yᵉ →
    leq-Large-Localeᵉ Lᵉ xᵉ yᵉ
  backward-implication-adjoint-relation-nucleus-Large-Localeᵉ {xᵉ = xᵉ} {yᵉ} Hᵉ =
    transitive-leq-Large-Localeᵉ Lᵉ
      ( xᵉ)
      ( map-nucleus-Large-Localeᵉ Lᵉ jᵉ xᵉ)
      ( yᵉ)
      ( Hᵉ)
      ( is-inflationary-nucleus-Large-Localeᵉ jᵉ xᵉ)

  adjoint-relation-nucleus-Large-Localeᵉ :
    {l1ᵉ l2ᵉ : Level}
    (xᵉ : type-Large-Localeᵉ Lᵉ l1ᵉ)
    (yᵉ : type-Large-Localeᵉ Lᵉ l2ᵉ) →
    is-closed-element-nucleus-Large-Localeᵉ yᵉ →
    leq-Large-Localeᵉ Lᵉ xᵉ yᵉ ↔ᵉ
    leq-Large-Localeᵉ Lᵉ (map-nucleus-Large-Localeᵉ Lᵉ jᵉ xᵉ) yᵉ
  pr1ᵉ (adjoint-relation-nucleus-Large-Localeᵉ xᵉ yᵉ Hᵉ) =
    forward-implication-adjoint-relation-nucleus-Large-Localeᵉ Hᵉ
  pr2ᵉ (adjoint-relation-nucleus-Large-Localeᵉ xᵉ yᵉ Hᵉ) =
    backward-implication-adjoint-relation-nucleus-Large-Localeᵉ

  sup-closed-element-nucleus-Large-Localeᵉ :
    {l1ᵉ l2ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ}
    (xᵉ : Iᵉ → closed-element-nucleus-Large-Localeᵉ l2ᵉ) →
    closed-element-nucleus-Large-Localeᵉ (γᵉ ⊔ l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ (sup-closed-element-nucleus-Large-Localeᵉ xᵉ) =
    map-nucleus-Large-Localeᵉ Lᵉ jᵉ (sup-Large-Localeᵉ Lᵉ (pr1ᵉ ∘ᵉ xᵉ))
  pr2ᵉ (sup-closed-element-nucleus-Large-Localeᵉ xᵉ) =
    is-idempotent-nucleus-Large-Localeᵉ jᵉ (sup-Large-Localeᵉ Lᵉ (pr1ᵉ ∘ᵉ xᵉ))

  is-least-upper-bound-sup-closed-element-nucleus-Large-Localeᵉ :
    {l1ᵉ l2ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ}
    (xᵉ : Iᵉ → closed-element-nucleus-Large-Localeᵉ l2ᵉ) →
    is-least-upper-bound-family-of-elements-Large-Posetᵉ
      ( large-poset-nucleus-Large-Localeᵉ)
      ( xᵉ)
      ( sup-closed-element-nucleus-Large-Localeᵉ xᵉ)
  pr1ᵉ (is-least-upper-bound-sup-closed-element-nucleus-Large-Localeᵉ xᵉ yᵉ) Hᵉ =
    forward-implication-adjoint-relation-nucleus-Large-Localeᵉ
      ( pr2ᵉ yᵉ)
      ( forward-implicationᵉ
        ( is-least-upper-bound-sup-Large-Localeᵉ Lᵉ (pr1ᵉ ∘ᵉ xᵉ) (pr1ᵉ yᵉ))
        ( Hᵉ))
  pr2ᵉ (is-least-upper-bound-sup-closed-element-nucleus-Large-Localeᵉ xᵉ yᵉ) Hᵉ =
    backward-implicationᵉ
      ( is-least-upper-bound-sup-Large-Localeᵉ Lᵉ (pr1ᵉ ∘ᵉ xᵉ) (pr1ᵉ yᵉ))
      ( backward-implication-adjoint-relation-nucleus-Large-Localeᵉ Hᵉ)

  is-large-suplattice-large-poset-nucleus-Large-Localeᵉ :
    is-large-suplattice-Large-Posetᵉ γᵉ
      ( large-poset-nucleus-Large-Localeᵉ)
  sup-has-least-upper-bound-family-of-elements-Large-Posetᵉ
    ( is-large-suplattice-large-poset-nucleus-Large-Localeᵉ xᵉ) =
    sup-closed-element-nucleus-Large-Localeᵉ xᵉ
  is-least-upper-bound-sup-has-least-upper-bound-family-of-elements-Large-Posetᵉ
    ( is-large-suplattice-large-poset-nucleus-Large-Localeᵉ xᵉ) =
    is-least-upper-bound-sup-closed-element-nucleus-Large-Localeᵉ xᵉ

  large-suplattice-nucleus-Large-Localeᵉ :
    Large-Suplatticeᵉ αᵉ βᵉ γᵉ
  large-poset-Large-Suplatticeᵉ
    large-suplattice-nucleus-Large-Localeᵉ =
    large-poset-nucleus-Large-Localeᵉ
  is-large-suplattice-Large-Suplatticeᵉ
    large-suplattice-nucleus-Large-Localeᵉ =
    is-large-suplattice-large-poset-nucleus-Large-Localeᵉ

  distributive-meet-sup-nucleus-Large-Localeᵉ :
    {l1ᵉ l2ᵉ l3ᵉ : Level}
    (xᵉ : closed-element-nucleus-Large-Localeᵉ l1ᵉ)
    {Iᵉ : UUᵉ l2ᵉ} (yᵉ : Iᵉ → closed-element-nucleus-Large-Localeᵉ l3ᵉ) →
    meet-closed-element-nucleus-Large-Localeᵉ xᵉ
      ( sup-closed-element-nucleus-Large-Localeᵉ yᵉ) ＝ᵉ
    sup-closed-element-nucleus-Large-Localeᵉ
      ( λ iᵉ →
        meet-closed-element-nucleus-Large-Localeᵉ xᵉ (yᵉ iᵉ))
  distributive-meet-sup-nucleus-Large-Localeᵉ (xᵉ ,ᵉ pᵉ) yᵉ =
    eq-type-subtypeᵉ
      ( large-subpreorder-nucleus-Large-Localeᵉ)
      ( ( apᵉ (λ uᵉ → meet-Large-Localeᵉ Lᵉ uᵉ _) (invᵉ pᵉ)) ∙ᵉ
        ( ( invᵉ ( preserves-meets-nucleus-Large-Localeᵉ Lᵉ jᵉ xᵉ _)) ∙ᵉ
          ( apᵉ
            ( map-nucleus-Large-Localeᵉ Lᵉ jᵉ)
            ( distributive-meet-sup-Large-Localeᵉ Lᵉ xᵉ (pr1ᵉ ∘ᵉ yᵉ)))))

  large-frame-nucleus-Large-Localeᵉ :
    Large-Frameᵉ αᵉ βᵉ γᵉ
  large-poset-Large-Frameᵉ
    large-frame-nucleus-Large-Localeᵉ =
    large-poset-nucleus-Large-Localeᵉ
  is-large-meet-semilattice-Large-Frameᵉ
    large-frame-nucleus-Large-Localeᵉ =
    is-large-meet-semilattice-nucleus-Large-Localeᵉ
  is-large-suplattice-Large-Frameᵉ
    large-frame-nucleus-Large-Localeᵉ =
    is-large-suplattice-large-poset-nucleus-Large-Localeᵉ
  distributive-meet-sup-Large-Frameᵉ
    large-frame-nucleus-Large-Localeᵉ =
    distributive-meet-sup-nucleus-Large-Localeᵉ

  large-locale-nucleus-Large-Localeᵉ :
    Large-Localeᵉ αᵉ βᵉ γᵉ
  large-locale-nucleus-Large-Localeᵉ = large-frame-nucleus-Large-Localeᵉ
```