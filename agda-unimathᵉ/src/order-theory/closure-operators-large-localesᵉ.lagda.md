# Closure operators on large locales

```agda
module order-theory.closure-operators-large-localesᵉ where
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

open import order-theory.closure-operators-large-posetsᵉ
open import order-theory.large-framesᵉ
open import order-theory.large-localesᵉ
open import order-theory.large-meet-semilatticesᵉ
open import order-theory.large-meet-subsemilatticesᵉ
open import order-theory.large-posetsᵉ
open import order-theory.large-subposetsᵉ
open import order-theory.large-subpreordersᵉ
open import order-theory.large-suplatticesᵉ
open import order-theory.least-upper-bounds-large-posetsᵉ
open import order-theory.order-preserving-maps-large-posetsᵉ
```

</details>

## Idea

Aᵉ **closureᵉ operator**ᵉ onᵉ aᵉ [largeᵉ locale](order-theory.large-locales.mdᵉ) `L`ᵉ isᵉ
aᵉ [closureᵉ operator](order-theory.closure-operators-large-posets.mdᵉ) onᵉ theᵉ
underlyingᵉ [largeᵉ poset](order-theory.large-posets.mdᵉ) ofᵉ `L`.ᵉ

Weᵉ showᵉ thatᵉ ifᵉ theᵉ closedᵉ elementsᵉ areᵉ closedᵉ underᵉ meets,ᵉ thenᵉ theᵉ closedᵉ
elementsᵉ formᵉ aᵉ largeᵉ locale.ᵉ Noteᵉ thatᵉ theᵉ conditionᵉ thatᵉ theᵉ closedᵉ elementsᵉ
areᵉ closedᵉ underᵉ meetsᵉ isᵉ moreᵉ generalᵉ thanᵉ theᵉ conditionᵉ thatᵉ theᵉ closureᵉ
operatorᵉ isᵉ aᵉ [nucleus](order-theory.nuclei-large-locales.md).ᵉ

## Definitions

### Closure operators on large locales

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level} {γᵉ : Level}
  (Lᵉ : Large-Localeᵉ αᵉ βᵉ γᵉ)
  where

  closure-operator-Large-Localeᵉ : UUωᵉ
  closure-operator-Large-Localeᵉ =
    closure-operator-Large-Posetᵉ (large-poset-Large-Localeᵉ Lᵉ)

  module _
    (jᵉ : closure-operator-Large-Localeᵉ)
    where

    hom-large-poset-closure-operator-Large-Localeᵉ :
      hom-Large-Posetᵉ
        ( λ lᵉ → lᵉ)
        ( large-poset-Large-Localeᵉ Lᵉ)
        ( large-poset-Large-Localeᵉ Lᵉ)
    hom-large-poset-closure-operator-Large-Localeᵉ =
      hom-closure-operator-Large-Posetᵉ jᵉ

    map-closure-operator-Large-Localeᵉ :
      {l1ᵉ : Level} → type-Large-Localeᵉ Lᵉ l1ᵉ → type-Large-Localeᵉ Lᵉ l1ᵉ
    map-closure-operator-Large-Localeᵉ =
      map-hom-Large-Posetᵉ
        ( large-poset-Large-Localeᵉ Lᵉ)
        ( large-poset-Large-Localeᵉ Lᵉ)
        ( hom-large-poset-closure-operator-Large-Localeᵉ)

    preserves-order-closure-operator-Large-Localeᵉ :
      {l1ᵉ l2ᵉ : Level}
      (xᵉ : type-Large-Localeᵉ Lᵉ l1ᵉ)
      (yᵉ : type-Large-Localeᵉ Lᵉ l2ᵉ) →
      leq-Large-Localeᵉ Lᵉ xᵉ yᵉ →
      leq-Large-Localeᵉ Lᵉ
        ( map-closure-operator-Large-Localeᵉ xᵉ)
        ( map-closure-operator-Large-Localeᵉ yᵉ)
    preserves-order-closure-operator-Large-Localeᵉ =
      preserves-order-hom-Large-Posetᵉ
        ( large-poset-Large-Localeᵉ Lᵉ)
        ( large-poset-Large-Localeᵉ Lᵉ)
        ( hom-large-poset-closure-operator-Large-Localeᵉ)

    is-inflationary-closure-operator-Large-Localeᵉ :
      {l1ᵉ : Level} (xᵉ : type-Large-Localeᵉ Lᵉ l1ᵉ) →
      leq-Large-Localeᵉ Lᵉ xᵉ
        ( map-closure-operator-Large-Localeᵉ xᵉ)
    is-inflationary-closure-operator-Large-Localeᵉ =
      is-inflationary-closure-operator-Large-Posetᵉ jᵉ

    is-idempotent-closure-operator-Large-Localeᵉ :
      {l1ᵉ : Level} (xᵉ : type-Large-Localeᵉ Lᵉ l1ᵉ) →
      map-closure-operator-Large-Localeᵉ
        ( map-closure-operator-Large-Localeᵉ xᵉ) ＝ᵉ
      map-closure-operator-Large-Localeᵉ xᵉ
    is-idempotent-closure-operator-Large-Localeᵉ =
      is-idempotent-closure-operator-Large-Posetᵉ jᵉ
```

### The large suplattice of `j`-closed elements of a closure operator

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level} {γᵉ : Level}
  (Lᵉ : Large-Localeᵉ αᵉ βᵉ γᵉ) (jᵉ : closure-operator-Large-Localeᵉ Lᵉ)
  where

  large-subpreorder-closure-operator-Large-Localeᵉ :
    Large-Subpreorderᵉ αᵉ (large-preorder-Large-Localeᵉ Lᵉ)
  large-subpreorder-closure-operator-Large-Localeᵉ {l1ᵉ} xᵉ =
    Id-Propᵉ (set-Large-Localeᵉ Lᵉ l1ᵉ) (map-closure-operator-Large-Localeᵉ Lᵉ jᵉ xᵉ) xᵉ

  is-closed-element-closure-operator-Large-Localeᵉ :
    {l1ᵉ : Level} → type-Large-Localeᵉ Lᵉ l1ᵉ → UUᵉ (αᵉ l1ᵉ)
  is-closed-element-closure-operator-Large-Localeᵉ =
    is-in-Large-Subpreorderᵉ
      ( large-preorder-Large-Localeᵉ Lᵉ)
      ( large-subpreorder-closure-operator-Large-Localeᵉ)

  is-prop-is-closed-element-closure-operator-Large-Localeᵉ :
    {l1ᵉ : Level} (xᵉ : type-Large-Localeᵉ Lᵉ l1ᵉ) →
    is-propᵉ (is-closed-element-closure-operator-Large-Localeᵉ xᵉ)
  is-prop-is-closed-element-closure-operator-Large-Localeᵉ =
    is-prop-is-in-Large-Subpreorderᵉ
      ( large-preorder-Large-Localeᵉ Lᵉ)
      ( large-subpreorder-closure-operator-Large-Localeᵉ)

  is-closed-element-leq-closure-operator-Large-Localeᵉ :
    {l1ᵉ : Level} (xᵉ : type-Large-Localeᵉ Lᵉ l1ᵉ) →
    leq-Large-Localeᵉ Lᵉ (map-closure-operator-Large-Localeᵉ Lᵉ jᵉ xᵉ) xᵉ →
    is-closed-element-closure-operator-Large-Localeᵉ xᵉ
  is-closed-element-leq-closure-operator-Large-Localeᵉ xᵉ Hᵉ =
    antisymmetric-leq-Large-Localeᵉ Lᵉ
      ( map-closure-operator-Large-Localeᵉ Lᵉ jᵉ xᵉ)
      ( xᵉ)
      ( Hᵉ)
      ( is-inflationary-closure-operator-Large-Localeᵉ Lᵉ jᵉ xᵉ)

  closed-element-closure-operator-Large-Localeᵉ :
    (l1ᵉ : Level) → UUᵉ (αᵉ l1ᵉ)
  closed-element-closure-operator-Large-Localeᵉ =
    type-Large-Subpreorderᵉ
      ( large-preorder-Large-Localeᵉ Lᵉ)
      ( large-subpreorder-closure-operator-Large-Localeᵉ)

  is-closed-under-sim-closure-operator-Large-Localeᵉ :
    {l1ᵉ l2ᵉ : Level}
    (xᵉ : type-Large-Localeᵉ Lᵉ l1ᵉ)
    (yᵉ : type-Large-Localeᵉ Lᵉ l2ᵉ) →
    leq-Large-Localeᵉ Lᵉ xᵉ yᵉ → leq-Large-Localeᵉ Lᵉ yᵉ xᵉ →
    is-closed-element-closure-operator-Large-Localeᵉ xᵉ →
    is-closed-element-closure-operator-Large-Localeᵉ yᵉ
  is-closed-under-sim-closure-operator-Large-Localeᵉ xᵉ yᵉ Hᵉ Kᵉ cᵉ =
    is-closed-element-leq-closure-operator-Large-Localeᵉ yᵉ
      ( transitive-leq-Large-Localeᵉ Lᵉ
        ( map-closure-operator-Large-Localeᵉ Lᵉ jᵉ yᵉ)
        ( map-closure-operator-Large-Localeᵉ Lᵉ jᵉ xᵉ)
        ( yᵉ)
        ( transitive-leq-Large-Localeᵉ Lᵉ
          ( map-closure-operator-Large-Localeᵉ Lᵉ jᵉ xᵉ)
          ( xᵉ)
          ( yᵉ)
          ( Hᵉ)
          ( leq-eq-Large-Localeᵉ Lᵉ cᵉ))
        ( preserves-order-closure-operator-Large-Localeᵉ Lᵉ jᵉ yᵉ xᵉ Kᵉ))

  large-subposet-closure-operator-Large-Localeᵉ :
    Large-Subposetᵉ αᵉ (large-poset-Large-Localeᵉ Lᵉ)
  large-subpreorder-Large-Subposetᵉ
    large-subposet-closure-operator-Large-Localeᵉ =
    large-subpreorder-closure-operator-Large-Localeᵉ
  is-closed-under-sim-Large-Subposetᵉ
    large-subposet-closure-operator-Large-Localeᵉ =
    is-closed-under-sim-closure-operator-Large-Localeᵉ

  large-poset-closure-operator-Large-Localeᵉ :
    Large-Posetᵉ αᵉ βᵉ
  large-poset-closure-operator-Large-Localeᵉ =
    large-poset-Large-Subposetᵉ
      ( large-poset-Large-Localeᵉ Lᵉ)
      ( large-subposet-closure-operator-Large-Localeᵉ)

  leq-prop-closed-element-closure-operator-Large-Localeᵉ :
    Large-Relation-Propᵉ βᵉ closed-element-closure-operator-Large-Localeᵉ
  leq-prop-closed-element-closure-operator-Large-Localeᵉ =
    leq-prop-Large-Subposetᵉ
      ( large-poset-Large-Localeᵉ Lᵉ)
      ( large-subposet-closure-operator-Large-Localeᵉ)

  leq-closed-element-closure-operator-Large-Localeᵉ :
    Large-Relationᵉ βᵉ closed-element-closure-operator-Large-Localeᵉ
  leq-closed-element-closure-operator-Large-Localeᵉ =
    leq-Large-Subposetᵉ
      ( large-poset-Large-Localeᵉ Lᵉ)
      ( large-subposet-closure-operator-Large-Localeᵉ)

  is-prop-leq-closed-element-closure-operator-Large-Localeᵉ :
    is-prop-Large-Relationᵉ
      ( closed-element-closure-operator-Large-Localeᵉ)
      ( leq-closed-element-closure-operator-Large-Localeᵉ)
  is-prop-leq-closed-element-closure-operator-Large-Localeᵉ =
    is-prop-leq-Large-Subposetᵉ
      ( large-poset-Large-Localeᵉ Lᵉ)
      ( large-subposet-closure-operator-Large-Localeᵉ)

  refl-leq-closed-element-closure-operator-Large-Localeᵉ :
    is-reflexive-Large-Relationᵉ
      ( closed-element-closure-operator-Large-Localeᵉ)
      ( leq-closed-element-closure-operator-Large-Localeᵉ)
  refl-leq-closed-element-closure-operator-Large-Localeᵉ =
    refl-leq-Large-Subposetᵉ
      ( large-poset-Large-Localeᵉ Lᵉ)
      ( large-subposet-closure-operator-Large-Localeᵉ)

  antisymmetric-leq-closed-element-closure-operator-Large-Localeᵉ :
    is-antisymmetric-Large-Relationᵉ
      ( closed-element-closure-operator-Large-Localeᵉ)
      ( leq-closed-element-closure-operator-Large-Localeᵉ)
  antisymmetric-leq-closed-element-closure-operator-Large-Localeᵉ =
    antisymmetric-leq-Large-Subposetᵉ
      ( large-poset-Large-Localeᵉ Lᵉ)
      ( large-subposet-closure-operator-Large-Localeᵉ)

  transitive-leq-closed-element-closure-operator-Large-Localeᵉ :
    is-transitive-Large-Relationᵉ
      ( closed-element-closure-operator-Large-Localeᵉ)
      ( leq-closed-element-closure-operator-Large-Localeᵉ)
  transitive-leq-closed-element-closure-operator-Large-Localeᵉ =
    transitive-leq-Large-Subposetᵉ
      ( large-poset-Large-Localeᵉ Lᵉ)
      ( large-subposet-closure-operator-Large-Localeᵉ)

  contains-top-large-subposet-closure-operator-Large-Localeᵉ :
    is-closed-element-closure-operator-Large-Localeᵉ
      ( top-Large-Localeᵉ Lᵉ)
  contains-top-large-subposet-closure-operator-Large-Localeᵉ =
    antisymmetric-leq-Large-Localeᵉ Lᵉ
      ( map-closure-operator-Large-Localeᵉ Lᵉ jᵉ (top-Large-Localeᵉ Lᵉ))
      ( top-Large-Localeᵉ Lᵉ)
      ( is-top-element-top-Large-Localeᵉ Lᵉ
        ( map-closure-operator-Large-Localeᵉ Lᵉ jᵉ (top-Large-Localeᵉ Lᵉ)))
      ( is-inflationary-closure-operator-Large-Localeᵉ Lᵉ jᵉ (top-Large-Localeᵉ Lᵉ))

  forward-implication-adjoint-relation-closure-operator-Large-Localeᵉ :
    {l1ᵉ l2ᵉ : Level}
    {xᵉ : type-Large-Localeᵉ Lᵉ l1ᵉ}
    {yᵉ : type-Large-Localeᵉ Lᵉ l2ᵉ} →
    is-closed-element-closure-operator-Large-Localeᵉ yᵉ →
    leq-Large-Localeᵉ Lᵉ xᵉ yᵉ →
    leq-Large-Localeᵉ Lᵉ (map-closure-operator-Large-Localeᵉ Lᵉ jᵉ xᵉ) yᵉ
  forward-implication-adjoint-relation-closure-operator-Large-Localeᵉ
    {xᵉ = xᵉ} {yᵉ} Hᵉ Kᵉ =
    transitive-leq-Large-Localeᵉ Lᵉ
      ( map-closure-operator-Large-Localeᵉ Lᵉ jᵉ xᵉ)
      ( map-closure-operator-Large-Localeᵉ Lᵉ jᵉ yᵉ)
      ( yᵉ)
      ( leq-eq-Large-Localeᵉ Lᵉ Hᵉ)
      ( preserves-order-closure-operator-Large-Localeᵉ Lᵉ jᵉ
        ( xᵉ)
        ( yᵉ)
        ( Kᵉ))

  backward-implication-adjoint-relation-closure-operator-Large-Localeᵉ :
    {l1ᵉ l2ᵉ : Level}
    {xᵉ : type-Large-Localeᵉ Lᵉ l1ᵉ}
    {yᵉ : type-Large-Localeᵉ Lᵉ l2ᵉ} →
    leq-Large-Localeᵉ Lᵉ (map-closure-operator-Large-Localeᵉ Lᵉ jᵉ xᵉ) yᵉ →
    leq-Large-Localeᵉ Lᵉ xᵉ yᵉ
  backward-implication-adjoint-relation-closure-operator-Large-Localeᵉ
    {xᵉ = xᵉ} {yᵉ} Hᵉ =
    transitive-leq-Large-Localeᵉ Lᵉ
      ( xᵉ)
      ( map-closure-operator-Large-Localeᵉ Lᵉ jᵉ xᵉ)
      ( yᵉ)
      ( Hᵉ)
      ( is-inflationary-closure-operator-Large-Localeᵉ Lᵉ jᵉ xᵉ)

  adjoint-relation-closure-operator-Large-Localeᵉ :
    {l1ᵉ l2ᵉ : Level}
    (xᵉ : type-Large-Localeᵉ Lᵉ l1ᵉ)
    (yᵉ : type-Large-Localeᵉ Lᵉ l2ᵉ) →
    is-closed-element-closure-operator-Large-Localeᵉ yᵉ →
    leq-Large-Localeᵉ Lᵉ xᵉ yᵉ ↔ᵉ
    leq-Large-Localeᵉ Lᵉ (map-closure-operator-Large-Localeᵉ Lᵉ jᵉ xᵉ) yᵉ
  pr1ᵉ (adjoint-relation-closure-operator-Large-Localeᵉ xᵉ yᵉ Hᵉ) =
    forward-implication-adjoint-relation-closure-operator-Large-Localeᵉ Hᵉ
  pr2ᵉ (adjoint-relation-closure-operator-Large-Localeᵉ xᵉ yᵉ Hᵉ) =
    backward-implication-adjoint-relation-closure-operator-Large-Localeᵉ

  sup-closed-element-closure-operator-Large-Localeᵉ :
    {l1ᵉ l2ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ}
    (xᵉ : Iᵉ → closed-element-closure-operator-Large-Localeᵉ l2ᵉ) →
    closed-element-closure-operator-Large-Localeᵉ (γᵉ ⊔ l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ (sup-closed-element-closure-operator-Large-Localeᵉ xᵉ) =
    map-closure-operator-Large-Localeᵉ Lᵉ jᵉ (sup-Large-Localeᵉ Lᵉ (pr1ᵉ ∘ᵉ xᵉ))
  pr2ᵉ (sup-closed-element-closure-operator-Large-Localeᵉ xᵉ) =
    is-idempotent-closure-operator-Large-Localeᵉ Lᵉ jᵉ
      ( sup-Large-Localeᵉ Lᵉ (pr1ᵉ ∘ᵉ xᵉ))

  is-least-upper-bound-sup-closed-element-closure-operator-Large-Localeᵉ :
    {l1ᵉ l2ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ}
    (xᵉ : Iᵉ → closed-element-closure-operator-Large-Localeᵉ l2ᵉ) →
    is-least-upper-bound-family-of-elements-Large-Posetᵉ
      ( large-poset-closure-operator-Large-Localeᵉ)
      ( xᵉ)
      ( sup-closed-element-closure-operator-Large-Localeᵉ xᵉ)
  pr1ᵉ
    ( is-least-upper-bound-sup-closed-element-closure-operator-Large-Localeᵉ xᵉ yᵉ)
    ( Hᵉ) =
    forward-implication-adjoint-relation-closure-operator-Large-Localeᵉ
      ( pr2ᵉ yᵉ)
      ( forward-implicationᵉ
        ( is-least-upper-bound-sup-Large-Localeᵉ Lᵉ (pr1ᵉ ∘ᵉ xᵉ) (pr1ᵉ yᵉ))
        ( Hᵉ))
  pr2ᵉ
    ( is-least-upper-bound-sup-closed-element-closure-operator-Large-Localeᵉ xᵉ yᵉ)
    ( Hᵉ) =
    backward-implicationᵉ
      ( is-least-upper-bound-sup-Large-Localeᵉ Lᵉ (pr1ᵉ ∘ᵉ xᵉ) (pr1ᵉ yᵉ))
      ( backward-implication-adjoint-relation-closure-operator-Large-Localeᵉ Hᵉ)

  is-large-suplattice-large-poset-closure-operator-Large-Localeᵉ :
    is-large-suplattice-Large-Posetᵉ γᵉ
      ( large-poset-closure-operator-Large-Localeᵉ)
  sup-has-least-upper-bound-family-of-elements-Large-Posetᵉ
    ( is-large-suplattice-large-poset-closure-operator-Large-Localeᵉ xᵉ) =
    sup-closed-element-closure-operator-Large-Localeᵉ xᵉ
  is-least-upper-bound-sup-has-least-upper-bound-family-of-elements-Large-Posetᵉ
    ( is-large-suplattice-large-poset-closure-operator-Large-Localeᵉ xᵉ) =
    is-least-upper-bound-sup-closed-element-closure-operator-Large-Localeᵉ xᵉ

  large-suplattice-closure-operator-Large-Localeᵉ :
    Large-Suplatticeᵉ αᵉ βᵉ γᵉ
  large-poset-Large-Suplatticeᵉ
    large-suplattice-closure-operator-Large-Localeᵉ =
    large-poset-closure-operator-Large-Localeᵉ
  is-large-suplattice-Large-Suplatticeᵉ
    large-suplattice-closure-operator-Large-Localeᵉ =
    is-large-suplattice-large-poset-closure-operator-Large-Localeᵉ
```

### The predicate that the closed elements of a closure operator on a large locale are closed under meets

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level} {γᵉ : Level}
  (Lᵉ : Large-Localeᵉ αᵉ βᵉ γᵉ) (jᵉ : closure-operator-Large-Localeᵉ Lᵉ)
  where

  is-closed-under-meets-closure-operator-Large-Localeᵉ : UUωᵉ
  is-closed-under-meets-closure-operator-Large-Localeᵉ =
    is-closed-under-meets-Large-Subposetᵉ
      ( large-meet-semilattice-Large-Localeᵉ Lᵉ)
      ( large-subposet-closure-operator-Large-Localeᵉ Lᵉ jᵉ)
```

## Properties

### If the closed elements are closed under meets, then the closed elements of a closure operator form a large locale

Weᵉ alsoᵉ assumeᵉ thatᵉ `xᵉ ∧ᵉ jᵉ yᵉ ＝ᵉ jᵉ (xᵉ ∧ᵉ y)`ᵉ forᵉ anyᵉ closedᵉ elementᵉ `x`.ᵉ Inᵉ largeᵉ
localesᵉ with exponentialsᵉ itᵉ seemsᵉ thatᵉ weᵉ canᵉ omitᵉ thisᵉ extraᵉ hypothesis.ᵉ

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level} {γᵉ : Level}
  (Lᵉ : Large-Localeᵉ αᵉ βᵉ γᵉ) (jᵉ : closure-operator-Large-Localeᵉ Lᵉ)
  (Hᵉ : is-closed-under-meets-closure-operator-Large-Localeᵉ Lᵉ jᵉ)
  (Kᵉ :
    {l1ᵉ l2ᵉ : Level} (xᵉ : type-Large-Localeᵉ Lᵉ l1ᵉ) (yᵉ : type-Large-Localeᵉ Lᵉ l2ᵉ) →
    is-closed-element-closure-operator-Large-Localeᵉ Lᵉ jᵉ xᵉ →
    meet-Large-Localeᵉ Lᵉ xᵉ (map-closure-operator-Large-Localeᵉ Lᵉ jᵉ yᵉ) ＝ᵉ
    map-closure-operator-Large-Localeᵉ Lᵉ jᵉ (meet-Large-Localeᵉ Lᵉ xᵉ yᵉ))
  where

  large-meet-subsemilattice-closure-operator-Large-Localeᵉ :
    Large-Meet-Subsemilatticeᵉ αᵉ (large-meet-semilattice-Large-Localeᵉ Lᵉ)
  large-subposet-Large-Meet-Subsemilatticeᵉ
    large-meet-subsemilattice-closure-operator-Large-Localeᵉ =
    large-subposet-closure-operator-Large-Localeᵉ Lᵉ jᵉ
  is-closed-under-meets-Large-Meet-Subsemilatticeᵉ
    large-meet-subsemilattice-closure-operator-Large-Localeᵉ =
    Hᵉ
  contains-top-Large-Meet-Subsemilatticeᵉ
    large-meet-subsemilattice-closure-operator-Large-Localeᵉ =
    contains-top-large-subposet-closure-operator-Large-Localeᵉ Lᵉ jᵉ

  large-meet-semilattice-closure-operator-Large-Localeᵉ :
    Large-Meet-Semilatticeᵉ αᵉ βᵉ
  large-meet-semilattice-closure-operator-Large-Localeᵉ =
    large-meet-semilattice-Large-Meet-Subsemilatticeᵉ
      ( large-meet-semilattice-Large-Localeᵉ Lᵉ)
      ( large-meet-subsemilattice-closure-operator-Large-Localeᵉ)

  is-large-meet-semilattice-large-poset-closure-operator-Large-Localeᵉ :
    is-large-meet-semilattice-Large-Posetᵉ
      ( large-poset-closure-operator-Large-Localeᵉ Lᵉ jᵉ)
  is-large-meet-semilattice-large-poset-closure-operator-Large-Localeᵉ =
    is-large-meet-semilattice-Large-Meet-Semilatticeᵉ
      large-meet-semilattice-closure-operator-Large-Localeᵉ

  meet-closed-element-closure-operator-Large-Localeᵉ :
    {l1ᵉ l2ᵉ : Level} →
    closed-element-closure-operator-Large-Localeᵉ Lᵉ jᵉ l1ᵉ →
    closed-element-closure-operator-Large-Localeᵉ Lᵉ jᵉ l2ᵉ →
    closed-element-closure-operator-Large-Localeᵉ Lᵉ jᵉ (l1ᵉ ⊔ l2ᵉ)
  meet-closed-element-closure-operator-Large-Localeᵉ =
    meet-Large-Meet-Semilatticeᵉ
      large-meet-semilattice-closure-operator-Large-Localeᵉ

  distributive-meet-sup-closure-operator-Large-Localeᵉ :
    {l1ᵉ l2ᵉ l3ᵉ : Level}
    (xᵉ : closed-element-closure-operator-Large-Localeᵉ Lᵉ jᵉ l1ᵉ)
    {Iᵉ : UUᵉ l2ᵉ} (yᵉ : Iᵉ → closed-element-closure-operator-Large-Localeᵉ Lᵉ jᵉ l3ᵉ) →
    meet-closed-element-closure-operator-Large-Localeᵉ xᵉ
      ( sup-closed-element-closure-operator-Large-Localeᵉ Lᵉ jᵉ yᵉ) ＝ᵉ
    sup-closed-element-closure-operator-Large-Localeᵉ Lᵉ jᵉ
      ( λ iᵉ →
        meet-closed-element-closure-operator-Large-Localeᵉ xᵉ (yᵉ iᵉ))
  distributive-meet-sup-closure-operator-Large-Localeᵉ (xᵉ ,ᵉ pᵉ) yᵉ =
    eq-type-subtypeᵉ
      ( large-subpreorder-closure-operator-Large-Localeᵉ Lᵉ jᵉ)
      ( ( Kᵉ xᵉ _ pᵉ) ∙ᵉ
        ( apᵉ
          ( map-closure-operator-Large-Localeᵉ Lᵉ jᵉ)
          ( distributive-meet-sup-Large-Localeᵉ Lᵉ xᵉ _)))

  large-frame-closure-operator-Large-Localeᵉ :
    Large-Frameᵉ αᵉ βᵉ γᵉ
  large-poset-Large-Frameᵉ
    large-frame-closure-operator-Large-Localeᵉ =
    large-poset-closure-operator-Large-Localeᵉ Lᵉ jᵉ
  is-large-meet-semilattice-Large-Frameᵉ
    large-frame-closure-operator-Large-Localeᵉ =
    is-large-meet-semilattice-large-poset-closure-operator-Large-Localeᵉ
  is-large-suplattice-Large-Frameᵉ
    large-frame-closure-operator-Large-Localeᵉ =
    is-large-suplattice-large-poset-closure-operator-Large-Localeᵉ Lᵉ jᵉ
  distributive-meet-sup-Large-Frameᵉ
    large-frame-closure-operator-Large-Localeᵉ xᵉ yᵉ =
    distributive-meet-sup-closure-operator-Large-Localeᵉ xᵉ yᵉ

  large-locale-closure-operator-Large-Localeᵉ :
    Large-Localeᵉ αᵉ βᵉ γᵉ
  large-locale-closure-operator-Large-Localeᵉ =
    large-frame-closure-operator-Large-Localeᵉ
```