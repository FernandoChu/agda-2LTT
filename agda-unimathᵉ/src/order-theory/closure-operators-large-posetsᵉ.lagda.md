# Closure operators on large posets

```agda
module order-theory.closure-operators-large-posetsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.identity-typesᵉ
open import foundation.large-binary-relationsᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ

open import order-theory.large-posetsᵉ
open import order-theory.large-subposetsᵉ
open import order-theory.large-subpreordersᵉ
open import order-theory.order-preserving-maps-large-posetsᵉ
```

</details>

## Idea

Aᵉ **closureᵉ operator**ᵉ onᵉ aᵉ [largeᵉ poset](order-theory.large-posets.mdᵉ) `P`ᵉ
consistsᵉ ofᵉ anᵉ orderᵉ preservingᵉ mapᵉ `clᵉ : Pᵉ → P`ᵉ suchᵉ thatᵉ

1.ᵉ `cl`ᵉ isᵉ increasing,ᵉ i.e.,ᵉ `xᵉ ≤ᵉ clᵉ x`ᵉ forᵉ eachᵉ `xᵉ : P`,ᵉ andᵉ
2.ᵉ `cl`ᵉ isᵉ idempotent,ᵉ i.e.,ᵉ `clᵉ (clᵉ xᵉ) ＝ᵉ clᵉ x`ᵉ forᵉ eachᵉ `xᵉ : P`.ᵉ

Inᵉ otherᵉ words,ᵉ closureᵉ operatorsᵉ areᵉ idempotentᵉ monadsᵉ onᵉ (largeᵉ) posets.ᵉ

## Definitions

### Closure operators on large posets

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Pᵉ : Large-Posetᵉ αᵉ βᵉ)
  where

  record
    closure-operator-Large-Posetᵉ : UUωᵉ
    where
    field
      hom-closure-operator-Large-Posetᵉ :
        hom-Large-Posetᵉ (λ lᵉ → lᵉ) Pᵉ Pᵉ
      is-inflationary-closure-operator-Large-Posetᵉ :
        {l1ᵉ : Level} (xᵉ : type-Large-Posetᵉ Pᵉ l1ᵉ) →
        leq-Large-Posetᵉ Pᵉ xᵉ
          ( map-hom-Large-Posetᵉ Pᵉ Pᵉ hom-closure-operator-Large-Posetᵉ xᵉ)
      is-idempotent-closure-operator-Large-Posetᵉ :
        {l1ᵉ : Level} (xᵉ : type-Large-Posetᵉ Pᵉ l1ᵉ) →
        map-hom-Large-Posetᵉ Pᵉ Pᵉ hom-closure-operator-Large-Posetᵉ
          ( map-hom-Large-Posetᵉ Pᵉ Pᵉ hom-closure-operator-Large-Posetᵉ xᵉ) ＝ᵉ
        map-hom-Large-Posetᵉ Pᵉ Pᵉ hom-closure-operator-Large-Posetᵉ xᵉ

  open closure-operator-Large-Posetᵉ public

  module _
    (clᵉ : closure-operator-Large-Posetᵉ)
    where

    map-closure-operator-Large-Posetᵉ :
      {l1ᵉ : Level} → type-Large-Posetᵉ Pᵉ l1ᵉ → type-Large-Posetᵉ Pᵉ l1ᵉ
    map-closure-operator-Large-Posetᵉ =
      map-hom-Large-Posetᵉ Pᵉ Pᵉ (hom-closure-operator-Large-Posetᵉ clᵉ)

    preserves-order-closure-operator-Large-Posetᵉ :
      {l1ᵉ l2ᵉ : Level}
      (xᵉ : type-Large-Posetᵉ Pᵉ l1ᵉ) (yᵉ : type-Large-Posetᵉ Pᵉ l2ᵉ) →
      leq-Large-Posetᵉ Pᵉ xᵉ yᵉ →
      leq-Large-Posetᵉ Pᵉ
        ( map-closure-operator-Large-Posetᵉ xᵉ)
        ( map-closure-operator-Large-Posetᵉ yᵉ)
    preserves-order-closure-operator-Large-Posetᵉ =
      preserves-order-hom-Large-Posetᵉ Pᵉ Pᵉ (hom-closure-operator-Large-Posetᵉ clᵉ)
```

### The large subposet of closed elements of a closure operator

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Pᵉ : Large-Posetᵉ αᵉ βᵉ) (clᵉ : closure-operator-Large-Posetᵉ Pᵉ)
  where

  large-subpreorder-closure-operator-Large-Posetᵉ :
    Large-Subpreorderᵉ αᵉ (large-preorder-Large-Posetᵉ Pᵉ)
  large-subpreorder-closure-operator-Large-Posetᵉ {l1ᵉ} xᵉ =
    Id-Propᵉ (set-Large-Posetᵉ Pᵉ l1ᵉ) (map-closure-operator-Large-Posetᵉ Pᵉ clᵉ xᵉ) xᵉ

  is-closed-element-closure-operator-Large-Posetᵉ :
    {l1ᵉ : Level} → type-Large-Posetᵉ Pᵉ l1ᵉ → UUᵉ (αᵉ l1ᵉ)
  is-closed-element-closure-operator-Large-Posetᵉ =
    is-in-Large-Subpreorderᵉ
      ( large-preorder-Large-Posetᵉ Pᵉ)
      ( large-subpreorder-closure-operator-Large-Posetᵉ)

  is-prop-is-closed-element-closure-operator-Large-Posetᵉ :
    {l1ᵉ : Level} (xᵉ : type-Large-Posetᵉ Pᵉ l1ᵉ) →
    is-propᵉ (is-closed-element-closure-operator-Large-Posetᵉ xᵉ)
  is-prop-is-closed-element-closure-operator-Large-Posetᵉ =
    is-prop-is-in-Large-Subpreorderᵉ
      ( large-preorder-Large-Posetᵉ Pᵉ)
      ( large-subpreorder-closure-operator-Large-Posetᵉ)

  is-closed-element-leq-closure-operator-Large-Posetᵉ :
    {l1ᵉ : Level} (xᵉ : type-Large-Posetᵉ Pᵉ l1ᵉ) →
    leq-Large-Posetᵉ Pᵉ (map-closure-operator-Large-Posetᵉ Pᵉ clᵉ xᵉ) xᵉ →
    is-closed-element-closure-operator-Large-Posetᵉ xᵉ
  is-closed-element-leq-closure-operator-Large-Posetᵉ xᵉ Hᵉ =
    antisymmetric-leq-Large-Posetᵉ Pᵉ
      ( map-closure-operator-Large-Posetᵉ Pᵉ clᵉ xᵉ)
      ( xᵉ)
      ( Hᵉ)
      ( is-inflationary-closure-operator-Large-Posetᵉ clᵉ xᵉ)

  closed-element-closure-operator-Large-Posetᵉ :
    (l1ᵉ : Level) → UUᵉ (αᵉ l1ᵉ)
  closed-element-closure-operator-Large-Posetᵉ =
    type-Large-Subpreorderᵉ
      ( large-preorder-Large-Posetᵉ Pᵉ)
      ( large-subpreorder-closure-operator-Large-Posetᵉ)

  is-closed-under-sim-closure-operator-Large-Posetᵉ :
    {l1ᵉ l2ᵉ : Level}
    (xᵉ : type-Large-Posetᵉ Pᵉ l1ᵉ)
    (yᵉ : type-Large-Posetᵉ Pᵉ l2ᵉ) →
    leq-Large-Posetᵉ Pᵉ xᵉ yᵉ → leq-Large-Posetᵉ Pᵉ yᵉ xᵉ →
    is-closed-element-closure-operator-Large-Posetᵉ xᵉ →
    is-closed-element-closure-operator-Large-Posetᵉ yᵉ
  is-closed-under-sim-closure-operator-Large-Posetᵉ xᵉ yᵉ Hᵉ Kᵉ cᵉ =
    is-closed-element-leq-closure-operator-Large-Posetᵉ yᵉ
      ( transitive-leq-Large-Posetᵉ Pᵉ
        ( map-closure-operator-Large-Posetᵉ Pᵉ clᵉ yᵉ)
        ( map-closure-operator-Large-Posetᵉ Pᵉ clᵉ xᵉ)
        ( yᵉ)
        ( transitive-leq-Large-Posetᵉ Pᵉ
          ( map-closure-operator-Large-Posetᵉ Pᵉ clᵉ xᵉ)
          ( xᵉ)
          ( yᵉ)
          ( Hᵉ)
          ( leq-eq-Large-Posetᵉ Pᵉ cᵉ))
        ( preserves-order-closure-operator-Large-Posetᵉ Pᵉ clᵉ yᵉ xᵉ Kᵉ))

  large-subposet-closure-operator-Large-Posetᵉ :
    Large-Subposetᵉ αᵉ Pᵉ
  large-subpreorder-Large-Subposetᵉ
    large-subposet-closure-operator-Large-Posetᵉ =
    large-subpreorder-closure-operator-Large-Posetᵉ
  is-closed-under-sim-Large-Subposetᵉ
    large-subposet-closure-operator-Large-Posetᵉ =
    is-closed-under-sim-closure-operator-Large-Posetᵉ

  large-poset-closure-operator-Large-Posetᵉ :
    Large-Posetᵉ αᵉ βᵉ
  large-poset-closure-operator-Large-Posetᵉ =
    large-poset-Large-Subposetᵉ Pᵉ
      ( large-subposet-closure-operator-Large-Posetᵉ)

  leq-prop-closed-element-closure-operator-Large-Posetᵉ :
    Large-Relation-Propᵉ βᵉ closed-element-closure-operator-Large-Posetᵉ
  leq-prop-closed-element-closure-operator-Large-Posetᵉ =
    leq-prop-Large-Subposetᵉ Pᵉ
      ( large-subposet-closure-operator-Large-Posetᵉ)

  leq-closed-element-closure-operator-Large-Posetᵉ :
    Large-Relationᵉ βᵉ closed-element-closure-operator-Large-Posetᵉ
  leq-closed-element-closure-operator-Large-Posetᵉ =
    leq-Large-Subposetᵉ Pᵉ
      ( large-subposet-closure-operator-Large-Posetᵉ)

  is-prop-leq-closed-element-closure-operator-Large-Posetᵉ :
    is-prop-Large-Relationᵉ
      ( closed-element-closure-operator-Large-Posetᵉ)
      ( leq-closed-element-closure-operator-Large-Posetᵉ)
  is-prop-leq-closed-element-closure-operator-Large-Posetᵉ =
    is-prop-leq-Large-Subposetᵉ Pᵉ
      ( large-subposet-closure-operator-Large-Posetᵉ)

  refl-leq-closed-element-closure-operator-Large-Posetᵉ :
    is-reflexive-Large-Relationᵉ
      ( closed-element-closure-operator-Large-Posetᵉ)
      ( leq-closed-element-closure-operator-Large-Posetᵉ)
  refl-leq-closed-element-closure-operator-Large-Posetᵉ =
    refl-leq-Large-Subposetᵉ Pᵉ
      ( large-subposet-closure-operator-Large-Posetᵉ)

  antisymmetric-leq-closed-element-closure-operator-Large-Posetᵉ :
    is-antisymmetric-Large-Relationᵉ
      ( closed-element-closure-operator-Large-Posetᵉ)
      ( leq-closed-element-closure-operator-Large-Posetᵉ)
  antisymmetric-leq-closed-element-closure-operator-Large-Posetᵉ =
    antisymmetric-leq-Large-Subposetᵉ Pᵉ
      ( large-subposet-closure-operator-Large-Posetᵉ)

  transitive-leq-closed-element-closure-operator-Large-Posetᵉ :
    is-transitive-Large-Relationᵉ
      ( closed-element-closure-operator-Large-Posetᵉ)
      ( leq-closed-element-closure-operator-Large-Posetᵉ)
  transitive-leq-closed-element-closure-operator-Large-Posetᵉ =
    transitive-leq-Large-Subposetᵉ Pᵉ
      ( large-subposet-closure-operator-Large-Posetᵉ)
```