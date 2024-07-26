# Galois connections

```agda
module order-theory.galois-connectionsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.identity-typesᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.propositionsᵉ
open import foundation.subtype-identity-principleᵉ
open import foundation.subtypesᵉ
open import foundation.universe-levelsᵉ

open import order-theory.order-preserving-maps-posetsᵉ
open import order-theory.posetsᵉ
```

</details>

## Idea

Aᵉ **Galoisᵉ connection**ᵉ betweenᵉ [posets](order-theory.posets.mdᵉ) `P`ᵉ andᵉ `Q`ᵉ isᵉ
aᵉ pairᵉ ofᵉ orderᵉ preservingᵉ mapsᵉ `fᵉ : Pᵉ → Q`ᵉ andᵉ `gᵉ : Qᵉ → P`ᵉ suchᵉ thatᵉ theᵉ
[logicalᵉ equivalence](foundation.logical-equivalences.mdᵉ)

```text
  (fᵉ xᵉ ≤ᵉ yᵉ) ↔ᵉ (xᵉ ≤ᵉ gᵉ yᵉ)
```

holdsᵉ forᵉ anyᵉ `xᵉ : P`ᵉ andᵉ `yᵉ : Q`.ᵉ

## Definitions

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Pᵉ : Posetᵉ l1ᵉ l2ᵉ) (Qᵉ : Posetᵉ l3ᵉ l4ᵉ)
  where

  adjoint-relation-galois-connection-Propᵉ :
    hom-Posetᵉ Pᵉ Qᵉ → hom-Posetᵉ Qᵉ Pᵉ → Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  adjoint-relation-galois-connection-Propᵉ fᵉ gᵉ =
    Π-Propᵉ
      ( type-Posetᵉ Pᵉ)
      ( λ xᵉ →
        Π-Propᵉ
          ( type-Posetᵉ Qᵉ)
          ( λ yᵉ →
            iff-Propᵉ
              ( leq-Poset-Propᵉ Qᵉ (map-hom-Posetᵉ Pᵉ Qᵉ fᵉ xᵉ) yᵉ)
              ( leq-Poset-Propᵉ Pᵉ xᵉ (map-hom-Posetᵉ Qᵉ Pᵉ gᵉ yᵉ))))

  is-lower-adjoint-Galois-Connectionᵉ :
    hom-Posetᵉ Pᵉ Qᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  is-lower-adjoint-Galois-Connectionᵉ fᵉ =
    type-subtypeᵉ (adjoint-relation-galois-connection-Propᵉ fᵉ)

  is-upper-adjoint-Galois-Connectionᵉ :
    hom-Posetᵉ Qᵉ Pᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  is-upper-adjoint-Galois-Connectionᵉ gᵉ =
    type-subtypeᵉ (λ fᵉ → adjoint-relation-galois-connection-Propᵉ fᵉ gᵉ)

  Galois-Connectionᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  Galois-Connectionᵉ =
    Σᵉ ( hom-Posetᵉ Qᵉ Pᵉ) is-upper-adjoint-Galois-Connectionᵉ

  module _
    (Gᵉ : Galois-Connectionᵉ)
    where

    upper-adjoint-Galois-Connectionᵉ : hom-Posetᵉ Qᵉ Pᵉ
    upper-adjoint-Galois-Connectionᵉ = pr1ᵉ Gᵉ

    map-upper-adjoint-Galois-Connectionᵉ :
      type-Posetᵉ Qᵉ → type-Posetᵉ Pᵉ
    map-upper-adjoint-Galois-Connectionᵉ =
      map-hom-Posetᵉ Qᵉ Pᵉ upper-adjoint-Galois-Connectionᵉ

    preserves-order-upper-adjoint-Galois-Connectionᵉ :
      preserves-order-Posetᵉ Qᵉ Pᵉ map-upper-adjoint-Galois-Connectionᵉ
    preserves-order-upper-adjoint-Galois-Connectionᵉ =
      preserves-order-map-hom-Posetᵉ Qᵉ Pᵉ upper-adjoint-Galois-Connectionᵉ

    is-upper-adjoint-upper-adjoint-Galois-Connectionᵉ :
      is-upper-adjoint-Galois-Connectionᵉ upper-adjoint-Galois-Connectionᵉ
    is-upper-adjoint-upper-adjoint-Galois-Connectionᵉ = pr2ᵉ Gᵉ

    lower-adjoint-Galois-Connectionᵉ : hom-Posetᵉ Pᵉ Qᵉ
    lower-adjoint-Galois-Connectionᵉ =
      pr1ᵉ is-upper-adjoint-upper-adjoint-Galois-Connectionᵉ

    map-lower-adjoint-Galois-Connectionᵉ :
      type-Posetᵉ Pᵉ → type-Posetᵉ Qᵉ
    map-lower-adjoint-Galois-Connectionᵉ =
      map-hom-Posetᵉ Pᵉ Qᵉ lower-adjoint-Galois-Connectionᵉ

    preserves-order-lower-adjoint-Galois-Connectionᵉ :
      preserves-order-Posetᵉ Pᵉ Qᵉ map-lower-adjoint-Galois-Connectionᵉ
    preserves-order-lower-adjoint-Galois-Connectionᵉ =
      preserves-order-map-hom-Posetᵉ Pᵉ Qᵉ lower-adjoint-Galois-Connectionᵉ

    adjoint-relation-Galois-Connectionᵉ :
      (xᵉ : type-Posetᵉ Pᵉ) (yᵉ : type-Posetᵉ Qᵉ) →
      leq-Posetᵉ Qᵉ (map-lower-adjoint-Galois-Connectionᵉ xᵉ) yᵉ ↔ᵉ
      leq-Posetᵉ Pᵉ xᵉ (map-upper-adjoint-Galois-Connectionᵉ yᵉ)
    adjoint-relation-Galois-Connectionᵉ =
      pr2ᵉ is-upper-adjoint-upper-adjoint-Galois-Connectionᵉ

    map-adjoint-relation-Galois-Connectionᵉ :
      (xᵉ : type-Posetᵉ Pᵉ) (yᵉ : type-Posetᵉ Qᵉ) →
      leq-Posetᵉ Qᵉ (map-lower-adjoint-Galois-Connectionᵉ xᵉ) yᵉ →
      leq-Posetᵉ Pᵉ xᵉ (map-upper-adjoint-Galois-Connectionᵉ yᵉ)
    map-adjoint-relation-Galois-Connectionᵉ xᵉ yᵉ =
      forward-implicationᵉ (adjoint-relation-Galois-Connectionᵉ xᵉ yᵉ)

    map-inv-adjoint-relation-Galois-Connectionᵉ :
      (xᵉ : type-Posetᵉ Pᵉ) (yᵉ : type-Posetᵉ Qᵉ) →
      leq-Posetᵉ Pᵉ xᵉ (map-upper-adjoint-Galois-Connectionᵉ yᵉ) →
      leq-Posetᵉ Qᵉ (map-lower-adjoint-Galois-Connectionᵉ xᵉ) yᵉ
    map-inv-adjoint-relation-Galois-Connectionᵉ xᵉ yᵉ =
      backward-implicationᵉ (adjoint-relation-Galois-Connectionᵉ xᵉ yᵉ)

    is-lower-adjoint-lower-adjoint-Galois-Connectionᵉ :
      is-lower-adjoint-Galois-Connectionᵉ lower-adjoint-Galois-Connectionᵉ
    pr1ᵉ is-lower-adjoint-lower-adjoint-Galois-Connectionᵉ =
      upper-adjoint-Galois-Connectionᵉ
    pr2ᵉ is-lower-adjoint-lower-adjoint-Galois-Connectionᵉ =
      adjoint-relation-Galois-Connectionᵉ
```

## Properties

### Being a lower adjoint of a Galois connection is a property

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Pᵉ : Posetᵉ l1ᵉ l2ᵉ) (Qᵉ : Posetᵉ l3ᵉ l4ᵉ)
  (fᵉ : hom-Posetᵉ Pᵉ Qᵉ)
  where

  htpy-is-lower-adjoint-Galois-Connectionᵉ :
    (gᵉ hᵉ : is-lower-adjoint-Galois-Connectionᵉ Pᵉ Qᵉ fᵉ) → UUᵉ (l1ᵉ ⊔ l3ᵉ)
  htpy-is-lower-adjoint-Galois-Connectionᵉ (gᵉ ,ᵉ Gᵉ) (hᵉ ,ᵉ Hᵉ) =
    htpy-hom-Posetᵉ Qᵉ Pᵉ gᵉ hᵉ

  refl-htpy-is-lower-adjoint-Galois-Connectionᵉ :
    (gᵉ : is-lower-adjoint-Galois-Connectionᵉ Pᵉ Qᵉ fᵉ) →
    htpy-is-lower-adjoint-Galois-Connectionᵉ gᵉ gᵉ
  refl-htpy-is-lower-adjoint-Galois-Connectionᵉ (gᵉ ,ᵉ Gᵉ) =
    refl-htpy-hom-Posetᵉ Qᵉ Pᵉ gᵉ

  extensionality-is-lower-adjoint-Galois-Connectionᵉ :
    (gᵉ hᵉ : is-lower-adjoint-Galois-Connectionᵉ Pᵉ Qᵉ fᵉ) →
    (gᵉ ＝ᵉ hᵉ) ≃ᵉ htpy-is-lower-adjoint-Galois-Connectionᵉ gᵉ hᵉ
  extensionality-is-lower-adjoint-Galois-Connectionᵉ (gᵉ ,ᵉ Gᵉ) =
    extensionality-type-subtypeᵉ
      ( adjoint-relation-galois-connection-Propᵉ Pᵉ Qᵉ fᵉ)
      ( Gᵉ)
      ( refl-htpy-is-lower-adjoint-Galois-Connectionᵉ (gᵉ ,ᵉ Gᵉ))
      ( extensionality-hom-Posetᵉ Qᵉ Pᵉ gᵉ)

  eq-htpy-is-lower-adjoint-Galois-Connectionᵉ :
    (gᵉ hᵉ : is-lower-adjoint-Galois-Connectionᵉ Pᵉ Qᵉ fᵉ) →
    htpy-is-lower-adjoint-Galois-Connectionᵉ gᵉ hᵉ → gᵉ ＝ᵉ hᵉ
  eq-htpy-is-lower-adjoint-Galois-Connectionᵉ gᵉ hᵉ =
    map-inv-equivᵉ (extensionality-is-lower-adjoint-Galois-Connectionᵉ gᵉ hᵉ)

  all-elements-equal-is-lower-adjoint-Galois-Connectionᵉ :
    (gᵉ hᵉ : is-lower-adjoint-Galois-Connectionᵉ Pᵉ Qᵉ fᵉ) → gᵉ ＝ᵉ hᵉ
  all-elements-equal-is-lower-adjoint-Galois-Connectionᵉ (gᵉ ,ᵉ Gᵉ) (hᵉ ,ᵉ Hᵉ) =
    eq-htpy-is-lower-adjoint-Galois-Connectionᵉ
      ( gᵉ ,ᵉ Gᵉ)
      ( hᵉ ,ᵉ Hᵉ)
      ( λ yᵉ →
        antisymmetric-leq-Posetᵉ Pᵉ
          ( map-hom-Posetᵉ Qᵉ Pᵉ gᵉ yᵉ)
          ( map-hom-Posetᵉ Qᵉ Pᵉ hᵉ yᵉ)
          ( forward-implicationᵉ
            ( Hᵉ (map-hom-Posetᵉ Qᵉ Pᵉ gᵉ yᵉ) yᵉ)
            ( backward-implicationᵉ
              ( Gᵉ (map-hom-Posetᵉ Qᵉ Pᵉ gᵉ yᵉ) yᵉ)
              ( refl-leq-Posetᵉ Pᵉ (map-hom-Posetᵉ Qᵉ Pᵉ gᵉ yᵉ))))
          ( forward-implicationᵉ
            ( Gᵉ (map-hom-Posetᵉ Qᵉ Pᵉ hᵉ yᵉ) yᵉ)
            ( backward-implicationᵉ
              ( Hᵉ (map-hom-Posetᵉ Qᵉ Pᵉ hᵉ yᵉ) yᵉ)
              ( refl-leq-Posetᵉ Pᵉ (map-hom-Posetᵉ Qᵉ Pᵉ hᵉ yᵉ)))))

  is-prop-is-lower-adjoint-Galois-Connectionᵉ :
    is-propᵉ (is-lower-adjoint-Galois-Connectionᵉ Pᵉ Qᵉ fᵉ)
  is-prop-is-lower-adjoint-Galois-Connectionᵉ =
    is-prop-all-elements-equalᵉ
      all-elements-equal-is-lower-adjoint-Galois-Connectionᵉ

  is-lower-adjoint-galois-connection-Propᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  pr1ᵉ is-lower-adjoint-galois-connection-Propᵉ =
    is-lower-adjoint-Galois-Connectionᵉ Pᵉ Qᵉ fᵉ
  pr2ᵉ is-lower-adjoint-galois-connection-Propᵉ =
    is-prop-is-lower-adjoint-Galois-Connectionᵉ
```

### Being a upper adjoint of a Galois connection is a property

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Pᵉ : Posetᵉ l1ᵉ l2ᵉ) (Qᵉ : Posetᵉ l3ᵉ l4ᵉ)
  (gᵉ : hom-Posetᵉ Qᵉ Pᵉ)
  where

  htpy-is-upper-adjoint-Galois-Connectionᵉ :
    (fᵉ hᵉ : is-upper-adjoint-Galois-Connectionᵉ Pᵉ Qᵉ gᵉ) → UUᵉ (l1ᵉ ⊔ l3ᵉ)
  htpy-is-upper-adjoint-Galois-Connectionᵉ (fᵉ ,ᵉ Fᵉ) (hᵉ ,ᵉ Hᵉ) =
    htpy-hom-Posetᵉ Pᵉ Qᵉ fᵉ hᵉ

  refl-htpy-is-upper-adjoint-Galois-Connectionᵉ :
    (fᵉ : is-upper-adjoint-Galois-Connectionᵉ Pᵉ Qᵉ gᵉ) →
    htpy-is-upper-adjoint-Galois-Connectionᵉ fᵉ fᵉ
  refl-htpy-is-upper-adjoint-Galois-Connectionᵉ (fᵉ ,ᵉ Fᵉ) =
    refl-htpy-hom-Posetᵉ Pᵉ Qᵉ fᵉ

  extensionality-is-upper-adjoint-Galois-Connectionᵉ :
    (fᵉ hᵉ : is-upper-adjoint-Galois-Connectionᵉ Pᵉ Qᵉ gᵉ) →
    (fᵉ ＝ᵉ hᵉ) ≃ᵉ htpy-is-upper-adjoint-Galois-Connectionᵉ fᵉ hᵉ
  extensionality-is-upper-adjoint-Galois-Connectionᵉ (fᵉ ,ᵉ Fᵉ) =
    extensionality-type-subtypeᵉ
      ( λ uᵉ → adjoint-relation-galois-connection-Propᵉ Pᵉ Qᵉ uᵉ gᵉ)
      ( Fᵉ)
      ( refl-htpy-is-upper-adjoint-Galois-Connectionᵉ (fᵉ ,ᵉ Fᵉ))
      ( extensionality-hom-Posetᵉ Pᵉ Qᵉ fᵉ)

  eq-htpy-is-upper-adjoint-Galois-Connectionᵉ :
    (fᵉ hᵉ : is-upper-adjoint-Galois-Connectionᵉ Pᵉ Qᵉ gᵉ) →
    htpy-is-upper-adjoint-Galois-Connectionᵉ fᵉ hᵉ → fᵉ ＝ᵉ hᵉ
  eq-htpy-is-upper-adjoint-Galois-Connectionᵉ fᵉ hᵉ =
    map-inv-equivᵉ (extensionality-is-upper-adjoint-Galois-Connectionᵉ fᵉ hᵉ)

  all-elements-equal-is-upper-adjoint-Galois-Connectionᵉ :
    (fᵉ hᵉ : is-upper-adjoint-Galois-Connectionᵉ Pᵉ Qᵉ gᵉ) → fᵉ ＝ᵉ hᵉ
  all-elements-equal-is-upper-adjoint-Galois-Connectionᵉ (fᵉ ,ᵉ Fᵉ) (hᵉ ,ᵉ Hᵉ) =
    eq-htpy-is-upper-adjoint-Galois-Connectionᵉ
      ( fᵉ ,ᵉ Fᵉ)
      ( hᵉ ,ᵉ Hᵉ)
      ( λ xᵉ →
        antisymmetric-leq-Posetᵉ Qᵉ
          ( map-hom-Posetᵉ Pᵉ Qᵉ fᵉ xᵉ)
          ( map-hom-Posetᵉ Pᵉ Qᵉ hᵉ xᵉ)
          ( backward-implicationᵉ
            ( Fᵉ xᵉ (map-hom-Posetᵉ Pᵉ Qᵉ hᵉ xᵉ))
            ( forward-implicationᵉ
              ( Hᵉ xᵉ (map-hom-Posetᵉ Pᵉ Qᵉ hᵉ xᵉ))
              ( refl-leq-Posetᵉ Qᵉ (map-hom-Posetᵉ Pᵉ Qᵉ hᵉ xᵉ))))
          ( backward-implicationᵉ
            ( Hᵉ xᵉ (map-hom-Posetᵉ Pᵉ Qᵉ fᵉ xᵉ))
            ( forward-implicationᵉ
              ( Fᵉ xᵉ (map-hom-Posetᵉ Pᵉ Qᵉ fᵉ xᵉ))
              ( refl-leq-Posetᵉ Qᵉ (map-hom-Posetᵉ Pᵉ Qᵉ fᵉ xᵉ)))))

  is-prop-is-upper-adjoint-Galois-Connectionᵉ :
    is-propᵉ (is-upper-adjoint-Galois-Connectionᵉ Pᵉ Qᵉ gᵉ)
  is-prop-is-upper-adjoint-Galois-Connectionᵉ =
    is-prop-all-elements-equalᵉ
      all-elements-equal-is-upper-adjoint-Galois-Connectionᵉ

  is-upper-adjoint-galois-connection-Propᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  pr1ᵉ is-upper-adjoint-galois-connection-Propᵉ =
    is-upper-adjoint-Galois-Connectionᵉ Pᵉ Qᵉ gᵉ
  pr2ᵉ is-upper-adjoint-galois-connection-Propᵉ =
    is-prop-is-upper-adjoint-Galois-Connectionᵉ
```

### Characterizing equalities of Galois connections

#### Characterizing equalities of Galois connections as homotopies of their upper adjoints

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Pᵉ : Posetᵉ l1ᵉ l2ᵉ) (Qᵉ : Posetᵉ l3ᵉ l4ᵉ)
  where

  htpy-upper-adjoint-Galois-Connectionᵉ :
    (Gᵉ Hᵉ : Galois-Connectionᵉ Pᵉ Qᵉ) → UUᵉ (l1ᵉ ⊔ l3ᵉ)
  htpy-upper-adjoint-Galois-Connectionᵉ Gᵉ Hᵉ =
    htpy-hom-Posetᵉ Qᵉ Pᵉ
      ( upper-adjoint-Galois-Connectionᵉ Pᵉ Qᵉ Gᵉ)
      ( upper-adjoint-Galois-Connectionᵉ Pᵉ Qᵉ Hᵉ)

  is-prop-htpy-upper-adjoint-Galois-Connectionᵉ :
    (Gᵉ Hᵉ : Galois-Connectionᵉ Pᵉ Qᵉ) →
    is-propᵉ (htpy-upper-adjoint-Galois-Connectionᵉ Gᵉ Hᵉ)
  is-prop-htpy-upper-adjoint-Galois-Connectionᵉ Gᵉ Hᵉ =
    is-prop-htpy-hom-Posetᵉ Qᵉ Pᵉ
      ( upper-adjoint-Galois-Connectionᵉ Pᵉ Qᵉ Gᵉ)
      ( upper-adjoint-Galois-Connectionᵉ Pᵉ Qᵉ Hᵉ)

  extensionality-upper-adjoint-Galois-Connectionᵉ :
    (Gᵉ Hᵉ : Galois-Connectionᵉ Pᵉ Qᵉ) →
    (Gᵉ ＝ᵉ Hᵉ) ≃ᵉ htpy-upper-adjoint-Galois-Connectionᵉ Gᵉ Hᵉ
  extensionality-upper-adjoint-Galois-Connectionᵉ (gᵉ ,ᵉ Gᵉ) =
    extensionality-type-subtypeᵉ
      ( is-upper-adjoint-galois-connection-Propᵉ Pᵉ Qᵉ)
      ( Gᵉ)
      ( refl-htpy-hom-Posetᵉ Qᵉ Pᵉ gᵉ)
      ( extensionality-hom-Posetᵉ Qᵉ Pᵉ gᵉ)

  eq-htpy-upper-adjoint-Galois-Connectionᵉ :
    (Gᵉ Hᵉ : Galois-Connectionᵉ Pᵉ Qᵉ) →
    htpy-upper-adjoint-Galois-Connectionᵉ Gᵉ Hᵉ → Gᵉ ＝ᵉ Hᵉ
  eq-htpy-upper-adjoint-Galois-Connectionᵉ Gᵉ Hᵉ =
    map-inv-equivᵉ (extensionality-upper-adjoint-Galois-Connectionᵉ Gᵉ Hᵉ)
```

#### Characterizing equalities of Galois connection by homotopies of their lower adjoints

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Pᵉ : Posetᵉ l1ᵉ l2ᵉ) (Qᵉ : Posetᵉ l3ᵉ l4ᵉ)
  where

  htpy-lower-adjoint-Galois-Connectionᵉ :
    (Gᵉ Hᵉ : Galois-Connectionᵉ Pᵉ Qᵉ) → UUᵉ (l1ᵉ ⊔ l3ᵉ)
  htpy-lower-adjoint-Galois-Connectionᵉ Gᵉ Hᵉ =
    htpy-hom-Posetᵉ Pᵉ Qᵉ
      ( lower-adjoint-Galois-Connectionᵉ Pᵉ Qᵉ Gᵉ)
      ( lower-adjoint-Galois-Connectionᵉ Pᵉ Qᵉ Hᵉ)

  is-prop-htpy-lower-adjoint-Galois-Connectionᵉ :
    (Gᵉ Hᵉ : Galois-Connectionᵉ Pᵉ Qᵉ) →
    is-propᵉ (htpy-lower-adjoint-Galois-Connectionᵉ Gᵉ Hᵉ)
  is-prop-htpy-lower-adjoint-Galois-Connectionᵉ Gᵉ Hᵉ =
    is-prop-htpy-hom-Posetᵉ Pᵉ Qᵉ
      ( lower-adjoint-Galois-Connectionᵉ Pᵉ Qᵉ Gᵉ)
      ( lower-adjoint-Galois-Connectionᵉ Pᵉ Qᵉ Hᵉ)

  htpy-upper-adjoint-htpy-lower-adjoint-Galois-Connectionᵉ :
    (Gᵉ Hᵉ : Galois-Connectionᵉ Pᵉ Qᵉ) →
    htpy-lower-adjoint-Galois-Connectionᵉ Gᵉ Hᵉ →
    htpy-upper-adjoint-Galois-Connectionᵉ Pᵉ Qᵉ Gᵉ Hᵉ
  htpy-upper-adjoint-htpy-lower-adjoint-Galois-Connectionᵉ Gᵉ Hᵉ Kᵉ yᵉ =
    antisymmetric-leq-Posetᵉ Pᵉ
      ( map-upper-adjoint-Galois-Connectionᵉ Pᵉ Qᵉ Gᵉ yᵉ)
      ( map-upper-adjoint-Galois-Connectionᵉ Pᵉ Qᵉ Hᵉ yᵉ)
      ( map-adjoint-relation-Galois-Connectionᵉ Pᵉ Qᵉ Hᵉ
        ( map-upper-adjoint-Galois-Connectionᵉ Pᵉ Qᵉ Gᵉ yᵉ)
        ( yᵉ)
        ( concatenate-eq-leq-Posetᵉ Qᵉ
          ( invᵉ (Kᵉ (map-upper-adjoint-Galois-Connectionᵉ Pᵉ Qᵉ Gᵉ yᵉ)))
          ( map-inv-adjoint-relation-Galois-Connectionᵉ Pᵉ Qᵉ Gᵉ
            ( map-upper-adjoint-Galois-Connectionᵉ Pᵉ Qᵉ Gᵉ yᵉ)
            ( yᵉ)
            ( refl-leq-Posetᵉ Pᵉ (map-upper-adjoint-Galois-Connectionᵉ Pᵉ Qᵉ Gᵉ yᵉ)))))
      ( map-adjoint-relation-Galois-Connectionᵉ Pᵉ Qᵉ Gᵉ
        ( map-upper-adjoint-Galois-Connectionᵉ Pᵉ Qᵉ Hᵉ yᵉ)
        ( yᵉ)
        ( concatenate-eq-leq-Posetᵉ Qᵉ
          ( Kᵉ (map-upper-adjoint-Galois-Connectionᵉ Pᵉ Qᵉ Hᵉ yᵉ))
          ( map-inv-adjoint-relation-Galois-Connectionᵉ Pᵉ Qᵉ Hᵉ
            ( map-upper-adjoint-Galois-Connectionᵉ Pᵉ Qᵉ Hᵉ yᵉ)
            ( yᵉ)
            ( refl-leq-Posetᵉ Pᵉ (map-upper-adjoint-Galois-Connectionᵉ Pᵉ Qᵉ Hᵉ yᵉ)))))

  htpy-lower-adjoint-htpy-upper-adjoint-Galois-Connectionᵉ :
    (Gᵉ Hᵉ : Galois-Connectionᵉ Pᵉ Qᵉ) →
    htpy-upper-adjoint-Galois-Connectionᵉ Pᵉ Qᵉ Gᵉ Hᵉ →
    htpy-lower-adjoint-Galois-Connectionᵉ Gᵉ Hᵉ
  htpy-lower-adjoint-htpy-upper-adjoint-Galois-Connectionᵉ Gᵉ Hᵉ Kᵉ xᵉ =
    antisymmetric-leq-Posetᵉ Qᵉ
      ( map-lower-adjoint-Galois-Connectionᵉ Pᵉ Qᵉ Gᵉ xᵉ)
      ( map-lower-adjoint-Galois-Connectionᵉ Pᵉ Qᵉ Hᵉ xᵉ)
      ( map-inv-adjoint-relation-Galois-Connectionᵉ Pᵉ Qᵉ Gᵉ xᵉ
        ( map-lower-adjoint-Galois-Connectionᵉ Pᵉ Qᵉ Hᵉ xᵉ)
        ( concatenate-leq-eq-Posetᵉ Pᵉ
          ( map-adjoint-relation-Galois-Connectionᵉ Pᵉ Qᵉ Hᵉ xᵉ
            ( map-lower-adjoint-Galois-Connectionᵉ Pᵉ Qᵉ Hᵉ xᵉ)
            ( refl-leq-Posetᵉ Qᵉ (map-lower-adjoint-Galois-Connectionᵉ Pᵉ Qᵉ Hᵉ xᵉ)))
          ( invᵉ (Kᵉ (map-lower-adjoint-Galois-Connectionᵉ Pᵉ Qᵉ Hᵉ xᵉ)))))
      ( map-inv-adjoint-relation-Galois-Connectionᵉ Pᵉ Qᵉ Hᵉ xᵉ
        ( map-lower-adjoint-Galois-Connectionᵉ Pᵉ Qᵉ Gᵉ xᵉ)
        ( concatenate-leq-eq-Posetᵉ Pᵉ
          ( map-adjoint-relation-Galois-Connectionᵉ Pᵉ Qᵉ Gᵉ xᵉ
            ( map-lower-adjoint-Galois-Connectionᵉ Pᵉ Qᵉ Gᵉ xᵉ)
            ( refl-leq-Posetᵉ Qᵉ (map-lower-adjoint-Galois-Connectionᵉ Pᵉ Qᵉ Gᵉ xᵉ)))
          ( Kᵉ (map-lower-adjoint-Galois-Connectionᵉ Pᵉ Qᵉ Gᵉ xᵉ))))

  is-equiv-htpy-upper-adjoint-htpy-lower-adjoint-Galois-Connectionᵉ :
    (Gᵉ Hᵉ : Galois-Connectionᵉ Pᵉ Qᵉ) →
    is-equivᵉ (htpy-upper-adjoint-htpy-lower-adjoint-Galois-Connectionᵉ Gᵉ Hᵉ)
  is-equiv-htpy-upper-adjoint-htpy-lower-adjoint-Galois-Connectionᵉ Gᵉ Hᵉ =
    is-equiv-has-converse-is-propᵉ
      ( is-prop-htpy-lower-adjoint-Galois-Connectionᵉ Gᵉ Hᵉ)
      ( is-prop-htpy-upper-adjoint-Galois-Connectionᵉ Pᵉ Qᵉ Gᵉ Hᵉ)
      ( htpy-lower-adjoint-htpy-upper-adjoint-Galois-Connectionᵉ Gᵉ Hᵉ)

  is-equiv-htpy-lower-adjoint-htpy-upper-adjoint-Galois-Connectionᵉ :
    (Gᵉ Hᵉ : Galois-Connectionᵉ Pᵉ Qᵉ) →
    is-equivᵉ (htpy-lower-adjoint-htpy-upper-adjoint-Galois-Connectionᵉ Gᵉ Hᵉ)
  is-equiv-htpy-lower-adjoint-htpy-upper-adjoint-Galois-Connectionᵉ Gᵉ Hᵉ =
    is-equiv-has-converse-is-propᵉ
      ( is-prop-htpy-upper-adjoint-Galois-Connectionᵉ Pᵉ Qᵉ Gᵉ Hᵉ)
      ( is-prop-htpy-lower-adjoint-Galois-Connectionᵉ Gᵉ Hᵉ)
      ( htpy-upper-adjoint-htpy-lower-adjoint-Galois-Connectionᵉ Gᵉ Hᵉ)

  equiv-htpy-lower-adjoint-htpy-upper-adjoint-Galois-Connectionᵉ :
    (Gᵉ Hᵉ : Galois-Connectionᵉ Pᵉ Qᵉ) →
    htpy-upper-adjoint-Galois-Connectionᵉ Pᵉ Qᵉ Gᵉ Hᵉ ≃ᵉ
    htpy-lower-adjoint-Galois-Connectionᵉ Gᵉ Hᵉ
  pr1ᵉ (equiv-htpy-lower-adjoint-htpy-upper-adjoint-Galois-Connectionᵉ Gᵉ Hᵉ) =
    htpy-lower-adjoint-htpy-upper-adjoint-Galois-Connectionᵉ Gᵉ Hᵉ
  pr2ᵉ (equiv-htpy-lower-adjoint-htpy-upper-adjoint-Galois-Connectionᵉ Gᵉ Hᵉ) =
    is-equiv-htpy-lower-adjoint-htpy-upper-adjoint-Galois-Connectionᵉ Gᵉ Hᵉ

  extensionality-lower-adjoint-Galois-Connectionᵉ :
    (Gᵉ Hᵉ : Galois-Connectionᵉ Pᵉ Qᵉ) →
    (Gᵉ ＝ᵉ Hᵉ) ≃ᵉ htpy-lower-adjoint-Galois-Connectionᵉ Gᵉ Hᵉ
  extensionality-lower-adjoint-Galois-Connectionᵉ Gᵉ Hᵉ =
    equiv-htpy-lower-adjoint-htpy-upper-adjoint-Galois-Connectionᵉ Gᵉ Hᵉ ∘eᵉ
    extensionality-upper-adjoint-Galois-Connectionᵉ Pᵉ Qᵉ Gᵉ Hᵉ
```

### `G y = GFG y` for any Galois connection `(G , F)`

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Pᵉ : Posetᵉ l1ᵉ l2ᵉ) (Qᵉ : Posetᵉ l3ᵉ l4ᵉ)
  (Gᵉ : Galois-Connectionᵉ Pᵉ Qᵉ)
  where

  compute-upper-lower-upper-adjoint-Galois-Connectionᵉ :
    (yᵉ : type-Posetᵉ Qᵉ) →
    map-upper-adjoint-Galois-Connectionᵉ Pᵉ Qᵉ Gᵉ yᵉ ＝ᵉ
    map-upper-adjoint-Galois-Connectionᵉ Pᵉ Qᵉ Gᵉ
      ( map-lower-adjoint-Galois-Connectionᵉ Pᵉ Qᵉ Gᵉ
        ( map-upper-adjoint-Galois-Connectionᵉ Pᵉ Qᵉ Gᵉ yᵉ))
  compute-upper-lower-upper-adjoint-Galois-Connectionᵉ yᵉ =
    antisymmetric-leq-Posetᵉ Pᵉ
      ( map-upper-adjoint-Galois-Connectionᵉ Pᵉ Qᵉ Gᵉ yᵉ)
      ( map-upper-adjoint-Galois-Connectionᵉ Pᵉ Qᵉ Gᵉ
        ( map-lower-adjoint-Galois-Connectionᵉ Pᵉ Qᵉ Gᵉ
          ( map-upper-adjoint-Galois-Connectionᵉ Pᵉ Qᵉ Gᵉ yᵉ)))
      ( map-adjoint-relation-Galois-Connectionᵉ Pᵉ Qᵉ Gᵉ
        ( map-upper-adjoint-Galois-Connectionᵉ Pᵉ Qᵉ Gᵉ yᵉ)
        ( map-lower-adjoint-Galois-Connectionᵉ Pᵉ Qᵉ Gᵉ
          ( map-upper-adjoint-Galois-Connectionᵉ Pᵉ Qᵉ Gᵉ yᵉ))
        ( refl-leq-Posetᵉ Qᵉ _))
      ( preserves-order-upper-adjoint-Galois-Connectionᵉ Pᵉ Qᵉ Gᵉ
        ( map-lower-adjoint-Galois-Connectionᵉ Pᵉ Qᵉ Gᵉ
          ( map-upper-adjoint-Galois-Connectionᵉ Pᵉ Qᵉ Gᵉ yᵉ))
        ( yᵉ)
        ( map-inv-adjoint-relation-Galois-Connectionᵉ Pᵉ Qᵉ Gᵉ
          ( map-upper-adjoint-Galois-Connectionᵉ Pᵉ Qᵉ Gᵉ yᵉ)
          ( yᵉ)
          ( refl-leq-Posetᵉ Pᵉ _)))
```

### `F x = FGF x` for any Galois connection `(G , F)`

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Pᵉ : Posetᵉ l1ᵉ l2ᵉ) (Qᵉ : Posetᵉ l3ᵉ l4ᵉ)
  (Gᵉ : Galois-Connectionᵉ Pᵉ Qᵉ)
  where

  compute-lower-upper-lower-adjoint-Galois-Connectionᵉ :
    (xᵉ : type-Posetᵉ Pᵉ) →
    map-lower-adjoint-Galois-Connectionᵉ Pᵉ Qᵉ Gᵉ xᵉ ＝ᵉ
    map-lower-adjoint-Galois-Connectionᵉ Pᵉ Qᵉ Gᵉ
      ( map-upper-adjoint-Galois-Connectionᵉ Pᵉ Qᵉ Gᵉ
        ( map-lower-adjoint-Galois-Connectionᵉ Pᵉ Qᵉ Gᵉ xᵉ))
  compute-lower-upper-lower-adjoint-Galois-Connectionᵉ xᵉ =
    antisymmetric-leq-Posetᵉ Qᵉ
      ( map-lower-adjoint-Galois-Connectionᵉ Pᵉ Qᵉ Gᵉ xᵉ)
      ( map-lower-adjoint-Galois-Connectionᵉ Pᵉ Qᵉ Gᵉ
        ( map-upper-adjoint-Galois-Connectionᵉ Pᵉ Qᵉ Gᵉ
          ( map-lower-adjoint-Galois-Connectionᵉ Pᵉ Qᵉ Gᵉ xᵉ)))
      ( preserves-order-lower-adjoint-Galois-Connectionᵉ Pᵉ Qᵉ Gᵉ xᵉ
        ( map-upper-adjoint-Galois-Connectionᵉ Pᵉ Qᵉ Gᵉ
          ( map-lower-adjoint-Galois-Connectionᵉ Pᵉ Qᵉ Gᵉ xᵉ))
        ( map-adjoint-relation-Galois-Connectionᵉ Pᵉ Qᵉ Gᵉ xᵉ
          ( map-lower-adjoint-Galois-Connectionᵉ Pᵉ Qᵉ Gᵉ xᵉ)
          ( refl-leq-Posetᵉ Qᵉ _)))
      ( map-inv-adjoint-relation-Galois-Connectionᵉ Pᵉ Qᵉ Gᵉ
        ( map-upper-adjoint-Galois-Connectionᵉ Pᵉ Qᵉ Gᵉ
          ( map-lower-adjoint-Galois-Connectionᵉ Pᵉ Qᵉ Gᵉ xᵉ))
        ( map-lower-adjoint-Galois-Connectionᵉ Pᵉ Qᵉ Gᵉ xᵉ)
        ( refl-leq-Posetᵉ Pᵉ _))
```

### The composite `FG` is idempotent for every Galois connection `(G , F)`

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Pᵉ : Posetᵉ l1ᵉ l2ᵉ) (Qᵉ : Posetᵉ l3ᵉ l4ᵉ)
  (Gᵉ : Galois-Connectionᵉ Pᵉ Qᵉ)
  where

  htpy-idempotent-lower-upper-Galois-Connectionᵉ :
    htpy-hom-Posetᵉ Qᵉ Qᵉ
      ( comp-hom-Posetᵉ Qᵉ Qᵉ Qᵉ
        ( comp-hom-Posetᵉ Qᵉ Pᵉ Qᵉ
          ( lower-adjoint-Galois-Connectionᵉ Pᵉ Qᵉ Gᵉ)
          ( upper-adjoint-Galois-Connectionᵉ Pᵉ Qᵉ Gᵉ))
        ( comp-hom-Posetᵉ Qᵉ Pᵉ Qᵉ
          ( lower-adjoint-Galois-Connectionᵉ Pᵉ Qᵉ Gᵉ)
          ( upper-adjoint-Galois-Connectionᵉ Pᵉ Qᵉ Gᵉ)))
      ( comp-hom-Posetᵉ Qᵉ Pᵉ Qᵉ
        ( lower-adjoint-Galois-Connectionᵉ Pᵉ Qᵉ Gᵉ)
        ( upper-adjoint-Galois-Connectionᵉ Pᵉ Qᵉ Gᵉ))
  htpy-idempotent-lower-upper-Galois-Connectionᵉ xᵉ =
    apᵉ
      ( map-lower-adjoint-Galois-Connectionᵉ Pᵉ Qᵉ Gᵉ)
      ( invᵉ
        ( compute-upper-lower-upper-adjoint-Galois-Connectionᵉ Pᵉ Qᵉ Gᵉ xᵉ))
```

### The composite `GF` is idempotent for every Galois connection `(G , F)`

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Pᵉ : Posetᵉ l1ᵉ l2ᵉ) (Qᵉ : Posetᵉ l3ᵉ l4ᵉ)
  (Gᵉ : Galois-Connectionᵉ Pᵉ Qᵉ)
  where

  htpy-idempotent-upper-lower-Galois-Connectionᵉ :
    htpy-hom-Posetᵉ Pᵉ Pᵉ
      ( comp-hom-Posetᵉ Pᵉ Pᵉ Pᵉ
        ( comp-hom-Posetᵉ Pᵉ Qᵉ Pᵉ
          ( upper-adjoint-Galois-Connectionᵉ Pᵉ Qᵉ Gᵉ)
          ( lower-adjoint-Galois-Connectionᵉ Pᵉ Qᵉ Gᵉ))
        ( comp-hom-Posetᵉ Pᵉ Qᵉ Pᵉ
          ( upper-adjoint-Galois-Connectionᵉ Pᵉ Qᵉ Gᵉ)
          ( lower-adjoint-Galois-Connectionᵉ Pᵉ Qᵉ Gᵉ)))
      ( comp-hom-Posetᵉ Pᵉ Qᵉ Pᵉ
        ( upper-adjoint-Galois-Connectionᵉ Pᵉ Qᵉ Gᵉ)
        ( lower-adjoint-Galois-Connectionᵉ Pᵉ Qᵉ Gᵉ))
  htpy-idempotent-upper-lower-Galois-Connectionᵉ yᵉ =
    apᵉ
      ( map-upper-adjoint-Galois-Connectionᵉ Pᵉ Qᵉ Gᵉ)
      ( invᵉ
        ( compute-lower-upper-lower-adjoint-Galois-Connectionᵉ Pᵉ Qᵉ Gᵉ yᵉ))
```

## References

{{#bibliographyᵉ}} {{#referenceᵉ EKMS93ᵉ}}