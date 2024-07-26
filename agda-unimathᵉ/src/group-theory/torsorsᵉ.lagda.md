# Torsors of abstract groups

```agda
module group-theory.torsorsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.0-connected-typesᵉ
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.mere-equalityᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.propositionsᵉ
open import foundation.retractionsᵉ
open import foundation.sectionsᵉ
open import foundation.setsᵉ
open import foundation.subtype-identity-principleᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.concrete-groupsᵉ
open import group-theory.equivalences-group-actionsᵉ
open import group-theory.group-actionsᵉ
open import group-theory.groupsᵉ
open import group-theory.homomorphisms-groupsᵉ
open import group-theory.isomorphisms-groupsᵉ
open import group-theory.mere-equivalences-group-actionsᵉ
open import group-theory.principal-group-actionsᵉ
open import group-theory.symmetric-groupsᵉ

open import higher-group-theory.higher-groupsᵉ
```

</details>

## Idea

Aᵉ **torsor**ᵉ ofᵉ aᵉ [group](group-theory.groups.mdᵉ) `G`ᵉ isᵉ aᵉ
[groupᵉ action](group-theory.group-actions.mdᵉ) whichᵉ isᵉ
[merelyᵉ equivalent](foundation.mere-equivalences.mdᵉ) to theᵉ
[principalᵉ groupᵉ action](group-theory.principal-group-actions.mdᵉ) ofᵉ `G`.ᵉ

## Definitions

### The predicate of being a torsor

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Xᵉ : action-Groupᵉ Gᵉ l2ᵉ)
  where

  is-torsor-prop-action-Groupᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  is-torsor-prop-action-Groupᵉ =
    mere-equiv-prop-action-Groupᵉ Gᵉ (principal-action-Groupᵉ Gᵉ) Xᵉ

  is-torsor-Groupᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-torsor-Groupᵉ = type-Propᵉ is-torsor-prop-action-Groupᵉ

  is-prop-is-torsor-Groupᵉ : is-propᵉ is-torsor-Groupᵉ
  is-prop-is-torsor-Groupᵉ = is-prop-type-Propᵉ is-torsor-prop-action-Groupᵉ
```

### The type of torsors

```agda
module _
  {l1ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ)
  where

  Torsor-Groupᵉ : (lᵉ : Level) → UUᵉ (l1ᵉ ⊔ lsuc lᵉ)
  Torsor-Groupᵉ lᵉ = Σᵉ (action-Groupᵉ Gᵉ lᵉ) (is-torsor-Groupᵉ Gᵉ)

module _
  {l1ᵉ lᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Xᵉ : Torsor-Groupᵉ Gᵉ lᵉ)
  where

  action-Torsor-Groupᵉ : action-Groupᵉ Gᵉ lᵉ
  action-Torsor-Groupᵉ = pr1ᵉ Xᵉ

  set-Torsor-Groupᵉ : Setᵉ lᵉ
  set-Torsor-Groupᵉ = set-action-Groupᵉ Gᵉ action-Torsor-Groupᵉ

  type-Torsor-Groupᵉ : UUᵉ lᵉ
  type-Torsor-Groupᵉ = type-Setᵉ set-Torsor-Groupᵉ

  is-set-type-Torsor-Groupᵉ : is-setᵉ type-Torsor-Groupᵉ
  is-set-type-Torsor-Groupᵉ = is-set-type-Setᵉ set-Torsor-Groupᵉ

  mul-hom-Torsor-Groupᵉ : hom-Groupᵉ Gᵉ (symmetric-Groupᵉ set-Torsor-Groupᵉ)
  mul-hom-Torsor-Groupᵉ = pr2ᵉ action-Torsor-Groupᵉ

  equiv-mul-Torsor-Groupᵉ : type-Groupᵉ Gᵉ → type-Torsor-Groupᵉ ≃ᵉ type-Torsor-Groupᵉ
  equiv-mul-Torsor-Groupᵉ = equiv-mul-action-Groupᵉ Gᵉ action-Torsor-Groupᵉ

  mul-Torsor-Groupᵉ : type-Groupᵉ Gᵉ → type-Torsor-Groupᵉ → type-Torsor-Groupᵉ
  mul-Torsor-Groupᵉ = mul-action-Groupᵉ Gᵉ action-Torsor-Groupᵉ

  is-torsor-action-Torsor-Groupᵉ : is-torsor-Groupᵉ Gᵉ action-Torsor-Groupᵉ
  is-torsor-action-Torsor-Groupᵉ = pr2ᵉ Xᵉ
```

### Principal torsor

```agda
module _
  {l1ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ)
  where

  principal-Torsor-Groupᵉ : Torsor-Groupᵉ Gᵉ l1ᵉ
  pr1ᵉ principal-Torsor-Groupᵉ = principal-action-Groupᵉ Gᵉ
  pr2ᵉ principal-Torsor-Groupᵉ =
    unit-trunc-Propᵉ (id-equiv-action-Groupᵉ Gᵉ (principal-action-Groupᵉ Gᵉ))
```

## Properties

### Characterization of the identity type of `Torsor-Group`

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Xᵉ : Torsor-Groupᵉ Gᵉ l2ᵉ)
  where

  equiv-Torsor-Groupᵉ :
    {l3ᵉ : Level} (Yᵉ : Torsor-Groupᵉ Gᵉ l3ᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  equiv-Torsor-Groupᵉ Yᵉ =
    equiv-action-Groupᵉ Gᵉ (action-Torsor-Groupᵉ Gᵉ Xᵉ) (action-Torsor-Groupᵉ Gᵉ Yᵉ)

  id-equiv-Torsor-Groupᵉ : equiv-Torsor-Groupᵉ Xᵉ
  id-equiv-Torsor-Groupᵉ = id-equiv-action-Groupᵉ Gᵉ (action-Torsor-Groupᵉ Gᵉ Xᵉ)

  equiv-eq-Torsor-Groupᵉ :
    (Yᵉ : Torsor-Groupᵉ Gᵉ l2ᵉ) → Xᵉ ＝ᵉ Yᵉ → equiv-Torsor-Groupᵉ Yᵉ
  equiv-eq-Torsor-Groupᵉ .Xᵉ reflᵉ = id-equiv-Torsor-Groupᵉ

  is-torsorial-equiv-Torsor-Groupᵉ :
    is-torsorialᵉ equiv-Torsor-Groupᵉ
  is-torsorial-equiv-Torsor-Groupᵉ =
    is-torsorial-Eq-subtypeᵉ
      ( is-torsorial-equiv-action-Groupᵉ Gᵉ (action-Torsor-Groupᵉ Gᵉ Xᵉ))
      ( is-prop-is-torsor-Groupᵉ Gᵉ)
      ( action-Torsor-Groupᵉ Gᵉ Xᵉ)
      ( id-equiv-Torsor-Groupᵉ)
      ( is-torsor-action-Torsor-Groupᵉ Gᵉ Xᵉ)

  is-equiv-equiv-eq-Torsor-Groupᵉ :
    (Yᵉ : Torsor-Groupᵉ Gᵉ l2ᵉ) →
    is-equivᵉ (equiv-eq-Torsor-Groupᵉ Yᵉ)
  is-equiv-equiv-eq-Torsor-Groupᵉ =
    fundamental-theorem-idᵉ
      is-torsorial-equiv-Torsor-Groupᵉ
      equiv-eq-Torsor-Groupᵉ

  eq-equiv-Torsor-Groupᵉ :
    (Yᵉ : Torsor-Groupᵉ Gᵉ l2ᵉ) → equiv-Torsor-Groupᵉ Yᵉ → Xᵉ ＝ᵉ Yᵉ
  eq-equiv-Torsor-Groupᵉ Yᵉ =
    map-inv-is-equivᵉ (is-equiv-equiv-eq-Torsor-Groupᵉ Yᵉ)

  extensionality-Torsor-Groupᵉ :
    (Yᵉ : Torsor-Groupᵉ Gᵉ l2ᵉ) → (Xᵉ ＝ᵉ Yᵉ) ≃ᵉ equiv-Torsor-Groupᵉ Yᵉ
  pr1ᵉ (extensionality-Torsor-Groupᵉ Yᵉ) = equiv-eq-Torsor-Groupᵉ Yᵉ
  pr2ᵉ (extensionality-Torsor-Groupᵉ Yᵉ) = is-equiv-equiv-eq-Torsor-Groupᵉ Yᵉ
```

### Characterization of the identity type of equivalences between `Torsor-Group`

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ)
  (Xᵉ : Torsor-Groupᵉ Gᵉ l2ᵉ)
  (Yᵉ : Torsor-Groupᵉ Gᵉ l3ᵉ)
  (eᵉ : equiv-Torsor-Groupᵉ Gᵉ Xᵉ Yᵉ)
  where

  htpy-equiv-Torsor-Groupᵉ :
    equiv-Torsor-Groupᵉ Gᵉ Xᵉ Yᵉ → UUᵉ (l2ᵉ ⊔ l3ᵉ)
  htpy-equiv-Torsor-Groupᵉ =
    htpy-equiv-action-Groupᵉ Gᵉ
      ( action-Torsor-Groupᵉ Gᵉ Xᵉ)
      ( action-Torsor-Groupᵉ Gᵉ Yᵉ)
      ( eᵉ)

  refl-htpy-equiv-Torsor-Groupᵉ :
    htpy-equiv-Torsor-Groupᵉ eᵉ
  refl-htpy-equiv-Torsor-Groupᵉ =
    refl-htpy-equiv-action-Groupᵉ Gᵉ
      ( action-Torsor-Groupᵉ Gᵉ Xᵉ)
      ( action-Torsor-Groupᵉ Gᵉ Yᵉ)
      ( eᵉ)

  htpy-eq-equiv-Torsor-Groupᵉ :
    (fᵉ : equiv-Torsor-Groupᵉ Gᵉ Xᵉ Yᵉ) →
    eᵉ ＝ᵉ fᵉ → htpy-equiv-Torsor-Groupᵉ fᵉ
  htpy-eq-equiv-Torsor-Groupᵉ .eᵉ reflᵉ =
    refl-htpy-equiv-Torsor-Groupᵉ

  is-torsorial-htpy-equiv-Torsor-Groupᵉ :
    is-torsorialᵉ htpy-equiv-Torsor-Groupᵉ
  is-torsorial-htpy-equiv-Torsor-Groupᵉ =
    is-torsorial-htpy-equiv-action-Groupᵉ Gᵉ
      ( action-Torsor-Groupᵉ Gᵉ Xᵉ)
      ( action-Torsor-Groupᵉ Gᵉ Yᵉ)
      ( eᵉ)

  is-equiv-htpy-eq-equiv-Torsor-Groupᵉ :
    (fᵉ : equiv-Torsor-Groupᵉ Gᵉ Xᵉ Yᵉ) →
    is-equivᵉ (htpy-eq-equiv-Torsor-Groupᵉ fᵉ)
  is-equiv-htpy-eq-equiv-Torsor-Groupᵉ =
    fundamental-theorem-idᵉ
      is-torsorial-htpy-equiv-Torsor-Groupᵉ
      htpy-eq-equiv-Torsor-Groupᵉ

  extensionality-equiv-Torsor-Groupᵉ :
    (fᵉ : equiv-Torsor-Groupᵉ Gᵉ Xᵉ Yᵉ) →
    (eᵉ ＝ᵉ fᵉ) ≃ᵉ htpy-equiv-Torsor-Groupᵉ fᵉ
  pr1ᵉ (extensionality-equiv-Torsor-Groupᵉ fᵉ) =
    htpy-eq-equiv-Torsor-Groupᵉ fᵉ
  pr2ᵉ (extensionality-equiv-Torsor-Groupᵉ fᵉ) =
    is-equiv-htpy-eq-equiv-Torsor-Groupᵉ fᵉ

  eq-htpy-equiv-Torsor-Groupᵉ :
    (fᵉ : equiv-Torsor-Groupᵉ Gᵉ Xᵉ Yᵉ) → htpy-equiv-Torsor-Groupᵉ fᵉ → eᵉ ＝ᵉ fᵉ
  eq-htpy-equiv-Torsor-Groupᵉ fᵉ =
    map-inv-is-equivᵉ (is-equiv-htpy-eq-equiv-Torsor-Groupᵉ fᵉ)
```

### Definition of the group `aut-principal-Torsor-Group` from a `Torsor-Group`

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ)
  (Xᵉ : Torsor-Groupᵉ Gᵉ l2ᵉ)
  (Yᵉ : Torsor-Groupᵉ Gᵉ l3ᵉ)
  where

  is-set-equiv-Torsor-Groupᵉ :
    is-setᵉ (equiv-Torsor-Groupᵉ Gᵉ Xᵉ Yᵉ)
  is-set-equiv-Torsor-Groupᵉ eᵉ fᵉ =
    is-prop-equivᵉ
      ( extensionality-equiv-Torsor-Groupᵉ Gᵉ Xᵉ Yᵉ eᵉ fᵉ)
      ( is-prop-Πᵉ
        ( λ xᵉ →
          is-set-type-Torsor-Groupᵉ Gᵉ Yᵉ
            ( map-equivᵉ (pr1ᵉ eᵉ) xᵉ)
            ( map-equivᵉ (pr1ᵉ fᵉ) xᵉ)))

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ)
  (Xᵉ : Torsor-Groupᵉ Gᵉ l2ᵉ)
  (Yᵉ : Torsor-Groupᵉ Gᵉ l3ᵉ)
  (Zᵉ : Torsor-Groupᵉ Gᵉ l4ᵉ)
  where

  comp-equiv-Torsor-Groupᵉ :
    equiv-Torsor-Groupᵉ Gᵉ Yᵉ Zᵉ →
    equiv-Torsor-Groupᵉ Gᵉ Xᵉ Yᵉ →
    equiv-Torsor-Groupᵉ Gᵉ Xᵉ Zᵉ
  comp-equiv-Torsor-Groupᵉ =
    comp-equiv-action-Groupᵉ Gᵉ
      ( action-Torsor-Groupᵉ Gᵉ Xᵉ)
      ( action-Torsor-Groupᵉ Gᵉ Yᵉ)
      ( action-Torsor-Groupᵉ Gᵉ Zᵉ)

  comp-equiv-Torsor-Group'ᵉ :
    equiv-Torsor-Groupᵉ Gᵉ Xᵉ Yᵉ →
    equiv-Torsor-Groupᵉ Gᵉ Yᵉ Zᵉ →
    equiv-Torsor-Groupᵉ Gᵉ Xᵉ Zᵉ
  comp-equiv-Torsor-Group'ᵉ eᵉ fᵉ =
    comp-equiv-Torsor-Groupᵉ fᵉ eᵉ

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ)
  (Xᵉ : Torsor-Groupᵉ Gᵉ l2ᵉ)
  (Yᵉ : Torsor-Groupᵉ Gᵉ l3ᵉ)
  where

  inv-equiv-Torsor-Groupᵉ :
    equiv-Torsor-Groupᵉ Gᵉ Xᵉ Yᵉ →
    equiv-Torsor-Groupᵉ Gᵉ Yᵉ Xᵉ
  inv-equiv-Torsor-Groupᵉ =
    inv-equiv-action-Groupᵉ Gᵉ
      ( action-Torsor-Groupᵉ Gᵉ Xᵉ)
      ( action-Torsor-Groupᵉ Gᵉ Yᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ)
  (X1ᵉ : Torsor-Groupᵉ Gᵉ l2ᵉ)
  (X2ᵉ : Torsor-Groupᵉ Gᵉ l3ᵉ)
  (X3ᵉ : Torsor-Groupᵉ Gᵉ l4ᵉ)
  (X4ᵉ : Torsor-Groupᵉ Gᵉ l5ᵉ)
  where

  associative-comp-equiv-Torsor-Groupᵉ :
    (hᵉ : equiv-Torsor-Groupᵉ Gᵉ X3ᵉ X4ᵉ)
    (gᵉ : equiv-Torsor-Groupᵉ Gᵉ X2ᵉ X3ᵉ)
    (fᵉ : equiv-Torsor-Groupᵉ Gᵉ X1ᵉ X2ᵉ) →
    ( comp-equiv-Torsor-Groupᵉ Gᵉ X1ᵉ X2ᵉ X4ᵉ
      ( comp-equiv-Torsor-Groupᵉ Gᵉ X2ᵉ X3ᵉ X4ᵉ hᵉ gᵉ)
      ( fᵉ)) ＝ᵉ
    ( comp-equiv-Torsor-Groupᵉ Gᵉ X1ᵉ X3ᵉ X4ᵉ hᵉ
      ( comp-equiv-Torsor-Groupᵉ Gᵉ X1ᵉ X2ᵉ X3ᵉ gᵉ fᵉ))
  associative-comp-equiv-Torsor-Groupᵉ hᵉ gᵉ fᵉ =
    eq-htpy-equiv-Torsor-Groupᵉ Gᵉ X1ᵉ X4ᵉ
      ( comp-equiv-Torsor-Groupᵉ Gᵉ X1ᵉ X2ᵉ X4ᵉ
        ( comp-equiv-Torsor-Groupᵉ Gᵉ X2ᵉ X3ᵉ X4ᵉ hᵉ gᵉ)
        ( fᵉ))
      ( comp-equiv-Torsor-Groupᵉ Gᵉ X1ᵉ X3ᵉ X4ᵉ hᵉ
        ( comp-equiv-Torsor-Groupᵉ Gᵉ X1ᵉ X2ᵉ X3ᵉ gᵉ fᵉ))
      ( refl-htpyᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ)
  (Xᵉ : Torsor-Groupᵉ Gᵉ l2ᵉ)
  (Yᵉ : Torsor-Groupᵉ Gᵉ l3ᵉ)
  where

  left-unit-law-comp-equiv-Torsor-Groupᵉ :
    (fᵉ : equiv-Torsor-Groupᵉ Gᵉ Xᵉ Yᵉ) →
    ( comp-equiv-Torsor-Groupᵉ Gᵉ Xᵉ Yᵉ Yᵉ (id-equiv-Torsor-Groupᵉ Gᵉ Yᵉ) fᵉ) ＝ᵉ fᵉ
  left-unit-law-comp-equiv-Torsor-Groupᵉ fᵉ =
    eq-htpy-equiv-Torsor-Groupᵉ Gᵉ Xᵉ Yᵉ
      ( comp-equiv-Torsor-Groupᵉ Gᵉ Xᵉ Yᵉ Yᵉ
        ( id-equiv-Torsor-Groupᵉ Gᵉ Yᵉ)
        ( fᵉ))
      ( fᵉ)
      ( refl-htpyᵉ)

  right-unit-law-comp-equiv-Torsor-Groupᵉ :
    (fᵉ : equiv-Torsor-Groupᵉ Gᵉ Xᵉ Yᵉ) →
    ( comp-equiv-Torsor-Groupᵉ Gᵉ Xᵉ Xᵉ Yᵉ fᵉ (id-equiv-Torsor-Groupᵉ Gᵉ Xᵉ)) ＝ᵉ fᵉ
  right-unit-law-comp-equiv-Torsor-Groupᵉ fᵉ =
    eq-htpy-equiv-Torsor-Groupᵉ Gᵉ Xᵉ Yᵉ
      ( comp-equiv-Torsor-Groupᵉ Gᵉ Xᵉ Xᵉ Yᵉ fᵉ
        ( id-equiv-Torsor-Groupᵉ Gᵉ Xᵉ))
      ( fᵉ)
      ( refl-htpyᵉ)

  left-inverse-law-comp-equiv-Torsor-Groupᵉ :
    (fᵉ : equiv-Torsor-Groupᵉ Gᵉ Xᵉ Yᵉ) →
    ( comp-equiv-Torsor-Groupᵉ Gᵉ Xᵉ Yᵉ Xᵉ (inv-equiv-Torsor-Groupᵉ Gᵉ Xᵉ Yᵉ fᵉ) fᵉ) ＝ᵉ
    ( id-equiv-Torsor-Groupᵉ Gᵉ Xᵉ)
  left-inverse-law-comp-equiv-Torsor-Groupᵉ fᵉ =
    eq-htpy-equiv-Torsor-Groupᵉ Gᵉ Xᵉ Xᵉ
      ( comp-equiv-Torsor-Groupᵉ Gᵉ Xᵉ Yᵉ Xᵉ
        ( inv-equiv-Torsor-Groupᵉ Gᵉ Xᵉ Yᵉ fᵉ)
        ( fᵉ))
      ( id-equiv-Torsor-Groupᵉ Gᵉ Xᵉ)
      ( is-retraction-map-inv-equivᵉ (pr1ᵉ fᵉ))

  right-inverse-law-comp-equiv-Torsor-Groupᵉ :
    (fᵉ : equiv-Torsor-Groupᵉ Gᵉ Xᵉ Yᵉ) →
    ( comp-equiv-Torsor-Groupᵉ Gᵉ Yᵉ Xᵉ Yᵉ fᵉ (inv-equiv-Torsor-Groupᵉ Gᵉ Xᵉ Yᵉ fᵉ)) ＝ᵉ
    ( id-equiv-Torsor-Groupᵉ Gᵉ Yᵉ)
  right-inverse-law-comp-equiv-Torsor-Groupᵉ fᵉ =
    eq-htpy-equiv-Torsor-Groupᵉ Gᵉ Yᵉ Yᵉ
      ( comp-equiv-Torsor-Groupᵉ Gᵉ Yᵉ Xᵉ Yᵉ fᵉ (inv-equiv-Torsor-Groupᵉ Gᵉ Xᵉ Yᵉ fᵉ))
      ( id-equiv-Torsor-Groupᵉ Gᵉ Yᵉ)
      ( is-section-map-inv-equivᵉ (pr1ᵉ fᵉ))

module _
  {l1ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ)
  where

  preserves-mul-equiv-eq-Torsor-Groupᵉ :
    {l2ᵉ : Level} (Xᵉ Yᵉ Zᵉ : Torsor-Groupᵉ Gᵉ l2ᵉ)
    (pᵉ : Xᵉ ＝ᵉ Yᵉ) (qᵉ : Yᵉ ＝ᵉ Zᵉ) →
    ( equiv-eq-Torsor-Groupᵉ Gᵉ Xᵉ Zᵉ (pᵉ ∙ᵉ qᵉ)) ＝ᵉ
    ( comp-equiv-Torsor-Groupᵉ Gᵉ Xᵉ Yᵉ Zᵉ
      ( equiv-eq-Torsor-Groupᵉ Gᵉ Yᵉ Zᵉ qᵉ)
      ( equiv-eq-Torsor-Groupᵉ Gᵉ Xᵉ Yᵉ pᵉ))
  preserves-mul-equiv-eq-Torsor-Groupᵉ Xᵉ .Xᵉ Zᵉ reflᵉ qᵉ =
    invᵉ
      ( right-unit-law-comp-equiv-Torsor-Groupᵉ Gᵉ Xᵉ Zᵉ
        ( equiv-eq-Torsor-Groupᵉ Gᵉ Xᵉ Zᵉ qᵉ))

module _
  {l1ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ)
  where

  aut-principal-Torsor-Groupᵉ : Groupᵉ l1ᵉ
  pr1ᵉ (pr1ᵉ (pr1ᵉ aut-principal-Torsor-Groupᵉ)) =
    equiv-Torsor-Groupᵉ Gᵉ
      ( principal-Torsor-Groupᵉ Gᵉ)
      ( principal-Torsor-Groupᵉ Gᵉ)
  pr2ᵉ (pr1ᵉ (pr1ᵉ aut-principal-Torsor-Groupᵉ)) =
    is-set-equiv-Torsor-Groupᵉ Gᵉ
      ( principal-Torsor-Groupᵉ Gᵉ)
      ( principal-Torsor-Groupᵉ Gᵉ)
  pr1ᵉ (pr2ᵉ (pr1ᵉ aut-principal-Torsor-Groupᵉ)) =
    comp-equiv-Torsor-Groupᵉ Gᵉ
      ( principal-Torsor-Groupᵉ Gᵉ)
      ( principal-Torsor-Groupᵉ Gᵉ)
      ( principal-Torsor-Groupᵉ Gᵉ)
  pr2ᵉ (pr2ᵉ (pr1ᵉ aut-principal-Torsor-Groupᵉ)) =
    associative-comp-equiv-Torsor-Groupᵉ Gᵉ
      ( principal-Torsor-Groupᵉ Gᵉ)
      ( principal-Torsor-Groupᵉ Gᵉ)
      ( principal-Torsor-Groupᵉ Gᵉ)
      ( principal-Torsor-Groupᵉ Gᵉ)
  pr1ᵉ (pr1ᵉ (pr2ᵉ aut-principal-Torsor-Groupᵉ)) =
    id-equiv-Torsor-Groupᵉ Gᵉ (principal-Torsor-Groupᵉ Gᵉ)
  pr1ᵉ (pr2ᵉ (pr1ᵉ (pr2ᵉ aut-principal-Torsor-Groupᵉ))) =
    left-unit-law-comp-equiv-Torsor-Groupᵉ Gᵉ
      ( principal-Torsor-Groupᵉ Gᵉ)
      ( principal-Torsor-Groupᵉ Gᵉ)
  pr2ᵉ (pr2ᵉ (pr1ᵉ (pr2ᵉ aut-principal-Torsor-Groupᵉ))) =
    right-unit-law-comp-equiv-Torsor-Groupᵉ Gᵉ
      ( principal-Torsor-Groupᵉ Gᵉ)
      ( principal-Torsor-Groupᵉ Gᵉ)
  pr1ᵉ (pr2ᵉ (pr2ᵉ aut-principal-Torsor-Groupᵉ)) =
    inv-equiv-Torsor-Groupᵉ Gᵉ
      ( principal-Torsor-Groupᵉ Gᵉ)
      ( principal-Torsor-Groupᵉ Gᵉ)
  pr1ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ aut-principal-Torsor-Groupᵉ))) =
    left-inverse-law-comp-equiv-Torsor-Groupᵉ Gᵉ
      ( principal-Torsor-Groupᵉ Gᵉ)
      ( principal-Torsor-Groupᵉ Gᵉ)
  pr2ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ aut-principal-Torsor-Groupᵉ))) =
    right-inverse-law-comp-equiv-Torsor-Groupᵉ Gᵉ
      ( principal-Torsor-Groupᵉ Gᵉ)
      ( principal-Torsor-Groupᵉ Gᵉ)
```

### The type `Torsor-Group` is `0-connected`

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Xᵉ : Torsor-Groupᵉ Gᵉ l2ᵉ)
  where

  mere-eq-Torsor-Groupᵉ :
    (Yᵉ : Torsor-Groupᵉ Gᵉ l2ᵉ) → mere-eqᵉ Xᵉ Yᵉ
  mere-eq-Torsor-Groupᵉ Yᵉ =
    apply-universal-property-trunc-Propᵉ
      ( pr2ᵉ Xᵉ)
      ( mere-eq-Propᵉ Xᵉ Yᵉ)
      ( λ eᵉ →
        apply-universal-property-trunc-Propᵉ
          ( pr2ᵉ Yᵉ)
          ( mere-eq-Propᵉ Xᵉ Yᵉ)
          ( λ fᵉ →
            unit-trunc-Propᵉ
              ( eq-equiv-Torsor-Groupᵉ Gᵉ Xᵉ Yᵉ
                ( comp-equiv-Torsor-Groupᵉ Gᵉ
                  ( Xᵉ)
                  ( principal-Torsor-Groupᵉ Gᵉ)
                  ( Yᵉ)
                  ( fᵉ)
                  ( inv-equiv-Torsor-Groupᵉ Gᵉ
                    ( principal-Torsor-Groupᵉ Gᵉ)
                    ( Xᵉ)
                    ( eᵉ))))))

module _
  {l1ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ)
  where

  is-0-connected-Torsor-Groupᵉ :
    is-0-connectedᵉ (Torsor-Groupᵉ Gᵉ l1ᵉ)
  is-0-connected-Torsor-Groupᵉ =
    is-0-connected-mere-eqᵉ
      ( principal-Torsor-Groupᵉ Gᵉ)
      ( mere-eq-Torsor-Groupᵉ Gᵉ (principal-Torsor-Groupᵉ Gᵉ))
```

### The group `aut-principal-Torsor-Group` is isomorphic to `G`

```agda
module _
  {l1ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ)
  where

  Eq-Torsor-Groupᵉ :
    (Xᵉ : Torsor-Groupᵉ Gᵉ l1ᵉ) → UUᵉ l1ᵉ
  Eq-Torsor-Groupᵉ Xᵉ = type-Torsor-Groupᵉ Gᵉ Xᵉ

  refl-Eq-Torsor-Groupᵉ :
    Eq-Torsor-Groupᵉ (principal-Torsor-Groupᵉ Gᵉ)
  refl-Eq-Torsor-Groupᵉ = unit-Groupᵉ Gᵉ

  Eq-equiv-Torsor-Groupᵉ :
    (Xᵉ : Torsor-Groupᵉ Gᵉ l1ᵉ) →
    equiv-Torsor-Groupᵉ Gᵉ (principal-Torsor-Groupᵉ Gᵉ) Xᵉ →
    Eq-Torsor-Groupᵉ Xᵉ
  Eq-equiv-Torsor-Groupᵉ Xᵉ (eᵉ ,ᵉ Hᵉ) = map-equivᵉ eᵉ (unit-Groupᵉ Gᵉ)

  preserves-mul-Eq-equiv-Torsor-Groupᵉ :
    ( eᵉ fᵉ :
      equiv-Torsor-Groupᵉ Gᵉ
        ( principal-Torsor-Groupᵉ Gᵉ)
        ( principal-Torsor-Groupᵉ Gᵉ)) →
    ( Eq-equiv-Torsor-Groupᵉ
      ( principal-Torsor-Groupᵉ Gᵉ)
      ( comp-equiv-Torsor-Groupᵉ Gᵉ
        ( principal-Torsor-Groupᵉ Gᵉ)
        ( principal-Torsor-Groupᵉ Gᵉ)
        ( principal-Torsor-Groupᵉ Gᵉ)
        ( fᵉ)
        ( eᵉ))) ＝ᵉ
    ( mul-Groupᵉ Gᵉ
      ( Eq-equiv-Torsor-Groupᵉ
        ( principal-Torsor-Groupᵉ Gᵉ)
        ( eᵉ))
      ( Eq-equiv-Torsor-Groupᵉ
        ( principal-Torsor-Groupᵉ Gᵉ)
        ( fᵉ)))
  preserves-mul-Eq-equiv-Torsor-Groupᵉ (eᵉ ,ᵉ Hᵉ) (fᵉ ,ᵉ Kᵉ) =
    ( apᵉ
      ( map-equivᵉ fᵉ)
      ( invᵉ (right-unit-law-mul-Groupᵉ Gᵉ (map-equivᵉ eᵉ (unit-Groupᵉ Gᵉ))))) ∙ᵉ
    ( Kᵉ (map-equivᵉ eᵉ (unit-Groupᵉ Gᵉ)) (unit-Groupᵉ Gᵉ))

  equiv-Eq-Torsor-Groupᵉ :
    Eq-Torsor-Groupᵉ (principal-Torsor-Groupᵉ Gᵉ) →
    equiv-Torsor-Groupᵉ Gᵉ
      ( principal-Torsor-Groupᵉ Gᵉ)
      ( principal-Torsor-Groupᵉ Gᵉ)
  pr1ᵉ (equiv-Eq-Torsor-Groupᵉ uᵉ) = equiv-mul-Group'ᵉ Gᵉ uᵉ
  pr2ᵉ (equiv-Eq-Torsor-Groupᵉ uᵉ) gᵉ xᵉ = associative-mul-Groupᵉ Gᵉ gᵉ xᵉ uᵉ

  is-section-equiv-Eq-Torsor-Groupᵉ :
    ( Eq-equiv-Torsor-Groupᵉ (principal-Torsor-Groupᵉ Gᵉ) ∘ᵉ
      equiv-Eq-Torsor-Groupᵉ) ~ᵉ
    ( idᵉ)
  is-section-equiv-Eq-Torsor-Groupᵉ uᵉ = left-unit-law-mul-Groupᵉ Gᵉ uᵉ

  is-retraction-equiv-Eq-Torsor-Groupᵉ :
    is-retractionᵉ
      ( Eq-equiv-Torsor-Groupᵉ (principal-Torsor-Groupᵉ Gᵉ))
      ( equiv-Eq-Torsor-Groupᵉ)
  is-retraction-equiv-Eq-Torsor-Groupᵉ eᵉ =
    eq-htpy-equiv-Torsor-Groupᵉ Gᵉ
      ( principal-Torsor-Groupᵉ Gᵉ)
      ( principal-Torsor-Groupᵉ Gᵉ)
      ( equiv-Eq-Torsor-Groupᵉ
        ( Eq-equiv-Torsor-Groupᵉ (principal-Torsor-Groupᵉ Gᵉ) eᵉ))
      ( eᵉ)
      ( λ gᵉ →
        ( invᵉ (pr2ᵉ eᵉ gᵉ (unit-Groupᵉ Gᵉ))) ∙ᵉ
        ( apᵉ (map-equivᵉ (pr1ᵉ eᵉ)) (right-unit-law-mul-Groupᵉ Gᵉ gᵉ)))

  abstract
    is-equiv-Eq-equiv-Torsor-Groupᵉ :
      (Xᵉ : Torsor-Groupᵉ Gᵉ l1ᵉ) →
      is-equivᵉ (Eq-equiv-Torsor-Groupᵉ Xᵉ)
    is-equiv-Eq-equiv-Torsor-Groupᵉ Xᵉ =
      apply-universal-property-trunc-Propᵉ
        ( is-torsor-action-Torsor-Groupᵉ Gᵉ Xᵉ)
        ( is-equiv-Propᵉ (Eq-equiv-Torsor-Groupᵉ Xᵉ))
        ( λ eᵉ →
          trᵉ
            ( λ Yᵉ → is-equivᵉ (Eq-equiv-Torsor-Groupᵉ Yᵉ))
            ( eq-equiv-Torsor-Groupᵉ Gᵉ (principal-Torsor-Groupᵉ Gᵉ) Xᵉ eᵉ)
            ( is-equiv-is-invertibleᵉ
                equiv-Eq-Torsor-Groupᵉ
                is-section-equiv-Eq-Torsor-Groupᵉ
                is-retraction-equiv-Eq-Torsor-Groupᵉ))

  equiv-Eq-equiv-Torsor-Groupᵉ :
    (Xᵉ : Torsor-Groupᵉ Gᵉ l1ᵉ) →
    (principal-Torsor-Groupᵉ Gᵉ ＝ᵉ Xᵉ) ≃ᵉ Eq-Torsor-Groupᵉ Xᵉ
  equiv-Eq-equiv-Torsor-Groupᵉ Xᵉ =
    ( Eq-equiv-Torsor-Groupᵉ Xᵉ ,ᵉ is-equiv-Eq-equiv-Torsor-Groupᵉ Xᵉ) ∘eᵉ
    ( extensionality-Torsor-Groupᵉ Gᵉ (principal-Torsor-Groupᵉ Gᵉ) Xᵉ)

  preserves-mul-equiv-Eq-equiv-Torsor-Groupᵉ :
    { pᵉ qᵉ : principal-Torsor-Groupᵉ Gᵉ ＝ᵉ principal-Torsor-Groupᵉ Gᵉ} →
    Idᵉ
      ( map-equivᵉ
        ( equiv-Eq-equiv-Torsor-Groupᵉ (principal-Torsor-Groupᵉ Gᵉ))
        ( pᵉ ∙ᵉ qᵉ))
      ( mul-Groupᵉ Gᵉ
        ( map-equivᵉ
          ( equiv-Eq-equiv-Torsor-Groupᵉ (principal-Torsor-Groupᵉ Gᵉ))
          ( pᵉ))
        ( map-equivᵉ
          ( equiv-Eq-equiv-Torsor-Groupᵉ (principal-Torsor-Groupᵉ Gᵉ))
          ( qᵉ)))
  preserves-mul-equiv-Eq-equiv-Torsor-Groupᵉ {pᵉ} {qᵉ} =
    ( apᵉ
      ( Eq-equiv-Torsor-Groupᵉ (principal-Torsor-Groupᵉ Gᵉ))
      ( preserves-mul-equiv-eq-Torsor-Groupᵉ Gᵉ
        ( principal-Torsor-Groupᵉ Gᵉ)
        ( principal-Torsor-Groupᵉ Gᵉ)
        ( principal-Torsor-Groupᵉ Gᵉ)
        ( pᵉ)
        ( qᵉ))) ∙ᵉ
    ( preserves-mul-Eq-equiv-Torsor-Groupᵉ
      ( equiv-eq-Torsor-Groupᵉ Gᵉ
        ( principal-Torsor-Groupᵉ Gᵉ)
        ( principal-Torsor-Groupᵉ Gᵉ)
        ( pᵉ))
      ( equiv-eq-Torsor-Groupᵉ Gᵉ
        ( principal-Torsor-Groupᵉ Gᵉ)
        ( principal-Torsor-Groupᵉ Gᵉ)
        ( qᵉ)))
```

### From torsors to concrete group

```agda
  ∞-group-Groupᵉ : ∞-Groupᵉ (lsuc l1ᵉ)
  pr1ᵉ (pr1ᵉ ∞-group-Groupᵉ) = Torsor-Groupᵉ Gᵉ l1ᵉ
  pr2ᵉ (pr1ᵉ ∞-group-Groupᵉ) = principal-Torsor-Groupᵉ Gᵉ
  pr2ᵉ ∞-group-Groupᵉ = is-0-connected-Torsor-Groupᵉ Gᵉ

  concrete-group-Groupᵉ : Concrete-Groupᵉ (lsuc l1ᵉ)
  pr1ᵉ concrete-group-Groupᵉ = ∞-group-Groupᵉ
  pr2ᵉ concrete-group-Groupᵉ =
    is-set-equivᵉ
      ( type-Groupᵉ Gᵉ)
      ( equiv-Eq-equiv-Torsor-Groupᵉ (principal-Torsor-Groupᵉ Gᵉ))
      ( is-set-type-Groupᵉ Gᵉ)

  classifying-type-Groupᵉ : UUᵉ (lsuc l1ᵉ)
  classifying-type-Groupᵉ = classifying-type-Concrete-Groupᵉ concrete-group-Groupᵉ

  shape-Groupᵉ : classifying-type-Groupᵉ
  shape-Groupᵉ = shape-Concrete-Groupᵉ concrete-group-Groupᵉ

  is-0-connected-classifying-type-Groupᵉ : is-0-connectedᵉ classifying-type-Groupᵉ
  is-0-connected-classifying-type-Groupᵉ =
    is-0-connected-classifying-type-Concrete-Groupᵉ concrete-group-Groupᵉ

  group-concrete-group-Groupᵉ :
    iso-Groupᵉ (group-Concrete-Groupᵉ concrete-group-Groupᵉ) Gᵉ
  group-concrete-group-Groupᵉ =
    iso-equiv-Groupᵉ
      ( group-Concrete-Groupᵉ concrete-group-Groupᵉ)
      ( Gᵉ)
      ( ( equiv-Eq-equiv-Torsor-Groupᵉ (principal-Torsor-Groupᵉ Gᵉ)) ,ᵉ
        ( λ {pᵉ} {qᵉ} → preserves-mul-equiv-Eq-equiv-Torsor-Groupᵉ {pᵉ} {qᵉ}))
```