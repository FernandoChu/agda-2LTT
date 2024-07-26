# Isomorphisms of group actions

```agda
module group-theory.isomorphisms-group-actionsᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.isomorphisms-in-large-precategoriesᵉ

open import foundation.commuting-squares-of-mapsᵉ
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.propositionsᵉ
open import foundation.subtypesᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import group-theory.equivalences-group-actionsᵉ
open import group-theory.group-actionsᵉ
open import group-theory.groupsᵉ
open import group-theory.homomorphisms-group-actionsᵉ
open import group-theory.precategory-of-group-actionsᵉ
```

</details>

## Definitions

### The predicate of being an isomorphism of group actions

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ)
  (Xᵉ : action-Groupᵉ Gᵉ l2ᵉ) (Yᵉ : action-Groupᵉ Gᵉ l3ᵉ)
  where

  is-iso-action-Groupᵉ :
    (fᵉ : hom-action-Groupᵉ Gᵉ Xᵉ Yᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  is-iso-action-Groupᵉ =
    is-iso-Large-Precategoryᵉ (action-Group-Large-Precategoryᵉ Gᵉ) {Xᵉ = Xᵉ} {Yᵉ = Yᵉ}

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ)
  (Xᵉ : action-Groupᵉ Gᵉ l2ᵉ) (Yᵉ : action-Groupᵉ Gᵉ l3ᵉ)
  (fᵉ : hom-action-Groupᵉ Gᵉ Xᵉ Yᵉ) (is-iso-fᵉ : is-iso-action-Groupᵉ Gᵉ Xᵉ Yᵉ fᵉ)
  where

  hom-inv-is-iso-action-Groupᵉ : hom-action-Groupᵉ Gᵉ Yᵉ Xᵉ
  hom-inv-is-iso-action-Groupᵉ =
    hom-inv-is-iso-Large-Precategoryᵉ
      ( action-Group-Large-Precategoryᵉ Gᵉ) {Xᵉ = Xᵉ} {Yᵉ = Yᵉ} fᵉ is-iso-fᵉ

  map-hom-inv-is-iso-action-Groupᵉ :
    type-action-Groupᵉ Gᵉ Yᵉ → type-action-Groupᵉ Gᵉ Xᵉ
  map-hom-inv-is-iso-action-Groupᵉ =
    map-hom-action-Groupᵉ Gᵉ Yᵉ Xᵉ hom-inv-is-iso-action-Groupᵉ

  is-section-hom-inv-is-iso-action-Groupᵉ :
    ( comp-hom-action-Groupᵉ Gᵉ Yᵉ Xᵉ Yᵉ fᵉ hom-inv-is-iso-action-Groupᵉ) ＝ᵉ
    ( id-hom-action-Groupᵉ Gᵉ Yᵉ)
  is-section-hom-inv-is-iso-action-Groupᵉ =
    is-section-hom-inv-is-iso-Large-Precategoryᵉ
      ( action-Group-Large-Precategoryᵉ Gᵉ) {Xᵉ = Xᵉ} {Yᵉ = Yᵉ} fᵉ is-iso-fᵉ

  is-retraction-hom-inv-is-iso-action-Groupᵉ :
    ( comp-hom-action-Groupᵉ Gᵉ Xᵉ Yᵉ Xᵉ hom-inv-is-iso-action-Groupᵉ fᵉ) ＝ᵉ
    ( id-hom-action-Groupᵉ Gᵉ Xᵉ)
  is-retraction-hom-inv-is-iso-action-Groupᵉ =
    is-retraction-hom-inv-is-iso-Large-Precategoryᵉ
      ( action-Group-Large-Precategoryᵉ Gᵉ) {Xᵉ = Xᵉ} {Yᵉ = Yᵉ} fᵉ is-iso-fᵉ
```

### The type of isomorphisms of group actions

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Xᵉ : action-Groupᵉ Gᵉ l2ᵉ)
  (Yᵉ : action-Groupᵉ Gᵉ l3ᵉ)
  where

  iso-action-Groupᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  iso-action-Groupᵉ =
    iso-Large-Precategoryᵉ (action-Group-Large-Precategoryᵉ Gᵉ) Xᵉ Yᵉ

  hom-iso-action-Groupᵉ :
    iso-action-Groupᵉ → hom-action-Groupᵉ Gᵉ Xᵉ Yᵉ
  hom-iso-action-Groupᵉ =
    hom-iso-Large-Precategoryᵉ (action-Group-Large-Precategoryᵉ Gᵉ) {Xᵉ = Xᵉ} {Yᵉ = Yᵉ}

  map-iso-action-Groupᵉ :
    iso-action-Groupᵉ →
    type-action-Groupᵉ Gᵉ Xᵉ → type-action-Groupᵉ Gᵉ Yᵉ
  map-iso-action-Groupᵉ fᵉ =
    map-hom-action-Groupᵉ Gᵉ Xᵉ Yᵉ (hom-iso-action-Groupᵉ fᵉ)

  preserves-action-iso-action-Groupᵉ :
    (fᵉ : iso-action-Groupᵉ) (gᵉ : type-Groupᵉ Gᵉ) →
    coherence-square-mapsᵉ
      ( map-iso-action-Groupᵉ fᵉ)
      ( mul-action-Groupᵉ Gᵉ Xᵉ gᵉ)
      ( mul-action-Groupᵉ Gᵉ Yᵉ gᵉ)
      ( map-iso-action-Groupᵉ fᵉ)
  preserves-action-iso-action-Groupᵉ fᵉ =
    preserves-action-hom-action-Groupᵉ Gᵉ Xᵉ Yᵉ (hom-iso-action-Groupᵉ fᵉ)

  hom-inv-iso-action-Groupᵉ :
    iso-action-Groupᵉ → hom-action-Groupᵉ Gᵉ Yᵉ Xᵉ
  hom-inv-iso-action-Groupᵉ =
    hom-inv-iso-Large-Precategoryᵉ
      ( action-Group-Large-Precategoryᵉ Gᵉ) {Xᵉ = Xᵉ} {Yᵉ = Yᵉ}

  map-hom-inv-iso-action-Groupᵉ :
    iso-action-Groupᵉ →
    type-action-Groupᵉ Gᵉ Yᵉ → type-action-Groupᵉ Gᵉ Xᵉ
  map-hom-inv-iso-action-Groupᵉ fᵉ =
    map-hom-action-Groupᵉ Gᵉ Yᵉ Xᵉ (hom-inv-iso-action-Groupᵉ fᵉ)

  is-section-hom-inv-iso-action-Groupᵉ :
    (fᵉ : iso-action-Groupᵉ) →
    ( comp-hom-action-Groupᵉ Gᵉ Yᵉ Xᵉ Yᵉ
      ( hom-iso-action-Groupᵉ fᵉ)
      ( hom-inv-iso-action-Groupᵉ fᵉ)) ＝ᵉ
    ( id-hom-action-Groupᵉ Gᵉ Yᵉ)
  is-section-hom-inv-iso-action-Groupᵉ =
    is-section-hom-inv-iso-Large-Precategoryᵉ
      ( action-Group-Large-Precategoryᵉ Gᵉ) {Xᵉ = Xᵉ} {Yᵉ = Yᵉ}

  is-retraction-hom-inv-iso-action-Groupᵉ :
    (fᵉ : iso-action-Groupᵉ) →
    ( comp-hom-action-Groupᵉ Gᵉ Xᵉ Yᵉ Xᵉ
      ( hom-inv-iso-action-Groupᵉ fᵉ)
      ( hom-iso-action-Groupᵉ fᵉ)) ＝ᵉ
    ( id-hom-action-Groupᵉ Gᵉ Xᵉ)
  is-retraction-hom-inv-iso-action-Groupᵉ =
    is-retraction-hom-inv-iso-Large-Precategoryᵉ
      ( action-Group-Large-Precategoryᵉ Gᵉ) {Xᵉ = Xᵉ} {Yᵉ = Yᵉ}

  is-iso-iso-action-Groupᵉ :
    (fᵉ : iso-action-Groupᵉ) → is-iso-action-Groupᵉ Gᵉ Xᵉ Yᵉ (hom-iso-action-Groupᵉ fᵉ)
  is-iso-iso-action-Groupᵉ =
    is-iso-iso-Large-Precategoryᵉ
      ( action-Group-Large-Precategoryᵉ Gᵉ) {Xᵉ = Xᵉ} {Yᵉ = Yᵉ}
```

## Properties

### Isomorphisms of group actions are equivalent to equivalences of group actions

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ)
  (Xᵉ : action-Groupᵉ Gᵉ l2ᵉ) (Yᵉ : action-Groupᵉ Gᵉ l3ᵉ)
  (fᵉ : hom-action-Groupᵉ Gᵉ Xᵉ Yᵉ)
  where

  is-equiv-hom-is-iso-action-Groupᵉ :
    is-iso-action-Groupᵉ Gᵉ Xᵉ Yᵉ fᵉ → is-equiv-hom-action-Groupᵉ Gᵉ Xᵉ Yᵉ fᵉ
  is-equiv-hom-is-iso-action-Groupᵉ is-iso-fᵉ =
    is-equiv-is-invertibleᵉ
      ( map-hom-inv-is-iso-action-Groupᵉ Gᵉ Xᵉ Yᵉ fᵉ is-iso-fᵉ)
      ( htpy-eq-hom-action-Groupᵉ Gᵉ Yᵉ Yᵉ
        ( comp-hom-action-Groupᵉ Gᵉ Yᵉ Xᵉ Yᵉ
          ( fᵉ)
          ( hom-inv-is-iso-action-Groupᵉ Gᵉ Xᵉ Yᵉ fᵉ is-iso-fᵉ))
        ( id-hom-action-Groupᵉ Gᵉ Yᵉ)
        ( is-section-hom-inv-is-iso-action-Groupᵉ Gᵉ Xᵉ Yᵉ fᵉ is-iso-fᵉ))
      ( htpy-eq-hom-action-Groupᵉ Gᵉ Xᵉ Xᵉ
        ( comp-hom-action-Groupᵉ Gᵉ Xᵉ Yᵉ Xᵉ
          ( hom-inv-is-iso-action-Groupᵉ Gᵉ Xᵉ Yᵉ fᵉ is-iso-fᵉ)
          ( fᵉ))
        ( id-hom-action-Groupᵉ Gᵉ Xᵉ)
        ( is-retraction-hom-inv-is-iso-action-Groupᵉ Gᵉ Xᵉ Yᵉ fᵉ is-iso-fᵉ))

  is-iso-is-equiv-hom-action-Groupᵉ :
    is-equiv-hom-action-Groupᵉ Gᵉ Xᵉ Yᵉ fᵉ → is-iso-action-Groupᵉ Gᵉ Xᵉ Yᵉ fᵉ
  pr1ᵉ (pr1ᵉ (is-iso-is-equiv-hom-action-Groupᵉ is-equiv-fᵉ)) =
    map-inv-is-equivᵉ is-equiv-fᵉ
  pr2ᵉ (pr1ᵉ (is-iso-is-equiv-hom-action-Groupᵉ is-equiv-fᵉ)) =
    preserves-action-map-inv-is-equiv-hom-action-Groupᵉ Gᵉ Xᵉ Yᵉ fᵉ is-equiv-fᵉ
  pr1ᵉ (pr2ᵉ (is-iso-is-equiv-hom-action-Groupᵉ is-equiv-fᵉ)) =
    eq-type-subtypeᵉ
      ( preserves-action-prop-Groupᵉ Gᵉ Yᵉ Yᵉ)
      ( eq-htpyᵉ (is-section-map-inv-is-equivᵉ is-equiv-fᵉ))
  pr2ᵉ (pr2ᵉ (is-iso-is-equiv-hom-action-Groupᵉ is-equiv-fᵉ)) =
    eq-type-subtypeᵉ
      ( preserves-action-prop-Groupᵉ Gᵉ Xᵉ Xᵉ)
      ( eq-htpyᵉ (is-retraction-map-inv-is-equivᵉ is-equiv-fᵉ))

  is-equiv-is-equiv-hom-is-iso-action-Groupᵉ :
    is-equivᵉ is-equiv-hom-is-iso-action-Groupᵉ
  is-equiv-is-equiv-hom-is-iso-action-Groupᵉ =
    is-equiv-has-converse-is-propᵉ
      ( is-prop-is-iso-Large-Precategoryᵉ
        ( action-Group-Large-Precategoryᵉ Gᵉ) {Xᵉ = Xᵉ} {Yᵉ = Yᵉ} fᵉ)
      ( is-property-is-equivᵉ (map-hom-action-Groupᵉ Gᵉ Xᵉ Yᵉ fᵉ))
      ( is-iso-is-equiv-hom-action-Groupᵉ)

  is-equiv-is-iso-is-equiv-hom-action-Groupᵉ :
    is-equivᵉ is-iso-is-equiv-hom-action-Groupᵉ
  is-equiv-is-iso-is-equiv-hom-action-Groupᵉ =
    is-equiv-has-converse-is-propᵉ
      ( is-property-is-equivᵉ (map-hom-action-Groupᵉ Gᵉ Xᵉ Yᵉ fᵉ))
      ( is-prop-is-iso-Large-Precategoryᵉ
        ( action-Group-Large-Precategoryᵉ Gᵉ) {Xᵉ = Xᵉ} {Yᵉ = Yᵉ} fᵉ)
      ( is-equiv-hom-is-iso-action-Groupᵉ)

  equiv-is-equiv-hom-is-iso-action-Groupᵉ :
    is-iso-action-Groupᵉ Gᵉ Xᵉ Yᵉ fᵉ ≃ᵉ is-equiv-hom-action-Groupᵉ Gᵉ Xᵉ Yᵉ fᵉ
  pr1ᵉ equiv-is-equiv-hom-is-iso-action-Groupᵉ =
    is-equiv-hom-is-iso-action-Groupᵉ
  pr2ᵉ equiv-is-equiv-hom-is-iso-action-Groupᵉ =
    is-equiv-is-equiv-hom-is-iso-action-Groupᵉ

  equiv-is-iso-is-equiv-hom-action-Groupᵉ :
    is-equiv-hom-action-Groupᵉ Gᵉ Xᵉ Yᵉ fᵉ ≃ᵉ is-iso-action-Groupᵉ Gᵉ Xᵉ Yᵉ fᵉ
  pr1ᵉ equiv-is-iso-is-equiv-hom-action-Groupᵉ =
    is-iso-is-equiv-hom-action-Groupᵉ
  pr2ᵉ equiv-is-iso-is-equiv-hom-action-Groupᵉ =
    is-equiv-is-iso-is-equiv-hom-action-Groupᵉ

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ)
  (Xᵉ : action-Groupᵉ Gᵉ l2ᵉ) (Yᵉ : action-Groupᵉ Gᵉ l3ᵉ)
  (fᵉ : iso-action-Groupᵉ Gᵉ Xᵉ Yᵉ)
  where

  is-equiv-map-iso-action-Groupᵉ : is-equivᵉ (map-iso-action-Groupᵉ Gᵉ Xᵉ Yᵉ fᵉ)
  is-equiv-map-iso-action-Groupᵉ =
    is-equiv-hom-is-iso-action-Groupᵉ Gᵉ Xᵉ Yᵉ
      ( hom-iso-action-Groupᵉ Gᵉ Xᵉ Yᵉ fᵉ)
      ( is-iso-iso-action-Groupᵉ Gᵉ Xᵉ Yᵉ fᵉ)

  equiv-iso-action-Groupᵉ : equiv-action-Groupᵉ Gᵉ Xᵉ Yᵉ
  pr1ᵉ (pr1ᵉ equiv-iso-action-Groupᵉ) = map-iso-action-Groupᵉ Gᵉ Xᵉ Yᵉ fᵉ
  pr2ᵉ (pr1ᵉ equiv-iso-action-Groupᵉ) = is-equiv-map-iso-action-Groupᵉ
  pr2ᵉ equiv-iso-action-Groupᵉ = preserves-action-iso-action-Groupᵉ Gᵉ Xᵉ Yᵉ fᵉ

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ)
  (Xᵉ : action-Groupᵉ Gᵉ l2ᵉ) (Yᵉ : action-Groupᵉ Gᵉ l3ᵉ)
  where

  equiv-equiv-iso-action-Groupᵉ :
    iso-action-Groupᵉ Gᵉ Xᵉ Yᵉ ≃ᵉ equiv-action-Groupᵉ Gᵉ Xᵉ Yᵉ
  equiv-equiv-iso-action-Groupᵉ =
    equiv-right-swap-Σᵉ ∘eᵉ
    equiv-totᵉ (equiv-is-equiv-hom-is-iso-action-Groupᵉ Gᵉ Xᵉ Yᵉ)

  equiv-iso-equiv-action-Groupᵉ :
    equiv-action-Groupᵉ Gᵉ Xᵉ Yᵉ ≃ᵉ iso-action-Groupᵉ Gᵉ Xᵉ Yᵉ
  equiv-iso-equiv-action-Groupᵉ =
    equiv-totᵉ (equiv-is-iso-is-equiv-hom-action-Groupᵉ Gᵉ Xᵉ Yᵉ) ∘eᵉ
    equiv-right-swap-Σᵉ
```

### Isomorphisms characterize equality of `G`-sets

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Xᵉ : action-Groupᵉ Gᵉ l2ᵉ)
  where

  is-torsorial-iso-action-Groupᵉ : is-torsorialᵉ (iso-action-Groupᵉ {l3ᵉ = l2ᵉ} Gᵉ Xᵉ)
  is-torsorial-iso-action-Groupᵉ =
    is-contr-equivᵉ
      ( Σᵉ (action-Groupᵉ Gᵉ l2ᵉ) (equiv-action-Groupᵉ Gᵉ Xᵉ))
      ( equiv-totᵉ (equiv-equiv-iso-action-Groupᵉ Gᵉ Xᵉ))
      ( is-torsorial-equiv-action-Groupᵉ Gᵉ Xᵉ)
```