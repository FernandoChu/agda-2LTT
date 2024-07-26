# The precategory of maps and natural transformations between two precategories

```agda
module category-theory.precategory-of-maps-precategoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.composition-operations-on-binary-families-of-setsᵉ
open import category-theory.isomorphisms-in-precategoriesᵉ
open import category-theory.maps-precategoriesᵉ
open import category-theory.natural-isomorphisms-maps-precategoriesᵉ
open import category-theory.natural-transformations-maps-precategoriesᵉ
open import category-theory.precategoriesᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.propositionsᵉ
open import foundation.strictly-involutive-identity-typesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

[Maps](category-theory.maps-precategories.mdᵉ) betweenᵉ
[precategories](category-theory.precategories.mdᵉ) andᵉ
[naturalᵉ transformations](category-theory.natural-transformations-maps-precategories.mdᵉ)
betweenᵉ themᵉ introduceᵉ aᵉ newᵉ precategoryᵉ whoseᵉ identityᵉ mapᵉ andᵉ compositionᵉ
structureᵉ areᵉ inheritedᵉ pointwiseᵉ fromᵉ theᵉ codomainᵉ precategory.ᵉ Thisᵉ isᵉ calledᵉ
theᵉ **precategoryᵉ ofᵉ maps**.ᵉ

## Definitions

### The precategory of maps and natural transformations between precategories

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ) (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  where

  comp-hom-map-precategory-Precategoryᵉ :
    {Fᵉ Gᵉ Hᵉ : map-Precategoryᵉ Cᵉ Dᵉ} →
    natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Gᵉ Hᵉ →
    natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ →
    natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Hᵉ
  comp-hom-map-precategory-Precategoryᵉ {Fᵉ} {Gᵉ} {Hᵉ} =
    comp-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ Hᵉ

  associative-comp-hom-map-precategory-Precategoryᵉ :
    {Fᵉ Gᵉ Hᵉ Iᵉ : map-Precategoryᵉ Cᵉ Dᵉ}
    (hᵉ : natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Hᵉ Iᵉ)
    (gᵉ : natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Gᵉ Hᵉ)
    (fᵉ : natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ) →
    comp-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ Iᵉ
      ( comp-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Gᵉ Hᵉ Iᵉ hᵉ gᵉ)
      ( fᵉ) ＝ᵉ
    comp-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Hᵉ Iᵉ
      ( hᵉ)
      ( comp-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ Hᵉ gᵉ fᵉ)
  associative-comp-hom-map-precategory-Precategoryᵉ {Fᵉ} {Gᵉ} {Hᵉ} {Iᵉ} hᵉ gᵉ fᵉ =
    associative-comp-natural-transformation-map-Precategoryᵉ
      Cᵉ Dᵉ Fᵉ Gᵉ Hᵉ Iᵉ fᵉ gᵉ hᵉ

  involutive-eq-associative-comp-hom-map-precategory-Precategoryᵉ :
    {Fᵉ Gᵉ Hᵉ Iᵉ : map-Precategoryᵉ Cᵉ Dᵉ}
    (hᵉ : natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Hᵉ Iᵉ)
    (gᵉ : natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Gᵉ Hᵉ)
    (fᵉ : natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ) →
    comp-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ Iᵉ
      ( comp-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Gᵉ Hᵉ Iᵉ hᵉ gᵉ)
      ( fᵉ) ＝ⁱᵉ
    comp-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Hᵉ Iᵉ
      ( hᵉ)
      ( comp-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ Hᵉ gᵉ fᵉ)
  involutive-eq-associative-comp-hom-map-precategory-Precategoryᵉ
    { Fᵉ} {Gᵉ} {Hᵉ} {Iᵉ} hᵉ gᵉ fᵉ =
    involutive-eq-associative-comp-natural-transformation-map-Precategoryᵉ
      Cᵉ Dᵉ Fᵉ Gᵉ Hᵉ Iᵉ fᵉ gᵉ hᵉ

  associative-composition-operation-map-precategory-Precategoryᵉ :
    associative-composition-operation-binary-family-Setᵉ
      ( natural-transformation-map-set-Precategoryᵉ Cᵉ Dᵉ)
  pr1ᵉ associative-composition-operation-map-precategory-Precategoryᵉ
    {Fᵉ} {Gᵉ} {Hᵉ} =
    comp-hom-map-precategory-Precategoryᵉ {Fᵉ} {Gᵉ} {Hᵉ}
  pr2ᵉ
    associative-composition-operation-map-precategory-Precategoryᵉ
      {Fᵉ} {Gᵉ} {Hᵉ} {Iᵉ} hᵉ gᵉ fᵉ =
    involutive-eq-associative-comp-hom-map-precategory-Precategoryᵉ
      { Fᵉ} {Gᵉ} {Hᵉ} {Iᵉ} hᵉ gᵉ fᵉ

  id-hom-map-precategory-Precategoryᵉ :
    (Fᵉ : map-Precategoryᵉ Cᵉ Dᵉ) → natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Fᵉ
  id-hom-map-precategory-Precategoryᵉ =
    id-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ

  left-unit-law-comp-hom-map-precategory-Precategoryᵉ :
    {Fᵉ Gᵉ : map-Precategoryᵉ Cᵉ Dᵉ}
    (αᵉ : natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ) →
    ( comp-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ Gᵉ
      ( id-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Gᵉ) αᵉ) ＝ᵉ
    ( αᵉ)
  left-unit-law-comp-hom-map-precategory-Precategoryᵉ {Fᵉ} {Gᵉ} =
    left-unit-law-comp-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ

  right-unit-law-comp-hom-map-precategory-Precategoryᵉ :
    {Fᵉ Gᵉ : map-Precategoryᵉ Cᵉ Dᵉ}
    (αᵉ : natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ) →
    ( comp-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Fᵉ Gᵉ
        αᵉ (id-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ)) ＝ᵉ
    ( αᵉ)
  right-unit-law-comp-hom-map-precategory-Precategoryᵉ {Fᵉ} {Gᵉ} =
    right-unit-law-comp-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ

  is-unital-composition-operation-map-precategory-Precategoryᵉ :
    is-unital-composition-operation-binary-family-Setᵉ
      ( natural-transformation-map-set-Precategoryᵉ Cᵉ Dᵉ)
      ( comp-hom-map-precategory-Precategoryᵉ)
  pr1ᵉ is-unital-composition-operation-map-precategory-Precategoryᵉ =
    id-hom-map-precategory-Precategoryᵉ
  pr1ᵉ
    ( pr2ᵉ is-unital-composition-operation-map-precategory-Precategoryᵉ)
    { Fᵉ} {Gᵉ} =
    left-unit-law-comp-hom-map-precategory-Precategoryᵉ {Fᵉ} {Gᵉ}
  pr2ᵉ
    ( pr2ᵉ is-unital-composition-operation-map-precategory-Precategoryᵉ)
    { Fᵉ} {Gᵉ} =
    right-unit-law-comp-hom-map-precategory-Precategoryᵉ {Fᵉ} {Gᵉ}

  map-precategory-Precategoryᵉ :
    Precategoryᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ) (l1ᵉ ⊔ l2ᵉ ⊔ l4ᵉ)
  pr1ᵉ map-precategory-Precategoryᵉ = map-Precategoryᵉ Cᵉ Dᵉ
  pr1ᵉ (pr2ᵉ map-precategory-Precategoryᵉ) =
    natural-transformation-map-set-Precategoryᵉ Cᵉ Dᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ map-precategory-Precategoryᵉ)) =
    associative-composition-operation-map-precategory-Precategoryᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ map-precategory-Precategoryᵉ)) =
    is-unital-composition-operation-map-precategory-Precategoryᵉ
```

## Properties

### Isomorphisms in the map precategory are natural isomorphisms

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ Gᵉ : map-Precategoryᵉ Cᵉ Dᵉ)
  where

  is-iso-map-is-natural-isomorphism-map-Precategoryᵉ :
    (fᵉ : natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ) →
    is-natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ fᵉ →
    is-iso-Precategoryᵉ (map-precategory-Precategoryᵉ Cᵉ Dᵉ) {Fᵉ} {Gᵉ} fᵉ
  pr1ᵉ (is-iso-map-is-natural-isomorphism-map-Precategoryᵉ fᵉ is-iso-fᵉ) =
    natural-transformation-map-inv-is-natural-isomorphism-map-Precategoryᵉ
      Cᵉ Dᵉ Fᵉ Gᵉ fᵉ is-iso-fᵉ
  pr1ᵉ (pr2ᵉ (is-iso-map-is-natural-isomorphism-map-Precategoryᵉ fᵉ is-iso-fᵉ)) =
    is-section-natural-transformation-map-inv-is-natural-isomorphism-map-Precategoryᵉ
      Cᵉ Dᵉ Fᵉ Gᵉ fᵉ is-iso-fᵉ
  pr2ᵉ (pr2ᵉ (is-iso-map-is-natural-isomorphism-map-Precategoryᵉ fᵉ is-iso-fᵉ)) =
    is-retraction-natural-transformation-map-inv-is-natural-isomorphism-map-Precategoryᵉ
      Cᵉ Dᵉ Fᵉ Gᵉ fᵉ is-iso-fᵉ

  is-natural-isomorphism-map-is-iso-map-Precategoryᵉ :
    (fᵉ : natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ) →
    is-iso-Precategoryᵉ (map-precategory-Precategoryᵉ Cᵉ Dᵉ) {Fᵉ} {Gᵉ} fᵉ →
    is-natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ fᵉ
  pr1ᵉ (is-natural-isomorphism-map-is-iso-map-Precategoryᵉ fᵉ is-iso-fᵉ xᵉ) =
    hom-family-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Gᵉ Fᵉ
      ( hom-inv-is-iso-Precategoryᵉ
        ( map-precategory-Precategoryᵉ Cᵉ Dᵉ) {Fᵉ} {Gᵉ} is-iso-fᵉ)
      ( xᵉ)
  pr1ᵉ (pr2ᵉ (is-natural-isomorphism-map-is-iso-map-Precategoryᵉ fᵉ is-iso-fᵉ xᵉ)) =
    htpy-eqᵉ
      ( apᵉ
        ( hom-family-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Gᵉ Gᵉ)
        ( is-section-hom-inv-is-iso-Precategoryᵉ
          ( map-precategory-Precategoryᵉ Cᵉ Dᵉ) {Fᵉ} {Gᵉ} is-iso-fᵉ))
      ( xᵉ)
  pr2ᵉ (pr2ᵉ (is-natural-isomorphism-map-is-iso-map-Precategoryᵉ fᵉ is-iso-fᵉ xᵉ)) =
    htpy-eqᵉ
      ( apᵉ
        ( hom-family-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Fᵉ)
        ( is-retraction-hom-inv-is-iso-Precategoryᵉ
          ( map-precategory-Precategoryᵉ Cᵉ Dᵉ) {Fᵉ} {Gᵉ} is-iso-fᵉ))
      ( xᵉ)

  is-equiv-is-iso-map-is-natural-isomorphism-map-Precategoryᵉ :
    (fᵉ : natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ) →
    is-equivᵉ (is-iso-map-is-natural-isomorphism-map-Precategoryᵉ fᵉ)
  is-equiv-is-iso-map-is-natural-isomorphism-map-Precategoryᵉ fᵉ =
    is-equiv-has-converse-is-propᵉ
      ( is-prop-is-natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ fᵉ)
      ( is-prop-is-iso-Precategoryᵉ
        ( map-precategory-Precategoryᵉ Cᵉ Dᵉ) {Fᵉ} {Gᵉ} fᵉ)
      ( is-natural-isomorphism-map-is-iso-map-Precategoryᵉ fᵉ)

  is-equiv-is-natural-isomorphism-map-is-iso-map-Precategoryᵉ :
    (fᵉ : natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ) →
    is-equivᵉ (is-natural-isomorphism-map-is-iso-map-Precategoryᵉ fᵉ)
  is-equiv-is-natural-isomorphism-map-is-iso-map-Precategoryᵉ fᵉ =
    is-equiv-has-converse-is-propᵉ
      ( is-prop-is-iso-Precategoryᵉ
        ( map-precategory-Precategoryᵉ Cᵉ Dᵉ) {Fᵉ} {Gᵉ} fᵉ)
      ( is-prop-is-natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ fᵉ)
      ( is-iso-map-is-natural-isomorphism-map-Precategoryᵉ fᵉ)

  equiv-is-iso-map-is-natural-isomorphism-map-Precategoryᵉ :
    (fᵉ : natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ) →
    is-natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ fᵉ ≃ᵉ
    is-iso-Precategoryᵉ (map-precategory-Precategoryᵉ Cᵉ Dᵉ) {Fᵉ} {Gᵉ} fᵉ
  pr1ᵉ (equiv-is-iso-map-is-natural-isomorphism-map-Precategoryᵉ fᵉ) =
    is-iso-map-is-natural-isomorphism-map-Precategoryᵉ fᵉ
  pr2ᵉ (equiv-is-iso-map-is-natural-isomorphism-map-Precategoryᵉ fᵉ) =
    is-equiv-is-iso-map-is-natural-isomorphism-map-Precategoryᵉ fᵉ

  equiv-is-natural-isomorphism-map-is-iso-map-Precategoryᵉ :
    (fᵉ : natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ) →
    is-iso-Precategoryᵉ (map-precategory-Precategoryᵉ Cᵉ Dᵉ) {Fᵉ} {Gᵉ} fᵉ ≃ᵉ
    is-natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ fᵉ
  pr1ᵉ (equiv-is-natural-isomorphism-map-is-iso-map-Precategoryᵉ fᵉ) =
    is-natural-isomorphism-map-is-iso-map-Precategoryᵉ fᵉ
  pr2ᵉ (equiv-is-natural-isomorphism-map-is-iso-map-Precategoryᵉ fᵉ) =
    is-equiv-is-natural-isomorphism-map-is-iso-map-Precategoryᵉ fᵉ

  iso-map-natural-isomorphism-map-Precategoryᵉ :
    natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ →
    iso-Precategoryᵉ (map-precategory-Precategoryᵉ Cᵉ Dᵉ) Fᵉ Gᵉ
  iso-map-natural-isomorphism-map-Precategoryᵉ =
    totᵉ is-iso-map-is-natural-isomorphism-map-Precategoryᵉ

  natural-isomorphism-map-iso-map-Precategoryᵉ :
    iso-Precategoryᵉ (map-precategory-Precategoryᵉ Cᵉ Dᵉ) Fᵉ Gᵉ →
    natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ
  natural-isomorphism-map-iso-map-Precategoryᵉ =
    totᵉ is-natural-isomorphism-map-is-iso-map-Precategoryᵉ

  is-equiv-iso-map-natural-isomorphism-map-Precategoryᵉ :
    is-equivᵉ iso-map-natural-isomorphism-map-Precategoryᵉ
  is-equiv-iso-map-natural-isomorphism-map-Precategoryᵉ =
    is-equiv-tot-is-fiberwise-equivᵉ
      is-equiv-is-iso-map-is-natural-isomorphism-map-Precategoryᵉ

  is-equiv-natural-isomorphism-map-iso-map-Precategoryᵉ :
    is-equivᵉ natural-isomorphism-map-iso-map-Precategoryᵉ
  is-equiv-natural-isomorphism-map-iso-map-Precategoryᵉ =
    is-equiv-tot-is-fiberwise-equivᵉ
      is-equiv-is-natural-isomorphism-map-is-iso-map-Precategoryᵉ

  equiv-iso-map-natural-isomorphism-map-Precategoryᵉ :
    natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ ≃ᵉ
    iso-Precategoryᵉ (map-precategory-Precategoryᵉ Cᵉ Dᵉ) Fᵉ Gᵉ
  equiv-iso-map-natural-isomorphism-map-Precategoryᵉ =
    equiv-totᵉ equiv-is-iso-map-is-natural-isomorphism-map-Precategoryᵉ

  equiv-natural-isomorphism-map-iso-map-Precategoryᵉ :
    iso-Precategoryᵉ (map-precategory-Precategoryᵉ Cᵉ Dᵉ) Fᵉ Gᵉ ≃ᵉ
    natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ
  equiv-natural-isomorphism-map-iso-map-Precategoryᵉ =
    equiv-totᵉ equiv-is-natural-isomorphism-map-is-iso-map-Precategoryᵉ
```

#### Computing with the equivalence that isomorphisms are natural isomorphisms

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ Gᵉ : map-Precategoryᵉ Cᵉ Dᵉ)
  where

  compute-iso-map-natural-isomorphism-map-eq-Precategoryᵉ :
    (pᵉ : Fᵉ ＝ᵉ Gᵉ) →
    iso-eq-Precategoryᵉ (map-precategory-Precategoryᵉ Cᵉ Dᵉ) Fᵉ Gᵉ pᵉ ＝ᵉ
    iso-map-natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ
      ( natural-isomorphism-map-eq-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ pᵉ)
  compute-iso-map-natural-isomorphism-map-eq-Precategoryᵉ reflᵉ =
    eq-iso-eq-hom-Precategoryᵉ (map-precategory-Precategoryᵉ Cᵉ Dᵉ) _ _ reflᵉ
```