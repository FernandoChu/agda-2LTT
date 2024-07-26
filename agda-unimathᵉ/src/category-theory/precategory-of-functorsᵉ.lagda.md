# The precategory of functors and natural transformations between two precategories

```agda
module category-theory.precategory-of-functorsᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.composition-operations-on-binary-families-of-setsᵉ
open import category-theory.functors-precategoriesᵉ
open import category-theory.isomorphisms-in-precategoriesᵉ
open import category-theory.natural-isomorphisms-functors-precategoriesᵉ
open import category-theory.natural-transformations-functors-precategoriesᵉ
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

[Functors](category-theory.functors-precategories.mdᵉ) betweenᵉ
[precategories](category-theory.precategories.mdᵉ) andᵉ
[naturalᵉ transformations](category-theory.natural-transformations-functors-precategories.mdᵉ)
betweenᵉ themᵉ introduceᵉ aᵉ newᵉ precategoryᵉ whoseᵉ identityᵉ mapᵉ andᵉ compositionᵉ
structureᵉ areᵉ inheritedᵉ pointwiseᵉ fromᵉ theᵉ codomainᵉ precategory.ᵉ Thisᵉ isᵉ calledᵉ
theᵉ **precategoryᵉ ofᵉ functors**.ᵉ

## Definitions

### The precategory of functors and natural transformations between precategories

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ) (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  where

  comp-hom-functor-precategory-Precategoryᵉ :
    {Fᵉ Gᵉ Hᵉ : functor-Precategoryᵉ Cᵉ Dᵉ} →
    natural-transformation-Precategoryᵉ Cᵉ Dᵉ Gᵉ Hᵉ →
    natural-transformation-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ →
    natural-transformation-Precategoryᵉ Cᵉ Dᵉ Fᵉ Hᵉ
  comp-hom-functor-precategory-Precategoryᵉ {Fᵉ} {Gᵉ} {Hᵉ} =
    comp-natural-transformation-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ Hᵉ

  associative-comp-hom-functor-precategory-Precategoryᵉ :
    {Fᵉ Gᵉ Hᵉ Iᵉ : functor-Precategoryᵉ Cᵉ Dᵉ}
    (hᵉ : natural-transformation-Precategoryᵉ Cᵉ Dᵉ Hᵉ Iᵉ)
    (gᵉ : natural-transformation-Precategoryᵉ Cᵉ Dᵉ Gᵉ Hᵉ)
    (fᵉ : natural-transformation-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ) →
    comp-natural-transformation-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ Iᵉ
      ( comp-natural-transformation-Precategoryᵉ Cᵉ Dᵉ Gᵉ Hᵉ Iᵉ hᵉ gᵉ)
      ( fᵉ) ＝ᵉ
    comp-natural-transformation-Precategoryᵉ Cᵉ Dᵉ Fᵉ Hᵉ Iᵉ
      ( hᵉ)
      ( comp-natural-transformation-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ Hᵉ gᵉ fᵉ)
  associative-comp-hom-functor-precategory-Precategoryᵉ {Fᵉ} {Gᵉ} {Hᵉ} {Iᵉ} hᵉ gᵉ fᵉ =
    associative-comp-natural-transformation-Precategoryᵉ
      Cᵉ Dᵉ Fᵉ Gᵉ Hᵉ Iᵉ fᵉ gᵉ hᵉ

  involutive-eq-associative-comp-hom-functor-precategory-Precategoryᵉ :
    {Fᵉ Gᵉ Hᵉ Iᵉ : functor-Precategoryᵉ Cᵉ Dᵉ}
    (hᵉ : natural-transformation-Precategoryᵉ Cᵉ Dᵉ Hᵉ Iᵉ)
    (gᵉ : natural-transformation-Precategoryᵉ Cᵉ Dᵉ Gᵉ Hᵉ)
    (fᵉ : natural-transformation-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ) →
    comp-natural-transformation-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ Iᵉ
      ( comp-natural-transformation-Precategoryᵉ Cᵉ Dᵉ Gᵉ Hᵉ Iᵉ hᵉ gᵉ)
      ( fᵉ) ＝ⁱᵉ
    comp-natural-transformation-Precategoryᵉ Cᵉ Dᵉ Fᵉ Hᵉ Iᵉ
      ( hᵉ)
      ( comp-natural-transformation-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ Hᵉ gᵉ fᵉ)
  involutive-eq-associative-comp-hom-functor-precategory-Precategoryᵉ
    { Fᵉ} {Gᵉ} {Hᵉ} {Iᵉ} hᵉ gᵉ fᵉ =
    involutive-eq-associative-comp-natural-transformation-Precategoryᵉ
      Cᵉ Dᵉ Fᵉ Gᵉ Hᵉ Iᵉ fᵉ gᵉ hᵉ

  associative-composition-operation-functor-precategory-Precategoryᵉ :
    associative-composition-operation-binary-family-Setᵉ
      ( natural-transformation-set-Precategoryᵉ Cᵉ Dᵉ)
  pr1ᵉ associative-composition-operation-functor-precategory-Precategoryᵉ
    {Fᵉ} {Gᵉ} {Hᵉ} =
    comp-hom-functor-precategory-Precategoryᵉ {Fᵉ} {Gᵉ} {Hᵉ}
  pr2ᵉ
    associative-composition-operation-functor-precategory-Precategoryᵉ
      { Fᵉ} {Gᵉ} {Hᵉ} {Iᵉ} hᵉ gᵉ fᵉ =
    involutive-eq-associative-comp-hom-functor-precategory-Precategoryᵉ
      { Fᵉ} {Gᵉ} {Hᵉ} {Iᵉ} hᵉ gᵉ fᵉ

  id-hom-functor-precategory-Precategoryᵉ :
    (Fᵉ : functor-Precategoryᵉ Cᵉ Dᵉ) → natural-transformation-Precategoryᵉ Cᵉ Dᵉ Fᵉ Fᵉ
  id-hom-functor-precategory-Precategoryᵉ =
    id-natural-transformation-Precategoryᵉ Cᵉ Dᵉ

  left-unit-law-comp-hom-functor-precategory-Precategoryᵉ :
    {Fᵉ Gᵉ : functor-Precategoryᵉ Cᵉ Dᵉ}
    (αᵉ : natural-transformation-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ) →
    comp-natural-transformation-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ Gᵉ
      ( id-natural-transformation-Precategoryᵉ Cᵉ Dᵉ Gᵉ) αᵉ ＝ᵉ
    αᵉ
  left-unit-law-comp-hom-functor-precategory-Precategoryᵉ {Fᵉ} {Gᵉ} =
    left-unit-law-comp-natural-transformation-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ

  right-unit-law-comp-hom-functor-precategory-Precategoryᵉ :
    {Fᵉ Gᵉ : functor-Precategoryᵉ Cᵉ Dᵉ}
    (αᵉ : natural-transformation-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ) →
    comp-natural-transformation-Precategoryᵉ Cᵉ Dᵉ Fᵉ Fᵉ Gᵉ
        αᵉ (id-natural-transformation-Precategoryᵉ Cᵉ Dᵉ Fᵉ) ＝ᵉ
    αᵉ
  right-unit-law-comp-hom-functor-precategory-Precategoryᵉ {Fᵉ} {Gᵉ} =
    right-unit-law-comp-natural-transformation-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ

  is-unital-composition-operation-functor-precategory-Precategoryᵉ :
    is-unital-composition-operation-binary-family-Setᵉ
      ( natural-transformation-set-Precategoryᵉ Cᵉ Dᵉ)
      ( λ {Fᵉ} {Gᵉ} {Hᵉ} → comp-hom-functor-precategory-Precategoryᵉ {Fᵉ} {Gᵉ} {Hᵉ})
  pr1ᵉ is-unital-composition-operation-functor-precategory-Precategoryᵉ =
    id-hom-functor-precategory-Precategoryᵉ
  pr1ᵉ
    ( pr2ᵉ is-unital-composition-operation-functor-precategory-Precategoryᵉ)
    { Fᵉ} {Gᵉ} =
    left-unit-law-comp-hom-functor-precategory-Precategoryᵉ {Fᵉ} {Gᵉ}
  pr2ᵉ
    ( pr2ᵉ is-unital-composition-operation-functor-precategory-Precategoryᵉ)
    { Fᵉ} {Gᵉ} =
    right-unit-law-comp-hom-functor-precategory-Precategoryᵉ {Fᵉ} {Gᵉ}

  functor-precategory-Precategoryᵉ :
    Precategoryᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ) (l1ᵉ ⊔ l2ᵉ ⊔ l4ᵉ)
  pr1ᵉ functor-precategory-Precategoryᵉ = functor-Precategoryᵉ Cᵉ Dᵉ
  pr1ᵉ (pr2ᵉ functor-precategory-Precategoryᵉ) =
    natural-transformation-set-Precategoryᵉ Cᵉ Dᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ functor-precategory-Precategoryᵉ)) =
    associative-composition-operation-functor-precategory-Precategoryᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ functor-precategory-Precategoryᵉ)) =
    is-unital-composition-operation-functor-precategory-Precategoryᵉ
```

## Properties

### Isomorphisms in the functor precategory are natural isomorphisms

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ Gᵉ : functor-Precategoryᵉ Cᵉ Dᵉ)
  where

  is-iso-functor-is-natural-isomorphism-Precategoryᵉ :
    (fᵉ : natural-transformation-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ) →
    is-natural-isomorphism-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ fᵉ →
    is-iso-Precategoryᵉ (functor-precategory-Precategoryᵉ Cᵉ Dᵉ) {Fᵉ} {Gᵉ} fᵉ
  pr1ᵉ (is-iso-functor-is-natural-isomorphism-Precategoryᵉ fᵉ is-iso-fᵉ) =
    natural-transformation-inv-is-natural-isomorphism-Precategoryᵉ
      Cᵉ Dᵉ Fᵉ Gᵉ fᵉ is-iso-fᵉ
  pr1ᵉ (pr2ᵉ (is-iso-functor-is-natural-isomorphism-Precategoryᵉ fᵉ is-iso-fᵉ)) =
    is-section-natural-transformation-inv-is-natural-isomorphism-Precategoryᵉ
      Cᵉ Dᵉ Fᵉ Gᵉ fᵉ is-iso-fᵉ
  pr2ᵉ (pr2ᵉ (is-iso-functor-is-natural-isomorphism-Precategoryᵉ fᵉ is-iso-fᵉ)) =
    is-retraction-natural-transformation-inv-is-natural-isomorphism-Precategoryᵉ
      Cᵉ Dᵉ Fᵉ Gᵉ fᵉ is-iso-fᵉ

  is-natural-isomorphism-is-iso-functor-Precategoryᵉ :
    (fᵉ : natural-transformation-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ) →
    is-iso-Precategoryᵉ (functor-precategory-Precategoryᵉ Cᵉ Dᵉ) {Fᵉ} {Gᵉ} fᵉ →
    is-natural-isomorphism-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ fᵉ
  pr1ᵉ (is-natural-isomorphism-is-iso-functor-Precategoryᵉ fᵉ is-iso-fᵉ xᵉ) =
    hom-family-natural-transformation-Precategoryᵉ Cᵉ Dᵉ Gᵉ Fᵉ
      ( hom-inv-is-iso-Precategoryᵉ
        ( functor-precategory-Precategoryᵉ Cᵉ Dᵉ) {Fᵉ} {Gᵉ} is-iso-fᵉ)
      ( xᵉ)
  pr1ᵉ (pr2ᵉ (is-natural-isomorphism-is-iso-functor-Precategoryᵉ fᵉ is-iso-fᵉ xᵉ)) =
    htpy-eqᵉ
      ( apᵉ
        ( hom-family-natural-transformation-Precategoryᵉ Cᵉ Dᵉ Gᵉ Gᵉ)
        ( is-section-hom-inv-is-iso-Precategoryᵉ
          ( functor-precategory-Precategoryᵉ Cᵉ Dᵉ) {Fᵉ} {Gᵉ} is-iso-fᵉ))
      ( xᵉ)
  pr2ᵉ (pr2ᵉ (is-natural-isomorphism-is-iso-functor-Precategoryᵉ fᵉ is-iso-fᵉ xᵉ)) =
    htpy-eqᵉ
      ( apᵉ
        ( hom-family-natural-transformation-Precategoryᵉ Cᵉ Dᵉ Fᵉ Fᵉ)
        ( is-retraction-hom-inv-is-iso-Precategoryᵉ
          ( functor-precategory-Precategoryᵉ Cᵉ Dᵉ) {Fᵉ} {Gᵉ} is-iso-fᵉ))
      ( xᵉ)

  is-equiv-is-iso-functor-is-natural-isomorphism-Precategoryᵉ :
    (fᵉ : natural-transformation-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ) →
    is-equivᵉ (is-iso-functor-is-natural-isomorphism-Precategoryᵉ fᵉ)
  is-equiv-is-iso-functor-is-natural-isomorphism-Precategoryᵉ fᵉ =
    is-equiv-has-converse-is-propᵉ
      ( is-prop-is-natural-isomorphism-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ fᵉ)
      ( is-prop-is-iso-Precategoryᵉ
        ( functor-precategory-Precategoryᵉ Cᵉ Dᵉ) {Fᵉ} {Gᵉ} fᵉ)
      ( is-natural-isomorphism-is-iso-functor-Precategoryᵉ fᵉ)

  is-equiv-is-natural-isomorphism-is-iso-functor-Precategoryᵉ :
    (fᵉ : natural-transformation-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ) →
    is-equivᵉ (is-natural-isomorphism-is-iso-functor-Precategoryᵉ fᵉ)
  is-equiv-is-natural-isomorphism-is-iso-functor-Precategoryᵉ fᵉ =
    is-equiv-has-converse-is-propᵉ
      ( is-prop-is-iso-Precategoryᵉ
        ( functor-precategory-Precategoryᵉ Cᵉ Dᵉ) {Fᵉ} {Gᵉ} fᵉ)
      ( is-prop-is-natural-isomorphism-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ fᵉ)
      ( is-iso-functor-is-natural-isomorphism-Precategoryᵉ fᵉ)

  equiv-is-iso-functor-is-natural-isomorphism-Precategoryᵉ :
    (fᵉ : natural-transformation-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ) →
    is-natural-isomorphism-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ fᵉ ≃ᵉ
    is-iso-Precategoryᵉ (functor-precategory-Precategoryᵉ Cᵉ Dᵉ) {Fᵉ} {Gᵉ} fᵉ
  pr1ᵉ (equiv-is-iso-functor-is-natural-isomorphism-Precategoryᵉ fᵉ) =
    is-iso-functor-is-natural-isomorphism-Precategoryᵉ fᵉ
  pr2ᵉ (equiv-is-iso-functor-is-natural-isomorphism-Precategoryᵉ fᵉ) =
    is-equiv-is-iso-functor-is-natural-isomorphism-Precategoryᵉ fᵉ

  equiv-is-natural-isomorphism-is-iso-functor-Precategoryᵉ :
    (fᵉ : natural-transformation-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ) →
    is-iso-Precategoryᵉ (functor-precategory-Precategoryᵉ Cᵉ Dᵉ) {Fᵉ} {Gᵉ} fᵉ ≃ᵉ
    is-natural-isomorphism-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ fᵉ
  pr1ᵉ (equiv-is-natural-isomorphism-is-iso-functor-Precategoryᵉ fᵉ) =
    is-natural-isomorphism-is-iso-functor-Precategoryᵉ fᵉ
  pr2ᵉ (equiv-is-natural-isomorphism-is-iso-functor-Precategoryᵉ fᵉ) =
    is-equiv-is-natural-isomorphism-is-iso-functor-Precategoryᵉ fᵉ

  iso-functor-natural-isomorphism-Precategoryᵉ :
    natural-isomorphism-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ →
    iso-Precategoryᵉ (functor-precategory-Precategoryᵉ Cᵉ Dᵉ) Fᵉ Gᵉ
  iso-functor-natural-isomorphism-Precategoryᵉ =
    totᵉ is-iso-functor-is-natural-isomorphism-Precategoryᵉ

  natural-isomorphism-iso-functor-Precategoryᵉ :
    iso-Precategoryᵉ (functor-precategory-Precategoryᵉ Cᵉ Dᵉ) Fᵉ Gᵉ →
    natural-isomorphism-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ
  natural-isomorphism-iso-functor-Precategoryᵉ =
    totᵉ is-natural-isomorphism-is-iso-functor-Precategoryᵉ

  is-equiv-iso-functor-natural-isomorphism-Precategoryᵉ :
    is-equivᵉ iso-functor-natural-isomorphism-Precategoryᵉ
  is-equiv-iso-functor-natural-isomorphism-Precategoryᵉ =
    is-equiv-tot-is-fiberwise-equivᵉ
      is-equiv-is-iso-functor-is-natural-isomorphism-Precategoryᵉ

  is-equiv-natural-isomorphism-iso-functor-Precategoryᵉ :
    is-equivᵉ natural-isomorphism-iso-functor-Precategoryᵉ
  is-equiv-natural-isomorphism-iso-functor-Precategoryᵉ =
    is-equiv-tot-is-fiberwise-equivᵉ
      is-equiv-is-natural-isomorphism-is-iso-functor-Precategoryᵉ

  equiv-iso-functor-natural-isomorphism-Precategoryᵉ :
    natural-isomorphism-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ ≃ᵉ
    iso-Precategoryᵉ (functor-precategory-Precategoryᵉ Cᵉ Dᵉ) Fᵉ Gᵉ
  equiv-iso-functor-natural-isomorphism-Precategoryᵉ =
    equiv-totᵉ equiv-is-iso-functor-is-natural-isomorphism-Precategoryᵉ

  equiv-natural-isomorphism-iso-functor-Precategoryᵉ :
    iso-Precategoryᵉ (functor-precategory-Precategoryᵉ Cᵉ Dᵉ) Fᵉ Gᵉ ≃ᵉ
    natural-isomorphism-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ
  equiv-natural-isomorphism-iso-functor-Precategoryᵉ =
    equiv-totᵉ equiv-is-natural-isomorphism-is-iso-functor-Precategoryᵉ
```

#### Computing with the equivalence that isomorphisms are natural isomorphisms

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ Gᵉ : functor-Precategoryᵉ Cᵉ Dᵉ)
  where

  compute-iso-functor-natural-isomorphism-eq-Precategoryᵉ :
    (pᵉ : Fᵉ ＝ᵉ Gᵉ) →
    iso-eq-Precategoryᵉ (functor-precategory-Precategoryᵉ Cᵉ Dᵉ) Fᵉ Gᵉ pᵉ ＝ᵉ
    iso-functor-natural-isomorphism-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ
      ( natural-isomorphism-eq-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ pᵉ)
  compute-iso-functor-natural-isomorphism-eq-Precategoryᵉ reflᵉ =
    eq-iso-eq-hom-Precategoryᵉ
      ( functor-precategory-Precategoryᵉ Cᵉ Dᵉ)
      { Fᵉ} {Gᵉ} _ _ reflᵉ
```