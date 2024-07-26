# Natural isomorphisms between functors between precategories

```agda
module category-theory.natural-isomorphisms-functors-precategoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.functors-precategoriesᵉ
open import category-theory.isomorphisms-in-precategoriesᵉ
open import category-theory.natural-isomorphisms-maps-precategoriesᵉ
open import category-theory.natural-transformations-functors-precategoriesᵉ
open import category-theory.precategoriesᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.subtypesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Aᵉ **naturalᵉ isomorphism**ᵉ `γ`ᵉ fromᵉ
[functor](category-theory.functors-precategories.mdᵉ) `Fᵉ : Cᵉ → D`ᵉ to `Gᵉ : Cᵉ → D`ᵉ
isᵉ aᵉ
[naturalᵉ transformation](category-theory.natural-transformations-functors-precategories.mdᵉ)
fromᵉ `F`ᵉ to `G`ᵉ suchᵉ thatᵉ theᵉ morphismᵉ `γᵉ Fᵉ : homᵉ (Fᵉ xᵉ) (Gᵉ x)`ᵉ isᵉ anᵉ
[isomorphism](category-theory.isomorphisms-in-precategories.md),ᵉ forᵉ everyᵉ
objectᵉ `x`ᵉ in `C`.ᵉ

## Definition

### Families of isomorphisms between functors

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ Gᵉ : functor-Precategoryᵉ Cᵉ Dᵉ)
  where

  iso-family-functor-Precategoryᵉ : UUᵉ (l1ᵉ ⊔ l4ᵉ)
  iso-family-functor-Precategoryᵉ =
    iso-family-map-Precategoryᵉ Cᵉ Dᵉ
      ( map-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ)
      ( map-functor-Precategoryᵉ Cᵉ Dᵉ Gᵉ)
```

### The predicate of being an isomorphism in a precategory

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ Gᵉ : functor-Precategoryᵉ Cᵉ Dᵉ)
  where

  is-natural-isomorphism-Precategoryᵉ :
    natural-transformation-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ → UUᵉ (l1ᵉ ⊔ l4ᵉ)
  is-natural-isomorphism-Precategoryᵉ =
    is-natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ
      ( map-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ)
      ( map-functor-Precategoryᵉ Cᵉ Dᵉ Gᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ Gᵉ : functor-Precategoryᵉ Cᵉ Dᵉ)
  (fᵉ : natural-transformation-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ)
  where

  hom-inv-family-is-natural-isomorphism-Precategoryᵉ :
    is-natural-isomorphism-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ fᵉ →
    hom-family-functor-Precategoryᵉ Cᵉ Dᵉ Gᵉ Fᵉ
  hom-inv-family-is-natural-isomorphism-Precategoryᵉ =
    hom-inv-family-is-natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ
      ( map-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ)
      ( map-functor-Precategoryᵉ Cᵉ Dᵉ Gᵉ)
      ( fᵉ)

  is-section-hom-inv-family-is-natural-isomorphism-Precategoryᵉ :
    (is-iso-fᵉ : is-natural-isomorphism-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ fᵉ) →
    (xᵉ : obj-Precategoryᵉ Cᵉ) →
    comp-hom-Precategoryᵉ Dᵉ
      ( hom-family-natural-transformation-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ fᵉ xᵉ)
      ( hom-inv-is-iso-Precategoryᵉ Dᵉ (is-iso-fᵉ xᵉ)) ＝ᵉ
    id-hom-Precategoryᵉ Dᵉ
  is-section-hom-inv-family-is-natural-isomorphism-Precategoryᵉ =
    is-section-hom-inv-family-is-natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ
      ( map-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ)
      ( map-functor-Precategoryᵉ Cᵉ Dᵉ Gᵉ)
      ( fᵉ)

  is-retraction-hom-inv-family-is-natural-isomorphism-Precategoryᵉ :
    (is-iso-fᵉ : is-natural-isomorphism-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ fᵉ) →
    (xᵉ : obj-Precategoryᵉ Cᵉ) →
    comp-hom-Precategoryᵉ Dᵉ
      ( hom-inv-is-iso-Precategoryᵉ Dᵉ (is-iso-fᵉ xᵉ))
      ( hom-family-natural-transformation-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ fᵉ xᵉ) ＝ᵉ
    id-hom-Precategoryᵉ Dᵉ
  is-retraction-hom-inv-family-is-natural-isomorphism-Precategoryᵉ =
    is-retraction-hom-inv-family-is-natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ
      ( map-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ)
      ( map-functor-Precategoryᵉ Cᵉ Dᵉ Gᵉ)
      ( fᵉ)

  iso-family-is-natural-isomorphism-Precategoryᵉ :
    is-natural-isomorphism-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ fᵉ →
    iso-family-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ
  iso-family-is-natural-isomorphism-Precategoryᵉ =
    iso-family-is-natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ
      ( map-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ)
      ( map-functor-Precategoryᵉ Cᵉ Dᵉ Gᵉ)
      ( fᵉ)

  inv-iso-family-is-natural-isomorphism-Precategoryᵉ :
    is-natural-isomorphism-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ fᵉ →
    iso-family-functor-Precategoryᵉ Cᵉ Dᵉ Gᵉ Fᵉ
  inv-iso-family-is-natural-isomorphism-Precategoryᵉ =
    inv-iso-family-is-natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ
      ( map-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ)
      ( map-functor-Precategoryᵉ Cᵉ Dᵉ Gᵉ)
      ( fᵉ)
```

### Natural isomorphisms in a precategory

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ Gᵉ : functor-Precategoryᵉ Cᵉ Dᵉ)
  where

  natural-isomorphism-Precategoryᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l4ᵉ)
  natural-isomorphism-Precategoryᵉ =
    natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ
      ( map-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ)
      ( map-functor-Precategoryᵉ Cᵉ Dᵉ Gᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ Gᵉ : functor-Precategoryᵉ Cᵉ Dᵉ)
  (fᵉ : natural-isomorphism-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ)
  where

  natural-transformation-natural-isomorphism-Precategoryᵉ :
    natural-transformation-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ
  natural-transformation-natural-isomorphism-Precategoryᵉ =
    natural-transformation-map-natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ
      ( map-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ)
      ( map-functor-Precategoryᵉ Cᵉ Dᵉ Gᵉ)
      ( fᵉ)

  hom-family-natural-isomorphism-Precategoryᵉ :
    hom-family-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ
  hom-family-natural-isomorphism-Precategoryᵉ =
    hom-family-natural-transformation-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ
      ( natural-transformation-natural-isomorphism-Precategoryᵉ)

  coherence-square-natural-isomorphism-Precategoryᵉ :
    is-natural-transformation-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ
      ( hom-family-natural-transformation-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ
        ( natural-transformation-natural-isomorphism-Precategoryᵉ))
  coherence-square-natural-isomorphism-Precategoryᵉ =
    naturality-natural-transformation-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ
      ( natural-transformation-natural-isomorphism-Precategoryᵉ)

  is-natural-isomorphism-natural-isomorphism-Precategoryᵉ :
    is-natural-isomorphism-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ
      ( natural-transformation-natural-isomorphism-Precategoryᵉ)
  is-natural-isomorphism-natural-isomorphism-Precategoryᵉ = pr2ᵉ fᵉ

  hom-inv-family-natural-isomorphism-Precategoryᵉ :
    hom-family-functor-Precategoryᵉ Cᵉ Dᵉ Gᵉ Fᵉ
  hom-inv-family-natural-isomorphism-Precategoryᵉ =
    hom-inv-family-is-natural-isomorphism-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ
      ( natural-transformation-natural-isomorphism-Precategoryᵉ)
      ( is-natural-isomorphism-natural-isomorphism-Precategoryᵉ)

  is-section-hom-inv-family-natural-isomorphism-Precategoryᵉ :
    (xᵉ : obj-Precategoryᵉ Cᵉ) →
    comp-hom-Precategoryᵉ Dᵉ
      ( hom-family-natural-isomorphism-Precategoryᵉ xᵉ)
      ( hom-inv-family-natural-isomorphism-Precategoryᵉ xᵉ) ＝ᵉ
    id-hom-Precategoryᵉ Dᵉ
  is-section-hom-inv-family-natural-isomorphism-Precategoryᵉ =
    is-section-hom-inv-family-is-natural-isomorphism-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ
      ( natural-transformation-natural-isomorphism-Precategoryᵉ)
      ( is-natural-isomorphism-natural-isomorphism-Precategoryᵉ)

  is-retraction-hom-inv-family-natural-isomorphism-Precategoryᵉ :
    (xᵉ : obj-Precategoryᵉ Cᵉ) →
    comp-hom-Precategoryᵉ Dᵉ
      ( hom-inv-family-natural-isomorphism-Precategoryᵉ xᵉ)
      ( hom-family-natural-isomorphism-Precategoryᵉ xᵉ) ＝ᵉ
    id-hom-Precategoryᵉ Dᵉ
  is-retraction-hom-inv-family-natural-isomorphism-Precategoryᵉ =
    is-retraction-hom-inv-family-is-natural-isomorphism-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ
      ( natural-transformation-natural-isomorphism-Precategoryᵉ)
      ( is-natural-isomorphism-natural-isomorphism-Precategoryᵉ)

  iso-family-natural-isomorphism-Precategoryᵉ :
    iso-family-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ
  iso-family-natural-isomorphism-Precategoryᵉ =
    iso-family-is-natural-isomorphism-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ
      ( natural-transformation-natural-isomorphism-Precategoryᵉ)
      ( is-natural-isomorphism-natural-isomorphism-Precategoryᵉ)

  inv-iso-family-natural-isomorphism-Precategoryᵉ :
    iso-family-functor-Precategoryᵉ Cᵉ Dᵉ Gᵉ Fᵉ
  inv-iso-family-natural-isomorphism-Precategoryᵉ =
    inv-iso-family-is-natural-isomorphism-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ
      ( natural-transformation-natural-isomorphism-Precategoryᵉ)
      ( is-natural-isomorphism-natural-isomorphism-Precategoryᵉ)
```

## Examples

### The identity natural isomorphism

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  where

  id-natural-isomorphism-Precategoryᵉ :
    (Fᵉ : functor-Precategoryᵉ Cᵉ Dᵉ) → natural-isomorphism-Precategoryᵉ Cᵉ Dᵉ Fᵉ Fᵉ
  id-natural-isomorphism-Precategoryᵉ Fᵉ =
    id-natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ
      ( map-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ)
```

### Equalities induce natural isomorphisms

Anᵉ equalityᵉ betweenᵉ functorsᵉ `F`ᵉ andᵉ `G`ᵉ givesᵉ riseᵉ to aᵉ naturalᵉ isomorphismᵉ
betweenᵉ them.ᵉ Thisᵉ isᵉ because,ᵉ byᵉ theᵉ J-rule,ᵉ itᵉ isᵉ enoughᵉ to constructᵉ aᵉ
naturalᵉ isomorphismᵉ givenᵉ `reflᵉ : Fᵉ ＝ᵉ F`,ᵉ fromᵉ `F`ᵉ to itself.ᵉ Weᵉ takeᵉ theᵉ
identityᵉ naturalᵉ transformationᵉ asᵉ suchᵉ anᵉ isomorphism.ᵉ

```agda
natural-isomorphism-eq-Precategoryᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ Gᵉ : functor-Precategoryᵉ Cᵉ Dᵉ) →
  Fᵉ ＝ᵉ Gᵉ → natural-isomorphism-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ
natural-isomorphism-eq-Precategoryᵉ Cᵉ Dᵉ Fᵉ .Fᵉ reflᵉ =
  id-natural-isomorphism-Precategoryᵉ Cᵉ Dᵉ Fᵉ
```

## Propositions

### Being a natural isomorphism is a proposition

Thatᵉ aᵉ naturalᵉ transformationᵉ isᵉ aᵉ naturalᵉ isomorphismᵉ isᵉ aᵉ proposition.ᵉ Thisᵉ
followsᵉ fromᵉ theᵉ factᵉ thatᵉ beingᵉ anᵉ isomorphismᵉ isᵉ aᵉ proposition.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ Gᵉ : functor-Precategoryᵉ Cᵉ Dᵉ)
  where

  is-prop-is-natural-isomorphism-Precategoryᵉ :
    (fᵉ : natural-transformation-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ) →
    is-propᵉ (is-natural-isomorphism-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ fᵉ)
  is-prop-is-natural-isomorphism-Precategoryᵉ =
    is-prop-is-natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ
      ( map-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ)
      ( map-functor-Precategoryᵉ Cᵉ Dᵉ Gᵉ)

  is-natural-isomorphism-prop-hom-Precategoryᵉ :
    (fᵉ : natural-transformation-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ) → Propᵉ (l1ᵉ ⊔ l4ᵉ)
  is-natural-isomorphism-prop-hom-Precategoryᵉ =
    is-natural-isomorphism-map-prop-hom-Precategoryᵉ Cᵉ Dᵉ
      ( map-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ)
      ( map-functor-Precategoryᵉ Cᵉ Dᵉ Gᵉ)
```

### Equality of natural isomorphisms is equality of their underlying natural transformations

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ Gᵉ : functor-Precategoryᵉ Cᵉ Dᵉ)
  where

  extensionality-natural-isomorphism-Precategoryᵉ :
    (fᵉ gᵉ : natural-isomorphism-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ) →
    (fᵉ ＝ᵉ gᵉ) ≃ᵉ
    ( hom-family-natural-isomorphism-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ fᵉ ~ᵉ
      hom-family-natural-isomorphism-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ gᵉ)
  extensionality-natural-isomorphism-Precategoryᵉ =
    extensionality-natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ
      ( map-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ)
      ( map-functor-Precategoryᵉ Cᵉ Dᵉ Gᵉ)

  eq-eq-natural-transformation-natural-isomorphism-Precategoryᵉ :
    (fᵉ gᵉ : natural-isomorphism-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ) →
    ( natural-transformation-natural-isomorphism-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ fᵉ ＝ᵉ
      natural-transformation-natural-isomorphism-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ gᵉ) →
    fᵉ ＝ᵉ gᵉ
  eq-eq-natural-transformation-natural-isomorphism-Precategoryᵉ fᵉ gᵉ =
    eq-type-subtypeᵉ (is-natural-isomorphism-prop-hom-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ)

  eq-htpy-hom-family-natural-isomorphism-Precategoryᵉ :
        (fᵉ gᵉ : natural-isomorphism-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ) →
    ( hom-family-natural-isomorphism-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ fᵉ ~ᵉ
      hom-family-natural-isomorphism-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ gᵉ) →
    fᵉ ＝ᵉ gᵉ
  eq-htpy-hom-family-natural-isomorphism-Precategoryᵉ =
    eq-htpy-hom-family-natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ
      ( map-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ)
      ( map-functor-Precategoryᵉ Cᵉ Dᵉ Gᵉ)
```

### The type of natural isomorphisms form a set

Theᵉ typeᵉ ofᵉ naturalᵉ isomorphismsᵉ betweenᵉ functorsᵉ `F`ᵉ andᵉ `G`ᵉ isᵉ aᵉ
[subtype](foundation-core.subtypes.mdᵉ) ofᵉ theᵉ [set](foundation-core.sets.mdᵉ)
`natural-transformationᵉ Fᵉ G`ᵉ sinceᵉ beingᵉ anᵉ isomorphismᵉ isᵉ aᵉ proposition.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ Gᵉ : functor-Precategoryᵉ Cᵉ Dᵉ)
  where

  is-set-natural-isomorphism-Precategoryᵉ :
    is-setᵉ (natural-isomorphism-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ)
  is-set-natural-isomorphism-Precategoryᵉ =
    is-set-type-subtypeᵉ
      ( is-natural-isomorphism-prop-hom-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ)
      ( is-set-natural-transformation-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ)

  natural-isomorphism-set-Precategoryᵉ : Setᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l4ᵉ)
  pr1ᵉ natural-isomorphism-set-Precategoryᵉ =
    natural-isomorphism-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ
  pr2ᵉ natural-isomorphism-set-Precategoryᵉ =
    is-set-natural-isomorphism-Precategoryᵉ
```

### Inverses of natural isomorphisms are natural isomorphisms

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ Gᵉ : functor-Precategoryᵉ Cᵉ Dᵉ)
  (fᵉ : natural-transformation-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ)
  where

  natural-transformation-inv-is-natural-isomorphism-Precategoryᵉ :
    is-natural-isomorphism-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ fᵉ →
    natural-transformation-Precategoryᵉ Cᵉ Dᵉ Gᵉ Fᵉ
  natural-transformation-inv-is-natural-isomorphism-Precategoryᵉ =
    natural-transformation-map-inv-is-natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ
      ( map-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ)
      ( map-functor-Precategoryᵉ Cᵉ Dᵉ Gᵉ)
      ( fᵉ)

  is-section-natural-transformation-inv-is-natural-isomorphism-Precategoryᵉ :
    (is-iso-fᵉ : is-natural-isomorphism-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ fᵉ) →
    comp-natural-transformation-Precategoryᵉ Cᵉ Dᵉ Gᵉ Fᵉ Gᵉ
      ( fᵉ)
      ( natural-transformation-inv-is-natural-isomorphism-Precategoryᵉ
        ( is-iso-fᵉ)) ＝ᵉ
    id-natural-transformation-Precategoryᵉ Cᵉ Dᵉ Gᵉ
  is-section-natural-transformation-inv-is-natural-isomorphism-Precategoryᵉ
    is-iso-fᵉ =
    eq-htpy-hom-family-natural-transformation-Precategoryᵉ Cᵉ Dᵉ Gᵉ Gᵉ _ _
      ( is-section-hom-inv-is-iso-Precategoryᵉ Dᵉ ∘ᵉ is-iso-fᵉ)

  is-retraction-natural-transformation-inv-is-natural-isomorphism-Precategoryᵉ :
    (is-iso-fᵉ : is-natural-isomorphism-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ fᵉ) →
    comp-natural-transformation-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ Fᵉ
      ( natural-transformation-inv-is-natural-isomorphism-Precategoryᵉ is-iso-fᵉ)
      ( fᵉ) ＝ᵉ
    id-natural-transformation-Precategoryᵉ Cᵉ Dᵉ Fᵉ
  is-retraction-natural-transformation-inv-is-natural-isomorphism-Precategoryᵉ
    is-iso-fᵉ =
    eq-htpy-hom-family-natural-transformation-Precategoryᵉ Cᵉ Dᵉ Fᵉ Fᵉ _ _
      ( is-retraction-hom-inv-is-iso-Precategoryᵉ Dᵉ ∘ᵉ is-iso-fᵉ)

  is-natural-isomorphism-inv-is-natural-isomorphism-Precategoryᵉ :
    (is-iso-fᵉ : is-natural-isomorphism-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ fᵉ) →
    is-natural-isomorphism-Precategoryᵉ Cᵉ Dᵉ Gᵉ Fᵉ
      ( natural-transformation-inv-is-natural-isomorphism-Precategoryᵉ is-iso-fᵉ)
  is-natural-isomorphism-inv-is-natural-isomorphism-Precategoryᵉ is-iso-fᵉ =
    is-iso-inv-is-iso-Precategoryᵉ Dᵉ ∘ᵉ is-iso-fᵉ
```

### Inverses of natural isomorphisms

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ Gᵉ : functor-Precategoryᵉ Cᵉ Dᵉ)
  (fᵉ : natural-isomorphism-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ)
  where

  natural-transformation-inv-natural-isomorphism-Precategoryᵉ :
    natural-transformation-Precategoryᵉ Cᵉ Dᵉ Gᵉ Fᵉ
  natural-transformation-inv-natural-isomorphism-Precategoryᵉ =
    natural-transformation-inv-is-natural-isomorphism-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ
      ( natural-transformation-natural-isomorphism-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ fᵉ)
      ( is-natural-isomorphism-natural-isomorphism-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ fᵉ)

  is-section-natural-transformation-inv-natural-isomorphism-Precategoryᵉ :
    ( comp-natural-transformation-Precategoryᵉ Cᵉ Dᵉ Gᵉ Fᵉ Gᵉ
      ( natural-transformation-natural-isomorphism-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ fᵉ)
      ( natural-transformation-inv-natural-isomorphism-Precategoryᵉ)) ＝ᵉ
    ( id-natural-transformation-Precategoryᵉ Cᵉ Dᵉ Gᵉ)
  is-section-natural-transformation-inv-natural-isomorphism-Precategoryᵉ =
    is-section-natural-transformation-inv-is-natural-isomorphism-Precategoryᵉ
      Cᵉ Dᵉ Fᵉ Gᵉ
      ( natural-transformation-natural-isomorphism-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ fᵉ)
      ( is-natural-isomorphism-natural-isomorphism-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ fᵉ)

  is-retraction-natural-transformation-inv-natural-isomorphism-Precategoryᵉ :
    ( comp-natural-transformation-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ Fᵉ
      ( natural-transformation-inv-natural-isomorphism-Precategoryᵉ)
      ( natural-transformation-natural-isomorphism-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ fᵉ)) ＝ᵉ
    ( id-natural-transformation-Precategoryᵉ Cᵉ Dᵉ Fᵉ)
  is-retraction-natural-transformation-inv-natural-isomorphism-Precategoryᵉ =
    is-retraction-natural-transformation-inv-is-natural-isomorphism-Precategoryᵉ
      Cᵉ Dᵉ Fᵉ Gᵉ
      ( natural-transformation-natural-isomorphism-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ fᵉ)
      ( is-natural-isomorphism-natural-isomorphism-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ fᵉ)

  is-natural-isomorphism-inv-natural-isomorphism-Precategoryᵉ :
    is-natural-isomorphism-Precategoryᵉ Cᵉ Dᵉ Gᵉ Fᵉ
      ( natural-transformation-inv-natural-isomorphism-Precategoryᵉ)
  is-natural-isomorphism-inv-natural-isomorphism-Precategoryᵉ =
    is-natural-isomorphism-inv-is-natural-isomorphism-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ
      ( natural-transformation-natural-isomorphism-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ fᵉ)
      ( is-natural-isomorphism-natural-isomorphism-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ fᵉ)

  inv-natural-isomorphism-Precategoryᵉ :
    natural-isomorphism-Precategoryᵉ Cᵉ Dᵉ Gᵉ Fᵉ
  pr1ᵉ inv-natural-isomorphism-Precategoryᵉ =
    natural-transformation-inv-natural-isomorphism-Precategoryᵉ
  pr2ᵉ inv-natural-isomorphism-Precategoryᵉ =
    is-natural-isomorphism-inv-natural-isomorphism-Precategoryᵉ
```

### Natural isomorphisms are closed under composition

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ Gᵉ Hᵉ : functor-Precategoryᵉ Cᵉ Dᵉ)
  (gᵉ : natural-transformation-Precategoryᵉ Cᵉ Dᵉ Gᵉ Hᵉ)
  (fᵉ : natural-transformation-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ)
  where

  is-natural-isomorphism-comp-is-natural-isomorphism-Precategoryᵉ :
    is-natural-isomorphism-Precategoryᵉ Cᵉ Dᵉ Gᵉ Hᵉ gᵉ →
    is-natural-isomorphism-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ fᵉ →
    is-natural-isomorphism-Precategoryᵉ Cᵉ Dᵉ Fᵉ Hᵉ
      ( comp-natural-transformation-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ Hᵉ gᵉ fᵉ)
  is-natural-isomorphism-comp-is-natural-isomorphism-Precategoryᵉ
    is-iso-gᵉ is-iso-fᵉ xᵉ =
      is-iso-comp-is-iso-Precategoryᵉ Dᵉ (is-iso-gᵉ xᵉ) (is-iso-fᵉ xᵉ)
```

### The composition operation on natural isomorphisms

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ Gᵉ Hᵉ : functor-Precategoryᵉ Cᵉ Dᵉ)
  (gᵉ : natural-isomorphism-Precategoryᵉ Cᵉ Dᵉ Gᵉ Hᵉ)
  (fᵉ : natural-isomorphism-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ)
  where

  hom-comp-natural-isomorphism-Precategoryᵉ :
    natural-transformation-Precategoryᵉ Cᵉ Dᵉ Fᵉ Hᵉ
  hom-comp-natural-isomorphism-Precategoryᵉ =
    comp-natural-transformation-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ Hᵉ
      ( natural-transformation-natural-isomorphism-Precategoryᵉ Cᵉ Dᵉ Gᵉ Hᵉ gᵉ)
      ( natural-transformation-natural-isomorphism-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ fᵉ)

  is-natural-isomorphism-comp-natural-isomorphism-Precategoryᵉ :
    is-natural-isomorphism-Precategoryᵉ Cᵉ Dᵉ Fᵉ Hᵉ
      ( hom-comp-natural-isomorphism-Precategoryᵉ)
  is-natural-isomorphism-comp-natural-isomorphism-Precategoryᵉ =
    is-natural-isomorphism-comp-is-natural-isomorphism-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ Hᵉ
      ( natural-transformation-natural-isomorphism-Precategoryᵉ Cᵉ Dᵉ Gᵉ Hᵉ gᵉ)
      ( natural-transformation-natural-isomorphism-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ fᵉ)
      ( is-natural-isomorphism-natural-isomorphism-Precategoryᵉ Cᵉ Dᵉ Gᵉ Hᵉ gᵉ)
      ( is-natural-isomorphism-natural-isomorphism-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ fᵉ)

  comp-natural-isomorphism-Precategoryᵉ : natural-isomorphism-Precategoryᵉ Cᵉ Dᵉ Fᵉ Hᵉ
  pr1ᵉ comp-natural-isomorphism-Precategoryᵉ =
    hom-comp-natural-isomorphism-Precategoryᵉ
  pr2ᵉ comp-natural-isomorphism-Precategoryᵉ =
    is-natural-isomorphism-comp-natural-isomorphism-Precategoryᵉ

  natural-transformation-inv-comp-natural-isomorphism-Precategoryᵉ :
    natural-transformation-Precategoryᵉ Cᵉ Dᵉ Hᵉ Fᵉ
  natural-transformation-inv-comp-natural-isomorphism-Precategoryᵉ =
    natural-transformation-inv-natural-isomorphism-Precategoryᵉ Cᵉ Dᵉ Fᵉ Hᵉ
      ( comp-natural-isomorphism-Precategoryᵉ)

  is-section-inv-comp-natural-isomorphism-Precategoryᵉ :
    ( comp-natural-transformation-Precategoryᵉ Cᵉ Dᵉ Hᵉ Fᵉ Hᵉ
      ( hom-comp-natural-isomorphism-Precategoryᵉ)
      ( natural-transformation-inv-comp-natural-isomorphism-Precategoryᵉ)) ＝ᵉ
    ( id-natural-transformation-Precategoryᵉ Cᵉ Dᵉ Hᵉ)
  is-section-inv-comp-natural-isomorphism-Precategoryᵉ =
    is-section-natural-transformation-inv-natural-isomorphism-Precategoryᵉ
      Cᵉ Dᵉ Fᵉ Hᵉ comp-natural-isomorphism-Precategoryᵉ

  is-retraction-inv-comp-natural-isomorphism-Precategoryᵉ :
    ( comp-natural-transformation-Precategoryᵉ Cᵉ Dᵉ Fᵉ Hᵉ Fᵉ
      ( natural-transformation-inv-comp-natural-isomorphism-Precategoryᵉ)
      ( hom-comp-natural-isomorphism-Precategoryᵉ)) ＝ᵉ
    ( id-natural-transformation-Precategoryᵉ Cᵉ Dᵉ Fᵉ)
  is-retraction-inv-comp-natural-isomorphism-Precategoryᵉ =
    is-retraction-natural-transformation-inv-natural-isomorphism-Precategoryᵉ
      Cᵉ Dᵉ Fᵉ Hᵉ comp-natural-isomorphism-Precategoryᵉ
```

### Groupoid laws of natural isomorphisms in precategories

#### Composition of natural isomorphisms satisfies the unit laws

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ Gᵉ : functor-Precategoryᵉ Cᵉ Dᵉ)
  (fᵉ : natural-isomorphism-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ)
  where

  left-unit-law-comp-natural-isomorphism-Precategoryᵉ :
    comp-natural-isomorphism-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ Gᵉ
      ( id-natural-isomorphism-Precategoryᵉ Cᵉ Dᵉ Gᵉ)
      ( fᵉ) ＝ᵉ
    fᵉ
  left-unit-law-comp-natural-isomorphism-Precategoryᵉ =
    left-unit-law-comp-natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ
      ( map-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ)
      ( map-functor-Precategoryᵉ Cᵉ Dᵉ Gᵉ)
      ( fᵉ)

  right-unit-law-comp-natural-isomorphism-Precategoryᵉ :
    comp-natural-isomorphism-Precategoryᵉ Cᵉ Dᵉ Fᵉ Fᵉ Gᵉ fᵉ
      ( id-natural-isomorphism-Precategoryᵉ Cᵉ Dᵉ Fᵉ) ＝ᵉ
    fᵉ
  right-unit-law-comp-natural-isomorphism-Precategoryᵉ =
    right-unit-law-comp-natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ
      ( map-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ)
      ( map-functor-Precategoryᵉ Cᵉ Dᵉ Gᵉ)
      ( fᵉ)
```

#### Composition of natural isomorphisms is associative

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ Gᵉ Hᵉ Iᵉ : functor-Precategoryᵉ Cᵉ Dᵉ)
  (fᵉ : natural-isomorphism-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ)
  (gᵉ : natural-isomorphism-Precategoryᵉ Cᵉ Dᵉ Gᵉ Hᵉ)
  (hᵉ : natural-isomorphism-Precategoryᵉ Cᵉ Dᵉ Hᵉ Iᵉ)
  where

  associative-comp-natural-isomorphism-Precategoryᵉ :
    ( comp-natural-isomorphism-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ Iᵉ
      ( comp-natural-isomorphism-Precategoryᵉ Cᵉ Dᵉ Gᵉ Hᵉ Iᵉ hᵉ gᵉ)
      ( fᵉ)) ＝ᵉ
    ( comp-natural-isomorphism-Precategoryᵉ Cᵉ Dᵉ Fᵉ Hᵉ Iᵉ hᵉ
      ( comp-natural-isomorphism-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ Hᵉ gᵉ fᵉ))
  associative-comp-natural-isomorphism-Precategoryᵉ =
    associative-comp-natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ
      ( map-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ)
      ( map-functor-Precategoryᵉ Cᵉ Dᵉ Gᵉ)
      ( map-functor-Precategoryᵉ Cᵉ Dᵉ Hᵉ)
      ( map-functor-Precategoryᵉ Cᵉ Dᵉ Iᵉ)
      ( fᵉ)
      ( gᵉ)
      ( hᵉ)
```

#### Composition of natural isomorphisms satisfies inverse laws

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ Gᵉ : functor-Precategoryᵉ Cᵉ Dᵉ)
  (fᵉ : natural-isomorphism-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ)
  where

  left-inverse-law-comp-natural-isomorphism-Precategoryᵉ :
    ( comp-natural-isomorphism-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ Fᵉ
      ( inv-natural-isomorphism-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ fᵉ)
      ( fᵉ)) ＝ᵉ
    ( id-natural-isomorphism-Precategoryᵉ Cᵉ Dᵉ Fᵉ)
  left-inverse-law-comp-natural-isomorphism-Precategoryᵉ =
    left-inverse-law-comp-natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ
      ( map-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ)
      ( map-functor-Precategoryᵉ Cᵉ Dᵉ Gᵉ)
      ( fᵉ)

  right-inverse-law-comp-natural-isomorphism-Precategoryᵉ :
    ( comp-natural-isomorphism-Precategoryᵉ Cᵉ Dᵉ Gᵉ Fᵉ Gᵉ
      ( fᵉ)
      ( inv-natural-isomorphism-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ fᵉ)) ＝ᵉ
    ( id-natural-isomorphism-Precategoryᵉ Cᵉ Dᵉ Gᵉ)
  right-inverse-law-comp-natural-isomorphism-Precategoryᵉ =
    right-inverse-law-comp-natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ
      ( map-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ)
      ( map-functor-Precategoryᵉ Cᵉ Dᵉ Gᵉ)
      ( fᵉ)
```

### When the type of natural transformations is a proposition, the type of natural isomorphisms is a proposition

Theᵉ typeᵉ ofᵉ naturalᵉ isomorphismsᵉ betweenᵉ functorsᵉ `F`ᵉ andᵉ `G`ᵉ isᵉ aᵉ subtypeᵉ ofᵉ
`natural-transformationᵉ Fᵉ G`,ᵉ soᵉ whenᵉ thisᵉ typeᵉ isᵉ aᵉ proposition,ᵉ thenᵉ theᵉ typeᵉ
ofᵉ naturalᵉ isomorphismsᵉ fromᵉ `F`ᵉ to `G`ᵉ formᵉ aᵉ proposition.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ Gᵉ : functor-Precategoryᵉ Cᵉ Dᵉ)
  where

  is-prop-natural-isomorphism-Precategoryᵉ :
    is-propᵉ (natural-transformation-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ) →
    is-propᵉ (natural-isomorphism-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ)
  is-prop-natural-isomorphism-Precategoryᵉ =
    is-prop-natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ
      ( map-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ)
      ( map-functor-Precategoryᵉ Cᵉ Dᵉ Gᵉ)

  natural-isomorphism-prop-Precategoryᵉ :
    is-propᵉ (natural-transformation-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ) → Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l4ᵉ)
  natural-isomorphism-prop-Precategoryᵉ =
    natural-isomorphism-map-prop-Precategoryᵉ Cᵉ Dᵉ
      ( map-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ)
      ( map-functor-Precategoryᵉ Cᵉ Dᵉ Gᵉ)
```

### Functoriality of `natural-isomorphism-eq`

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ Gᵉ Hᵉ : functor-Precategoryᵉ Cᵉ Dᵉ)
  where

  preserves-concat-natural-isomorphism-eq-Precategoryᵉ :
    (pᵉ : Fᵉ ＝ᵉ Gᵉ) (qᵉ : Gᵉ ＝ᵉ Hᵉ) →
    natural-isomorphism-eq-Precategoryᵉ Cᵉ Dᵉ Fᵉ Hᵉ (pᵉ ∙ᵉ qᵉ) ＝ᵉ
    comp-natural-isomorphism-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ Hᵉ
      ( natural-isomorphism-eq-Precategoryᵉ Cᵉ Dᵉ Gᵉ Hᵉ qᵉ)
      ( natural-isomorphism-eq-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ pᵉ)
  preserves-concat-natural-isomorphism-eq-Precategoryᵉ reflᵉ qᵉ =
    invᵉ
      ( right-unit-law-comp-natural-isomorphism-Precategoryᵉ Cᵉ Dᵉ Fᵉ Hᵉ
        ( natural-isomorphism-eq-Precategoryᵉ Cᵉ Dᵉ Gᵉ Hᵉ qᵉ))
```