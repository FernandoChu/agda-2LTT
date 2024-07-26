# Natural isomorphisms between functors between categories

```agda
module category-theory.natural-isomorphisms-functors-categoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categoriesᵉ
open import category-theory.functors-categoriesᵉ
open import category-theory.isomorphisms-in-categoriesᵉ
open import category-theory.natural-isomorphisms-functors-precategoriesᵉ
open import category-theory.natural-transformations-functors-categoriesᵉ

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
[functor](category-theory.functors-categories.mdᵉ) `Fᵉ : Cᵉ → D`ᵉ to `Gᵉ : Cᵉ → D`ᵉ isᵉ
aᵉ
[naturalᵉ transformation](category-theory.natural-transformations-functors-categories.mdᵉ)
fromᵉ `F`ᵉ to `G`ᵉ suchᵉ thatᵉ theᵉ morphismᵉ `γᵉ Fᵉ : homᵉ (Fᵉ xᵉ) (Gᵉ x)`ᵉ isᵉ anᵉ
[isomorphism](category-theory.isomorphisms-in-categories.md),ᵉ forᵉ everyᵉ objectᵉ
`x`ᵉ in `C`.ᵉ

## Definition

### Families of isomorphisms between functors

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Categoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ Gᵉ : functor-Categoryᵉ Cᵉ Dᵉ)
  where

  iso-family-functor-Categoryᵉ : UUᵉ (l1ᵉ ⊔ l4ᵉ)
  iso-family-functor-Categoryᵉ =
    iso-family-functor-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( precategory-Categoryᵉ Dᵉ)
      ( Fᵉ)
      ( Gᵉ)
```

### The predicate of being an isomorphism in a category

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Categoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ Gᵉ : functor-Categoryᵉ Cᵉ Dᵉ)
  where

  is-natural-isomorphism-Categoryᵉ :
    natural-transformation-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ → UUᵉ (l1ᵉ ⊔ l4ᵉ)
  is-natural-isomorphism-Categoryᵉ =
    is-natural-isomorphism-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( precategory-Categoryᵉ Dᵉ)
      ( Fᵉ)
      ( Gᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Categoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ Gᵉ : functor-Categoryᵉ Cᵉ Dᵉ)
  (fᵉ : natural-transformation-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ)
  where

  hom-inv-family-is-natural-isomorphism-Categoryᵉ :
    is-natural-isomorphism-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ fᵉ →
    hom-family-functor-Categoryᵉ Cᵉ Dᵉ Gᵉ Fᵉ
  hom-inv-family-is-natural-isomorphism-Categoryᵉ =
    hom-inv-family-is-natural-isomorphism-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( precategory-Categoryᵉ Dᵉ)
      ( Fᵉ)
      ( Gᵉ)
      ( fᵉ)

  is-section-hom-inv-family-is-natural-isomorphism-Categoryᵉ :
    (is-iso-fᵉ : is-natural-isomorphism-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ fᵉ) →
    (xᵉ : obj-Categoryᵉ Cᵉ) →
    comp-hom-Categoryᵉ Dᵉ
      ( hom-family-natural-transformation-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ fᵉ xᵉ)
      ( hom-inv-is-iso-Categoryᵉ Dᵉ (is-iso-fᵉ xᵉ)) ＝ᵉ
    id-hom-Categoryᵉ Dᵉ
  is-section-hom-inv-family-is-natural-isomorphism-Categoryᵉ =
    is-section-hom-inv-family-is-natural-isomorphism-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( precategory-Categoryᵉ Dᵉ)
      ( Fᵉ)
      ( Gᵉ)
      ( fᵉ)

  is-retraction-hom-inv-family-is-natural-isomorphism-Categoryᵉ :
    (is-iso-fᵉ : is-natural-isomorphism-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ fᵉ) →
    (xᵉ : obj-Categoryᵉ Cᵉ) →
    comp-hom-Categoryᵉ Dᵉ
      ( hom-inv-is-iso-Categoryᵉ Dᵉ (is-iso-fᵉ xᵉ))
      ( hom-family-natural-transformation-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ fᵉ xᵉ) ＝ᵉ
    id-hom-Categoryᵉ Dᵉ
  is-retraction-hom-inv-family-is-natural-isomorphism-Categoryᵉ =
    is-retraction-hom-inv-family-is-natural-isomorphism-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( precategory-Categoryᵉ Dᵉ)
      ( Fᵉ)
      ( Gᵉ)
      ( fᵉ)

  iso-family-is-natural-isomorphism-Categoryᵉ :
    is-natural-isomorphism-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ fᵉ →
    iso-family-functor-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ
  iso-family-is-natural-isomorphism-Categoryᵉ =
    iso-family-is-natural-isomorphism-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( precategory-Categoryᵉ Dᵉ)
      ( Fᵉ)
      ( Gᵉ)
      ( fᵉ)

  inv-iso-family-is-natural-isomorphism-Categoryᵉ :
    is-natural-isomorphism-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ fᵉ →
    iso-family-functor-Categoryᵉ Cᵉ Dᵉ Gᵉ Fᵉ
  inv-iso-family-is-natural-isomorphism-Categoryᵉ =
    inv-iso-family-is-natural-isomorphism-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( precategory-Categoryᵉ Dᵉ)
      ( Fᵉ)
      ( Gᵉ)
      ( fᵉ)
```

### Natural isomorphisms in a category

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Categoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ Gᵉ : functor-Categoryᵉ Cᵉ Dᵉ)
  where

  natural-isomorphism-Categoryᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l4ᵉ)
  natural-isomorphism-Categoryᵉ =
    natural-isomorphism-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( precategory-Categoryᵉ Dᵉ)
      ( Fᵉ)
      ( Gᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Categoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ Gᵉ : functor-Categoryᵉ Cᵉ Dᵉ)
  (fᵉ : natural-isomorphism-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ)
  where

  natural-transformation-natural-isomorphism-Categoryᵉ :
    natural-transformation-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ
  natural-transformation-natural-isomorphism-Categoryᵉ =
    natural-transformation-natural-isomorphism-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( precategory-Categoryᵉ Dᵉ)
      ( Fᵉ)
      ( Gᵉ)
      ( fᵉ)

  hom-family-natural-isomorphism-Categoryᵉ :
    hom-family-functor-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ
  hom-family-natural-isomorphism-Categoryᵉ =
    hom-family-natural-transformation-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ
      ( natural-transformation-natural-isomorphism-Categoryᵉ)

  coherence-square-natural-isomorphism-Categoryᵉ :
    is-natural-transformation-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ
      ( hom-family-natural-transformation-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ
        ( natural-transformation-natural-isomorphism-Categoryᵉ))
  coherence-square-natural-isomorphism-Categoryᵉ =
    naturality-natural-transformation-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ
      ( natural-transformation-natural-isomorphism-Categoryᵉ)

  is-natural-isomorphism-natural-isomorphism-Categoryᵉ :
    is-natural-isomorphism-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ
      ( natural-transformation-natural-isomorphism-Categoryᵉ)
  is-natural-isomorphism-natural-isomorphism-Categoryᵉ = pr2ᵉ fᵉ

  hom-inv-family-natural-isomorphism-Categoryᵉ :
    hom-family-functor-Categoryᵉ Cᵉ Dᵉ Gᵉ Fᵉ
  hom-inv-family-natural-isomorphism-Categoryᵉ =
    hom-inv-family-is-natural-isomorphism-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ
      ( natural-transformation-natural-isomorphism-Categoryᵉ)
      ( is-natural-isomorphism-natural-isomorphism-Categoryᵉ)

  is-section-hom-inv-family-natural-isomorphism-Categoryᵉ :
    (xᵉ : obj-Categoryᵉ Cᵉ) →
    comp-hom-Categoryᵉ Dᵉ
      ( hom-family-natural-isomorphism-Categoryᵉ xᵉ)
      ( hom-inv-family-natural-isomorphism-Categoryᵉ xᵉ) ＝ᵉ
    id-hom-Categoryᵉ Dᵉ
  is-section-hom-inv-family-natural-isomorphism-Categoryᵉ =
    is-section-hom-inv-family-is-natural-isomorphism-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ
      ( natural-transformation-natural-isomorphism-Categoryᵉ)
      ( is-natural-isomorphism-natural-isomorphism-Categoryᵉ)

  is-retraction-hom-inv-family-natural-isomorphism-Categoryᵉ :
    (xᵉ : obj-Categoryᵉ Cᵉ) →
    comp-hom-Categoryᵉ Dᵉ
      ( hom-inv-family-natural-isomorphism-Categoryᵉ xᵉ)
      ( hom-family-natural-isomorphism-Categoryᵉ xᵉ) ＝ᵉ
    id-hom-Categoryᵉ Dᵉ
  is-retraction-hom-inv-family-natural-isomorphism-Categoryᵉ =
    is-retraction-hom-inv-family-is-natural-isomorphism-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ
      ( natural-transformation-natural-isomorphism-Categoryᵉ)
      ( is-natural-isomorphism-natural-isomorphism-Categoryᵉ)

  iso-family-natural-isomorphism-Categoryᵉ :
    iso-family-functor-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ
  iso-family-natural-isomorphism-Categoryᵉ =
    iso-family-is-natural-isomorphism-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ
      ( natural-transformation-natural-isomorphism-Categoryᵉ)
      ( is-natural-isomorphism-natural-isomorphism-Categoryᵉ)

  inv-iso-family-natural-isomorphism-Categoryᵉ :
    iso-family-functor-Categoryᵉ Cᵉ Dᵉ Gᵉ Fᵉ
  inv-iso-family-natural-isomorphism-Categoryᵉ =
    inv-iso-family-is-natural-isomorphism-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ
      ( natural-transformation-natural-isomorphism-Categoryᵉ)
      ( is-natural-isomorphism-natural-isomorphism-Categoryᵉ)
```

## Examples

### The identity natural isomorphism

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Categoryᵉ l3ᵉ l4ᵉ)
  where

  id-natural-isomorphism-Categoryᵉ :
    (Fᵉ : functor-Categoryᵉ Cᵉ Dᵉ) → natural-isomorphism-Categoryᵉ Cᵉ Dᵉ Fᵉ Fᵉ
  id-natural-isomorphism-Categoryᵉ =
    id-natural-isomorphism-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( precategory-Categoryᵉ Dᵉ)
```

### Equalities induce natural isomorphisms

Anᵉ equalityᵉ betweenᵉ functorsᵉ `F`ᵉ andᵉ `G`ᵉ givesᵉ riseᵉ to aᵉ naturalᵉ isomorphismᵉ
betweenᵉ them.ᵉ Thisᵉ isᵉ because,ᵉ byᵉ theᵉ J-rule,ᵉ itᵉ isᵉ enoughᵉ to constructᵉ aᵉ
naturalᵉ isomorphismᵉ givenᵉ `reflᵉ : Fᵉ ＝ᵉ F`,ᵉ fromᵉ `F`ᵉ to itself.ᵉ Weᵉ takeᵉ theᵉ
identityᵉ naturalᵉ transformationᵉ asᵉ suchᵉ anᵉ isomorphism.ᵉ

```agda
natural-isomorphism-eq-Categoryᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Categoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ Gᵉ : functor-Categoryᵉ Cᵉ Dᵉ) →
  Fᵉ ＝ᵉ Gᵉ → natural-isomorphism-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ
natural-isomorphism-eq-Categoryᵉ Cᵉ Dᵉ Fᵉ .Fᵉ reflᵉ =
  id-natural-isomorphism-Categoryᵉ Cᵉ Dᵉ Fᵉ
```

## Propositions

### Being a natural isomorphism is a proposition

Thatᵉ aᵉ naturalᵉ transformationᵉ isᵉ aᵉ naturalᵉ isomorphismᵉ isᵉ aᵉ proposition.ᵉ Thisᵉ
followsᵉ fromᵉ theᵉ factᵉ thatᵉ beingᵉ anᵉ isomorphismᵉ isᵉ aᵉ proposition.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Categoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ Gᵉ : functor-Categoryᵉ Cᵉ Dᵉ)
  where

  is-prop-is-natural-isomorphism-Categoryᵉ :
    (fᵉ : natural-transformation-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ) →
    is-propᵉ (is-natural-isomorphism-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ fᵉ)
  is-prop-is-natural-isomorphism-Categoryᵉ =
    is-prop-is-natural-isomorphism-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( precategory-Categoryᵉ Dᵉ)
      ( Fᵉ)
      ( Gᵉ)

  is-natural-isomorphism-prop-hom-Categoryᵉ :
    (fᵉ : natural-transformation-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ) → Propᵉ (l1ᵉ ⊔ l4ᵉ)
  is-natural-isomorphism-prop-hom-Categoryᵉ =
    is-natural-isomorphism-prop-hom-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( precategory-Categoryᵉ Dᵉ)
      ( Fᵉ)
      ( Gᵉ)
```

### Equality of natural isomorphisms is equality of their underlying natural transformations

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Categoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ Gᵉ : functor-Categoryᵉ Cᵉ Dᵉ)
  where

  extensionality-natural-isomorphism-Categoryᵉ :
    (fᵉ gᵉ : natural-isomorphism-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ) →
    (fᵉ ＝ᵉ gᵉ) ≃ᵉ
    ( hom-family-natural-isomorphism-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ fᵉ ~ᵉ
      hom-family-natural-isomorphism-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ gᵉ)
  extensionality-natural-isomorphism-Categoryᵉ =
    extensionality-natural-isomorphism-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( precategory-Categoryᵉ Dᵉ)
      ( Fᵉ)
      ( Gᵉ)

  eq-eq-natural-transformation-natural-isomorphism-Categoryᵉ :
    (fᵉ gᵉ : natural-isomorphism-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ) →
    ( natural-transformation-natural-isomorphism-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ fᵉ ＝ᵉ
      natural-transformation-natural-isomorphism-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ gᵉ) →
    fᵉ ＝ᵉ gᵉ
  eq-eq-natural-transformation-natural-isomorphism-Categoryᵉ fᵉ gᵉ =
    eq-type-subtypeᵉ (is-natural-isomorphism-prop-hom-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ)

  eq-htpy-hom-family-natural-isomorphism-Categoryᵉ :
        (fᵉ gᵉ : natural-isomorphism-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ) →
    ( hom-family-natural-isomorphism-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ fᵉ ~ᵉ
      hom-family-natural-isomorphism-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ gᵉ) →
    fᵉ ＝ᵉ gᵉ
  eq-htpy-hom-family-natural-isomorphism-Categoryᵉ =
    eq-htpy-hom-family-natural-isomorphism-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( precategory-Categoryᵉ Dᵉ)
      ( Fᵉ)
      ( Gᵉ)
```

### The type of natural isomorphisms form a set

Theᵉ typeᵉ ofᵉ naturalᵉ isomorphismsᵉ betweenᵉ functorsᵉ `F`ᵉ andᵉ `G`ᵉ isᵉ aᵉ
[subtype](foundation-core.subtypes.mdᵉ) ofᵉ theᵉ [set](foundation-core.sets.mdᵉ)
`natural-transformationᵉ Fᵉ G`ᵉ sinceᵉ beingᵉ anᵉ isomorphismᵉ isᵉ aᵉ proposition.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Categoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ Gᵉ : functor-Categoryᵉ Cᵉ Dᵉ)
  where

  is-set-natural-isomorphism-Categoryᵉ :
    is-setᵉ (natural-isomorphism-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ)
  is-set-natural-isomorphism-Categoryᵉ =
    is-set-type-subtypeᵉ
      ( is-natural-isomorphism-prop-hom-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ)
      ( is-set-natural-transformation-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ)

  natural-isomorphism-set-Categoryᵉ : Setᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l4ᵉ)
  pr1ᵉ natural-isomorphism-set-Categoryᵉ =
    natural-isomorphism-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ
  pr2ᵉ natural-isomorphism-set-Categoryᵉ =
    is-set-natural-isomorphism-Categoryᵉ
```

### Inverses of natural isomorphisms are natural isomorphisms

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Categoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ Gᵉ : functor-Categoryᵉ Cᵉ Dᵉ)
  (fᵉ : natural-transformation-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ)
  where

  natural-transformation-inv-is-natural-isomorphism-Categoryᵉ :
    is-natural-isomorphism-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ fᵉ →
    natural-transformation-Categoryᵉ Cᵉ Dᵉ Gᵉ Fᵉ
  natural-transformation-inv-is-natural-isomorphism-Categoryᵉ =
    natural-transformation-inv-is-natural-isomorphism-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( precategory-Categoryᵉ Dᵉ)
      ( Fᵉ)
      ( Gᵉ)
      ( fᵉ)

  is-section-natural-transformation-inv-is-natural-isomorphism-Categoryᵉ :
    (is-iso-fᵉ : is-natural-isomorphism-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ fᵉ) →
    comp-natural-transformation-Categoryᵉ Cᵉ Dᵉ Gᵉ Fᵉ Gᵉ
      ( fᵉ)
      ( natural-transformation-inv-is-natural-isomorphism-Categoryᵉ
        ( is-iso-fᵉ)) ＝ᵉ
    id-natural-transformation-Categoryᵉ Cᵉ Dᵉ Gᵉ
  is-section-natural-transformation-inv-is-natural-isomorphism-Categoryᵉ
    is-iso-fᵉ =
    eq-htpy-hom-family-natural-transformation-Categoryᵉ Cᵉ Dᵉ Gᵉ Gᵉ _ _
      ( is-section-hom-inv-is-iso-Categoryᵉ Dᵉ ∘ᵉ is-iso-fᵉ)

  is-retraction-natural-transformation-inv-is-natural-isomorphism-Categoryᵉ :
    (is-iso-fᵉ : is-natural-isomorphism-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ fᵉ) →
    comp-natural-transformation-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ Fᵉ
      ( natural-transformation-inv-is-natural-isomorphism-Categoryᵉ is-iso-fᵉ)
      ( fᵉ) ＝ᵉ
    id-natural-transformation-Categoryᵉ Cᵉ Dᵉ Fᵉ
  is-retraction-natural-transformation-inv-is-natural-isomorphism-Categoryᵉ
    is-iso-fᵉ =
    eq-htpy-hom-family-natural-transformation-Categoryᵉ Cᵉ Dᵉ Fᵉ Fᵉ _ _
      ( is-retraction-hom-inv-is-iso-Categoryᵉ Dᵉ ∘ᵉ is-iso-fᵉ)

  is-natural-isomorphism-inv-is-natural-isomorphism-Categoryᵉ :
    (is-iso-fᵉ : is-natural-isomorphism-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ fᵉ) →
    is-natural-isomorphism-Categoryᵉ Cᵉ Dᵉ Gᵉ Fᵉ
      ( natural-transformation-inv-is-natural-isomorphism-Categoryᵉ is-iso-fᵉ)
  is-natural-isomorphism-inv-is-natural-isomorphism-Categoryᵉ is-iso-fᵉ =
    is-iso-inv-is-iso-Categoryᵉ Dᵉ ∘ᵉ is-iso-fᵉ
```

### Inverses of natural isomorphisms

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Categoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ Gᵉ : functor-Categoryᵉ Cᵉ Dᵉ)
  (fᵉ : natural-isomorphism-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ)
  where

  natural-transformation-inv-natural-isomorphism-Categoryᵉ :
    natural-transformation-Categoryᵉ Cᵉ Dᵉ Gᵉ Fᵉ
  natural-transformation-inv-natural-isomorphism-Categoryᵉ =
    natural-transformation-inv-is-natural-isomorphism-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ
      ( natural-transformation-natural-isomorphism-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ fᵉ)
      ( is-natural-isomorphism-natural-isomorphism-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ fᵉ)

  is-section-natural-transformation-inv-natural-isomorphism-Categoryᵉ :
    ( comp-natural-transformation-Categoryᵉ Cᵉ Dᵉ Gᵉ Fᵉ Gᵉ
      ( natural-transformation-natural-isomorphism-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ fᵉ)
      ( natural-transformation-inv-natural-isomorphism-Categoryᵉ)) ＝ᵉ
    ( id-natural-transformation-Categoryᵉ Cᵉ Dᵉ Gᵉ)
  is-section-natural-transformation-inv-natural-isomorphism-Categoryᵉ =
    is-section-natural-transformation-inv-is-natural-isomorphism-Categoryᵉ
      Cᵉ Dᵉ Fᵉ Gᵉ
      ( natural-transformation-natural-isomorphism-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ fᵉ)
      ( is-natural-isomorphism-natural-isomorphism-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ fᵉ)

  is-retraction-natural-transformation-inv-natural-isomorphism-Categoryᵉ :
    ( comp-natural-transformation-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ Fᵉ
      ( natural-transformation-inv-natural-isomorphism-Categoryᵉ)
      ( natural-transformation-natural-isomorphism-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ fᵉ)) ＝ᵉ
    ( id-natural-transformation-Categoryᵉ Cᵉ Dᵉ Fᵉ)
  is-retraction-natural-transformation-inv-natural-isomorphism-Categoryᵉ =
    is-retraction-natural-transformation-inv-is-natural-isomorphism-Categoryᵉ
      Cᵉ Dᵉ Fᵉ Gᵉ
      ( natural-transformation-natural-isomorphism-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ fᵉ)
      ( is-natural-isomorphism-natural-isomorphism-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ fᵉ)

  is-natural-isomorphism-inv-natural-isomorphism-Categoryᵉ :
    is-natural-isomorphism-Categoryᵉ Cᵉ Dᵉ Gᵉ Fᵉ
      ( natural-transformation-inv-natural-isomorphism-Categoryᵉ)
  is-natural-isomorphism-inv-natural-isomorphism-Categoryᵉ =
    is-natural-isomorphism-inv-is-natural-isomorphism-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ
      ( natural-transformation-natural-isomorphism-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ fᵉ)
      ( is-natural-isomorphism-natural-isomorphism-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ fᵉ)

  inv-natural-isomorphism-Categoryᵉ :
    natural-isomorphism-Categoryᵉ Cᵉ Dᵉ Gᵉ Fᵉ
  pr1ᵉ inv-natural-isomorphism-Categoryᵉ =
    natural-transformation-inv-natural-isomorphism-Categoryᵉ
  pr2ᵉ inv-natural-isomorphism-Categoryᵉ =
    is-natural-isomorphism-inv-natural-isomorphism-Categoryᵉ
```

### Natural isomorphisms are closed under composition

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Categoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ Gᵉ Hᵉ : functor-Categoryᵉ Cᵉ Dᵉ)
  (gᵉ : natural-transformation-Categoryᵉ Cᵉ Dᵉ Gᵉ Hᵉ)
  (fᵉ : natural-transformation-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ)
  where

  is-natural-isomorphism-comp-is-natural-isomorphism-Categoryᵉ :
    is-natural-isomorphism-Categoryᵉ Cᵉ Dᵉ Gᵉ Hᵉ gᵉ →
    is-natural-isomorphism-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ fᵉ →
    is-natural-isomorphism-Categoryᵉ Cᵉ Dᵉ Fᵉ Hᵉ
      ( comp-natural-transformation-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ Hᵉ gᵉ fᵉ)
  is-natural-isomorphism-comp-is-natural-isomorphism-Categoryᵉ
    is-iso-gᵉ is-iso-fᵉ xᵉ =
      is-iso-comp-is-iso-Categoryᵉ Dᵉ (is-iso-gᵉ xᵉ) (is-iso-fᵉ xᵉ)
```

### The composition operation on natural isomorphisms

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Categoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ Gᵉ Hᵉ : functor-Categoryᵉ Cᵉ Dᵉ)
  (gᵉ : natural-isomorphism-Categoryᵉ Cᵉ Dᵉ Gᵉ Hᵉ)
  (fᵉ : natural-isomorphism-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ)
  where

  hom-comp-natural-isomorphism-Categoryᵉ :
    natural-transformation-Categoryᵉ Cᵉ Dᵉ Fᵉ Hᵉ
  hom-comp-natural-isomorphism-Categoryᵉ =
    comp-natural-transformation-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ Hᵉ
      ( natural-transformation-natural-isomorphism-Categoryᵉ Cᵉ Dᵉ Gᵉ Hᵉ gᵉ)
      ( natural-transformation-natural-isomorphism-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ fᵉ)

  is-natural-isomorphism-comp-natural-isomorphism-Categoryᵉ :
    is-natural-isomorphism-Categoryᵉ Cᵉ Dᵉ Fᵉ Hᵉ
      ( hom-comp-natural-isomorphism-Categoryᵉ)
  is-natural-isomorphism-comp-natural-isomorphism-Categoryᵉ =
    is-natural-isomorphism-comp-is-natural-isomorphism-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ Hᵉ
      ( natural-transformation-natural-isomorphism-Categoryᵉ Cᵉ Dᵉ Gᵉ Hᵉ gᵉ)
      ( natural-transformation-natural-isomorphism-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ fᵉ)
      ( is-natural-isomorphism-natural-isomorphism-Categoryᵉ Cᵉ Dᵉ Gᵉ Hᵉ gᵉ)
      ( is-natural-isomorphism-natural-isomorphism-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ fᵉ)

  comp-natural-isomorphism-Categoryᵉ : natural-isomorphism-Categoryᵉ Cᵉ Dᵉ Fᵉ Hᵉ
  pr1ᵉ comp-natural-isomorphism-Categoryᵉ =
    hom-comp-natural-isomorphism-Categoryᵉ
  pr2ᵉ comp-natural-isomorphism-Categoryᵉ =
    is-natural-isomorphism-comp-natural-isomorphism-Categoryᵉ

  natural-transformation-inv-comp-natural-isomorphism-Categoryᵉ :
    natural-transformation-Categoryᵉ Cᵉ Dᵉ Hᵉ Fᵉ
  natural-transformation-inv-comp-natural-isomorphism-Categoryᵉ =
    natural-transformation-inv-natural-isomorphism-Categoryᵉ Cᵉ Dᵉ Fᵉ Hᵉ
      ( comp-natural-isomorphism-Categoryᵉ)

  is-section-inv-comp-natural-isomorphism-Categoryᵉ :
    ( comp-natural-transformation-Categoryᵉ Cᵉ Dᵉ Hᵉ Fᵉ Hᵉ
      ( hom-comp-natural-isomorphism-Categoryᵉ)
      ( natural-transformation-inv-comp-natural-isomorphism-Categoryᵉ)) ＝ᵉ
    ( id-natural-transformation-Categoryᵉ Cᵉ Dᵉ Hᵉ)
  is-section-inv-comp-natural-isomorphism-Categoryᵉ =
    is-section-natural-transformation-inv-natural-isomorphism-Categoryᵉ
      Cᵉ Dᵉ Fᵉ Hᵉ comp-natural-isomorphism-Categoryᵉ

  is-retraction-inv-comp-natural-isomorphism-Categoryᵉ :
    ( comp-natural-transformation-Categoryᵉ Cᵉ Dᵉ Fᵉ Hᵉ Fᵉ
      ( natural-transformation-inv-comp-natural-isomorphism-Categoryᵉ)
      ( hom-comp-natural-isomorphism-Categoryᵉ)) ＝ᵉ
    ( id-natural-transformation-Categoryᵉ Cᵉ Dᵉ Fᵉ)
  is-retraction-inv-comp-natural-isomorphism-Categoryᵉ =
    is-retraction-natural-transformation-inv-natural-isomorphism-Categoryᵉ
      Cᵉ Dᵉ Fᵉ Hᵉ comp-natural-isomorphism-Categoryᵉ
```

### Groupoid laws of natural isomorphisms in categories

#### Composition of natural isomorphisms satisfies the unit laws

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Categoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ Gᵉ : functor-Categoryᵉ Cᵉ Dᵉ)
  (fᵉ : natural-isomorphism-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ)
  where

  left-unit-law-comp-natural-isomorphism-Categoryᵉ :
    comp-natural-isomorphism-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ Gᵉ
      ( id-natural-isomorphism-Categoryᵉ Cᵉ Dᵉ Gᵉ)
      ( fᵉ) ＝ᵉ
    fᵉ
  left-unit-law-comp-natural-isomorphism-Categoryᵉ =
    left-unit-law-comp-natural-isomorphism-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( precategory-Categoryᵉ Dᵉ)
      ( Fᵉ)
      ( Gᵉ)
      ( fᵉ)

  right-unit-law-comp-natural-isomorphism-Categoryᵉ :
    comp-natural-isomorphism-Categoryᵉ Cᵉ Dᵉ Fᵉ Fᵉ Gᵉ fᵉ
      ( id-natural-isomorphism-Categoryᵉ Cᵉ Dᵉ Fᵉ) ＝ᵉ
    fᵉ
  right-unit-law-comp-natural-isomorphism-Categoryᵉ =
    right-unit-law-comp-natural-isomorphism-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( precategory-Categoryᵉ Dᵉ)
      ( Fᵉ)
      ( Gᵉ)
      ( fᵉ)
```

#### Composition of natural isomorphisms is associative

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Categoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ Gᵉ Hᵉ Iᵉ : functor-Categoryᵉ Cᵉ Dᵉ)
  (fᵉ : natural-isomorphism-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ)
  (gᵉ : natural-isomorphism-Categoryᵉ Cᵉ Dᵉ Gᵉ Hᵉ)
  (hᵉ : natural-isomorphism-Categoryᵉ Cᵉ Dᵉ Hᵉ Iᵉ)
  where

  associative-comp-natural-isomorphism-Categoryᵉ :
    ( comp-natural-isomorphism-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ Iᵉ
      ( comp-natural-isomorphism-Categoryᵉ Cᵉ Dᵉ Gᵉ Hᵉ Iᵉ hᵉ gᵉ)
      ( fᵉ)) ＝ᵉ
    ( comp-natural-isomorphism-Categoryᵉ Cᵉ Dᵉ Fᵉ Hᵉ Iᵉ hᵉ
      ( comp-natural-isomorphism-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ Hᵉ gᵉ fᵉ))
  associative-comp-natural-isomorphism-Categoryᵉ =
    associative-comp-natural-isomorphism-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( precategory-Categoryᵉ Dᵉ)
      ( Fᵉ)
      ( Gᵉ)
      ( Hᵉ)
      ( Iᵉ)
      ( fᵉ)
      ( gᵉ)
      ( hᵉ)
```

#### Composition of natural isomorphisms satisfies inverse laws

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Categoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ Gᵉ : functor-Categoryᵉ Cᵉ Dᵉ)
  (fᵉ : natural-isomorphism-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ)
  where

  left-inverse-law-comp-natural-isomorphism-Categoryᵉ :
    ( comp-natural-isomorphism-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ Fᵉ
      ( inv-natural-isomorphism-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ fᵉ)
      ( fᵉ)) ＝ᵉ
    ( id-natural-isomorphism-Categoryᵉ Cᵉ Dᵉ Fᵉ)
  left-inverse-law-comp-natural-isomorphism-Categoryᵉ =
    left-inverse-law-comp-natural-isomorphism-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( precategory-Categoryᵉ Dᵉ)
      ( Fᵉ)
      ( Gᵉ)
      ( fᵉ)

  right-inverse-law-comp-natural-isomorphism-Categoryᵉ :
    ( comp-natural-isomorphism-Categoryᵉ Cᵉ Dᵉ Gᵉ Fᵉ Gᵉ
      ( fᵉ)
      ( inv-natural-isomorphism-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ fᵉ)) ＝ᵉ
    ( id-natural-isomorphism-Categoryᵉ Cᵉ Dᵉ Gᵉ)
  right-inverse-law-comp-natural-isomorphism-Categoryᵉ =
    right-inverse-law-comp-natural-isomorphism-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( precategory-Categoryᵉ Dᵉ)
      ( Fᵉ)
      ( Gᵉ)
      ( fᵉ)
```

### When the type of natural transformations is a proposition, the type of natural isomorphisms is a proposition

Theᵉ typeᵉ ofᵉ naturalᵉ isomorphismsᵉ betweenᵉ functorsᵉ `F`ᵉ andᵉ `G`ᵉ isᵉ aᵉ subtypeᵉ ofᵉ
`natural-transformationᵉ Fᵉ G`,ᵉ soᵉ whenᵉ thisᵉ typeᵉ isᵉ aᵉ proposition,ᵉ thenᵉ theᵉ typeᵉ
ofᵉ naturalᵉ isomorphismsᵉ fromᵉ `F`ᵉ to `G`ᵉ formᵉ aᵉ proposition.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Categoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ Gᵉ : functor-Categoryᵉ Cᵉ Dᵉ)
  where

  is-prop-natural-isomorphism-Categoryᵉ :
    is-propᵉ (natural-transformation-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ) →
    is-propᵉ (natural-isomorphism-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ)
  is-prop-natural-isomorphism-Categoryᵉ =
    is-prop-natural-isomorphism-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( precategory-Categoryᵉ Dᵉ)
      ( Fᵉ)
      ( Gᵉ)

  natural-isomorphism-prop-Categoryᵉ :
    is-propᵉ (natural-transformation-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ) → Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l4ᵉ)
  natural-isomorphism-prop-Categoryᵉ =
    natural-isomorphism-prop-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( precategory-Categoryᵉ Dᵉ)
      ( Fᵉ)
      ( Gᵉ)
```

### Functoriality of `natural-isomorphism-eq`

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Categoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ Gᵉ Hᵉ : functor-Categoryᵉ Cᵉ Dᵉ)
  where

  preserves-concat-natural-isomorphism-eq-Categoryᵉ :
    (pᵉ : Fᵉ ＝ᵉ Gᵉ) (qᵉ : Gᵉ ＝ᵉ Hᵉ) →
    natural-isomorphism-eq-Categoryᵉ Cᵉ Dᵉ Fᵉ Hᵉ (pᵉ ∙ᵉ qᵉ) ＝ᵉ
    comp-natural-isomorphism-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ Hᵉ
      ( natural-isomorphism-eq-Categoryᵉ Cᵉ Dᵉ Gᵉ Hᵉ qᵉ)
      ( natural-isomorphism-eq-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ pᵉ)
  preserves-concat-natural-isomorphism-eq-Categoryᵉ reflᵉ qᵉ =
    invᵉ
      ( right-unit-law-comp-natural-isomorphism-Categoryᵉ Cᵉ Dᵉ Fᵉ Hᵉ
        ( natural-isomorphism-eq-Categoryᵉ Cᵉ Dᵉ Gᵉ Hᵉ qᵉ))
```