# Natural isomorphisms between maps between precategories

```agda
module category-theory.natural-isomorphisms-maps-precategoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.isomorphisms-in-precategoriesᵉ
open import category-theory.maps-precategoriesᵉ
open import category-theory.natural-transformations-maps-precategoriesᵉ
open import category-theory.precategoriesᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.embeddingsᵉ
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

Aᵉ **naturalᵉ isomorphism**ᵉ `γ`ᵉ fromᵉ [map](category-theory.maps-precategories.mdᵉ)
`Fᵉ : Cᵉ → D`ᵉ to `Gᵉ : Cᵉ → D`ᵉ isᵉ aᵉ
[naturalᵉ transformation](category-theory.natural-transformations-maps-precategories.mdᵉ)
fromᵉ `F`ᵉ to `G`ᵉ suchᵉ thatᵉ theᵉ morphismᵉ `γᵉ Fᵉ : homᵉ (Fᵉ xᵉ) (Gᵉ x)`ᵉ isᵉ anᵉ
[isomorphism](category-theory.isomorphisms-in-precategories.md),ᵉ forᵉ everyᵉ
objectᵉ `x`ᵉ in `C`.ᵉ

## Definition

### Families of isomorphisms between maps

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ Gᵉ : map-Precategoryᵉ Cᵉ Dᵉ)
  where

  iso-family-map-Precategoryᵉ : UUᵉ (l1ᵉ ⊔ l4ᵉ)
  iso-family-map-Precategoryᵉ =
    (xᵉ : obj-Precategoryᵉ Cᵉ) →
    iso-Precategoryᵉ Dᵉ
      ( obj-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ xᵉ)
      ( obj-map-Precategoryᵉ Cᵉ Dᵉ Gᵉ xᵉ)
```

### The predicate of being an isomorphism in a precategory

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ Gᵉ : map-Precategoryᵉ Cᵉ Dᵉ)
  where

  is-natural-isomorphism-map-Precategoryᵉ :
    natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ → UUᵉ (l1ᵉ ⊔ l4ᵉ)
  is-natural-isomorphism-map-Precategoryᵉ fᵉ =
    (xᵉ : obj-Precategoryᵉ Cᵉ) →
    is-iso-Precategoryᵉ Dᵉ
      ( hom-family-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ fᵉ xᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ Gᵉ : map-Precategoryᵉ Cᵉ Dᵉ)
  (fᵉ : natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ)
  where

  hom-inv-family-is-natural-isomorphism-map-Precategoryᵉ :
    is-natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ fᵉ →
    hom-family-map-Precategoryᵉ Cᵉ Dᵉ Gᵉ Fᵉ
  hom-inv-family-is-natural-isomorphism-map-Precategoryᵉ is-iso-fᵉ =
    hom-inv-is-iso-Precategoryᵉ Dᵉ ∘ᵉ is-iso-fᵉ

  is-section-hom-inv-family-is-natural-isomorphism-map-Precategoryᵉ :
    (is-iso-fᵉ : is-natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ fᵉ) →
    (xᵉ : obj-Precategoryᵉ Cᵉ) →
    comp-hom-Precategoryᵉ Dᵉ
      ( hom-family-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ fᵉ xᵉ)
      ( hom-inv-is-iso-Precategoryᵉ Dᵉ (is-iso-fᵉ xᵉ)) ＝ᵉ
    id-hom-Precategoryᵉ Dᵉ
  is-section-hom-inv-family-is-natural-isomorphism-map-Precategoryᵉ is-iso-fᵉ =
    is-section-hom-inv-is-iso-Precategoryᵉ Dᵉ ∘ᵉ is-iso-fᵉ

  is-retraction-hom-inv-family-is-natural-isomorphism-map-Precategoryᵉ :
    (is-iso-fᵉ : is-natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ fᵉ) →
    (xᵉ : obj-Precategoryᵉ Cᵉ) →
    comp-hom-Precategoryᵉ Dᵉ
      ( hom-inv-is-iso-Precategoryᵉ Dᵉ (is-iso-fᵉ xᵉ))
      ( hom-family-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ fᵉ xᵉ) ＝ᵉ
    id-hom-Precategoryᵉ Dᵉ
  is-retraction-hom-inv-family-is-natural-isomorphism-map-Precategoryᵉ is-iso-fᵉ =
    is-retraction-hom-inv-is-iso-Precategoryᵉ Dᵉ ∘ᵉ is-iso-fᵉ

  iso-family-is-natural-isomorphism-map-Precategoryᵉ :
    is-natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ fᵉ →
    iso-family-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ
  pr1ᵉ (iso-family-is-natural-isomorphism-map-Precategoryᵉ is-iso-fᵉ xᵉ) =
    hom-family-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ fᵉ xᵉ
  pr2ᵉ (iso-family-is-natural-isomorphism-map-Precategoryᵉ is-iso-fᵉ xᵉ) =
    is-iso-fᵉ xᵉ

  inv-iso-family-is-natural-isomorphism-map-Precategoryᵉ :
    is-natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ fᵉ →
    iso-family-map-Precategoryᵉ Cᵉ Dᵉ Gᵉ Fᵉ
  inv-iso-family-is-natural-isomorphism-map-Precategoryᵉ is-iso-fᵉ =
    inv-iso-Precategoryᵉ Dᵉ ∘ᵉ
    iso-family-is-natural-isomorphism-map-Precategoryᵉ is-iso-fᵉ
```

### Natural isomorphisms in a precategory

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ Gᵉ : map-Precategoryᵉ Cᵉ Dᵉ)
  where

  natural-isomorphism-map-Precategoryᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l4ᵉ)
  natural-isomorphism-map-Precategoryᵉ =
    Σᵉ ( natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ)
      ( is-natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ Gᵉ : map-Precategoryᵉ Cᵉ Dᵉ)
  (fᵉ : natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ)
  where

  natural-transformation-map-natural-isomorphism-map-Precategoryᵉ :
    natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ
  natural-transformation-map-natural-isomorphism-map-Precategoryᵉ = pr1ᵉ fᵉ

  hom-family-natural-isomorphism-map-Precategoryᵉ :
    hom-family-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ
  hom-family-natural-isomorphism-map-Precategoryᵉ =
    hom-family-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ
      ( natural-transformation-map-natural-isomorphism-map-Precategoryᵉ)

  coherence-square-natural-isomorphism-map-Precategoryᵉ :
    is-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ
      ( hom-family-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ
        ( natural-transformation-map-natural-isomorphism-map-Precategoryᵉ))
  coherence-square-natural-isomorphism-map-Precategoryᵉ =
    naturality-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ
      ( natural-transformation-map-natural-isomorphism-map-Precategoryᵉ)

  is-natural-isomorphism-map-natural-isomorphism-map-Precategoryᵉ :
    is-natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ
      ( natural-transformation-map-natural-isomorphism-map-Precategoryᵉ)
  is-natural-isomorphism-map-natural-isomorphism-map-Precategoryᵉ = pr2ᵉ fᵉ

  hom-inv-family-natural-isomorphism-map-Precategoryᵉ :
    hom-family-map-Precategoryᵉ Cᵉ Dᵉ Gᵉ Fᵉ
  hom-inv-family-natural-isomorphism-map-Precategoryᵉ =
    hom-inv-family-is-natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ
      ( natural-transformation-map-natural-isomorphism-map-Precategoryᵉ)
      ( is-natural-isomorphism-map-natural-isomorphism-map-Precategoryᵉ)

  is-section-hom-inv-family-natural-isomorphism-map-Precategoryᵉ :
    (xᵉ : obj-Precategoryᵉ Cᵉ) →
    comp-hom-Precategoryᵉ Dᵉ
      ( hom-family-natural-isomorphism-map-Precategoryᵉ xᵉ)
      ( hom-inv-family-natural-isomorphism-map-Precategoryᵉ xᵉ) ＝ᵉ
    id-hom-Precategoryᵉ Dᵉ
  is-section-hom-inv-family-natural-isomorphism-map-Precategoryᵉ =
    is-section-hom-inv-family-is-natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ
      ( natural-transformation-map-natural-isomorphism-map-Precategoryᵉ)
      ( is-natural-isomorphism-map-natural-isomorphism-map-Precategoryᵉ)

  is-retraction-hom-inv-family-natural-isomorphism-map-Precategoryᵉ :
    (xᵉ : obj-Precategoryᵉ Cᵉ) →
    comp-hom-Precategoryᵉ Dᵉ
      ( hom-inv-family-natural-isomorphism-map-Precategoryᵉ xᵉ)
      ( hom-family-natural-isomorphism-map-Precategoryᵉ xᵉ) ＝ᵉ
    id-hom-Precategoryᵉ Dᵉ
  is-retraction-hom-inv-family-natural-isomorphism-map-Precategoryᵉ =
    is-retraction-hom-inv-family-is-natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ
      ( natural-transformation-map-natural-isomorphism-map-Precategoryᵉ)
      ( is-natural-isomorphism-map-natural-isomorphism-map-Precategoryᵉ)

  iso-family-natural-isomorphism-map-Precategoryᵉ :
    iso-family-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ
  iso-family-natural-isomorphism-map-Precategoryᵉ =
    iso-family-is-natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ
      ( natural-transformation-map-natural-isomorphism-map-Precategoryᵉ)
      ( is-natural-isomorphism-map-natural-isomorphism-map-Precategoryᵉ)

  inv-iso-family-natural-isomorphism-map-Precategoryᵉ :
    iso-family-map-Precategoryᵉ Cᵉ Dᵉ Gᵉ Fᵉ
  inv-iso-family-natural-isomorphism-map-Precategoryᵉ =
    inv-iso-family-is-natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ
      ( natural-transformation-map-natural-isomorphism-map-Precategoryᵉ)
      ( is-natural-isomorphism-map-natural-isomorphism-map-Precategoryᵉ)
```

## Examples

### The identity natural isomorphism

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  where

  id-natural-isomorphism-map-Precategoryᵉ :
    (Fᵉ : map-Precategoryᵉ Cᵉ Dᵉ) → natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Fᵉ
  pr1ᵉ (id-natural-isomorphism-map-Precategoryᵉ Fᵉ) =
    id-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ
  pr2ᵉ (id-natural-isomorphism-map-Precategoryᵉ Fᵉ) xᵉ =
    is-iso-id-hom-Precategoryᵉ Dᵉ
```

### Equalities induce natural isomorphisms

Anᵉ equalityᵉ betweenᵉ mapsᵉ `F`ᵉ andᵉ `G`ᵉ givesᵉ riseᵉ to aᵉ naturalᵉ isomorphismᵉ betweenᵉ
them.ᵉ Thisᵉ isᵉ because,ᵉ byᵉ theᵉ J-rule,ᵉ itᵉ isᵉ enoughᵉ to constructᵉ aᵉ naturalᵉ
isomorphismᵉ givenᵉ `reflᵉ : Fᵉ ＝ᵉ F`,ᵉ fromᵉ `F`ᵉ to itself.ᵉ Weᵉ takeᵉ theᵉ identityᵉ
naturalᵉ transformationᵉ asᵉ suchᵉ anᵉ isomorphism.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  where

  natural-isomorphism-map-eq-Precategoryᵉ :
    (Fᵉ Gᵉ : map-Precategoryᵉ Cᵉ Dᵉ) →
    Fᵉ ＝ᵉ Gᵉ → natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ
  natural-isomorphism-map-eq-Precategoryᵉ Fᵉ .Fᵉ reflᵉ =
    id-natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ
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
  (Fᵉ Gᵉ : map-Precategoryᵉ Cᵉ Dᵉ)
  where

  is-prop-is-natural-isomorphism-map-Precategoryᵉ :
    (fᵉ : natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ) →
    is-propᵉ (is-natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ fᵉ)
  is-prop-is-natural-isomorphism-map-Precategoryᵉ fᵉ =
    is-prop-Πᵉ (is-prop-is-iso-Precategoryᵉ Dᵉ ∘ᵉ
    hom-family-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ fᵉ)

  is-natural-isomorphism-map-prop-hom-Precategoryᵉ :
    (fᵉ : natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ) → Propᵉ (l1ᵉ ⊔ l4ᵉ)
  pr1ᵉ (is-natural-isomorphism-map-prop-hom-Precategoryᵉ fᵉ) =
    is-natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ fᵉ
  pr2ᵉ (is-natural-isomorphism-map-prop-hom-Precategoryᵉ fᵉ) =
    is-prop-is-natural-isomorphism-map-Precategoryᵉ fᵉ
```

### Equality of natural isomorphisms is equality of their underlying natural transformations

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ Gᵉ : map-Precategoryᵉ Cᵉ Dᵉ)
  where

  extensionality-natural-isomorphism-map-Precategoryᵉ :
    (fᵉ gᵉ : natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ) →
    (fᵉ ＝ᵉ gᵉ) ≃ᵉ
    ( hom-family-natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ fᵉ ~ᵉ
      hom-family-natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ gᵉ)
  extensionality-natural-isomorphism-map-Precategoryᵉ fᵉ gᵉ =
    ( extensionality-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ
      ( natural-transformation-map-natural-isomorphism-map-Precategoryᵉ
          Cᵉ Dᵉ Fᵉ Gᵉ fᵉ)
      ( natural-transformation-map-natural-isomorphism-map-Precategoryᵉ
          Cᵉ Dᵉ Fᵉ Gᵉ gᵉ)) ∘eᵉ
    ( equiv-ap-embᵉ
      ( emb-subtypeᵉ (is-natural-isomorphism-map-prop-hom-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ)))

  eq-eq-natural-transformation-map-natural-isomorphism-map-Precategoryᵉ :
    (fᵉ gᵉ : natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ) →
    ( ( natural-transformation-map-natural-isomorphism-map-Precategoryᵉ
          Cᵉ Dᵉ Fᵉ Gᵉ fᵉ) ＝ᵉ
      ( natural-transformation-map-natural-isomorphism-map-Precategoryᵉ
          Cᵉ Dᵉ Fᵉ Gᵉ gᵉ)) →
    fᵉ ＝ᵉ gᵉ
  eq-eq-natural-transformation-map-natural-isomorphism-map-Precategoryᵉ fᵉ gᵉ =
    eq-type-subtypeᵉ (is-natural-isomorphism-map-prop-hom-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ)

  eq-htpy-hom-family-natural-isomorphism-map-Precategoryᵉ :
        (fᵉ gᵉ : natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ) →
    ( hom-family-natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ fᵉ ~ᵉ
      hom-family-natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ gᵉ) →
    fᵉ ＝ᵉ gᵉ
  eq-htpy-hom-family-natural-isomorphism-map-Precategoryᵉ fᵉ gᵉ =
    eq-eq-natural-transformation-map-natural-isomorphism-map-Precategoryᵉ fᵉ gᵉ ∘ᵉ
    eq-htpy-hom-family-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ
      ( natural-transformation-map-natural-isomorphism-map-Precategoryᵉ
          Cᵉ Dᵉ Fᵉ Gᵉ fᵉ)
      ( natural-transformation-map-natural-isomorphism-map-Precategoryᵉ
          Cᵉ Dᵉ Fᵉ Gᵉ gᵉ)
```

### The type of natural isomorphisms form a set

Theᵉ typeᵉ ofᵉ naturalᵉ isomorphismsᵉ betweenᵉ mapsᵉ `F`ᵉ andᵉ `G`ᵉ isᵉ aᵉ
[subtype](foundation-core.subtypes.mdᵉ) ofᵉ theᵉ [set](foundation-core.sets.mdᵉ)
`natural-transformationᵉ Fᵉ G`ᵉ sinceᵉ beingᵉ anᵉ isomorphismᵉ isᵉ aᵉ proposition.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ Gᵉ : map-Precategoryᵉ Cᵉ Dᵉ)
  where

  is-set-natural-isomorphism-map-Precategoryᵉ :
    is-setᵉ (natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ)
  is-set-natural-isomorphism-map-Precategoryᵉ =
    is-set-type-subtypeᵉ
      ( is-natural-isomorphism-map-prop-hom-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ)
      ( is-set-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ)

  natural-isomorphism-map-set-Precategoryᵉ : Setᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l4ᵉ)
  pr1ᵉ natural-isomorphism-map-set-Precategoryᵉ =
    natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ
  pr2ᵉ natural-isomorphism-map-set-Precategoryᵉ =
    is-set-natural-isomorphism-map-Precategoryᵉ
```

### Inverses of natural isomorphisms are natural isomorphisms

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ Gᵉ : map-Precategoryᵉ Cᵉ Dᵉ)
  (fᵉ : natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ)
  where

  natural-transformation-map-inv-is-natural-isomorphism-map-Precategoryᵉ :
    is-natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ fᵉ →
    natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Gᵉ Fᵉ
  pr1ᵉ
    ( natural-transformation-map-inv-is-natural-isomorphism-map-Precategoryᵉ
      ( is-iso-fᵉ)) =
    hom-inv-is-iso-Precategoryᵉ Dᵉ ∘ᵉ is-iso-fᵉ
  pr2ᵉ
    ( natural-transformation-map-inv-is-natural-isomorphism-map-Precategoryᵉ
      ( is-iso-fᵉ))
    { xᵉ} {yᵉ} gᵉ =
    ( invᵉ
      ( left-unit-law-comp-hom-Precategoryᵉ Dᵉ
        ( comp-hom-Precategoryᵉ Dᵉ
          ( hom-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ gᵉ)
          ( hom-inv-family-is-natural-isomorphism-map-Precategoryᵉ
              Cᵉ Dᵉ Fᵉ Gᵉ fᵉ is-iso-fᵉ xᵉ)))) ∙ᵉ
    ( apᵉ
      ( comp-hom-Precategory'ᵉ Dᵉ
        ( comp-hom-Precategoryᵉ Dᵉ
          ( hom-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ gᵉ)
          ( hom-inv-family-is-natural-isomorphism-map-Precategoryᵉ
              Cᵉ Dᵉ Fᵉ Gᵉ fᵉ is-iso-fᵉ xᵉ)))
      ( invᵉ (is-retraction-hom-inv-is-iso-Precategoryᵉ Dᵉ (is-iso-fᵉ yᵉ)))) ∙ᵉ
    ( associative-comp-hom-Precategoryᵉ Dᵉ
      ( hom-inv-family-is-natural-isomorphism-map-Precategoryᵉ
          Cᵉ Dᵉ Fᵉ Gᵉ fᵉ is-iso-fᵉ yᵉ)
      ( hom-family-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ fᵉ yᵉ)
      ( comp-hom-Precategoryᵉ Dᵉ
        ( hom-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ gᵉ)
        ( hom-inv-family-is-natural-isomorphism-map-Precategoryᵉ
            Cᵉ Dᵉ Fᵉ Gᵉ fᵉ is-iso-fᵉ xᵉ))) ∙ᵉ
    ( apᵉ
      ( comp-hom-Precategoryᵉ Dᵉ
        ( hom-inv-family-is-natural-isomorphism-map-Precategoryᵉ
            Cᵉ Dᵉ Fᵉ Gᵉ fᵉ is-iso-fᵉ yᵉ))
      ( ( invᵉ
          ( associative-comp-hom-Precategoryᵉ Dᵉ
            ( hom-family-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ fᵉ yᵉ)
            ( hom-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ gᵉ)
            ( hom-inv-family-is-natural-isomorphism-map-Precategoryᵉ
                Cᵉ Dᵉ Fᵉ Gᵉ fᵉ is-iso-fᵉ xᵉ))) ∙ᵉ
        ( apᵉ
          ( comp-hom-Precategory'ᵉ Dᵉ _)
          ( invᵉ
            ( naturality-natural-transformation-map-Precategoryᵉ
                Cᵉ Dᵉ Fᵉ Gᵉ fᵉ gᵉ))) ∙ᵉ
        ( associative-comp-hom-Precategoryᵉ Dᵉ
          ( hom-map-Precategoryᵉ Cᵉ Dᵉ Gᵉ gᵉ)
          ( hom-family-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ fᵉ xᵉ)
          ( hom-inv-is-iso-Precategoryᵉ Dᵉ (is-iso-fᵉ xᵉ))) ∙ᵉ
        ( apᵉ
          ( comp-hom-Precategoryᵉ Dᵉ (hom-map-Precategoryᵉ Cᵉ Dᵉ Gᵉ gᵉ))
          ( is-section-hom-inv-is-iso-Precategoryᵉ Dᵉ (is-iso-fᵉ xᵉ))) ∙ᵉ
        ( right-unit-law-comp-hom-Precategoryᵉ Dᵉ
          ( hom-map-Precategoryᵉ Cᵉ Dᵉ Gᵉ gᵉ))))

  is-section-natural-transformation-map-inv-is-natural-isomorphism-map-Precategoryᵉ :
    (is-iso-fᵉ : is-natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ fᵉ) →
    comp-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Gᵉ Fᵉ Gᵉ
      ( fᵉ)
      ( natural-transformation-map-inv-is-natural-isomorphism-map-Precategoryᵉ
        ( is-iso-fᵉ)) ＝ᵉ
    id-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Gᵉ
  is-section-natural-transformation-map-inv-is-natural-isomorphism-map-Precategoryᵉ
    is-iso-fᵉ =
    eq-htpy-hom-family-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Gᵉ Gᵉ _ _
      ( is-section-hom-inv-is-iso-Precategoryᵉ Dᵉ ∘ᵉ is-iso-fᵉ)

  is-retraction-natural-transformation-map-inv-is-natural-isomorphism-map-Precategoryᵉ :
    (is-iso-fᵉ : is-natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ fᵉ) →
    comp-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ Fᵉ
      ( natural-transformation-map-inv-is-natural-isomorphism-map-Precategoryᵉ
        ( is-iso-fᵉ))
      ( fᵉ) ＝ᵉ
    id-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ
  is-retraction-natural-transformation-map-inv-is-natural-isomorphism-map-Precategoryᵉ
    is-iso-fᵉ =
    eq-htpy-hom-family-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Fᵉ _ _
      ( is-retraction-hom-inv-is-iso-Precategoryᵉ Dᵉ ∘ᵉ is-iso-fᵉ)

  is-natural-isomorphism-map-inv-is-natural-isomorphism-map-Precategoryᵉ :
    (is-iso-fᵉ : is-natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ fᵉ) →
    is-natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ Gᵉ Fᵉ
      ( natural-transformation-map-inv-is-natural-isomorphism-map-Precategoryᵉ
        ( is-iso-fᵉ))
  is-natural-isomorphism-map-inv-is-natural-isomorphism-map-Precategoryᵉ
    is-iso-fᵉ =
    is-iso-inv-is-iso-Precategoryᵉ Dᵉ ∘ᵉ is-iso-fᵉ
```

### Inverses of natural isomorphisms

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ Gᵉ : map-Precategoryᵉ Cᵉ Dᵉ)
  (fᵉ : natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ)
  where

  natural-transformation-map-inv-natural-isomorphism-map-Precategoryᵉ :
    natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Gᵉ Fᵉ
  natural-transformation-map-inv-natural-isomorphism-map-Precategoryᵉ =
    natural-transformation-map-inv-is-natural-isomorphism-map-Precategoryᵉ
      Cᵉ Dᵉ Fᵉ Gᵉ
      ( natural-transformation-map-natural-isomorphism-map-Precategoryᵉ
          Cᵉ Dᵉ Fᵉ Gᵉ fᵉ)
      ( is-natural-isomorphism-map-natural-isomorphism-map-Precategoryᵉ
          Cᵉ Dᵉ Fᵉ Gᵉ fᵉ)

  is-section-natural-transformation-map-inv-natural-isomorphism-map-Precategoryᵉ :
    ( comp-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Gᵉ Fᵉ Gᵉ
      ( natural-transformation-map-natural-isomorphism-map-Precategoryᵉ
          Cᵉ Dᵉ Fᵉ Gᵉ fᵉ)
      ( natural-transformation-map-inv-natural-isomorphism-map-Precategoryᵉ)) ＝ᵉ
    ( id-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Gᵉ)
  is-section-natural-transformation-map-inv-natural-isomorphism-map-Precategoryᵉ =
    is-section-natural-transformation-map-inv-is-natural-isomorphism-map-Precategoryᵉ
      Cᵉ Dᵉ Fᵉ Gᵉ
      ( natural-transformation-map-natural-isomorphism-map-Precategoryᵉ
          Cᵉ Dᵉ Fᵉ Gᵉ fᵉ)
      ( is-natural-isomorphism-map-natural-isomorphism-map-Precategoryᵉ
          Cᵉ Dᵉ Fᵉ Gᵉ fᵉ)

  is-retraction-natural-transformation-map-inv-natural-isomorphism-map-Precategoryᵉ :
    ( comp-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ Fᵉ
      ( natural-transformation-map-inv-natural-isomorphism-map-Precategoryᵉ)
      ( natural-transformation-map-natural-isomorphism-map-Precategoryᵉ
          Cᵉ Dᵉ Fᵉ Gᵉ fᵉ)) ＝ᵉ
    ( id-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ)
  is-retraction-natural-transformation-map-inv-natural-isomorphism-map-Precategoryᵉ =
    is-retraction-natural-transformation-map-inv-is-natural-isomorphism-map-Precategoryᵉ
      Cᵉ Dᵉ Fᵉ Gᵉ
      ( natural-transformation-map-natural-isomorphism-map-Precategoryᵉ
          Cᵉ Dᵉ Fᵉ Gᵉ fᵉ)
      ( is-natural-isomorphism-map-natural-isomorphism-map-Precategoryᵉ
          Cᵉ Dᵉ Fᵉ Gᵉ fᵉ)

  is-natural-isomorphism-map-inv-natural-isomorphism-map-Precategoryᵉ :
    is-natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ Gᵉ Fᵉ
      ( natural-transformation-map-inv-natural-isomorphism-map-Precategoryᵉ)
  is-natural-isomorphism-map-inv-natural-isomorphism-map-Precategoryᵉ =
    is-natural-isomorphism-map-inv-is-natural-isomorphism-map-Precategoryᵉ
      Cᵉ Dᵉ Fᵉ Gᵉ
      ( natural-transformation-map-natural-isomorphism-map-Precategoryᵉ
          Cᵉ Dᵉ Fᵉ Gᵉ fᵉ)
      ( is-natural-isomorphism-map-natural-isomorphism-map-Precategoryᵉ
          Cᵉ Dᵉ Fᵉ Gᵉ fᵉ)

  inv-natural-isomorphism-map-Precategoryᵉ :
    natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ Gᵉ Fᵉ
  pr1ᵉ inv-natural-isomorphism-map-Precategoryᵉ =
    natural-transformation-map-inv-natural-isomorphism-map-Precategoryᵉ
  pr2ᵉ inv-natural-isomorphism-map-Precategoryᵉ =
    is-natural-isomorphism-map-inv-natural-isomorphism-map-Precategoryᵉ
```

### Natural isomorphisms are closed under composition

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ Gᵉ Hᵉ : map-Precategoryᵉ Cᵉ Dᵉ)
  (gᵉ : natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Gᵉ Hᵉ)
  (fᵉ : natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ)
  where

  is-natural-isomorphism-map-comp-is-natural-isomorphism-map-Precategoryᵉ :
    is-natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ Gᵉ Hᵉ gᵉ →
    is-natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ fᵉ →
    is-natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Hᵉ
      ( comp-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ Hᵉ gᵉ fᵉ)
  is-natural-isomorphism-map-comp-is-natural-isomorphism-map-Precategoryᵉ
    is-iso-gᵉ is-iso-fᵉ xᵉ =
    is-iso-comp-is-iso-Precategoryᵉ Dᵉ (is-iso-gᵉ xᵉ) (is-iso-fᵉ xᵉ)
```

### The composition operation on natural isomorphisms

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ Gᵉ Hᵉ : map-Precategoryᵉ Cᵉ Dᵉ)
  (gᵉ : natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ Gᵉ Hᵉ)
  (fᵉ : natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ)
  where

  hom-comp-natural-isomorphism-map-Precategoryᵉ :
    natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Hᵉ
  hom-comp-natural-isomorphism-map-Precategoryᵉ =
    comp-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ Hᵉ
      ( natural-transformation-map-natural-isomorphism-map-Precategoryᵉ
          Cᵉ Dᵉ Gᵉ Hᵉ gᵉ)
      ( natural-transformation-map-natural-isomorphism-map-Precategoryᵉ
          Cᵉ Dᵉ Fᵉ Gᵉ fᵉ)

  is-natural-isomorphism-map-comp-natural-isomorphism-map-Precategoryᵉ :
    is-natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Hᵉ
      ( hom-comp-natural-isomorphism-map-Precategoryᵉ)
  is-natural-isomorphism-map-comp-natural-isomorphism-map-Precategoryᵉ =
    is-natural-isomorphism-map-comp-is-natural-isomorphism-map-Precategoryᵉ
      Cᵉ Dᵉ Fᵉ Gᵉ Hᵉ
      ( natural-transformation-map-natural-isomorphism-map-Precategoryᵉ
          Cᵉ Dᵉ Gᵉ Hᵉ gᵉ)
      ( natural-transformation-map-natural-isomorphism-map-Precategoryᵉ
          Cᵉ Dᵉ Fᵉ Gᵉ fᵉ)
      ( is-natural-isomorphism-map-natural-isomorphism-map-Precategoryᵉ
          Cᵉ Dᵉ Gᵉ Hᵉ gᵉ)
      ( is-natural-isomorphism-map-natural-isomorphism-map-Precategoryᵉ
          Cᵉ Dᵉ Fᵉ Gᵉ fᵉ)

  comp-natural-isomorphism-map-Precategoryᵉ :
    natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Hᵉ
  pr1ᵉ comp-natural-isomorphism-map-Precategoryᵉ =
    hom-comp-natural-isomorphism-map-Precategoryᵉ
  pr2ᵉ comp-natural-isomorphism-map-Precategoryᵉ =
    is-natural-isomorphism-map-comp-natural-isomorphism-map-Precategoryᵉ

  natural-transformation-map-inv-comp-natural-isomorphism-map-Precategoryᵉ :
    natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Hᵉ Fᵉ
  natural-transformation-map-inv-comp-natural-isomorphism-map-Precategoryᵉ =
    natural-transformation-map-inv-natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Hᵉ
      ( comp-natural-isomorphism-map-Precategoryᵉ)

  is-section-inv-comp-natural-isomorphism-map-Precategoryᵉ :
    ( comp-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Hᵉ Fᵉ Hᵉ
      ( hom-comp-natural-isomorphism-map-Precategoryᵉ)
      ( natural-transformation-map-inv-comp-natural-isomorphism-map-Precategoryᵉ)) ＝ᵉ
    ( id-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Hᵉ)
  is-section-inv-comp-natural-isomorphism-map-Precategoryᵉ =
    is-section-natural-transformation-map-inv-natural-isomorphism-map-Precategoryᵉ
      Cᵉ Dᵉ Fᵉ Hᵉ comp-natural-isomorphism-map-Precategoryᵉ

  is-retraction-inv-comp-natural-isomorphism-map-Precategoryᵉ :
    ( comp-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Hᵉ Fᵉ
      ( natural-transformation-map-inv-comp-natural-isomorphism-map-Precategoryᵉ)
      ( hom-comp-natural-isomorphism-map-Precategoryᵉ)) ＝ᵉ
    ( id-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ)
  is-retraction-inv-comp-natural-isomorphism-map-Precategoryᵉ =
    is-retraction-natural-transformation-map-inv-natural-isomorphism-map-Precategoryᵉ
      Cᵉ Dᵉ Fᵉ Hᵉ comp-natural-isomorphism-map-Precategoryᵉ
```

### Groupoid laws of natural isomorphisms in precategories

#### Composition of natural isomorphisms satisfies the unit laws

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ Gᵉ : map-Precategoryᵉ Cᵉ Dᵉ)
  (fᵉ : natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ)
  where

  left-unit-law-comp-natural-isomorphism-map-Precategoryᵉ :
    comp-natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ Gᵉ
      ( id-natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ Gᵉ)
      ( fᵉ) ＝ᵉ
    fᵉ
  left-unit-law-comp-natural-isomorphism-map-Precategoryᵉ =
    eq-eq-natural-transformation-map-natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ
      ( comp-natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ Gᵉ
        ( id-natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ Gᵉ) fᵉ)
      ( fᵉ)
      ( left-unit-law-comp-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ
        ( natural-transformation-map-natural-isomorphism-map-Precategoryᵉ
            Cᵉ Dᵉ Fᵉ Gᵉ fᵉ))

  right-unit-law-comp-natural-isomorphism-map-Precategoryᵉ :
    comp-natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Fᵉ Gᵉ fᵉ
      ( id-natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ) ＝ᵉ
    fᵉ
  right-unit-law-comp-natural-isomorphism-map-Precategoryᵉ =
    eq-eq-natural-transformation-map-natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ
      ( comp-natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Fᵉ Gᵉ fᵉ
        ( id-natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ))
      ( fᵉ)
      ( right-unit-law-comp-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ
        ( natural-transformation-map-natural-isomorphism-map-Precategoryᵉ
            Cᵉ Dᵉ Fᵉ Gᵉ fᵉ))
```

#### Composition of natural isomorphisms is associative

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ Gᵉ Hᵉ Iᵉ : map-Precategoryᵉ Cᵉ Dᵉ)
  (fᵉ : natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ)
  (gᵉ : natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ Gᵉ Hᵉ)
  (hᵉ : natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ Hᵉ Iᵉ)
  where

  associative-comp-natural-isomorphism-map-Precategoryᵉ :
    ( comp-natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ Iᵉ
      ( comp-natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ Gᵉ Hᵉ Iᵉ hᵉ gᵉ)
      ( fᵉ)) ＝ᵉ
    ( comp-natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Hᵉ Iᵉ hᵉ
      ( comp-natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ Hᵉ gᵉ fᵉ))
  associative-comp-natural-isomorphism-map-Precategoryᵉ =
    eq-eq-natural-transformation-map-natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Iᵉ
      ( comp-natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ Iᵉ
        ( comp-natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ Gᵉ Hᵉ Iᵉ hᵉ gᵉ)
        ( fᵉ))
      ( comp-natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Hᵉ Iᵉ hᵉ
        ( comp-natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ Hᵉ gᵉ fᵉ))
      ( associative-comp-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ Hᵉ Iᵉ
        ( natural-transformation-map-natural-isomorphism-map-Precategoryᵉ
            Cᵉ Dᵉ Fᵉ Gᵉ fᵉ)
        ( natural-transformation-map-natural-isomorphism-map-Precategoryᵉ
            Cᵉ Dᵉ Gᵉ Hᵉ gᵉ)
        ( natural-transformation-map-natural-isomorphism-map-Precategoryᵉ
            Cᵉ Dᵉ Hᵉ Iᵉ hᵉ))
```

#### Composition of natural isomorphisms satisfies inverse laws

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ Gᵉ : map-Precategoryᵉ Cᵉ Dᵉ)
  (fᵉ : natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ)
  where

  left-inverse-law-comp-natural-isomorphism-map-Precategoryᵉ :
    ( comp-natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ Fᵉ
      ( inv-natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ fᵉ)
      ( fᵉ)) ＝ᵉ
    ( id-natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ)
  left-inverse-law-comp-natural-isomorphism-map-Precategoryᵉ =
    eq-eq-natural-transformation-map-natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Fᵉ
      ( comp-natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ Fᵉ
        ( inv-natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ fᵉ) fᵉ)
      ( id-natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ)
      ( is-retraction-natural-transformation-map-inv-natural-isomorphism-map-Precategoryᵉ
          Cᵉ Dᵉ Fᵉ Gᵉ fᵉ)

  right-inverse-law-comp-natural-isomorphism-map-Precategoryᵉ :
    ( comp-natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ Gᵉ Fᵉ Gᵉ
      ( fᵉ)
      ( inv-natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ fᵉ)) ＝ᵉ
    ( id-natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ Gᵉ)
  right-inverse-law-comp-natural-isomorphism-map-Precategoryᵉ =
    eq-eq-natural-transformation-map-natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ Gᵉ Gᵉ
      ( comp-natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ Gᵉ Fᵉ Gᵉ
        ( fᵉ)
        ( inv-natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ fᵉ))
      ( id-natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ Gᵉ)
      ( is-section-natural-transformation-map-inv-natural-isomorphism-map-Precategoryᵉ
          Cᵉ Dᵉ Fᵉ Gᵉ fᵉ)
```

### When the type of natural transformations is a proposition, the type of natural isomorphisms is a proposition

Theᵉ typeᵉ ofᵉ naturalᵉ isomorphismsᵉ betweenᵉ mapsᵉ `F`ᵉ andᵉ `G`ᵉ isᵉ aᵉ subtypeᵉ ofᵉ
`natural-transformationᵉ Fᵉ G`,ᵉ soᵉ whenᵉ thisᵉ typeᵉ isᵉ aᵉ proposition,ᵉ thenᵉ theᵉ typeᵉ
ofᵉ naturalᵉ isomorphismsᵉ fromᵉ `F`ᵉ to `G`ᵉ formᵉ aᵉ proposition.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ Gᵉ : map-Precategoryᵉ Cᵉ Dᵉ)
  where

  is-prop-natural-isomorphism-map-Precategoryᵉ :
    is-propᵉ (natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ) →
    is-propᵉ (natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ)
  is-prop-natural-isomorphism-map-Precategoryᵉ =
    is-prop-type-subtypeᵉ
      ( is-natural-isomorphism-map-prop-hom-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ)

  natural-isomorphism-map-prop-Precategoryᵉ :
    is-propᵉ (natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ) →
    Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l4ᵉ)
  pr1ᵉ (natural-isomorphism-map-prop-Precategoryᵉ _) =
    natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ
  pr2ᵉ (natural-isomorphism-map-prop-Precategoryᵉ is-prop-hom-C-F-Gᵉ) =
    is-prop-natural-isomorphism-map-Precategoryᵉ is-prop-hom-C-F-Gᵉ
```

### Functoriality of `natural-isomorphism-map-eq`

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ Gᵉ Hᵉ : map-Precategoryᵉ Cᵉ Dᵉ)
  where

  preserves-concat-natural-isomorphism-map-eq-Precategoryᵉ :
    (pᵉ : Fᵉ ＝ᵉ Gᵉ) (qᵉ : Gᵉ ＝ᵉ Hᵉ) →
    natural-isomorphism-map-eq-Precategoryᵉ Cᵉ Dᵉ Fᵉ Hᵉ (pᵉ ∙ᵉ qᵉ) ＝ᵉ
    comp-natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ Hᵉ
      ( natural-isomorphism-map-eq-Precategoryᵉ Cᵉ Dᵉ Gᵉ Hᵉ qᵉ)
      ( natural-isomorphism-map-eq-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ pᵉ)
  preserves-concat-natural-isomorphism-map-eq-Precategoryᵉ reflᵉ qᵉ =
    invᵉ
      ( right-unit-law-comp-natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Hᵉ
        ( natural-isomorphism-map-eq-Precategoryᵉ Cᵉ Dᵉ Gᵉ Hᵉ qᵉ))
```