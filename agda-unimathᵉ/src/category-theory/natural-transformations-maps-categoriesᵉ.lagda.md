# Natural transformations between maps between categories

```agda
module category-theory.natural-transformations-maps-categoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categoriesᵉ
open import category-theory.maps-categoriesᵉ
open import category-theory.natural-transformations-maps-precategoriesᵉ

open import foundation.embeddingsᵉ
open import foundation.equivalencesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Aᵉ **naturalᵉ transformation**ᵉ betweenᵉ
[mapsᵉ betweenᵉ categories](category-theory.maps-categories.mdᵉ) isᵉ aᵉ
[naturalᵉ transformation](category-theory.natural-transformations-maps-precategories.mdᵉ)
betweenᵉ theᵉ [maps](category-theory.maps-precategories.mdᵉ) onᵉ theᵉ underlyingᵉ
[precategories](category-theory.precategories.md).ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Categoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ Gᵉ : map-Categoryᵉ Cᵉ Dᵉ)
  where

  hom-family-map-Categoryᵉ : UUᵉ (l1ᵉ ⊔ l4ᵉ)
  hom-family-map-Categoryᵉ =
    hom-family-map-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( precategory-Categoryᵉ Dᵉ)
      ( Fᵉ)
      ( Gᵉ)

  is-natural-transformation-map-Categoryᵉ :
    hom-family-map-Categoryᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l4ᵉ)
  is-natural-transformation-map-Categoryᵉ =
    is-natural-transformation-map-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( precategory-Categoryᵉ Dᵉ)
      ( Fᵉ)
      ( Gᵉ)

  natural-transformation-map-Categoryᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l4ᵉ)
  natural-transformation-map-Categoryᵉ =
    natural-transformation-map-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( precategory-Categoryᵉ Dᵉ)
      ( Fᵉ)
      ( Gᵉ)

  hom-family-natural-transformation-map-Categoryᵉ :
    natural-transformation-map-Categoryᵉ → hom-family-map-Categoryᵉ
  hom-family-natural-transformation-map-Categoryᵉ =
    hom-family-natural-transformation-map-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( precategory-Categoryᵉ Dᵉ)
      ( Fᵉ)
      ( Gᵉ)

  naturality-natural-transformation-map-Categoryᵉ :
    (γᵉ : natural-transformation-map-Categoryᵉ) →
    is-natural-transformation-map-Categoryᵉ
      ( hom-family-natural-transformation-map-Categoryᵉ γᵉ)
  naturality-natural-transformation-map-Categoryᵉ =
    naturality-natural-transformation-map-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( precategory-Categoryᵉ Dᵉ)
      ( Fᵉ)
      ( Gᵉ)
```

## Composition and identity of natural transformations

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ) (Dᵉ : Categoryᵉ l3ᵉ l4ᵉ)
  where

  id-natural-transformation-map-Categoryᵉ :
    (Fᵉ : map-Categoryᵉ Cᵉ Dᵉ) → natural-transformation-map-Categoryᵉ Cᵉ Dᵉ Fᵉ Fᵉ
  id-natural-transformation-map-Categoryᵉ =
    id-natural-transformation-map-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( precategory-Categoryᵉ Dᵉ)

  comp-natural-transformation-map-Categoryᵉ :
    (Fᵉ Gᵉ Hᵉ : map-Categoryᵉ Cᵉ Dᵉ) →
    natural-transformation-map-Categoryᵉ Cᵉ Dᵉ Gᵉ Hᵉ →
    natural-transformation-map-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ →
    natural-transformation-map-Categoryᵉ Cᵉ Dᵉ Fᵉ Hᵉ
  comp-natural-transformation-map-Categoryᵉ =
    comp-natural-transformation-map-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( precategory-Categoryᵉ Dᵉ)
```

## Properties

### That a family of morphisms is a natural transformation is a proposition

Thisᵉ followsᵉ fromᵉ theᵉ factᵉ thatᵉ theᵉ hom-typesᵉ areᵉ
[sets](foundation-core.sets.md).ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Categoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ Gᵉ : map-Categoryᵉ Cᵉ Dᵉ)
  where

  is-prop-is-natural-transformation-map-Categoryᵉ :
    ( γᵉ : hom-family-map-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ) →
    is-propᵉ (is-natural-transformation-map-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ γᵉ)
  is-prop-is-natural-transformation-map-Categoryᵉ =
    is-prop-is-natural-transformation-map-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( precategory-Categoryᵉ Dᵉ)
      ( Fᵉ)
      ( Gᵉ)

  is-natural-transformation-prop-map-Categoryᵉ :
    ( γᵉ : hom-family-map-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ) → Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l4ᵉ)
  is-natural-transformation-prop-map-Categoryᵉ =
    is-natural-transformation-prop-map-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( precategory-Categoryᵉ Dᵉ)
      ( Fᵉ)
      ( Gᵉ)
```

### The set of natural transformations

```agda
  is-emb-hom-family-natural-transformation-map-Categoryᵉ :
    is-embᵉ (hom-family-natural-transformation-map-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ)
  is-emb-hom-family-natural-transformation-map-Categoryᵉ =
    is-emb-hom-family-natural-transformation-map-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( precategory-Categoryᵉ Dᵉ)
      ( Fᵉ)
      ( Gᵉ)

  is-set-natural-transformation-map-Categoryᵉ :
    is-setᵉ (natural-transformation-map-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ)
  is-set-natural-transformation-map-Categoryᵉ =
    is-set-natural-transformation-map-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( precategory-Categoryᵉ Dᵉ)
      ( Fᵉ)
      ( Gᵉ)

  natural-transformation-map-set-Categoryᵉ : Setᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l4ᵉ)
  natural-transformation-map-set-Categoryᵉ =
    natural-transformation-map-set-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( precategory-Categoryᵉ Dᵉ)
      ( Fᵉ)
      ( Gᵉ)

  extensionality-natural-transformation-map-Categoryᵉ :
    (αᵉ βᵉ : natural-transformation-map-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ) →
    ( αᵉ ＝ᵉ βᵉ) ≃ᵉ
    ( hom-family-natural-transformation-map-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ αᵉ ~ᵉ
      hom-family-natural-transformation-map-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ βᵉ)
  extensionality-natural-transformation-map-Categoryᵉ =
    extensionality-natural-transformation-map-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( precategory-Categoryᵉ Dᵉ)
      ( Fᵉ)
      ( Gᵉ)

  eq-htpy-hom-family-natural-transformation-map-Categoryᵉ :
    (αᵉ βᵉ : natural-transformation-map-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ) →
    ( hom-family-natural-transformation-map-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ αᵉ ~ᵉ
      hom-family-natural-transformation-map-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ βᵉ) →
    αᵉ ＝ᵉ βᵉ
  eq-htpy-hom-family-natural-transformation-map-Categoryᵉ =
    eq-htpy-hom-family-natural-transformation-map-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( precategory-Categoryᵉ Dᵉ)
      ( Fᵉ)
      ( Gᵉ)
```

### Categorical laws for natural transformations

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ) (Dᵉ : Categoryᵉ l3ᵉ l4ᵉ)
  where

  right-unit-law-comp-natural-transformation-map-Categoryᵉ :
    {Fᵉ Gᵉ : map-Categoryᵉ Cᵉ Dᵉ}
    (αᵉ : natural-transformation-map-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ) →
    comp-natural-transformation-map-Categoryᵉ Cᵉ Dᵉ Fᵉ Fᵉ Gᵉ αᵉ
      ( id-natural-transformation-map-Categoryᵉ Cᵉ Dᵉ Fᵉ) ＝ᵉ αᵉ
  right-unit-law-comp-natural-transformation-map-Categoryᵉ {Fᵉ} {Gᵉ} =
    right-unit-law-comp-natural-transformation-map-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( precategory-Categoryᵉ Dᵉ)
      Fᵉ Gᵉ

  left-unit-law-comp-natural-transformation-map-Categoryᵉ :
    {Fᵉ Gᵉ : map-Categoryᵉ Cᵉ Dᵉ}
    (αᵉ : natural-transformation-map-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ) →
    comp-natural-transformation-map-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ Gᵉ
      ( id-natural-transformation-map-Categoryᵉ Cᵉ Dᵉ Gᵉ) αᵉ ＝ᵉ αᵉ
  left-unit-law-comp-natural-transformation-map-Categoryᵉ {Fᵉ} {Gᵉ} =
    left-unit-law-comp-natural-transformation-map-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( precategory-Categoryᵉ Dᵉ)
      Fᵉ Gᵉ

  associative-comp-natural-transformation-map-Categoryᵉ :
    (Fᵉ Gᵉ Hᵉ Iᵉ : map-Categoryᵉ Cᵉ Dᵉ)
    (αᵉ : natural-transformation-map-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ)
    (βᵉ : natural-transformation-map-Categoryᵉ Cᵉ Dᵉ Gᵉ Hᵉ)
    (γᵉ : natural-transformation-map-Categoryᵉ Cᵉ Dᵉ Hᵉ Iᵉ) →
    comp-natural-transformation-map-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ Iᵉ
      ( comp-natural-transformation-map-Categoryᵉ Cᵉ Dᵉ Gᵉ Hᵉ Iᵉ γᵉ βᵉ) αᵉ ＝ᵉ
    comp-natural-transformation-map-Categoryᵉ Cᵉ Dᵉ Fᵉ Hᵉ Iᵉ γᵉ
      ( comp-natural-transformation-map-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ Hᵉ βᵉ αᵉ)
  associative-comp-natural-transformation-map-Categoryᵉ =
    associative-comp-natural-transformation-map-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( precategory-Categoryᵉ Dᵉ)
```