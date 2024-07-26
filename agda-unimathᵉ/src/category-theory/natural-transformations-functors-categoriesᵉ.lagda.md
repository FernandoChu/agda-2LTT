# Natural transformations between functors between categories

```agda
module category-theory.natural-transformations-functors-categoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categoriesᵉ
open import category-theory.functors-categoriesᵉ
open import category-theory.natural-transformations-functors-precategoriesᵉ

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
[functorsᵉ betweenᵉ categories](category-theory.functors-categories.mdᵉ) isᵉ aᵉ
[naturalᵉ transformation](category-theory.natural-transformations-functors-precategories.mdᵉ)
betweenᵉ theᵉ [functors](category-theory.functors-precategories.mdᵉ) onᵉ theᵉ
underlyingᵉ [precategories](category-theory.precategories.md).ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Categoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ Gᵉ : functor-Categoryᵉ Cᵉ Dᵉ)
  where

  hom-family-functor-Categoryᵉ : UUᵉ (l1ᵉ ⊔ l4ᵉ)
  hom-family-functor-Categoryᵉ =
    hom-family-functor-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( precategory-Categoryᵉ Dᵉ)
      ( Fᵉ)
      ( Gᵉ)

  is-natural-transformation-Categoryᵉ :
    hom-family-functor-Categoryᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l4ᵉ)
  is-natural-transformation-Categoryᵉ =
    is-natural-transformation-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( precategory-Categoryᵉ Dᵉ)
      ( Fᵉ)
      ( Gᵉ)

  natural-transformation-Categoryᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l4ᵉ)
  natural-transformation-Categoryᵉ =
    natural-transformation-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( precategory-Categoryᵉ Dᵉ)
      ( Fᵉ)
      ( Gᵉ)

  hom-family-natural-transformation-Categoryᵉ :
    natural-transformation-Categoryᵉ → hom-family-functor-Categoryᵉ
  hom-family-natural-transformation-Categoryᵉ =
    hom-family-natural-transformation-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( precategory-Categoryᵉ Dᵉ)
      ( Fᵉ)
      ( Gᵉ)

  naturality-natural-transformation-Categoryᵉ :
    (γᵉ : natural-transformation-Categoryᵉ) →
    is-natural-transformation-Categoryᵉ
      ( hom-family-natural-transformation-Categoryᵉ γᵉ)
  naturality-natural-transformation-Categoryᵉ =
    naturality-natural-transformation-Precategoryᵉ
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

  id-natural-transformation-Categoryᵉ :
    (Fᵉ : functor-Categoryᵉ Cᵉ Dᵉ) → natural-transformation-Categoryᵉ Cᵉ Dᵉ Fᵉ Fᵉ
  id-natural-transformation-Categoryᵉ =
    id-natural-transformation-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( precategory-Categoryᵉ Dᵉ)

  comp-natural-transformation-Categoryᵉ :
    (Fᵉ Gᵉ Hᵉ : functor-Categoryᵉ Cᵉ Dᵉ) →
    natural-transformation-Categoryᵉ Cᵉ Dᵉ Gᵉ Hᵉ →
    natural-transformation-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ →
    natural-transformation-Categoryᵉ Cᵉ Dᵉ Fᵉ Hᵉ
  comp-natural-transformation-Categoryᵉ =
    comp-natural-transformation-Precategoryᵉ
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
  (Fᵉ Gᵉ : functor-Categoryᵉ Cᵉ Dᵉ)
  where

  is-prop-is-natural-transformation-Categoryᵉ :
    ( γᵉ : hom-family-functor-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ) →
    is-propᵉ (is-natural-transformation-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ γᵉ)
  is-prop-is-natural-transformation-Categoryᵉ =
    is-prop-is-natural-transformation-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( precategory-Categoryᵉ Dᵉ)
      ( Fᵉ)
      ( Gᵉ)

  is-natural-transformation-prop-Categoryᵉ :
    ( γᵉ : hom-family-functor-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ) → Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l4ᵉ)
  is-natural-transformation-prop-Categoryᵉ =
    is-natural-transformation-prop-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( precategory-Categoryᵉ Dᵉ)
      ( Fᵉ)
      ( Gᵉ)
```

### The set of natural transformations

```agda
  is-emb-hom-family-natural-transformation-Categoryᵉ :
    is-embᵉ (hom-family-natural-transformation-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ)
  is-emb-hom-family-natural-transformation-Categoryᵉ =
    is-emb-hom-family-natural-transformation-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( precategory-Categoryᵉ Dᵉ)
      ( Fᵉ)
      ( Gᵉ)

  is-set-natural-transformation-Categoryᵉ :
    is-setᵉ (natural-transformation-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ)
  is-set-natural-transformation-Categoryᵉ =
    is-set-natural-transformation-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( precategory-Categoryᵉ Dᵉ)
      ( Fᵉ)
      ( Gᵉ)

  natural-transformation-set-Categoryᵉ : Setᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l4ᵉ)
  natural-transformation-set-Categoryᵉ =
    natural-transformation-set-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( precategory-Categoryᵉ Dᵉ)
      ( Fᵉ)
      ( Gᵉ)

  extensionality-natural-transformation-Categoryᵉ :
    (αᵉ βᵉ : natural-transformation-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ) →
    ( αᵉ ＝ᵉ βᵉ) ≃ᵉ
    ( hom-family-natural-transformation-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ αᵉ ~ᵉ
      hom-family-natural-transformation-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ βᵉ)
  extensionality-natural-transformation-Categoryᵉ =
    extensionality-natural-transformation-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( precategory-Categoryᵉ Dᵉ)
      ( Fᵉ)
      ( Gᵉ)

  eq-htpy-hom-family-natural-transformation-Categoryᵉ :
    (αᵉ βᵉ : natural-transformation-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ) →
    ( hom-family-natural-transformation-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ αᵉ ~ᵉ
      hom-family-natural-transformation-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ βᵉ) →
    αᵉ ＝ᵉ βᵉ
  eq-htpy-hom-family-natural-transformation-Categoryᵉ =
    eq-htpy-hom-family-natural-transformation-Precategoryᵉ
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

  right-unit-law-comp-natural-transformation-Categoryᵉ :
    {Fᵉ Gᵉ : functor-Categoryᵉ Cᵉ Dᵉ}
    (αᵉ : natural-transformation-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ) →
    comp-natural-transformation-Categoryᵉ Cᵉ Dᵉ Fᵉ Fᵉ Gᵉ αᵉ
      ( id-natural-transformation-Categoryᵉ Cᵉ Dᵉ Fᵉ) ＝ᵉ αᵉ
  right-unit-law-comp-natural-transformation-Categoryᵉ {Fᵉ} {Gᵉ} =
    right-unit-law-comp-natural-transformation-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( precategory-Categoryᵉ Dᵉ)
      Fᵉ Gᵉ

  left-unit-law-comp-natural-transformation-Categoryᵉ :
    {Fᵉ Gᵉ : functor-Categoryᵉ Cᵉ Dᵉ}
    (αᵉ : natural-transformation-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ) →
    comp-natural-transformation-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ Gᵉ
      ( id-natural-transformation-Categoryᵉ Cᵉ Dᵉ Gᵉ) αᵉ ＝ᵉ αᵉ
  left-unit-law-comp-natural-transformation-Categoryᵉ {Fᵉ} {Gᵉ} =
    left-unit-law-comp-natural-transformation-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( precategory-Categoryᵉ Dᵉ)
      Fᵉ Gᵉ

  associative-comp-natural-transformation-Categoryᵉ :
    (Fᵉ Gᵉ Hᵉ Iᵉ : functor-Categoryᵉ Cᵉ Dᵉ)
    (αᵉ : natural-transformation-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ)
    (βᵉ : natural-transformation-Categoryᵉ Cᵉ Dᵉ Gᵉ Hᵉ)
    (γᵉ : natural-transformation-Categoryᵉ Cᵉ Dᵉ Hᵉ Iᵉ) →
    comp-natural-transformation-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ Iᵉ
      ( comp-natural-transformation-Categoryᵉ Cᵉ Dᵉ Gᵉ Hᵉ Iᵉ γᵉ βᵉ) αᵉ ＝ᵉ
    comp-natural-transformation-Categoryᵉ Cᵉ Dᵉ Fᵉ Hᵉ Iᵉ γᵉ
      ( comp-natural-transformation-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ Hᵉ βᵉ αᵉ)
  associative-comp-natural-transformation-Categoryᵉ =
    associative-comp-natural-transformation-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( precategory-Categoryᵉ Dᵉ)
```