# The category of maps and natural transformations between two categories

```agda
module category-theory.category-of-maps-categoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categoriesᵉ
open import category-theory.commuting-squares-of-morphisms-in-precategoriesᵉ
open import category-theory.isomorphisms-in-categoriesᵉ
open import category-theory.isomorphisms-in-precategoriesᵉ
open import category-theory.maps-categoriesᵉ
open import category-theory.maps-precategoriesᵉ
open import category-theory.natural-isomorphisms-maps-categoriesᵉ
open import category-theory.natural-isomorphisms-maps-precategoriesᵉ
open import category-theory.natural-transformations-maps-precategoriesᵉ
open import category-theory.precategoriesᵉ
open import category-theory.precategory-of-maps-precategoriesᵉ

open import foundation.action-on-identifications-binary-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-dependent-function-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.type-theoretic-principle-of-choiceᵉ
open import foundation.univalenceᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

[Maps](category-theory.maps-categories.mdᵉ) betweenᵉ
[categories](category-theory.categories.mdᵉ) andᵉ
[naturalᵉ transformations](category-theory.natural-transformations-maps-categories.mdᵉ)
betweenᵉ themᵉ formᵉ anotherᵉ categoryᵉ whoseᵉ identityᵉ mapᵉ andᵉ compositionᵉ structureᵉ
areᵉ inheritedᵉ pointwiseᵉ fromᵉ theᵉ codomainᵉ category.ᵉ Thisᵉ isᵉ calledᵉ theᵉ
**categoryᵉ ofᵉ mapsᵉ betweenᵉ categories**.ᵉ

## Lemmas

### Extensionality of maps of precategories when the codomain is a category

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  (is-category-Dᵉ : is-category-Precategoryᵉ Dᵉ)
  where

  equiv-natural-isomorphism-htpy-map-is-category-Precategoryᵉ :
    (Fᵉ Gᵉ : map-Precategoryᵉ Cᵉ Dᵉ) →
    ( htpy-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ) ≃ᵉ
    ( natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ)
  equiv-natural-isomorphism-htpy-map-is-category-Precategoryᵉ Fᵉ Gᵉ =
      ( equiv-right-swap-Σᵉ) ∘eᵉ
      ( equiv-Σ-equiv-baseᵉ
        ( is-natural-transformation-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ ∘ᵉ pr1ᵉ)
        ( ( distributive-Π-Σᵉ) ∘eᵉ
          ( equiv-Π-equiv-familyᵉ
            ( λ xᵉ →
              extensionality-obj-Categoryᵉ
                ( Dᵉ ,ᵉ is-category-Dᵉ)
                ( obj-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ xᵉ)
                ( obj-map-Precategoryᵉ Cᵉ Dᵉ Gᵉ xᵉ)))))

  extensionality-map-is-category-Precategoryᵉ :
    (Fᵉ Gᵉ : map-Precategoryᵉ Cᵉ Dᵉ) →
    ( Fᵉ ＝ᵉ Gᵉ) ≃ᵉ
    ( natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ)
  extensionality-map-is-category-Precategoryᵉ Fᵉ Gᵉ =
    ( equiv-natural-isomorphism-htpy-map-is-category-Precategoryᵉ Fᵉ Gᵉ) ∘eᵉ
    ( equiv-htpy-eq-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ)
```

### When the codomain is a category the map precategory is a category

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  (is-category-Dᵉ : is-category-Precategoryᵉ Dᵉ)
  where

  abstract
    is-category-map-precategory-is-category-Precategoryᵉ :
      is-category-Precategoryᵉ (map-precategory-Precategoryᵉ Cᵉ Dᵉ)
    is-category-map-precategory-is-category-Precategoryᵉ Fᵉ Gᵉ =
      is-equiv-htpy-equivᵉ
        ( ( equiv-iso-map-natural-isomorphism-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ) ∘eᵉ
          ( extensionality-map-is-category-Precategoryᵉ Cᵉ Dᵉ is-category-Dᵉ Fᵉ Gᵉ))
        ( λ where
          reflᵉ →
            compute-iso-map-natural-isomorphism-map-eq-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ reflᵉ)
```

## Definitions

### The category of maps and natural transformations between categories

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ) (Dᵉ : Categoryᵉ l3ᵉ l4ᵉ)
  where

  map-category-Categoryᵉ :
    Categoryᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ) (l1ᵉ ⊔ l2ᵉ ⊔ l4ᵉ)
  pr1ᵉ map-category-Categoryᵉ =
    map-precategory-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( precategory-Categoryᵉ Dᵉ)
  pr2ᵉ map-category-Categoryᵉ =
    is-category-map-precategory-is-category-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( precategory-Categoryᵉ Dᵉ)
      ( is-category-Categoryᵉ Dᵉ)

  extensionality-map-Categoryᵉ :
    (Fᵉ Gᵉ : map-Categoryᵉ Cᵉ Dᵉ) →
    (Fᵉ ＝ᵉ Gᵉ) ≃ᵉ natural-isomorphism-map-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ
  extensionality-map-Categoryᵉ Fᵉ Gᵉ =
    ( equiv-natural-isomorphism-map-iso-map-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( precategory-Categoryᵉ Dᵉ) Fᵉ Gᵉ) ∘eᵉ
    ( extensionality-obj-Categoryᵉ map-category-Categoryᵉ Fᵉ Gᵉ)

  eq-natural-isomorphism-map-Categoryᵉ :
    (Fᵉ Gᵉ : map-Categoryᵉ Cᵉ Dᵉ) →
    natural-isomorphism-map-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ → Fᵉ ＝ᵉ Gᵉ
  eq-natural-isomorphism-map-Categoryᵉ Fᵉ Gᵉ =
    map-inv-equivᵉ (extensionality-map-Categoryᵉ Fᵉ Gᵉ)
```