# The category of functors and natural transformations between two categories

```agda
module category-theory.category-of-functorsᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categoriesᵉ
open import category-theory.category-of-maps-categoriesᵉ
open import category-theory.functors-categoriesᵉ
open import category-theory.functors-precategoriesᵉ
open import category-theory.isomorphisms-in-categoriesᵉ
open import category-theory.natural-isomorphisms-functors-categoriesᵉ
open import category-theory.natural-isomorphisms-functors-precategoriesᵉ
open import category-theory.precategoriesᵉ
open import category-theory.precategory-of-functorsᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

[Functors](category-theory.functors-categories.mdᵉ) betweenᵉ
[categories](category-theory.categories.mdᵉ) andᵉ
[naturalᵉ transformations](category-theory.natural-transformations-functors-categories.mdᵉ)
betweenᵉ themᵉ assembleᵉ to aᵉ newᵉ categoryᵉ whoseᵉ identityᵉ functorᵉ andᵉ compositionᵉ
structureᵉ areᵉ inheritedᵉ pointwiseᵉ fromᵉ theᵉ codomainᵉ category.ᵉ Thisᵉ isᵉ calledᵉ theᵉ
**categoryᵉ ofᵉ functors**.ᵉ

## Definitons

### Extensionality of functors of precategories when the codomain is a category

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  (is-category-Dᵉ : is-category-Precategoryᵉ Dᵉ)
  where

  equiv-natural-isomorphism-htpy-functor-is-category-Precategoryᵉ :
    (Fᵉ Gᵉ : functor-Precategoryᵉ Cᵉ Dᵉ) →
    htpy-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ ≃ᵉ natural-isomorphism-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ
  equiv-natural-isomorphism-htpy-functor-is-category-Precategoryᵉ Fᵉ Gᵉ =
    equiv-natural-isomorphism-htpy-map-is-category-Precategoryᵉ Cᵉ Dᵉ
      ( is-category-Dᵉ)
      ( map-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ)
      ( map-functor-Precategoryᵉ Cᵉ Dᵉ Gᵉ)

  extensionality-functor-is-category-Precategoryᵉ :
    (Fᵉ Gᵉ : functor-Precategoryᵉ Cᵉ Dᵉ) →
    ( Fᵉ ＝ᵉ Gᵉ) ≃ᵉ
    ( natural-isomorphism-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ)
  extensionality-functor-is-category-Precategoryᵉ Fᵉ Gᵉ =
    ( equiv-natural-isomorphism-htpy-functor-is-category-Precategoryᵉ Fᵉ Gᵉ) ∘eᵉ
    ( equiv-htpy-eq-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ)
```

### When the codomain is a category the functor precategory is a category

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  (is-category-Dᵉ : is-category-Precategoryᵉ Dᵉ)
  where

  abstract
    is-category-functor-precategory-is-category-Precategoryᵉ :
      is-category-Precategoryᵉ (functor-precategory-Precategoryᵉ Cᵉ Dᵉ)
    is-category-functor-precategory-is-category-Precategoryᵉ Fᵉ Gᵉ =
      is-equiv-htpy-equivᵉ
        ( ( equiv-iso-functor-natural-isomorphism-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ) ∘eᵉ
          ( extensionality-functor-is-category-Precategoryᵉ
              Cᵉ Dᵉ is-category-Dᵉ Fᵉ Gᵉ))
        ( λ where
          reflᵉ →
            compute-iso-functor-natural-isomorphism-eq-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ reflᵉ)
```

## Definitions

### The category of functors and natural transformations between categories

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ) (Dᵉ : Categoryᵉ l3ᵉ l4ᵉ)
  where

  functor-category-Categoryᵉ :
    Categoryᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ) (l1ᵉ ⊔ l2ᵉ ⊔ l4ᵉ)
  pr1ᵉ functor-category-Categoryᵉ =
    functor-precategory-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( precategory-Categoryᵉ Dᵉ)
  pr2ᵉ functor-category-Categoryᵉ =
    is-category-functor-precategory-is-category-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( precategory-Categoryᵉ Dᵉ)
      ( is-category-Categoryᵉ Dᵉ)

  extensionality-functor-Categoryᵉ :
    (Fᵉ Gᵉ : functor-Categoryᵉ Cᵉ Dᵉ) →
    (Fᵉ ＝ᵉ Gᵉ) ≃ᵉ natural-isomorphism-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ
  extensionality-functor-Categoryᵉ Fᵉ Gᵉ =
    ( equiv-natural-isomorphism-iso-functor-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( precategory-Categoryᵉ Dᵉ) Fᵉ Gᵉ) ∘eᵉ
    ( extensionality-obj-Categoryᵉ functor-category-Categoryᵉ Fᵉ Gᵉ)

  eq-natural-isomorphism-functor-Categoryᵉ :
    (Fᵉ Gᵉ : functor-Categoryᵉ Cᵉ Dᵉ) →
    natural-isomorphism-Categoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ → Fᵉ ＝ᵉ Gᵉ
  eq-natural-isomorphism-functor-Categoryᵉ Fᵉ Gᵉ =
    map-inv-equivᵉ (extensionality-functor-Categoryᵉ Fᵉ Gᵉ)
```