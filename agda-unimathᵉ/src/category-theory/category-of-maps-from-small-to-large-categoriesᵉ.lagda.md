# The category of maps and natural transformations from small to large categories

```agda
module category-theory.category-of-maps-from-small-to-large-categoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categoriesᵉ
open import category-theory.category-of-maps-categoriesᵉ
open import category-theory.isomorphisms-in-large-precategoriesᵉ
open import category-theory.isomorphisms-in-precategoriesᵉ
open import category-theory.large-categoriesᵉ
open import category-theory.large-precategoriesᵉ
open import category-theory.maps-from-small-to-large-categoriesᵉ
open import category-theory.maps-from-small-to-large-precategoriesᵉ
open import category-theory.natural-isomorphisms-maps-categoriesᵉ
open import category-theory.natural-isomorphisms-maps-precategoriesᵉ
open import category-theory.precategoriesᵉ
open import category-theory.precategory-of-maps-from-small-to-large-precategoriesᵉ

open import foundation.equivalencesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

[Maps](category-theory.maps-from-small-to-large-categories.mdᵉ) fromᵉ smallᵉ
[categories](category-theory.categories.mdᵉ) to
[largeᵉ categories](category-theory.large-categories.mdᵉ) andᵉ
[naturalᵉ transformations](category-theory.natural-transformations-maps-from-small-to-large-precategories.mdᵉ)
betweenᵉ themᵉ formᵉ aᵉ largeᵉ categoryᵉ whoseᵉ identityᵉ mapᵉ andᵉ compositionᵉ structureᵉ
areᵉ inheritedᵉ pointwiseᵉ fromᵉ theᵉ codomainᵉ category.ᵉ Thisᵉ isᵉ calledᵉ theᵉ
**categoryᵉ ofᵉ mapsᵉ fromᵉ smallᵉ to largeᵉ categories**.ᵉ

## Lemmas

### Extensionality of maps from small precategories to large categories

```agda
module _
  {l1ᵉ l2ᵉ : Level} {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Large-Precategoryᵉ αᵉ βᵉ)
  (is-large-category-Dᵉ : is-large-category-Large-Precategoryᵉ Dᵉ)
  where

  equiv-natural-isomorphism-htpy-map-is-large-category-Small-Large-Precategoryᵉ :
    {γᵉ : Level}
    (Fᵉ Gᵉ : map-Small-Large-Precategoryᵉ Cᵉ Dᵉ γᵉ) →
    ( htpy-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ) ≃ᵉ
    ( natural-isomorphism-map-Precategoryᵉ Cᵉ (precategory-Large-Precategoryᵉ Dᵉ γᵉ)
      ( Fᵉ)
      ( Gᵉ))
  equiv-natural-isomorphism-htpy-map-is-large-category-Small-Large-Precategoryᵉ
    { γᵉ} Fᵉ Gᵉ =
    equiv-natural-isomorphism-htpy-map-is-category-Precategoryᵉ
      ( Cᵉ)
      ( precategory-Large-Precategoryᵉ Dᵉ γᵉ)
      ( is-category-is-large-category-Large-Precategoryᵉ Dᵉ is-large-category-Dᵉ γᵉ)
      ( Fᵉ)
      ( Gᵉ)

  extensionality-map-is-category-Small-Large-Precategoryᵉ :
    {γᵉ : Level}
    (Fᵉ Gᵉ : map-Small-Large-Precategoryᵉ Cᵉ Dᵉ γᵉ) →
    ( Fᵉ ＝ᵉ Gᵉ) ≃ᵉ
    ( natural-isomorphism-map-Precategoryᵉ Cᵉ (precategory-Large-Precategoryᵉ Dᵉ γᵉ)
      ( Fᵉ)
      ( Gᵉ))
  extensionality-map-is-category-Small-Large-Precategoryᵉ Fᵉ Gᵉ =
    ( equiv-natural-isomorphism-htpy-map-is-large-category-Small-Large-Precategoryᵉ
      ( Fᵉ)
      ( Gᵉ)) ∘eᵉ
    ( equiv-htpy-eq-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ Gᵉ)
```

### When the codomain is a large category the map large precategory is a large category

```agda
module _
  {l1ᵉ l2ᵉ : Level} {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Large-Precategoryᵉ αᵉ βᵉ)
  (is-large-category-Dᵉ : is-large-category-Large-Precategoryᵉ Dᵉ)
  where

  abstract
    is-large-category-map-large-precategory-is-large-category-Small-Large-Precategoryᵉ :
      is-large-category-Large-Precategoryᵉ
        ( map-large-precategory-Small-Large-Precategoryᵉ Cᵉ Dᵉ)
    is-large-category-map-large-precategory-is-large-category-Small-Large-Precategoryᵉ
      { γᵉ} Fᵉ Gᵉ =
      is-equiv-htpy'ᵉ
        ( iso-eq-Precategoryᵉ
          ( map-precategory-Small-Large-Precategoryᵉ Cᵉ Dᵉ γᵉ)
          ( Fᵉ)
          ( Gᵉ))
        ( compute-iso-eq-Large-Precategoryᵉ
          ( map-large-precategory-Small-Large-Precategoryᵉ Cᵉ Dᵉ)
          ( Fᵉ)
          ( Gᵉ))
        ( is-category-map-precategory-is-category-Precategoryᵉ
          ( Cᵉ)
          ( precategory-Large-Precategoryᵉ Dᵉ γᵉ)
          ( is-category-is-large-category-Large-Precategoryᵉ
            ( Dᵉ)
            ( is-large-category-Dᵉ)
            ( γᵉ))
          ( Fᵉ)
          ( Gᵉ))
```

## Definitions

### The large category of maps and natural transformations from small to large categories

```agda
module _
  {l1ᵉ l2ᵉ : Level} {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Large-Categoryᵉ αᵉ βᵉ)
  where

  map-large-category-Small-Large-Categoryᵉ :
    Large-Categoryᵉ (λ lᵉ → l1ᵉ ⊔ l2ᵉ ⊔ αᵉ lᵉ ⊔ βᵉ lᵉ lᵉ) (λ lᵉ l'ᵉ → l1ᵉ ⊔ l2ᵉ ⊔ βᵉ lᵉ l'ᵉ)
  large-precategory-Large-Categoryᵉ map-large-category-Small-Large-Categoryᵉ =
    map-large-precategory-Small-Large-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( large-precategory-Large-Categoryᵉ Dᵉ)
  is-large-category-Large-Categoryᵉ map-large-category-Small-Large-Categoryᵉ =
    is-large-category-map-large-precategory-is-large-category-Small-Large-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( large-precategory-Large-Categoryᵉ Dᵉ)
      ( is-large-category-Large-Categoryᵉ Dᵉ)

  extensionality-map-Small-Large-Categoryᵉ :
    {γᵉ : Level} (Fᵉ Gᵉ : map-Small-Large-Categoryᵉ Cᵉ Dᵉ γᵉ) →
    (Fᵉ ＝ᵉ Gᵉ) ≃ᵉ
    natural-isomorphism-map-Categoryᵉ Cᵉ (category-Large-Categoryᵉ Dᵉ γᵉ) Fᵉ Gᵉ
  extensionality-map-Small-Large-Categoryᵉ {γᵉ} =
    extensionality-map-Categoryᵉ Cᵉ (category-Large-Categoryᵉ Dᵉ γᵉ)

  eq-natural-isomorphism-map-Small-Large-Categoryᵉ :
    {γᵉ : Level} (Fᵉ Gᵉ : map-Small-Large-Categoryᵉ Cᵉ Dᵉ γᵉ) →
    natural-isomorphism-map-Categoryᵉ Cᵉ (category-Large-Categoryᵉ Dᵉ γᵉ) Fᵉ Gᵉ → Fᵉ ＝ᵉ Gᵉ
  eq-natural-isomorphism-map-Small-Large-Categoryᵉ Fᵉ Gᵉ =
    map-inv-equivᵉ (extensionality-map-Small-Large-Categoryᵉ Fᵉ Gᵉ)
```

### The small categories of maps and natural transformations from small to large categories

```agda
module _
  {l1ᵉ l2ᵉ : Level} {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Large-Categoryᵉ αᵉ βᵉ)
  where

  map-category-Small-Large-Categoryᵉ :
    (lᵉ : Level) → Categoryᵉ (l1ᵉ ⊔ l2ᵉ ⊔ αᵉ lᵉ ⊔ βᵉ lᵉ lᵉ) (l1ᵉ ⊔ l2ᵉ ⊔ βᵉ lᵉ lᵉ)
  map-category-Small-Large-Categoryᵉ =
    category-Large-Categoryᵉ (map-large-category-Small-Large-Categoryᵉ Cᵉ Dᵉ)
```