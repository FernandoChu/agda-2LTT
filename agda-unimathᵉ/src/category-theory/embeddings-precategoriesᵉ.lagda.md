# Embeddings between precategories

```agda
module category-theory.embeddings-precategoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.embedding-maps-precategoriesᵉ
open import category-theory.functors-precategoriesᵉ
open import category-theory.maps-precategoriesᵉ
open import category-theory.precategoriesᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.propositionsᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Aᵉ [functor](category-theory.functors-precategories.mdᵉ) betweenᵉ
[precategories](category-theory.precategories.mdᵉ) `C`ᵉ andᵉ `D`ᵉ isᵉ anᵉ
**embedding**ᵉ ifᵉ it'sᵉ anᵉ [embedding](foundation-core.embeddings.mdᵉ) onᵉ objectsᵉ
andᵉ [fullyᵉ faithful](category-theory.fully-faithful-functors-precategories.md).ᵉ
Henceᵉ embeddingsᵉ areᵉ functorsᵉ thatᵉ areᵉ embeddingsᵉ onᵉ objectsᵉ andᵉ
[equivalences](foundation-core.equivalences.mdᵉ) onᵉ
hom-[sets](foundation-core.sets.md).ᵉ

## Definition

### The predicate on maps between precategories of being an embedding

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ : map-Precategoryᵉ Cᵉ Dᵉ)
  where

  is-embedding-prop-map-Precategoryᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  is-embedding-prop-map-Precategoryᵉ =
    product-Propᵉ
      ( is-functor-prop-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ)
      ( is-embedding-map-prop-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ)

  is-embedding-map-Precategoryᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  is-embedding-map-Precategoryᵉ =
    type-Propᵉ is-embedding-prop-map-Precategoryᵉ

  is-prop-is-embedding-map-Precategoryᵉ : is-propᵉ is-embedding-map-Precategoryᵉ
  is-prop-is-embedding-map-Precategoryᵉ =
    is-prop-type-Propᵉ is-embedding-prop-map-Precategoryᵉ
```

### The predicate on functors between precategories of being an embedding

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ : functor-Precategoryᵉ Cᵉ Dᵉ)
  where

  is-embedding-prop-functor-Precategoryᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  is-embedding-prop-functor-Precategoryᵉ =
    is-embedding-map-prop-map-Precategoryᵉ Cᵉ Dᵉ (map-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ)

  is-embedding-functor-Precategoryᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  is-embedding-functor-Precategoryᵉ =
    type-Propᵉ is-embedding-prop-functor-Precategoryᵉ

  is-prop-is-embedding-functor-Precategoryᵉ :
    is-propᵉ is-embedding-functor-Precategoryᵉ
  is-prop-is-embedding-functor-Precategoryᵉ =
    is-prop-type-Propᵉ is-embedding-prop-functor-Precategoryᵉ
```

### The type of embeddings between precategories

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  where

  embedding-Precategoryᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  embedding-Precategoryᵉ =
    Σᵉ (functor-Precategoryᵉ Cᵉ Dᵉ) (is-embedding-functor-Precategoryᵉ Cᵉ Dᵉ)

  functor-embedding-Precategoryᵉ :
    embedding-Precategoryᵉ → functor-Precategoryᵉ Cᵉ Dᵉ
  functor-embedding-Precategoryᵉ = pr1ᵉ

  is-embedding-embedding-Precategoryᵉ :
    (eᵉ : embedding-Precategoryᵉ) →
    is-embedding-functor-Precategoryᵉ Cᵉ Dᵉ (functor-embedding-Precategoryᵉ eᵉ)
  is-embedding-embedding-Precategoryᵉ = pr2ᵉ
```