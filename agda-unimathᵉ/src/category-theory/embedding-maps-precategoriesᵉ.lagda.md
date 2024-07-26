# Embedding maps between precategories

```agda
module category-theory.embedding-maps-precategoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.fully-faithful-maps-precategoriesᵉ
open import category-theory.maps-precategoriesᵉ
open import category-theory.precategoriesᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.embeddingsᵉ
open import foundation.propositionsᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Aᵉ [map](category-theory.maps-precategories.mdᵉ) betweenᵉ
[precategories](category-theory.precategories.mdᵉ) `C`ᵉ andᵉ `D`ᵉ isᵉ anᵉ **embeddingᵉ
map**ᵉ ifᵉ it'sᵉ anᵉ [embedding](foundation-core.embeddings.mdᵉ) onᵉ objectsᵉ andᵉ
[fullyᵉ faithful](category-theory.fully-faithful-maps-precategories.md).ᵉ Henceᵉ
embeddingᵉ mapsᵉ areᵉ mapsᵉ thatᵉ areᵉ embeddingsᵉ onᵉ objectsᵉ andᵉ
[equivalences](foundation-core.equivalences.mdᵉ) onᵉ
hom-[sets](foundation-core.sets.md).ᵉ

Noteᵉ thatᵉ forᵉ aᵉ mapᵉ ofᵉ precategoriesᵉ to beᵉ calledᵉ _anᵉ embedding_,ᵉ itᵉ mustᵉ alsoᵉ
beᵉ aᵉ [functor](category-theory.functors-precategories.md).ᵉ Thisᵉ notionᵉ isᵉ
consideredᵉ in
[`category-theory.embeddings-precategories`](category-theory.embeddings-precategories.md).ᵉ

## Definition

### The predicate on maps between precategories of being an embedding map

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ : map-Precategoryᵉ Cᵉ Dᵉ)
  where

  is-embedding-map-prop-map-Precategoryᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  is-embedding-map-prop-map-Precategoryᵉ =
    product-Propᵉ
      ( is-emb-Propᵉ (obj-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ))
      ( is-fully-faithful-prop-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ)

  is-embedding-map-map-Precategoryᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  is-embedding-map-map-Precategoryᵉ =
    type-Propᵉ is-embedding-map-prop-map-Precategoryᵉ

  is-prop-is-embedding-map-map-Precategoryᵉ :
    is-propᵉ is-embedding-map-map-Precategoryᵉ
  is-prop-is-embedding-map-map-Precategoryᵉ =
    is-prop-type-Propᵉ is-embedding-map-prop-map-Precategoryᵉ
```

### The type of embedding maps between precategories

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  where

  embedding-map-Precategoryᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  embedding-map-Precategoryᵉ =
    Σᵉ (map-Precategoryᵉ Cᵉ Dᵉ) (is-embedding-map-map-Precategoryᵉ Cᵉ Dᵉ)

  map-embedding-map-Precategoryᵉ :
    embedding-map-Precategoryᵉ → map-Precategoryᵉ Cᵉ Dᵉ
  map-embedding-map-Precategoryᵉ = pr1ᵉ

  is-embedding-map-embedding-map-Precategoryᵉ :
    (eᵉ : embedding-map-Precategoryᵉ) →
    is-embedding-map-map-Precategoryᵉ Cᵉ Dᵉ (map-embedding-map-Precategoryᵉ eᵉ)
  is-embedding-map-embedding-map-Precategoryᵉ = pr2ᵉ
```