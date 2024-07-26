# Full subcategories

```agda
module category-theory.full-subcategoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categoriesᵉ
open import category-theory.composition-operations-on-binary-families-of-setsᵉ
open import category-theory.embeddings-precategoriesᵉ
open import category-theory.full-subprecategoriesᵉ
open import category-theory.fully-faithful-functors-precategoriesᵉ
open import category-theory.functors-categoriesᵉ
open import category-theory.maps-categoriesᵉ
open import category-theory.precategoriesᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.embeddingsᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.strictly-involutive-identity-typesᵉ
open import foundation.subtypesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Aᵉ **fullᵉ subcategory**ᵉ ofᵉ aᵉ [precategory](category-theory.precategories.mdᵉ) `C`ᵉ
consistsᵉ ofᵉ aᵉ [subtype](foundation-core.subtypes.mdᵉ) `P₀`ᵉ ofᵉ theᵉ objectsᵉ ofᵉ `C`.ᵉ

Alternatively,ᵉ weᵉ sayᵉ thatᵉ aᵉ [subcategory](category-theory.subcategories.mdᵉ)
**isᵉ full**ᵉ ifᵉ forᵉ everyᵉ twoᵉ objectsᵉ `X`ᵉ andᵉ `Y`ᵉ in theᵉ subcategory,ᵉ theᵉ subtypeᵉ
ofᵉ morphismsᵉ fromᵉ `X`ᵉ to `Y`ᵉ in theᵉ subcategoryᵉ isᵉ
[full](foundation.full-subtypes.md).ᵉ

## Definitions

### Full subcategories

```agda
Full-Subcategoryᵉ :
  {l1ᵉ l2ᵉ : Level} (l3ᵉ : Level) (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ) → UUᵉ (l1ᵉ ⊔ lsuc l3ᵉ)
Full-Subcategoryᵉ l3ᵉ Cᵉ = Full-Subprecategoryᵉ l3ᵉ (precategory-Categoryᵉ Cᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level}
  (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  (Pᵉ : Full-Subcategoryᵉ l3ᵉ Cᵉ)
  where

  subtype-obj-Full-Subcategoryᵉ : subtypeᵉ l3ᵉ (obj-Categoryᵉ Cᵉ)
  subtype-obj-Full-Subcategoryᵉ =
    subtype-obj-Full-Subprecategoryᵉ (precategory-Categoryᵉ Cᵉ) Pᵉ

  obj-Full-Subcategoryᵉ : UUᵉ (l1ᵉ ⊔ l3ᵉ)
  obj-Full-Subcategoryᵉ = obj-Full-Subprecategoryᵉ (precategory-Categoryᵉ Cᵉ) Pᵉ

  inclusion-obj-Full-Subcategoryᵉ :
    obj-Full-Subcategoryᵉ → obj-Categoryᵉ Cᵉ
  inclusion-obj-Full-Subcategoryᵉ =
    inclusion-obj-Full-Subprecategoryᵉ (precategory-Categoryᵉ Cᵉ) Pᵉ

  is-in-obj-Full-Subcategoryᵉ : (xᵉ : obj-Categoryᵉ Cᵉ) → UUᵉ l3ᵉ
  is-in-obj-Full-Subcategoryᵉ =
    is-in-obj-Full-Subprecategoryᵉ (precategory-Categoryᵉ Cᵉ) Pᵉ

  is-prop-is-in-obj-Full-Subcategoryᵉ :
    (xᵉ : obj-Categoryᵉ Cᵉ) → is-propᵉ (is-in-obj-Full-Subcategoryᵉ xᵉ)
  is-prop-is-in-obj-Full-Subcategoryᵉ =
    is-prop-is-in-obj-Full-Subprecategoryᵉ (precategory-Categoryᵉ Cᵉ) Pᵉ

  is-in-obj-inclusion-obj-Full-Subcategoryᵉ :
    (xᵉ : obj-Full-Subcategoryᵉ) →
    is-in-obj-Full-Subcategoryᵉ (inclusion-obj-Full-Subcategoryᵉ xᵉ)
  is-in-obj-inclusion-obj-Full-Subcategoryᵉ =
    is-in-obj-inclusion-obj-Full-Subprecategoryᵉ (precategory-Categoryᵉ Cᵉ) Pᵉ
```

### The underlying precategory of a full subcategory

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level}
  (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  (Pᵉ : Full-Subcategoryᵉ l3ᵉ Cᵉ)
  where

  hom-set-Full-Subcategoryᵉ : (xᵉ yᵉ : obj-Full-Subcategoryᵉ Cᵉ Pᵉ) → Setᵉ l2ᵉ
  hom-set-Full-Subcategoryᵉ =
    hom-set-Full-Subprecategoryᵉ (precategory-Categoryᵉ Cᵉ) Pᵉ

  hom-Full-Subcategoryᵉ : (xᵉ yᵉ : obj-Full-Subcategoryᵉ Cᵉ Pᵉ) → UUᵉ l2ᵉ
  hom-Full-Subcategoryᵉ = hom-Full-Subprecategoryᵉ (precategory-Categoryᵉ Cᵉ) Pᵉ

  is-set-hom-Full-Subcategoryᵉ :
    (xᵉ yᵉ : obj-Full-Subcategoryᵉ Cᵉ Pᵉ) → is-setᵉ (hom-Full-Subcategoryᵉ xᵉ yᵉ)
  is-set-hom-Full-Subcategoryᵉ =
    is-set-hom-Full-Subprecategoryᵉ (precategory-Categoryᵉ Cᵉ) Pᵉ

  id-hom-Full-Subcategoryᵉ :
    {xᵉ : obj-Full-Subcategoryᵉ Cᵉ Pᵉ} → hom-Full-Subcategoryᵉ xᵉ xᵉ
  id-hom-Full-Subcategoryᵉ {xᵉ} =
    id-hom-Full-Subprecategoryᵉ (precategory-Categoryᵉ Cᵉ) Pᵉ {xᵉ}

  comp-hom-Full-Subcategoryᵉ :
    {xᵉ yᵉ zᵉ : obj-Full-Subcategoryᵉ Cᵉ Pᵉ} →
    hom-Full-Subcategoryᵉ yᵉ zᵉ →
    hom-Full-Subcategoryᵉ xᵉ yᵉ →
    hom-Full-Subcategoryᵉ xᵉ zᵉ
  comp-hom-Full-Subcategoryᵉ {xᵉ} {yᵉ} {zᵉ} =
    comp-hom-Full-Subprecategoryᵉ (precategory-Categoryᵉ Cᵉ) Pᵉ {xᵉ} {yᵉ} {zᵉ}

  associative-comp-hom-Full-Subcategoryᵉ :
    {xᵉ yᵉ zᵉ wᵉ : obj-Full-Subcategoryᵉ Cᵉ Pᵉ}
    (hᵉ : hom-Full-Subcategoryᵉ zᵉ wᵉ)
    (gᵉ : hom-Full-Subcategoryᵉ yᵉ zᵉ)
    (fᵉ : hom-Full-Subcategoryᵉ xᵉ yᵉ) →
    comp-hom-Full-Subcategoryᵉ {xᵉ} {yᵉ} {wᵉ}
      ( comp-hom-Full-Subcategoryᵉ {yᵉ} {zᵉ} {wᵉ} hᵉ gᵉ)
      ( fᵉ) ＝ᵉ
    comp-hom-Full-Subcategoryᵉ {xᵉ} {zᵉ} {wᵉ}
      ( hᵉ)
      ( comp-hom-Full-Subcategoryᵉ {xᵉ} {yᵉ} {zᵉ} gᵉ fᵉ)
  associative-comp-hom-Full-Subcategoryᵉ {xᵉ} {yᵉ} {zᵉ} {wᵉ} =
    associative-comp-hom-Full-Subprecategoryᵉ
      ( precategory-Categoryᵉ Cᵉ) Pᵉ {xᵉ} {yᵉ} {zᵉ} {wᵉ}

  involutive-eq-associative-comp-hom-Full-Subcategoryᵉ :
    {xᵉ yᵉ zᵉ wᵉ : obj-Full-Subcategoryᵉ Cᵉ Pᵉ}
    (hᵉ : hom-Full-Subcategoryᵉ zᵉ wᵉ)
    (gᵉ : hom-Full-Subcategoryᵉ yᵉ zᵉ)
    (fᵉ : hom-Full-Subcategoryᵉ xᵉ yᵉ) →
    comp-hom-Full-Subcategoryᵉ {xᵉ} {yᵉ} {wᵉ}
      ( comp-hom-Full-Subcategoryᵉ {yᵉ} {zᵉ} {wᵉ} hᵉ gᵉ)
      ( fᵉ) ＝ⁱᵉ
    comp-hom-Full-Subcategoryᵉ {xᵉ} {zᵉ} {wᵉ}
      ( hᵉ)
      ( comp-hom-Full-Subcategoryᵉ {xᵉ} {yᵉ} {zᵉ} gᵉ fᵉ)
  involutive-eq-associative-comp-hom-Full-Subcategoryᵉ {xᵉ} {yᵉ} {zᵉ} {wᵉ} =
    involutive-eq-associative-comp-hom-Full-Subprecategoryᵉ
      ( precategory-Categoryᵉ Cᵉ) Pᵉ {xᵉ} {yᵉ} {zᵉ} {wᵉ}

  left-unit-law-comp-hom-Full-Subcategoryᵉ :
    {xᵉ yᵉ : obj-Full-Subcategoryᵉ Cᵉ Pᵉ}
    (fᵉ : hom-Full-Subcategoryᵉ xᵉ yᵉ) →
    comp-hom-Full-Subcategoryᵉ {xᵉ} {yᵉ} {yᵉ}
      ( id-hom-Full-Subcategoryᵉ {yᵉ})
      ( fᵉ) ＝ᵉ
    fᵉ
  left-unit-law-comp-hom-Full-Subcategoryᵉ {xᵉ} {yᵉ} =
    left-unit-law-comp-hom-Full-Subprecategoryᵉ
      ( precategory-Categoryᵉ Cᵉ) Pᵉ {xᵉ} {yᵉ}

  right-unit-law-comp-hom-Full-Subcategoryᵉ :
    {xᵉ yᵉ : obj-Full-Subcategoryᵉ Cᵉ Pᵉ}
    (fᵉ : hom-Full-Subcategoryᵉ xᵉ yᵉ) →
    comp-hom-Full-Subcategoryᵉ {xᵉ} {xᵉ} {yᵉ}
      ( fᵉ)
      ( id-hom-Full-Subcategoryᵉ {xᵉ}) ＝ᵉ
    fᵉ
  right-unit-law-comp-hom-Full-Subcategoryᵉ {xᵉ} {yᵉ} =
    right-unit-law-comp-hom-Full-Subprecategoryᵉ
      ( precategory-Categoryᵉ Cᵉ) Pᵉ {xᵉ} {yᵉ}

  associative-composition-operation-Full-Subcategoryᵉ :
    associative-composition-operation-binary-family-Setᵉ hom-set-Full-Subcategoryᵉ
  associative-composition-operation-Full-Subcategoryᵉ =
    associative-composition-operation-Full-Subprecategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( Pᵉ)

  is-unital-composition-operation-Full-Subcategoryᵉ :
    is-unital-composition-operation-binary-family-Setᵉ
      ( hom-set-Full-Subcategoryᵉ)
      ( λ {xᵉ} {yᵉ} {zᵉ} → comp-hom-Full-Subcategoryᵉ {xᵉ} {yᵉ} {zᵉ})
  is-unital-composition-operation-Full-Subcategoryᵉ =
    is-unital-composition-operation-Full-Subprecategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( Pᵉ)

  precategory-Full-Subcategoryᵉ : Precategoryᵉ (l1ᵉ ⊔ l3ᵉ) l2ᵉ
  precategory-Full-Subcategoryᵉ =
    precategory-Full-Subprecategoryᵉ (precategory-Categoryᵉ Cᵉ) Pᵉ
```

### Isomorphisms in full subcategories

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level}
  (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  (Pᵉ : Full-Subcategoryᵉ l3ᵉ Cᵉ)
  where

  iso-Full-Subcategoryᵉ : (Xᵉ Yᵉ : obj-Full-Subcategoryᵉ Cᵉ Pᵉ) → UUᵉ l2ᵉ
  iso-Full-Subcategoryᵉ = iso-Full-Subprecategoryᵉ (precategory-Categoryᵉ Cᵉ) Pᵉ

  iso-eq-Full-Subcategoryᵉ :
    (Xᵉ Yᵉ : obj-Full-Subcategoryᵉ Cᵉ Pᵉ) → Xᵉ ＝ᵉ Yᵉ → iso-Full-Subcategoryᵉ Xᵉ Yᵉ
  iso-eq-Full-Subcategoryᵉ =
    iso-eq-Full-Subprecategoryᵉ (precategory-Categoryᵉ Cᵉ) Pᵉ
```

### The underlying category of a full subcategory

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level}
  (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  (Pᵉ : Full-Subcategoryᵉ l3ᵉ Cᵉ)
  where

  is-category-precategory-Full-Subcategoryᵉ :
    is-category-Precategoryᵉ (precategory-Full-Subcategoryᵉ Cᵉ Pᵉ)
  is-category-precategory-Full-Subcategoryᵉ =
    is-category-precategory-is-category-Full-Subprecategoryᵉ
      ( precategory-Categoryᵉ Cᵉ) Pᵉ (is-category-Categoryᵉ Cᵉ)

  category-Full-Subcategoryᵉ : Categoryᵉ (l1ᵉ ⊔ l3ᵉ) l2ᵉ
  pr1ᵉ category-Full-Subcategoryᵉ = precategory-Full-Subcategoryᵉ Cᵉ Pᵉ
  pr2ᵉ category-Full-Subcategoryᵉ = is-category-precategory-Full-Subcategoryᵉ
```

## Properties

### The inclusion functor is an embedding

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level}
  (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  (Pᵉ : Full-Subcategoryᵉ l3ᵉ Cᵉ)
  where

  inclusion-map-Full-Subcategoryᵉ :
    map-Categoryᵉ (category-Full-Subcategoryᵉ Cᵉ Pᵉ) Cᵉ
  inclusion-map-Full-Subcategoryᵉ =
    inclusion-map-Full-Subprecategoryᵉ (precategory-Categoryᵉ Cᵉ) Pᵉ

  is-functor-inclusion-Full-Subcategoryᵉ :
    is-functor-map-Categoryᵉ
      ( category-Full-Subcategoryᵉ Cᵉ Pᵉ)
      ( Cᵉ)
      ( inclusion-map-Full-Subcategoryᵉ)
  is-functor-inclusion-Full-Subcategoryᵉ =
    is-functor-inclusion-Full-Subprecategoryᵉ (precategory-Categoryᵉ Cᵉ) Pᵉ

  inclusion-Full-Subcategoryᵉ :
    functor-Categoryᵉ (category-Full-Subcategoryᵉ Cᵉ Pᵉ) Cᵉ
  inclusion-Full-Subcategoryᵉ =
    inclusion-Full-Subprecategoryᵉ (precategory-Categoryᵉ Cᵉ) Pᵉ

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level}
  (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  (Pᵉ : Full-Subcategoryᵉ l3ᵉ Cᵉ)
  where

  is-fully-faithful-inclusion-Full-Subcategoryᵉ :
    is-fully-faithful-functor-Precategoryᵉ
      ( precategory-Full-Subcategoryᵉ Cᵉ Pᵉ)
      ( precategory-Categoryᵉ Cᵉ)
      ( inclusion-Full-Subcategoryᵉ Cᵉ Pᵉ)
  is-fully-faithful-inclusion-Full-Subcategoryᵉ =
    is-fully-faithful-inclusion-Full-Subprecategoryᵉ (precategory-Categoryᵉ Cᵉ) Pᵉ

  is-emb-obj-inclusion-Full-Subcategoryᵉ :
    is-embᵉ
      ( obj-functor-Categoryᵉ
        ( category-Full-Subcategoryᵉ Cᵉ Pᵉ)
        ( Cᵉ)
        ( inclusion-Full-Subcategoryᵉ Cᵉ Pᵉ))
  is-emb-obj-inclusion-Full-Subcategoryᵉ =
    is-emb-obj-inclusion-Full-Subprecategoryᵉ (precategory-Categoryᵉ Cᵉ) Pᵉ

  is-embedding-inclusion-Full-Subcategoryᵉ :
    is-embedding-functor-Precategoryᵉ
      ( precategory-Full-Subcategoryᵉ Cᵉ Pᵉ)
      ( precategory-Categoryᵉ Cᵉ)
      ( inclusion-Full-Subcategoryᵉ Cᵉ Pᵉ)
  is-embedding-inclusion-Full-Subcategoryᵉ =
    is-embedding-inclusion-Full-Subprecategoryᵉ (precategory-Categoryᵉ Cᵉ) Pᵉ

  embedding-Full-Subcategoryᵉ :
    embedding-Precategoryᵉ
      ( precategory-Full-Subcategoryᵉ Cᵉ Pᵉ)
      ( precategory-Categoryᵉ Cᵉ)
  embedding-Full-Subcategoryᵉ =
    embedding-Full-Subprecategoryᵉ (precategory-Categoryᵉ Cᵉ) Pᵉ
```