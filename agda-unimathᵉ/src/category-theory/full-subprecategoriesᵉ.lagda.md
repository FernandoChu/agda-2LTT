# Full subprecategories

```agda
module category-theory.full-subprecategoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categoriesᵉ
open import category-theory.composition-operations-on-binary-families-of-setsᵉ
open import category-theory.embeddings-precategoriesᵉ
open import category-theory.fully-faithful-functors-precategoriesᵉ
open import category-theory.functors-precategoriesᵉ
open import category-theory.isomorphisms-in-categoriesᵉ
open import category-theory.isomorphisms-in-precategoriesᵉ
open import category-theory.maps-precategoriesᵉ
open import category-theory.precategoriesᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.embeddingsᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.strictly-involutive-identity-typesᵉ
open import foundation.subtype-identity-principleᵉ
open import foundation.subtypesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Aᵉ **fullᵉ subprecategory**ᵉ ofᵉ aᵉ [precategory](category-theory.precategories.mdᵉ)
`C`ᵉ consistsᵉ ofᵉ aᵉ [subtype](foundation-core.subtypes.mdᵉ) `P₀`ᵉ ofᵉ theᵉ objectsᵉ ofᵉ
`C`.ᵉ

Alternatively,ᵉ weᵉ sayᵉ thatᵉ aᵉ
[subprecategory](category-theory.subprecategories.mdᵉ) **isᵉ full**ᵉ ifᵉ forᵉ everyᵉ
twoᵉ objectsᵉ `X`ᵉ andᵉ `Y`ᵉ in theᵉ subprecategory,ᵉ theᵉ subtypeᵉ ofᵉ morphismsᵉ fromᵉ `X`ᵉ
to `Y`ᵉ in theᵉ subprecategoryᵉ isᵉ [full](foundation.full-subtypes.md).ᵉ

## Definitions

### Full subprecategories

```agda
Full-Subprecategoryᵉ :
  {l1ᵉ l2ᵉ : Level} (l3ᵉ : Level) (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ) → UUᵉ (l1ᵉ ⊔ lsuc l3ᵉ)
Full-Subprecategoryᵉ l3ᵉ Cᵉ = subtypeᵉ l3ᵉ (obj-Precategoryᵉ Cᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Pᵉ : Full-Subprecategoryᵉ l3ᵉ Cᵉ)
  where

  subtype-obj-Full-Subprecategoryᵉ : subtypeᵉ l3ᵉ (obj-Precategoryᵉ Cᵉ)
  subtype-obj-Full-Subprecategoryᵉ = Pᵉ

  obj-Full-Subprecategoryᵉ : UUᵉ (l1ᵉ ⊔ l3ᵉ)
  obj-Full-Subprecategoryᵉ = type-subtypeᵉ subtype-obj-Full-Subprecategoryᵉ

  inclusion-obj-Full-Subprecategoryᵉ :
    obj-Full-Subprecategoryᵉ → obj-Precategoryᵉ Cᵉ
  inclusion-obj-Full-Subprecategoryᵉ =
    inclusion-subtypeᵉ subtype-obj-Full-Subprecategoryᵉ

  is-in-obj-Full-Subprecategoryᵉ : (xᵉ : obj-Precategoryᵉ Cᵉ) → UUᵉ l3ᵉ
  is-in-obj-Full-Subprecategoryᵉ = is-in-subtypeᵉ subtype-obj-Full-Subprecategoryᵉ

  is-prop-is-in-obj-Full-Subprecategoryᵉ :
    (xᵉ : obj-Precategoryᵉ Cᵉ) → is-propᵉ (is-in-obj-Full-Subprecategoryᵉ xᵉ)
  is-prop-is-in-obj-Full-Subprecategoryᵉ =
    is-prop-is-in-subtypeᵉ subtype-obj-Full-Subprecategoryᵉ

  is-in-obj-inclusion-obj-Full-Subprecategoryᵉ :
    (xᵉ : obj-Full-Subprecategoryᵉ) →
    is-in-obj-Full-Subprecategoryᵉ (inclusion-obj-Full-Subprecategoryᵉ xᵉ)
  is-in-obj-inclusion-obj-Full-Subprecategoryᵉ =
    is-in-subtype-inclusion-subtypeᵉ subtype-obj-Full-Subprecategoryᵉ
```

### The underlying precategory of a full subprecategory

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Pᵉ : Full-Subprecategoryᵉ l3ᵉ Cᵉ)
  where

  hom-set-Full-Subprecategoryᵉ : (xᵉ yᵉ : obj-Full-Subprecategoryᵉ Cᵉ Pᵉ) → Setᵉ l2ᵉ
  hom-set-Full-Subprecategoryᵉ xᵉ yᵉ =
    hom-set-Precategoryᵉ Cᵉ
      ( inclusion-obj-Full-Subprecategoryᵉ Cᵉ Pᵉ xᵉ)
      ( inclusion-obj-Full-Subprecategoryᵉ Cᵉ Pᵉ yᵉ)

  hom-Full-Subprecategoryᵉ : (xᵉ yᵉ : obj-Full-Subprecategoryᵉ Cᵉ Pᵉ) → UUᵉ l2ᵉ
  hom-Full-Subprecategoryᵉ xᵉ yᵉ = type-Setᵉ (hom-set-Full-Subprecategoryᵉ xᵉ yᵉ)

  is-set-hom-Full-Subprecategoryᵉ :
    (xᵉ yᵉ : obj-Full-Subprecategoryᵉ Cᵉ Pᵉ) → is-setᵉ (hom-Full-Subprecategoryᵉ xᵉ yᵉ)
  is-set-hom-Full-Subprecategoryᵉ xᵉ yᵉ =
    is-set-type-Setᵉ (hom-set-Full-Subprecategoryᵉ xᵉ yᵉ)

  id-hom-Full-Subprecategoryᵉ :
    {xᵉ : obj-Full-Subprecategoryᵉ Cᵉ Pᵉ} → hom-Full-Subprecategoryᵉ xᵉ xᵉ
  id-hom-Full-Subprecategoryᵉ = id-hom-Precategoryᵉ Cᵉ

  comp-hom-Full-Subprecategoryᵉ :
    {xᵉ yᵉ zᵉ : obj-Full-Subprecategoryᵉ Cᵉ Pᵉ} →
    hom-Full-Subprecategoryᵉ yᵉ zᵉ →
    hom-Full-Subprecategoryᵉ xᵉ yᵉ →
    hom-Full-Subprecategoryᵉ xᵉ zᵉ
  comp-hom-Full-Subprecategoryᵉ = comp-hom-Precategoryᵉ Cᵉ

  involutive-eq-associative-comp-hom-Full-Subprecategoryᵉ :
    {xᵉ yᵉ zᵉ wᵉ : obj-Full-Subprecategoryᵉ Cᵉ Pᵉ}
    (hᵉ : hom-Full-Subprecategoryᵉ zᵉ wᵉ)
    (gᵉ : hom-Full-Subprecategoryᵉ yᵉ zᵉ)
    (fᵉ : hom-Full-Subprecategoryᵉ xᵉ yᵉ) →
    comp-hom-Full-Subprecategoryᵉ {xᵉ} {yᵉ} {wᵉ}
      ( comp-hom-Full-Subprecategoryᵉ {yᵉ} {zᵉ} {wᵉ} hᵉ gᵉ)
      ( fᵉ) ＝ⁱᵉ
    comp-hom-Full-Subprecategoryᵉ {xᵉ} {zᵉ} {wᵉ}
      ( hᵉ)
      ( comp-hom-Full-Subprecategoryᵉ {xᵉ} {yᵉ} {zᵉ} gᵉ fᵉ)
  involutive-eq-associative-comp-hom-Full-Subprecategoryᵉ =
    involutive-eq-associative-comp-hom-Precategoryᵉ Cᵉ

  associative-comp-hom-Full-Subprecategoryᵉ :
    {xᵉ yᵉ zᵉ wᵉ : obj-Full-Subprecategoryᵉ Cᵉ Pᵉ}
    (hᵉ : hom-Full-Subprecategoryᵉ zᵉ wᵉ)
    (gᵉ : hom-Full-Subprecategoryᵉ yᵉ zᵉ)
    (fᵉ : hom-Full-Subprecategoryᵉ xᵉ yᵉ) →
    comp-hom-Full-Subprecategoryᵉ {xᵉ} {yᵉ} {wᵉ}
      ( comp-hom-Full-Subprecategoryᵉ {yᵉ} {zᵉ} {wᵉ} hᵉ gᵉ)
      ( fᵉ) ＝ᵉ
    comp-hom-Full-Subprecategoryᵉ {xᵉ} {zᵉ} {wᵉ}
      ( hᵉ)
      ( comp-hom-Full-Subprecategoryᵉ {xᵉ} {yᵉ} {zᵉ} gᵉ fᵉ)
  associative-comp-hom-Full-Subprecategoryᵉ =
    associative-comp-hom-Precategoryᵉ Cᵉ

  left-unit-law-comp-hom-Full-Subprecategoryᵉ :
    {xᵉ yᵉ : obj-Full-Subprecategoryᵉ Cᵉ Pᵉ}
    (fᵉ : hom-Full-Subprecategoryᵉ xᵉ yᵉ) →
    comp-hom-Full-Subprecategoryᵉ {xᵉ} {yᵉ} {yᵉ}
      ( id-hom-Full-Subprecategoryᵉ {yᵉ})
      ( fᵉ) ＝ᵉ
    fᵉ
  left-unit-law-comp-hom-Full-Subprecategoryᵉ =
    left-unit-law-comp-hom-Precategoryᵉ Cᵉ

  right-unit-law-comp-hom-Full-Subprecategoryᵉ :
    {xᵉ yᵉ : obj-Full-Subprecategoryᵉ Cᵉ Pᵉ}
    (fᵉ : hom-Full-Subprecategoryᵉ xᵉ yᵉ) →
    comp-hom-Full-Subprecategoryᵉ {xᵉ} {xᵉ} {yᵉ}
      ( fᵉ)
      ( id-hom-Full-Subprecategoryᵉ {xᵉ}) ＝ᵉ
    fᵉ
  right-unit-law-comp-hom-Full-Subprecategoryᵉ =
    right-unit-law-comp-hom-Precategoryᵉ Cᵉ

  associative-composition-operation-Full-Subprecategoryᵉ :
    associative-composition-operation-binary-family-Setᵉ
      hom-set-Full-Subprecategoryᵉ
  pr1ᵉ associative-composition-operation-Full-Subprecategoryᵉ {xᵉ} {yᵉ} {zᵉ} =
    comp-hom-Full-Subprecategoryᵉ {xᵉ} {yᵉ} {zᵉ}
  pr2ᵉ
    associative-composition-operation-Full-Subprecategoryᵉ
    { xᵉ} {yᵉ} {zᵉ} {wᵉ} hᵉ gᵉ fᵉ =
    involutive-eq-associative-comp-hom-Full-Subprecategoryᵉ {xᵉ} {yᵉ} {zᵉ} {wᵉ} hᵉ gᵉ fᵉ

  is-unital-composition-operation-Full-Subprecategoryᵉ :
    is-unital-composition-operation-binary-family-Setᵉ
      ( hom-set-Full-Subprecategoryᵉ)
      ( λ {xᵉ} {yᵉ} {zᵉ} → comp-hom-Full-Subprecategoryᵉ {xᵉ} {yᵉ} {zᵉ})
  pr1ᵉ is-unital-composition-operation-Full-Subprecategoryᵉ xᵉ =
    id-hom-Full-Subprecategoryᵉ {xᵉ}
  pr1ᵉ (pr2ᵉ is-unital-composition-operation-Full-Subprecategoryᵉ) {xᵉ} {yᵉ} =
    left-unit-law-comp-hom-Full-Subprecategoryᵉ {xᵉ} {yᵉ}
  pr2ᵉ (pr2ᵉ is-unital-composition-operation-Full-Subprecategoryᵉ) {xᵉ} {yᵉ} =
    right-unit-law-comp-hom-Full-Subprecategoryᵉ {xᵉ} {yᵉ}

  precategory-Full-Subprecategoryᵉ : Precategoryᵉ (l1ᵉ ⊔ l3ᵉ) l2ᵉ
  pr1ᵉ precategory-Full-Subprecategoryᵉ = obj-Full-Subprecategoryᵉ Cᵉ Pᵉ
  pr1ᵉ (pr2ᵉ precategory-Full-Subprecategoryᵉ) = hom-set-Full-Subprecategoryᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ precategory-Full-Subprecategoryᵉ)) =
    associative-composition-operation-Full-Subprecategoryᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ precategory-Full-Subprecategoryᵉ)) =
    is-unital-composition-operation-Full-Subprecategoryᵉ
```

### Isomorphisms in full subprecategories

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Pᵉ : Full-Subprecategoryᵉ l3ᵉ Cᵉ)
  where

  iso-Full-Subprecategoryᵉ :
    (Xᵉ Yᵉ : obj-Full-Subprecategoryᵉ Cᵉ Pᵉ) → UUᵉ l2ᵉ
  iso-Full-Subprecategoryᵉ Xᵉ Yᵉ =
    iso-Precategoryᵉ Cᵉ (inclusion-subtypeᵉ Pᵉ Xᵉ) (inclusion-subtypeᵉ Pᵉ Yᵉ)

  iso-eq-Full-Subprecategoryᵉ :
    (Xᵉ Yᵉ : obj-Full-Subprecategoryᵉ Cᵉ Pᵉ) → Xᵉ ＝ᵉ Yᵉ → iso-Full-Subprecategoryᵉ Xᵉ Yᵉ
  iso-eq-Full-Subprecategoryᵉ =
    iso-eq-Precategoryᵉ (precategory-Full-Subprecategoryᵉ Cᵉ Pᵉ)
```

### The inclusion functor of a full subprecategory

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Pᵉ : Full-Subprecategoryᵉ l3ᵉ Cᵉ)
  where

  inclusion-map-Full-Subprecategoryᵉ :
    map-Precategoryᵉ (precategory-Full-Subprecategoryᵉ Cᵉ Pᵉ) Cᵉ
  pr1ᵉ inclusion-map-Full-Subprecategoryᵉ = inclusion-obj-Full-Subprecategoryᵉ Cᵉ Pᵉ
  pr2ᵉ inclusion-map-Full-Subprecategoryᵉ = idᵉ

  is-functor-inclusion-Full-Subprecategoryᵉ :
    is-functor-map-Precategoryᵉ
      ( precategory-Full-Subprecategoryᵉ Cᵉ Pᵉ)
      ( Cᵉ)
      ( inclusion-map-Full-Subprecategoryᵉ)
  pr1ᵉ is-functor-inclusion-Full-Subprecategoryᵉ gᵉ fᵉ = reflᵉ
  pr2ᵉ is-functor-inclusion-Full-Subprecategoryᵉ xᵉ = reflᵉ

  inclusion-Full-Subprecategoryᵉ :
    functor-Precategoryᵉ (precategory-Full-Subprecategoryᵉ Cᵉ Pᵉ) Cᵉ
  pr1ᵉ inclusion-Full-Subprecategoryᵉ =
    inclusion-obj-Full-Subprecategoryᵉ Cᵉ Pᵉ
  pr1ᵉ (pr2ᵉ inclusion-Full-Subprecategoryᵉ) = idᵉ
  pr2ᵉ (pr2ᵉ inclusion-Full-Subprecategoryᵉ) =
    is-functor-inclusion-Full-Subprecategoryᵉ
```

## Properties

### A full subprecategory of a category is a category

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Pᵉ : Full-Subprecategoryᵉ l3ᵉ Cᵉ)
  where

  is-category-precategory-is-category-Full-Subprecategoryᵉ :
    is-category-Precategoryᵉ Cᵉ →
    is-category-Precategoryᵉ (precategory-Full-Subprecategoryᵉ Cᵉ Pᵉ)
  is-category-precategory-is-category-Full-Subprecategoryᵉ is-category-Cᵉ Xᵉ =
    fundamental-theorem-idᵉ
      ( is-torsorial-Eq-subtypeᵉ
        ( is-torsorial-iso-Categoryᵉ (Cᵉ ,ᵉ is-category-Cᵉ) (inclusion-subtypeᵉ Pᵉ Xᵉ))
        ( is-prop-is-in-subtypeᵉ Pᵉ)
        ( inclusion-subtypeᵉ Pᵉ Xᵉ)
        ( id-iso-Precategoryᵉ Cᵉ)
        ( is-in-subtype-inclusion-subtypeᵉ Pᵉ Xᵉ))
      ( iso-eq-Full-Subprecategoryᵉ Cᵉ Pᵉ Xᵉ)
```

### The inclusion functor is an embedding

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Pᵉ : Full-Subprecategoryᵉ l3ᵉ Cᵉ)
  where

  is-fully-faithful-inclusion-Full-Subprecategoryᵉ :
    is-fully-faithful-functor-Precategoryᵉ
      ( precategory-Full-Subprecategoryᵉ Cᵉ Pᵉ)
      ( Cᵉ)
      ( inclusion-Full-Subprecategoryᵉ Cᵉ Pᵉ)
  is-fully-faithful-inclusion-Full-Subprecategoryᵉ xᵉ yᵉ = is-equiv-idᵉ

  is-emb-obj-inclusion-Full-Subprecategoryᵉ :
    is-embᵉ
      ( obj-functor-Precategoryᵉ
        ( precategory-Full-Subprecategoryᵉ Cᵉ Pᵉ)
        ( Cᵉ)
        ( inclusion-Full-Subprecategoryᵉ Cᵉ Pᵉ))
  is-emb-obj-inclusion-Full-Subprecategoryᵉ =
    is-emb-inclusion-subtypeᵉ (subtype-obj-Full-Subprecategoryᵉ Cᵉ Pᵉ)

  is-embedding-inclusion-Full-Subprecategoryᵉ :
    is-embedding-functor-Precategoryᵉ
      ( precategory-Full-Subprecategoryᵉ Cᵉ Pᵉ)
      ( Cᵉ)
      ( inclusion-Full-Subprecategoryᵉ Cᵉ Pᵉ)
  pr1ᵉ is-embedding-inclusion-Full-Subprecategoryᵉ =
    is-emb-obj-inclusion-Full-Subprecategoryᵉ
  pr2ᵉ is-embedding-inclusion-Full-Subprecategoryᵉ =
    is-fully-faithful-inclusion-Full-Subprecategoryᵉ

  embedding-Full-Subprecategoryᵉ :
    embedding-Precategoryᵉ
      ( precategory-Full-Subprecategoryᵉ Cᵉ Pᵉ)
      ( Cᵉ)
  pr1ᵉ embedding-Full-Subprecategoryᵉ = inclusion-Full-Subprecategoryᵉ Cᵉ Pᵉ
  pr2ᵉ embedding-Full-Subprecategoryᵉ = is-embedding-inclusion-Full-Subprecategoryᵉ
```

## See also

-ᵉ [Wideᵉ subprecategories](category-theory.wide-subprecategories.mdᵉ)

## External links

-ᵉ [Fullᵉ subcategories](https://1lab.dev/Cat.Functor.FullSubcategory.htmlᵉ) atᵉ
  1labᵉ
-ᵉ [fullᵉ subcategory](https://ncatlab.org/nlab/show/full+subcategoryᵉ) atᵉ $n$Labᵉ