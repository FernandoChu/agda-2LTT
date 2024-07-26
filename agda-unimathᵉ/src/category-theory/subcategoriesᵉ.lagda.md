# Subcategories

```agda
module category-theory.subcategoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categoriesᵉ
open import category-theory.composition-operations-on-binary-families-of-setsᵉ
open import category-theory.faithful-functors-precategoriesᵉ
open import category-theory.functors-precategoriesᵉ
open import category-theory.isomorphisms-in-categoriesᵉ
open import category-theory.isomorphisms-in-precategoriesᵉ
open import category-theory.isomorphisms-in-subprecategoriesᵉ
open import category-theory.maps-precategoriesᵉ
open import category-theory.precategoriesᵉ
open import category-theory.replete-subprecategoriesᵉ
open import category-theory.subprecategoriesᵉ

open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.embeddingsᵉ
open import foundation.equivalencesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
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

Aᵉ **subcategory**ᵉ ofᵉ aᵉ [category](category-theory.categories.mdᵉ) `C`ᵉ isᵉ aᵉ
[subprecategory](category-theory.subprecategories.md).ᵉ Itᵉ consistsᵉ ofᵉ aᵉ
[subtype](foundation-core.subtypes.mdᵉ) `P₀`ᵉ ofᵉ theᵉ objectsᵉ ofᵉ `C`,ᵉ andᵉ aᵉ familyᵉ
ofᵉ subtypesᵉ

```text
  P₁ᵉ : (Xᵉ Yᵉ : objᵉ Cᵉ) → P₀ᵉ Xᵉ → P₀ᵉ Yᵉ → subtypeᵉ (homᵉ Xᵉ Yᵉ)
```

ofᵉ theᵉ morphismsᵉ ofᵉ `C`,ᵉ suchᵉ thatᵉ `P₁`ᵉ containsᵉ allᵉ identityᵉ morphismsᵉ ofᵉ
objectsᵉ in `P₀`ᵉ andᵉ isᵉ closedᵉ underᵉ composition.ᵉ Byᵉ univalence,ᵉ itᵉ thereforeᵉ
containsᵉ theᵉ isomorphisms,ᵉ andᵉ henceᵉ definesᵉ aᵉ category.ᵉ

## Definitions

### Sub-hom-families of categories

```agda
subtype-hom-Categoryᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} (l4ᵉ : Level)
  (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  (P₀ᵉ : subtypeᵉ l3ᵉ (obj-Categoryᵉ Cᵉ)) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ lsuc l4ᵉ)
subtype-hom-Categoryᵉ l4ᵉ Cᵉ = subtype-hom-Precategoryᵉ l4ᵉ (precategory-Categoryᵉ Cᵉ)
```

### Categorical predicates on sub-hom-families of categories

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  (P₀ᵉ : subtypeᵉ l3ᵉ (obj-Categoryᵉ Cᵉ))
  (P₁ᵉ : subtype-hom-Categoryᵉ l4ᵉ Cᵉ P₀ᵉ)
  where

  contains-id-subtype-Categoryᵉ : UUᵉ (l1ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  contains-id-subtype-Categoryᵉ =
    contains-id-subtype-Precategoryᵉ (precategory-Categoryᵉ Cᵉ) P₀ᵉ P₁ᵉ

  is-prop-contains-id-subtype-Categoryᵉ :
    is-propᵉ contains-id-subtype-Categoryᵉ
  is-prop-contains-id-subtype-Categoryᵉ =
    is-prop-contains-id-subtype-Precategoryᵉ (precategory-Categoryᵉ Cᵉ) P₀ᵉ P₁ᵉ

  contains-id-prop-subtype-Categoryᵉ : Propᵉ (l1ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  contains-id-prop-subtype-Categoryᵉ =
    contains-id-prop-subtype-Precategoryᵉ (precategory-Categoryᵉ Cᵉ) P₀ᵉ P₁ᵉ

  is-closed-under-composition-subtype-Categoryᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  is-closed-under-composition-subtype-Categoryᵉ =
    is-closed-under-composition-subtype-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ) P₀ᵉ P₁ᵉ

  is-prop-is-closed-under-composition-subtype-Categoryᵉ :
    is-propᵉ is-closed-under-composition-subtype-Categoryᵉ
  is-prop-is-closed-under-composition-subtype-Categoryᵉ =
    is-prop-is-closed-under-composition-subtype-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ) P₀ᵉ P₁ᵉ

  is-closed-under-composition-prop-subtype-Categoryᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  is-closed-under-composition-prop-subtype-Categoryᵉ =
    is-closed-under-composition-prop-subtype-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ) P₀ᵉ P₁ᵉ
```

### The predicate of being a subcategory

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  (P₀ᵉ : subtypeᵉ l3ᵉ (obj-Categoryᵉ Cᵉ))
  (P₁ᵉ : subtype-hom-Categoryᵉ l4ᵉ Cᵉ P₀ᵉ)
  where

  is-subcategory-Propᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  is-subcategory-Propᵉ = is-subprecategory-Propᵉ (precategory-Categoryᵉ Cᵉ) P₀ᵉ P₁ᵉ

  is-subcategoryᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  is-subcategoryᵉ = type-Propᵉ is-subcategory-Propᵉ

  is-prop-is-subcategoryᵉ : is-propᵉ (is-subcategoryᵉ)
  is-prop-is-subcategoryᵉ = is-prop-type-Propᵉ is-subcategory-Propᵉ

  contains-id-is-subcategoryᵉ :
    is-subcategoryᵉ →
    contains-id-subtype-Categoryᵉ Cᵉ P₀ᵉ P₁ᵉ
  contains-id-is-subcategoryᵉ =
    contains-id-is-subprecategoryᵉ (precategory-Categoryᵉ Cᵉ) P₀ᵉ P₁ᵉ

  is-closed-under-composition-is-subcategoryᵉ :
    is-subcategoryᵉ →
    is-closed-under-composition-subtype-Categoryᵉ Cᵉ P₀ᵉ P₁ᵉ
  is-closed-under-composition-is-subcategoryᵉ =
    is-closed-under-composition-is-subprecategoryᵉ (precategory-Categoryᵉ Cᵉ) P₀ᵉ P₁ᵉ
```

### Subcategories

```agda
Subcategoryᵉ :
  {l1ᵉ l2ᵉ : Level} (l3ᵉ l4ᵉ : Level)
  (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ) →
  UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ lsuc l3ᵉ ⊔ lsuc l4ᵉ)
Subcategoryᵉ l3ᵉ l4ᵉ Cᵉ = Subprecategoryᵉ l3ᵉ l4ᵉ (precategory-Categoryᵉ Cᵉ)
```

#### Objects in subcategories

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  (Pᵉ : Subcategoryᵉ l3ᵉ l4ᵉ Cᵉ)
  where

  subtype-obj-Subcategoryᵉ : subtypeᵉ l3ᵉ (obj-Categoryᵉ Cᵉ)
  subtype-obj-Subcategoryᵉ =
    subtype-obj-Subprecategoryᵉ (precategory-Categoryᵉ Cᵉ) Pᵉ

  obj-Subcategoryᵉ : UUᵉ (l1ᵉ ⊔ l3ᵉ)
  obj-Subcategoryᵉ = type-subtypeᵉ subtype-obj-Subcategoryᵉ

  inclusion-obj-Subcategoryᵉ : obj-Subcategoryᵉ → obj-Categoryᵉ Cᵉ
  inclusion-obj-Subcategoryᵉ = inclusion-subtypeᵉ subtype-obj-Subcategoryᵉ

  is-in-obj-Subcategoryᵉ : (xᵉ : obj-Categoryᵉ Cᵉ) → UUᵉ l3ᵉ
  is-in-obj-Subcategoryᵉ = is-in-subtypeᵉ subtype-obj-Subcategoryᵉ

  is-prop-is-in-obj-Subcategoryᵉ :
    (xᵉ : obj-Categoryᵉ Cᵉ) → is-propᵉ (is-in-obj-Subcategoryᵉ xᵉ)
  is-prop-is-in-obj-Subcategoryᵉ =
    is-prop-is-in-subtypeᵉ subtype-obj-Subcategoryᵉ

  is-in-obj-inclusion-obj-Subcategoryᵉ :
    (xᵉ : obj-Subcategoryᵉ) →
    is-in-obj-Subcategoryᵉ (inclusion-obj-Subcategoryᵉ xᵉ)
  is-in-obj-inclusion-obj-Subcategoryᵉ =
    is-in-subtype-inclusion-subtypeᵉ subtype-obj-Subcategoryᵉ
```

#### Morphisms in subcategories

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  (Pᵉ : Subcategoryᵉ l3ᵉ l4ᵉ Cᵉ)
  where

  subtype-hom-Subcategoryᵉ :
    subtype-hom-Categoryᵉ l4ᵉ Cᵉ (subtype-obj-Subcategoryᵉ Cᵉ Pᵉ)
  subtype-hom-Subcategoryᵉ =
    subtype-hom-Subprecategoryᵉ (precategory-Categoryᵉ Cᵉ) Pᵉ

  subtype-hom-obj-subcategory-Subcategoryᵉ :
    (xᵉ yᵉ : obj-Subcategoryᵉ Cᵉ Pᵉ) →
    subtypeᵉ l4ᵉ
      ( hom-Categoryᵉ Cᵉ
        ( inclusion-obj-Subcategoryᵉ Cᵉ Pᵉ xᵉ)
        ( inclusion-obj-Subcategoryᵉ Cᵉ Pᵉ yᵉ))
  subtype-hom-obj-subcategory-Subcategoryᵉ =
    subtype-hom-obj-subprecategory-Subprecategoryᵉ (precategory-Categoryᵉ Cᵉ) Pᵉ

  hom-Subcategoryᵉ : (xᵉ yᵉ : obj-Subcategoryᵉ Cᵉ Pᵉ) → UUᵉ (l2ᵉ ⊔ l4ᵉ)
  hom-Subcategoryᵉ xᵉ yᵉ =
    type-subtypeᵉ (subtype-hom-obj-subcategory-Subcategoryᵉ xᵉ yᵉ)

  inclusion-hom-Subcategoryᵉ :
    (xᵉ yᵉ : obj-Subcategoryᵉ Cᵉ Pᵉ) →
    hom-Subcategoryᵉ xᵉ yᵉ →
    hom-Categoryᵉ Cᵉ
      ( inclusion-obj-Subcategoryᵉ Cᵉ Pᵉ xᵉ)
      ( inclusion-obj-Subcategoryᵉ Cᵉ Pᵉ yᵉ)
  inclusion-hom-Subcategoryᵉ xᵉ yᵉ =
    inclusion-subtypeᵉ (subtype-hom-obj-subcategory-Subcategoryᵉ xᵉ yᵉ)
```

Theᵉ predicateᵉ onᵉ morphismsᵉ betweenᵉ subobjectsᵉ ofᵉ beingᵉ containedᵉ in theᵉ
subcategoryᵉ:

```agda
  is-in-hom-obj-subcategory-Subcategoryᵉ :
    ( xᵉ yᵉ : obj-Subcategoryᵉ Cᵉ Pᵉ) →
    hom-Categoryᵉ Cᵉ
      ( inclusion-obj-Subcategoryᵉ Cᵉ Pᵉ xᵉ)
      ( inclusion-obj-Subcategoryᵉ Cᵉ Pᵉ yᵉ) →
    UUᵉ l4ᵉ
  is-in-hom-obj-subcategory-Subcategoryᵉ xᵉ yᵉ =
    is-in-subtypeᵉ (subtype-hom-obj-subcategory-Subcategoryᵉ xᵉ yᵉ)

  is-prop-is-in-hom-obj-subcategory-Subcategoryᵉ :
    ( xᵉ yᵉ : obj-Subcategoryᵉ Cᵉ Pᵉ)
    ( fᵉ :
      hom-Categoryᵉ Cᵉ
        ( inclusion-obj-Subcategoryᵉ Cᵉ Pᵉ xᵉ)
        ( inclusion-obj-Subcategoryᵉ Cᵉ Pᵉ yᵉ)) →
    is-propᵉ (is-in-hom-obj-subcategory-Subcategoryᵉ xᵉ yᵉ fᵉ)
  is-prop-is-in-hom-obj-subcategory-Subcategoryᵉ xᵉ yᵉ =
    is-prop-is-in-subtypeᵉ (subtype-hom-obj-subcategory-Subcategoryᵉ xᵉ yᵉ)
```

Theᵉ predicateᵉ onᵉ morphismsᵉ betweenᵉ anyᵉ objectsᵉ ofᵉ beingᵉ containedᵉ in theᵉ
subcategoryᵉ:

```agda
  is-in-hom-Subcategoryᵉ :
    (xᵉ yᵉ : obj-Categoryᵉ Cᵉ) (fᵉ : hom-Categoryᵉ Cᵉ xᵉ yᵉ) → UUᵉ (l3ᵉ ⊔ l4ᵉ)
  is-in-hom-Subcategoryᵉ =
    is-in-hom-Subprecategoryᵉ (precategory-Categoryᵉ Cᵉ) Pᵉ

  is-prop-is-in-hom-Subcategoryᵉ :
    (xᵉ yᵉ : obj-Categoryᵉ Cᵉ) (fᵉ : hom-Categoryᵉ Cᵉ xᵉ yᵉ) →
    is-propᵉ (is-in-hom-Subcategoryᵉ xᵉ yᵉ fᵉ)
  is-prop-is-in-hom-Subcategoryᵉ =
    is-prop-is-in-hom-Subprecategoryᵉ (precategory-Categoryᵉ Cᵉ) Pᵉ

  is-in-hom-obj-subcategory-inclusion-hom-Subcategoryᵉ :
    (xᵉ yᵉ : obj-Subcategoryᵉ Cᵉ Pᵉ)
    (fᵉ : hom-Subcategoryᵉ xᵉ yᵉ) →
    is-in-hom-obj-subcategory-Subcategoryᵉ xᵉ yᵉ
      ( inclusion-hom-Subcategoryᵉ xᵉ yᵉ fᵉ)
  is-in-hom-obj-subcategory-inclusion-hom-Subcategoryᵉ =
    is-in-hom-obj-subprecategory-inclusion-hom-Subprecategoryᵉ
      ( precategory-Categoryᵉ Cᵉ) Pᵉ

  is-in-hom-inclusion-hom-Subcategoryᵉ :
    (xᵉ yᵉ : obj-Subcategoryᵉ Cᵉ Pᵉ)
    (fᵉ : hom-Subcategoryᵉ xᵉ yᵉ) →
    is-in-hom-Subcategoryᵉ
      ( inclusion-obj-Subcategoryᵉ Cᵉ Pᵉ xᵉ)
      ( inclusion-obj-Subcategoryᵉ Cᵉ Pᵉ yᵉ)
      ( inclusion-hom-Subcategoryᵉ xᵉ yᵉ fᵉ)
  is-in-hom-inclusion-hom-Subcategoryᵉ =
    is-in-hom-inclusion-hom-Subprecategoryᵉ (precategory-Categoryᵉ Cᵉ) Pᵉ
```

#### Subcategories are subcategories

```agda
  is-subcategory-Subcategoryᵉ :
    is-subcategoryᵉ Cᵉ
      ( subtype-obj-Subcategoryᵉ Cᵉ Pᵉ) (subtype-hom-Subcategoryᵉ)
  is-subcategory-Subcategoryᵉ =
    is-subprecategory-Subprecategoryᵉ (precategory-Categoryᵉ Cᵉ) Pᵉ

  contains-id-Subcategoryᵉ :
    contains-id-subtype-Categoryᵉ Cᵉ
      ( subtype-obj-Subcategoryᵉ Cᵉ Pᵉ)
      ( subtype-hom-Subcategoryᵉ)
  contains-id-Subcategoryᵉ =
    contains-id-Subprecategoryᵉ (precategory-Categoryᵉ Cᵉ) Pᵉ

  is-closed-under-composition-Subcategoryᵉ :
    is-closed-under-composition-subtype-Categoryᵉ Cᵉ
      ( subtype-obj-Subcategoryᵉ Cᵉ Pᵉ)
      ( subtype-hom-Subcategoryᵉ)
  is-closed-under-composition-Subcategoryᵉ =
    is-closed-under-composition-Subprecategoryᵉ (precategory-Categoryᵉ Cᵉ) Pᵉ
```

### The underlying precategory of a subcategory

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  (Pᵉ : Subcategoryᵉ l3ᵉ l4ᵉ Cᵉ)
  where

  hom-set-Subcategoryᵉ : (xᵉ yᵉ : obj-Subcategoryᵉ Cᵉ Pᵉ) → Setᵉ (l2ᵉ ⊔ l4ᵉ)
  hom-set-Subcategoryᵉ =
    hom-set-Subprecategoryᵉ (precategory-Categoryᵉ Cᵉ) Pᵉ

  is-set-hom-Subcategoryᵉ :
    (xᵉ yᵉ : obj-Subcategoryᵉ Cᵉ Pᵉ) → is-setᵉ (hom-Subcategoryᵉ Cᵉ Pᵉ xᵉ yᵉ)
  is-set-hom-Subcategoryᵉ xᵉ yᵉ = is-set-type-Setᵉ (hom-set-Subcategoryᵉ xᵉ yᵉ)

  id-hom-Subcategoryᵉ :
    {xᵉ : obj-Subcategoryᵉ Cᵉ Pᵉ} → hom-Subcategoryᵉ Cᵉ Pᵉ xᵉ xᵉ
  id-hom-Subcategoryᵉ =
    id-hom-Subprecategoryᵉ (precategory-Categoryᵉ Cᵉ) Pᵉ

  comp-hom-Subcategoryᵉ :
    {xᵉ yᵉ zᵉ : obj-Subcategoryᵉ Cᵉ Pᵉ} →
    hom-Subcategoryᵉ Cᵉ Pᵉ yᵉ zᵉ →
    hom-Subcategoryᵉ Cᵉ Pᵉ xᵉ yᵉ →
    hom-Subcategoryᵉ Cᵉ Pᵉ xᵉ zᵉ
  comp-hom-Subcategoryᵉ =
    comp-hom-Subprecategoryᵉ (precategory-Categoryᵉ Cᵉ) Pᵉ

  associative-comp-hom-Subcategoryᵉ :
    {xᵉ yᵉ zᵉ wᵉ : obj-Subcategoryᵉ Cᵉ Pᵉ}
    (hᵉ : hom-Subcategoryᵉ Cᵉ Pᵉ zᵉ wᵉ)
    (gᵉ : hom-Subcategoryᵉ Cᵉ Pᵉ yᵉ zᵉ)
    (fᵉ : hom-Subcategoryᵉ Cᵉ Pᵉ xᵉ yᵉ) →
    comp-hom-Subcategoryᵉ {xᵉ} {yᵉ} {wᵉ}
      ( comp-hom-Subcategoryᵉ {yᵉ} {zᵉ} {wᵉ} hᵉ gᵉ)
      ( fᵉ) ＝ᵉ
    comp-hom-Subcategoryᵉ {xᵉ} {zᵉ} {wᵉ}
      ( hᵉ)
      ( comp-hom-Subcategoryᵉ {xᵉ} {yᵉ} {zᵉ} gᵉ fᵉ)
  associative-comp-hom-Subcategoryᵉ =
    associative-comp-hom-Subprecategoryᵉ (precategory-Categoryᵉ Cᵉ) Pᵉ

  involutive-eq-associative-comp-hom-Subcategoryᵉ :
    {xᵉ yᵉ zᵉ wᵉ : obj-Subcategoryᵉ Cᵉ Pᵉ}
    (hᵉ : hom-Subcategoryᵉ Cᵉ Pᵉ zᵉ wᵉ)
    (gᵉ : hom-Subcategoryᵉ Cᵉ Pᵉ yᵉ zᵉ)
    (fᵉ : hom-Subcategoryᵉ Cᵉ Pᵉ xᵉ yᵉ) →
    comp-hom-Subcategoryᵉ {xᵉ} {yᵉ} {wᵉ}
      ( comp-hom-Subcategoryᵉ {yᵉ} {zᵉ} {wᵉ} hᵉ gᵉ)
      ( fᵉ) ＝ⁱᵉ
    comp-hom-Subcategoryᵉ {xᵉ} {zᵉ} {wᵉ}
      ( hᵉ)
      ( comp-hom-Subcategoryᵉ {xᵉ} {yᵉ} {zᵉ} gᵉ fᵉ)
  involutive-eq-associative-comp-hom-Subcategoryᵉ =
    involutive-eq-associative-comp-hom-Subprecategoryᵉ (precategory-Categoryᵉ Cᵉ) Pᵉ

  left-unit-law-comp-hom-Subcategoryᵉ :
    {xᵉ yᵉ : obj-Subcategoryᵉ Cᵉ Pᵉ}
    (fᵉ : hom-Subcategoryᵉ Cᵉ Pᵉ xᵉ yᵉ) →
    comp-hom-Subcategoryᵉ {xᵉ} {yᵉ} {yᵉ} (id-hom-Subcategoryᵉ {yᵉ}) fᵉ ＝ᵉ fᵉ
  left-unit-law-comp-hom-Subcategoryᵉ =
    left-unit-law-comp-hom-Subprecategoryᵉ (precategory-Categoryᵉ Cᵉ) Pᵉ

  right-unit-law-comp-hom-Subcategoryᵉ :
    {xᵉ yᵉ : obj-Subcategoryᵉ Cᵉ Pᵉ}
    (fᵉ : hom-Subcategoryᵉ Cᵉ Pᵉ xᵉ yᵉ) →
    comp-hom-Subcategoryᵉ {xᵉ} {xᵉ} {yᵉ} fᵉ (id-hom-Subcategoryᵉ {xᵉ}) ＝ᵉ fᵉ
  right-unit-law-comp-hom-Subcategoryᵉ =
    right-unit-law-comp-hom-Subprecategoryᵉ (precategory-Categoryᵉ Cᵉ) Pᵉ

  associative-composition-operation-Subcategoryᵉ :
    associative-composition-operation-binary-family-Setᵉ hom-set-Subcategoryᵉ
  associative-composition-operation-Subcategoryᵉ =
    associative-composition-operation-Subprecategoryᵉ (precategory-Categoryᵉ Cᵉ) Pᵉ

  is-unital-composition-operation-Subcategoryᵉ :
    is-unital-composition-operation-binary-family-Setᵉ
      ( hom-set-Subcategoryᵉ)
      ( comp-hom-Subcategoryᵉ)
  is-unital-composition-operation-Subcategoryᵉ =
    is-unital-composition-operation-Subprecategoryᵉ (precategory-Categoryᵉ Cᵉ) Pᵉ

  precategory-Subcategoryᵉ : Precategoryᵉ (l1ᵉ ⊔ l3ᵉ) (l2ᵉ ⊔ l4ᵉ)
  precategory-Subcategoryᵉ =
    precategory-Subprecategoryᵉ (precategory-Categoryᵉ Cᵉ) Pᵉ
```

### The inclusion functor of a subcategory

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  (Pᵉ : Subcategoryᵉ l3ᵉ l4ᵉ Cᵉ)
  where

  inclusion-map-Subcategoryᵉ :
    map-Precategoryᵉ (precategory-Subcategoryᵉ Cᵉ Pᵉ) (precategory-Categoryᵉ Cᵉ)
  inclusion-map-Subcategoryᵉ =
    inclusion-map-Subprecategoryᵉ (precategory-Categoryᵉ Cᵉ) Pᵉ

  is-functor-inclusion-Subcategoryᵉ :
    is-functor-map-Precategoryᵉ
      ( precategory-Subcategoryᵉ Cᵉ Pᵉ)
      ( precategory-Categoryᵉ Cᵉ)
      ( inclusion-map-Subcategoryᵉ)
  is-functor-inclusion-Subcategoryᵉ =
    is-functor-inclusion-Subprecategoryᵉ (precategory-Categoryᵉ Cᵉ) Pᵉ

  inclusion-Subcategoryᵉ :
    functor-Precategoryᵉ (precategory-Subcategoryᵉ Cᵉ Pᵉ) (precategory-Categoryᵉ Cᵉ)
  inclusion-Subcategoryᵉ = inclusion-Subprecategoryᵉ (precategory-Categoryᵉ Cᵉ) Pᵉ
```

## Properties

### Subcategories are replete

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  (Pᵉ : Subcategoryᵉ l3ᵉ l4ᵉ Cᵉ)
  where

  is-replete-Subcategoryᵉ : is-replete-Subprecategoryᵉ (precategory-Categoryᵉ Cᵉ) Pᵉ
  is-replete-Subcategoryᵉ =
    is-replete-subprecategory-is-category-Subprecategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( Pᵉ)
      ( is-category-Categoryᵉ Cᵉ)

  compute-iso-Subcategoryᵉ :
    {xᵉ yᵉ : obj-Subcategoryᵉ Cᵉ Pᵉ} →
    iso-Categoryᵉ Cᵉ
      ( inclusion-obj-Subcategoryᵉ Cᵉ Pᵉ xᵉ)
      ( inclusion-obj-Subcategoryᵉ Cᵉ Pᵉ yᵉ) ≃ᵉ
    iso-Subprecategoryᵉ (precategory-Categoryᵉ Cᵉ) Pᵉ xᵉ yᵉ
  compute-iso-Subcategoryᵉ {xᵉ} {yᵉ} =
    compute-iso-is-replete-Subprecategoryᵉ
      ( precategory-Categoryᵉ Cᵉ) Pᵉ is-replete-Subcategoryᵉ xᵉ yᵉ

  inv-compute-iso-Subcategoryᵉ :
    {xᵉ yᵉ : obj-Subcategoryᵉ Cᵉ Pᵉ} →
    iso-Subprecategoryᵉ (precategory-Categoryᵉ Cᵉ) Pᵉ xᵉ yᵉ ≃ᵉ
    iso-Categoryᵉ Cᵉ
      ( inclusion-obj-Subcategoryᵉ Cᵉ Pᵉ xᵉ)
      ( inclusion-obj-Subcategoryᵉ Cᵉ Pᵉ yᵉ)
  inv-compute-iso-Subcategoryᵉ {xᵉ} {yᵉ} =
    inv-compute-iso-is-replete-Subprecategoryᵉ
      ( precategory-Categoryᵉ Cᵉ) Pᵉ is-replete-Subcategoryᵉ xᵉ yᵉ
```

### Subcategories are categories

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  (Pᵉ : Subcategoryᵉ l3ᵉ l4ᵉ Cᵉ)
  where

  is-category-Subcategoryᵉ :
    is-category-Precategoryᵉ (precategory-Subcategoryᵉ Cᵉ Pᵉ)
  is-category-Subcategoryᵉ xᵉ =
    fundamental-theorem-idᵉ
      ( is-contr-equivᵉ _
        ( equiv-totᵉ (λ yᵉ → inv-compute-iso-Subcategoryᵉ Cᵉ Pᵉ {xᵉ} {yᵉ}))
        ( is-torsorial-Eq-subtypeᵉ
          ( is-torsorial-iso-Categoryᵉ Cᵉ (inclusion-obj-Subcategoryᵉ Cᵉ Pᵉ xᵉ))
          ( is-prop-is-in-obj-Subcategoryᵉ Cᵉ Pᵉ)
          ( inclusion-obj-Subcategoryᵉ Cᵉ Pᵉ xᵉ)
          ( id-iso-Categoryᵉ Cᵉ)
          ( is-in-obj-inclusion-obj-Subcategoryᵉ Cᵉ Pᵉ xᵉ)))
      ( iso-eq-Precategoryᵉ (precategory-Subcategoryᵉ Cᵉ Pᵉ) xᵉ)

  category-Subcategoryᵉ : Categoryᵉ (l1ᵉ ⊔ l3ᵉ) (l2ᵉ ⊔ l4ᵉ)
  pr1ᵉ category-Subcategoryᵉ = precategory-Subcategoryᵉ Cᵉ Pᵉ
  pr2ᵉ category-Subcategoryᵉ = is-category-Subcategoryᵉ
```

### The inclusion functor is an embedding on objects and hom-sets

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  (Pᵉ : Subcategoryᵉ l3ᵉ l4ᵉ Cᵉ)
  where

  is-faithful-inclusion-Subcategoryᵉ :
    is-faithful-functor-Precategoryᵉ
      ( precategory-Subcategoryᵉ Cᵉ Pᵉ)
      ( precategory-Categoryᵉ Cᵉ)
      ( inclusion-Subcategoryᵉ Cᵉ Pᵉ)
  is-faithful-inclusion-Subcategoryᵉ =
    is-faithful-inclusion-Subprecategoryᵉ (precategory-Categoryᵉ Cᵉ) Pᵉ

  is-emb-obj-inclusion-Subcategoryᵉ :
    is-embᵉ
      ( obj-functor-Precategoryᵉ
        ( precategory-Subcategoryᵉ Cᵉ Pᵉ)
        ( precategory-Categoryᵉ Cᵉ)
        ( inclusion-Subcategoryᵉ Cᵉ Pᵉ))
  is-emb-obj-inclusion-Subcategoryᵉ =
    is-emb-obj-inclusion-Subprecategoryᵉ (precategory-Categoryᵉ Cᵉ) Pᵉ
```

### The inclusion functor is pseudomonic

Thisᵉ isᵉ anotherᵉ consequenceᵉ ofᵉ repleteness.ᵉ

## External links

-ᵉ [Univalentᵉ Subcategories](https://1lab.dev/Cat.Functor.Subcategory.html#univalent-subcategoriesᵉ)
  atᵉ 1labᵉ