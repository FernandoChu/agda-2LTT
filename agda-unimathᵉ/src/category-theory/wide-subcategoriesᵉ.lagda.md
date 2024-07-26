# Wide subcategories

```agda
module category-theory.wide-subcategoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categoriesᵉ
open import category-theory.composition-operations-on-binary-families-of-setsᵉ
open import category-theory.faithful-functors-precategoriesᵉ
open import category-theory.functors-categoriesᵉ
open import category-theory.isomorphisms-in-categoriesᵉ
open import category-theory.isomorphisms-in-precategoriesᵉ
open import category-theory.maps-categoriesᵉ
open import category-theory.precategoriesᵉ
open import category-theory.subcategoriesᵉ
open import category-theory.wide-subprecategoriesᵉ

open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.iterated-dependent-product-typesᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.strictly-involutive-identity-typesᵉ
open import foundation.subtypesᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Aᵉ **wideᵉ subcategory**ᵉ ofᵉ aᵉ [category](category-theory.categories.mdᵉ) `C`ᵉ isᵉ aᵉ
[subcategory](category-theory.subcategories.mdᵉ) thatᵉ containsᵉ allᵉ theᵉ objectsᵉ ofᵉ
`C`.ᵉ

## Lemma

### Wide subprecategories of categories are categories

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Pᵉ : Wide-Subprecategoryᵉ l3ᵉ Cᵉ)
  (is-category-Cᵉ : is-category-Precategoryᵉ Cᵉ)
  where

  is-category-is-category-Wide-Subprecategoryᵉ :
    is-category-Precategoryᵉ (precategory-Wide-Subprecategoryᵉ Cᵉ Pᵉ)
  is-category-is-category-Wide-Subprecategoryᵉ xᵉ =
    fundamental-theorem-idᵉ
      ( is-contr-equivᵉ _
        ( equiv-totᵉ
          ( λ yᵉ →
            inv-compute-iso-Subcategoryᵉ
              ( Cᵉ ,ᵉ is-category-Cᵉ)
              ( subprecategory-Wide-Subprecategoryᵉ Cᵉ Pᵉ)))
        ( is-torsorial-iso-Categoryᵉ (Cᵉ ,ᵉ is-category-Cᵉ) xᵉ))
      ( iso-eq-Precategoryᵉ (precategory-Wide-Subprecategoryᵉ Cᵉ Pᵉ) xᵉ)
```

## Definitions

### The predicate of being a wide subcategory

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  (Pᵉ : Subcategoryᵉ l3ᵉ l4ᵉ Cᵉ)
  where

  is-wide-prop-Subcategoryᵉ : Propᵉ (l1ᵉ ⊔ l3ᵉ)
  is-wide-prop-Subcategoryᵉ =
    is-wide-prop-Subprecategoryᵉ (precategory-Categoryᵉ Cᵉ) Pᵉ

  is-wide-Subcategoryᵉ : UUᵉ (l1ᵉ ⊔ l3ᵉ)
  is-wide-Subcategoryᵉ = type-Propᵉ is-wide-prop-Subcategoryᵉ

  is-prop-is-wide-Subcategoryᵉ : is-propᵉ (is-wide-Subcategoryᵉ)
  is-prop-is-wide-Subcategoryᵉ = is-prop-type-Propᵉ is-wide-prop-Subcategoryᵉ
```

### wide sub-hom-families of categories

```agda
module _
  {l1ᵉ l2ᵉ : Level} (l3ᵉ : Level)
  (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  where

  subtype-hom-wide-Categoryᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ lsuc l3ᵉ)
  subtype-hom-wide-Categoryᵉ =
    (xᵉ yᵉ : obj-Categoryᵉ Cᵉ) → subtypeᵉ l3ᵉ (hom-Categoryᵉ Cᵉ xᵉ yᵉ)
```

### Categorical predicates on wide sub-hom-families

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level}
  (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  (P₁ᵉ : subtype-hom-wide-Categoryᵉ l3ᵉ Cᵉ)
  where

  contains-id-prop-subtype-hom-wide-Categoryᵉ : Propᵉ (l1ᵉ ⊔ l3ᵉ)
  contains-id-prop-subtype-hom-wide-Categoryᵉ =
    Π-Propᵉ (obj-Categoryᵉ Cᵉ) (λ xᵉ → P₁ᵉ xᵉ xᵉ (id-hom-Categoryᵉ Cᵉ))

  contains-id-subtype-hom-wide-Categoryᵉ : UUᵉ (l1ᵉ ⊔ l3ᵉ)
  contains-id-subtype-hom-wide-Categoryᵉ =
    type-Propᵉ contains-id-prop-subtype-hom-wide-Categoryᵉ

  is-prop-contains-id-subtype-hom-wide-Categoryᵉ :
    is-propᵉ contains-id-subtype-hom-wide-Categoryᵉ
  is-prop-contains-id-subtype-hom-wide-Categoryᵉ =
    is-prop-type-Propᵉ contains-id-prop-subtype-hom-wide-Categoryᵉ

  is-closed-under-composition-subtype-hom-wide-Categoryᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  is-closed-under-composition-subtype-hom-wide-Categoryᵉ =
    (xᵉ yᵉ zᵉ : obj-Categoryᵉ Cᵉ) →
    (gᵉ : hom-Categoryᵉ Cᵉ yᵉ zᵉ) →
    (fᵉ : hom-Categoryᵉ Cᵉ xᵉ yᵉ) →
    is-in-subtypeᵉ (P₁ᵉ yᵉ zᵉ) gᵉ →
    is-in-subtypeᵉ (P₁ᵉ xᵉ yᵉ) fᵉ →
    is-in-subtypeᵉ (P₁ᵉ xᵉ zᵉ) (comp-hom-Categoryᵉ Cᵉ gᵉ fᵉ)

  is-prop-is-closed-under-composition-subtype-hom-wide-Categoryᵉ :
    is-propᵉ is-closed-under-composition-subtype-hom-wide-Categoryᵉ
  is-prop-is-closed-under-composition-subtype-hom-wide-Categoryᵉ =
    is-prop-iterated-Πᵉ 7
      ( λ xᵉ yᵉ zᵉ gᵉ fᵉ _ _ →
        is-prop-is-in-subtypeᵉ (P₁ᵉ xᵉ zᵉ) (comp-hom-Categoryᵉ Cᵉ gᵉ fᵉ))

  is-closed-under-composition-prop-subtype-hom-wide-Categoryᵉ :
    Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  pr1ᵉ is-closed-under-composition-prop-subtype-hom-wide-Categoryᵉ =
    is-closed-under-composition-subtype-hom-wide-Categoryᵉ
  pr2ᵉ is-closed-under-composition-prop-subtype-hom-wide-Categoryᵉ =
    is-prop-is-closed-under-composition-subtype-hom-wide-Categoryᵉ
```

### The predicate on subtypes of hom-sets of being a wide subcategory

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level}
  (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  (P₁ᵉ : subtype-hom-wide-Categoryᵉ l3ᵉ Cᵉ)
  where

  is-wide-subcategory-Propᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  is-wide-subcategory-Propᵉ =
    product-Propᵉ
      ( contains-id-prop-subtype-hom-wide-Categoryᵉ Cᵉ P₁ᵉ)
      ( is-closed-under-composition-prop-subtype-hom-wide-Categoryᵉ Cᵉ P₁ᵉ)

  is-wide-subcategoryᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  is-wide-subcategoryᵉ = type-Propᵉ is-wide-subcategory-Propᵉ

  is-prop-is-wide-subcategoryᵉ : is-propᵉ (is-wide-subcategoryᵉ)
  is-prop-is-wide-subcategoryᵉ = is-prop-type-Propᵉ is-wide-subcategory-Propᵉ

  contains-id-is-wide-subcategoryᵉ :
    is-wide-subcategoryᵉ → contains-id-subtype-hom-wide-Categoryᵉ Cᵉ P₁ᵉ
  contains-id-is-wide-subcategoryᵉ = pr1ᵉ

  is-closed-under-composition-is-wide-subcategoryᵉ :
    is-wide-subcategoryᵉ →
    is-closed-under-composition-subtype-hom-wide-Categoryᵉ Cᵉ P₁ᵉ
  is-closed-under-composition-is-wide-subcategoryᵉ = pr2ᵉ
```

### Wide subcategories

```agda
Wide-Subcategoryᵉ :
  {l1ᵉ l2ᵉ : Level} (l3ᵉ : Level)
  (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ) →
  UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ lsuc l3ᵉ)
Wide-Subcategoryᵉ l3ᵉ Cᵉ =
  Σᵉ (subtype-hom-wide-Categoryᵉ l3ᵉ Cᵉ) (is-wide-subcategoryᵉ Cᵉ)
```

#### Objects in wide subcategories

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level}
  (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  (Pᵉ : Wide-Subcategoryᵉ l3ᵉ Cᵉ)
  where

  subtype-obj-Wide-Subcategoryᵉ : subtypeᵉ lzero (obj-Categoryᵉ Cᵉ)
  subtype-obj-Wide-Subcategoryᵉ _ = unit-Propᵉ

  obj-Wide-Subcategoryᵉ : UUᵉ l1ᵉ
  obj-Wide-Subcategoryᵉ = obj-Categoryᵉ Cᵉ

  inclusion-obj-Wide-Subcategoryᵉ :
    obj-Wide-Subcategoryᵉ → obj-Categoryᵉ Cᵉ
  inclusion-obj-Wide-Subcategoryᵉ = idᵉ
```

#### Morphisms in wide subcategories

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level}
  (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  (Pᵉ : Wide-Subcategoryᵉ l3ᵉ Cᵉ)
  where

  subtype-hom-Wide-Subcategoryᵉ : subtype-hom-wide-Categoryᵉ l3ᵉ Cᵉ
  subtype-hom-Wide-Subcategoryᵉ = pr1ᵉ Pᵉ

  hom-Wide-Subcategoryᵉ : (xᵉ yᵉ : obj-Wide-Subcategoryᵉ Cᵉ Pᵉ) → UUᵉ (l2ᵉ ⊔ l3ᵉ)
  hom-Wide-Subcategoryᵉ xᵉ yᵉ =
    type-subtypeᵉ (subtype-hom-Wide-Subcategoryᵉ xᵉ yᵉ)

  inclusion-hom-Wide-Subcategoryᵉ :
    (xᵉ yᵉ : obj-Wide-Subcategoryᵉ Cᵉ Pᵉ) →
    hom-Wide-Subcategoryᵉ xᵉ yᵉ →
    hom-Categoryᵉ Cᵉ
      ( inclusion-obj-Wide-Subcategoryᵉ Cᵉ Pᵉ xᵉ)
      ( inclusion-obj-Wide-Subcategoryᵉ Cᵉ Pᵉ yᵉ)
  inclusion-hom-Wide-Subcategoryᵉ xᵉ yᵉ =
    inclusion-subtypeᵉ (subtype-hom-Wide-Subcategoryᵉ xᵉ yᵉ)
```

Theᵉ predicateᵉ onᵉ morphismsᵉ betweenᵉ anyᵉ objectsᵉ ofᵉ beingᵉ containedᵉ in theᵉ wideᵉ
subcategoryᵉ:

```agda
  is-in-hom-Wide-Subcategoryᵉ :
    (xᵉ yᵉ : obj-Categoryᵉ Cᵉ) (fᵉ : hom-Categoryᵉ Cᵉ xᵉ yᵉ) → UUᵉ l3ᵉ
  is-in-hom-Wide-Subcategoryᵉ xᵉ yᵉ =
    is-in-subtypeᵉ (subtype-hom-Wide-Subcategoryᵉ xᵉ yᵉ)

  is-prop-is-in-hom-Wide-Subcategoryᵉ :
    (xᵉ yᵉ : obj-Categoryᵉ Cᵉ) (fᵉ : hom-Categoryᵉ Cᵉ xᵉ yᵉ) →
    is-propᵉ (is-in-hom-Wide-Subcategoryᵉ xᵉ yᵉ fᵉ)
  is-prop-is-in-hom-Wide-Subcategoryᵉ xᵉ yᵉ =
    is-prop-is-in-subtypeᵉ (subtype-hom-Wide-Subcategoryᵉ xᵉ yᵉ)

  is-in-hom-inclusion-hom-Wide-Subcategoryᵉ :
    (xᵉ yᵉ : obj-Wide-Subcategoryᵉ Cᵉ Pᵉ)
    (fᵉ : hom-Wide-Subcategoryᵉ xᵉ yᵉ) →
    is-in-hom-Wide-Subcategoryᵉ
      ( inclusion-obj-Wide-Subcategoryᵉ Cᵉ Pᵉ xᵉ)
      ( inclusion-obj-Wide-Subcategoryᵉ Cᵉ Pᵉ yᵉ)
      ( inclusion-hom-Wide-Subcategoryᵉ xᵉ yᵉ fᵉ)
  is-in-hom-inclusion-hom-Wide-Subcategoryᵉ xᵉ yᵉ =
    is-in-subtype-inclusion-subtypeᵉ (subtype-hom-Wide-Subcategoryᵉ xᵉ yᵉ)
```

Wideᵉ subcategoriesᵉ areᵉ wideᵉ subcategoriesᵉ:

```agda
  is-wide-subcategory-Wide-Subcategoryᵉ :
    is-wide-subcategoryᵉ Cᵉ subtype-hom-Wide-Subcategoryᵉ
  is-wide-subcategory-Wide-Subcategoryᵉ = pr2ᵉ Pᵉ

  contains-id-Wide-Subcategoryᵉ :
    contains-id-subtype-hom-wide-Categoryᵉ Cᵉ
      ( subtype-hom-Wide-Subcategoryᵉ)
  contains-id-Wide-Subcategoryᵉ =
    contains-id-is-wide-subcategoryᵉ Cᵉ
      ( subtype-hom-Wide-Subcategoryᵉ)
      ( is-wide-subcategory-Wide-Subcategoryᵉ)

  is-closed-under-composition-Wide-Subcategoryᵉ :
    is-closed-under-composition-subtype-hom-wide-Categoryᵉ Cᵉ
      ( subtype-hom-Wide-Subcategoryᵉ)
  is-closed-under-composition-Wide-Subcategoryᵉ =
    is-closed-under-composition-is-wide-subcategoryᵉ Cᵉ
      ( subtype-hom-Wide-Subcategoryᵉ)
      ( is-wide-subcategory-Wide-Subcategoryᵉ)
```

Wideᵉ subcategoriesᵉ areᵉ subcategoriesᵉ:

```agda
  subtype-hom-subcategory-Wide-Subcategoryᵉ :
    subtype-hom-Categoryᵉ l3ᵉ Cᵉ (subtype-obj-Wide-Subcategoryᵉ Cᵉ Pᵉ)
  subtype-hom-subcategory-Wide-Subcategoryᵉ =
    subtype-hom-subprecategory-Wide-Subprecategoryᵉ (precategory-Categoryᵉ Cᵉ) Pᵉ

  is-subcategory-Wide-Subcategoryᵉ :
    is-subcategoryᵉ Cᵉ
      ( subtype-obj-Wide-Subcategoryᵉ Cᵉ Pᵉ)
      ( subtype-hom-subcategory-Wide-Subcategoryᵉ)
  is-subcategory-Wide-Subcategoryᵉ =
    is-subprecategory-Wide-Subprecategoryᵉ (precategory-Categoryᵉ Cᵉ) Pᵉ

  subcategory-Wide-Subcategoryᵉ : Subcategoryᵉ lzero l3ᵉ Cᵉ
  subcategory-Wide-Subcategoryᵉ =
    subprecategory-Wide-Subprecategoryᵉ (precategory-Categoryᵉ Cᵉ) Pᵉ

  is-wide-Wide-Subcategoryᵉ :
    is-wide-Subcategoryᵉ Cᵉ (subcategory-Wide-Subcategoryᵉ)
  is-wide-Wide-Subcategoryᵉ =
    is-wide-Wide-Subprecategoryᵉ (precategory-Categoryᵉ Cᵉ) Pᵉ
```

### The underlying category of a wide subcategory

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level}
  (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  (Pᵉ : Wide-Subcategoryᵉ l3ᵉ Cᵉ)
  where

  hom-set-Wide-Subcategoryᵉ :
    (xᵉ yᵉ : obj-Wide-Subcategoryᵉ Cᵉ Pᵉ) → Setᵉ (l2ᵉ ⊔ l3ᵉ)
  hom-set-Wide-Subcategoryᵉ =
    hom-set-Wide-Subprecategoryᵉ (precategory-Categoryᵉ Cᵉ) Pᵉ

  is-set-hom-Wide-Subcategoryᵉ :
    (xᵉ yᵉ : obj-Wide-Subcategoryᵉ Cᵉ Pᵉ) →
    is-setᵉ (hom-Wide-Subcategoryᵉ Cᵉ Pᵉ xᵉ yᵉ)
  is-set-hom-Wide-Subcategoryᵉ =
    is-set-hom-Wide-Subprecategoryᵉ (precategory-Categoryᵉ Cᵉ) Pᵉ

  id-hom-Wide-Subcategoryᵉ :
    {xᵉ : obj-Wide-Subcategoryᵉ Cᵉ Pᵉ} → hom-Wide-Subcategoryᵉ Cᵉ Pᵉ xᵉ xᵉ
  id-hom-Wide-Subcategoryᵉ =
    id-hom-Wide-Subprecategoryᵉ (precategory-Categoryᵉ Cᵉ) Pᵉ

  comp-hom-Wide-Subcategoryᵉ :
    {xᵉ yᵉ zᵉ : obj-Wide-Subcategoryᵉ Cᵉ Pᵉ} →
    hom-Wide-Subcategoryᵉ Cᵉ Pᵉ yᵉ zᵉ →
    hom-Wide-Subcategoryᵉ Cᵉ Pᵉ xᵉ yᵉ →
    hom-Wide-Subcategoryᵉ Cᵉ Pᵉ xᵉ zᵉ
  comp-hom-Wide-Subcategoryᵉ =
    comp-hom-Wide-Subprecategoryᵉ (precategory-Categoryᵉ Cᵉ) Pᵉ

  associative-comp-hom-Wide-Subcategoryᵉ :
    {xᵉ yᵉ zᵉ wᵉ : obj-Wide-Subcategoryᵉ Cᵉ Pᵉ}
    (hᵉ : hom-Wide-Subcategoryᵉ Cᵉ Pᵉ zᵉ wᵉ)
    (gᵉ : hom-Wide-Subcategoryᵉ Cᵉ Pᵉ yᵉ zᵉ)
    (fᵉ : hom-Wide-Subcategoryᵉ Cᵉ Pᵉ xᵉ yᵉ) →
    comp-hom-Wide-Subcategoryᵉ (comp-hom-Wide-Subcategoryᵉ hᵉ gᵉ) fᵉ ＝ᵉ
    comp-hom-Wide-Subcategoryᵉ hᵉ (comp-hom-Wide-Subcategoryᵉ gᵉ fᵉ)
  associative-comp-hom-Wide-Subcategoryᵉ =
    associative-comp-hom-Wide-Subprecategoryᵉ (precategory-Categoryᵉ Cᵉ) Pᵉ

  involutive-eq-associative-comp-hom-Wide-Subcategoryᵉ :
    {xᵉ yᵉ zᵉ wᵉ : obj-Wide-Subcategoryᵉ Cᵉ Pᵉ}
    (hᵉ : hom-Wide-Subcategoryᵉ Cᵉ Pᵉ zᵉ wᵉ)
    (gᵉ : hom-Wide-Subcategoryᵉ Cᵉ Pᵉ yᵉ zᵉ)
    (fᵉ : hom-Wide-Subcategoryᵉ Cᵉ Pᵉ xᵉ yᵉ) →
    comp-hom-Wide-Subcategoryᵉ (comp-hom-Wide-Subcategoryᵉ hᵉ gᵉ) fᵉ ＝ⁱᵉ
    comp-hom-Wide-Subcategoryᵉ hᵉ (comp-hom-Wide-Subcategoryᵉ gᵉ fᵉ)
  involutive-eq-associative-comp-hom-Wide-Subcategoryᵉ =
    involutive-eq-associative-comp-hom-Wide-Subprecategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( Pᵉ)

  left-unit-law-comp-hom-Wide-Subcategoryᵉ :
    {xᵉ yᵉ : obj-Wide-Subcategoryᵉ Cᵉ Pᵉ}
    (fᵉ : hom-Wide-Subcategoryᵉ Cᵉ Pᵉ xᵉ yᵉ) →
    comp-hom-Wide-Subcategoryᵉ (id-hom-Wide-Subcategoryᵉ) fᵉ ＝ᵉ fᵉ
  left-unit-law-comp-hom-Wide-Subcategoryᵉ =
    left-unit-law-comp-hom-Wide-Subprecategoryᵉ (precategory-Categoryᵉ Cᵉ) Pᵉ

  right-unit-law-comp-hom-Wide-Subcategoryᵉ :
    {xᵉ yᵉ : obj-Wide-Subcategoryᵉ Cᵉ Pᵉ}
    (fᵉ : hom-Wide-Subcategoryᵉ Cᵉ Pᵉ xᵉ yᵉ) →
    comp-hom-Wide-Subcategoryᵉ fᵉ (id-hom-Wide-Subcategoryᵉ) ＝ᵉ fᵉ
  right-unit-law-comp-hom-Wide-Subcategoryᵉ =
    right-unit-law-comp-hom-Wide-Subprecategoryᵉ (precategory-Categoryᵉ Cᵉ) Pᵉ

  associative-composition-operation-Wide-Subcategoryᵉ :
    associative-composition-operation-binary-family-Setᵉ
      ( hom-set-Wide-Subcategoryᵉ)
  associative-composition-operation-Wide-Subcategoryᵉ =
    associative-composition-operation-Wide-Subprecategoryᵉ
      ( precategory-Categoryᵉ Cᵉ) Pᵉ

  is-unital-composition-operation-Wide-Subcategoryᵉ :
    is-unital-composition-operation-binary-family-Setᵉ
      ( hom-set-Wide-Subcategoryᵉ)
      ( comp-hom-Wide-Subcategoryᵉ)
  is-unital-composition-operation-Wide-Subcategoryᵉ =
    is-unital-composition-operation-Wide-Subprecategoryᵉ
      ( precategory-Categoryᵉ Cᵉ) Pᵉ

  precategory-Wide-Subcategoryᵉ : Precategoryᵉ l1ᵉ (l2ᵉ ⊔ l3ᵉ)
  precategory-Wide-Subcategoryᵉ =
    precategory-Wide-Subprecategoryᵉ (precategory-Categoryᵉ Cᵉ) Pᵉ
```

### The underlying category of a wide subcategory

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level}
  (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  (Pᵉ : Wide-Subcategoryᵉ l3ᵉ Cᵉ)
  where

  category-Wide-Subcategoryᵉ : Categoryᵉ l1ᵉ (l2ᵉ ⊔ l3ᵉ)
  pr1ᵉ category-Wide-Subcategoryᵉ = precategory-Wide-Subcategoryᵉ Cᵉ Pᵉ
  pr2ᵉ category-Wide-Subcategoryᵉ =
    is-category-is-category-Wide-Subprecategoryᵉ
      ( precategory-Categoryᵉ Cᵉ) Pᵉ (is-category-Categoryᵉ Cᵉ)
```

### The inclusion functor of a wide subcategory

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level}
  (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  (Pᵉ : Wide-Subcategoryᵉ l3ᵉ Cᵉ)
  where

  inclusion-map-Wide-Subcategoryᵉ :
    map-Categoryᵉ (category-Wide-Subcategoryᵉ Cᵉ Pᵉ) Cᵉ
  inclusion-map-Wide-Subcategoryᵉ =
    inclusion-map-Wide-Subprecategoryᵉ (precategory-Categoryᵉ Cᵉ) Pᵉ

  is-functor-inclusion-Wide-Subcategoryᵉ :
    is-functor-map-Categoryᵉ
      ( category-Wide-Subcategoryᵉ Cᵉ Pᵉ)
      ( Cᵉ)
      ( inclusion-map-Wide-Subcategoryᵉ)
  is-functor-inclusion-Wide-Subcategoryᵉ =
    is-functor-inclusion-Wide-Subprecategoryᵉ (precategory-Categoryᵉ Cᵉ) Pᵉ

  inclusion-Wide-Subcategoryᵉ :
    functor-Categoryᵉ (category-Wide-Subcategoryᵉ Cᵉ Pᵉ) Cᵉ
  inclusion-Wide-Subcategoryᵉ =
    inclusion-Wide-Subprecategoryᵉ (precategory-Categoryᵉ Cᵉ) Pᵉ
```

## Properties

### The inclusion functor is faithful and an equivalence on objects

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level}
  (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  (Pᵉ : Wide-Subcategoryᵉ l3ᵉ Cᵉ)
  where

  is-faithful-inclusion-Wide-Subcategoryᵉ :
    is-faithful-functor-Precategoryᵉ
      ( precategory-Wide-Subcategoryᵉ Cᵉ Pᵉ)
      ( precategory-Categoryᵉ Cᵉ)
      ( inclusion-Wide-Subcategoryᵉ Cᵉ Pᵉ)
  is-faithful-inclusion-Wide-Subcategoryᵉ =
    is-faithful-inclusion-Wide-Subprecategoryᵉ (precategory-Categoryᵉ Cᵉ) Pᵉ

  is-equiv-obj-inclusion-Wide-Subcategoryᵉ :
    is-equivᵉ
      ( obj-functor-Categoryᵉ
        ( category-Wide-Subcategoryᵉ Cᵉ Pᵉ)
        ( Cᵉ)
        ( inclusion-Wide-Subcategoryᵉ Cᵉ Pᵉ))
  is-equiv-obj-inclusion-Wide-Subcategoryᵉ =
    is-equiv-obj-inclusion-Wide-Subprecategoryᵉ (precategory-Categoryᵉ Cᵉ) Pᵉ
```

### The inclusion functor is pseudomonic

Thisᵉ remainsᵉ to beᵉ formalized.ᵉ Thisᵉ isᵉ aᵉ consequenceᵉ ofᵉ repeleteness.ᵉ

## External links

-ᵉ [Wideᵉ subcategories](https://1lab.dev/Cat.Functor.WideSubcategory.htmlᵉ) atᵉ
  1labᵉ
-ᵉ [wideᵉ subcategory](https://ncatlab.org/nlab/show/wide+subcategoryᵉ) atᵉ $n$Labᵉ