# Wide subprecategories

```agda
module category-theory.wide-subprecategoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.composition-operations-on-binary-families-of-setsᵉ
open import category-theory.faithful-functors-precategoriesᵉ
open import category-theory.functors-precategoriesᵉ
open import category-theory.maps-precategoriesᵉ
open import category-theory.precategoriesᵉ
open import category-theory.subprecategoriesᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
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

Aᵉ **wideᵉ subprecategory**ᵉ ofᵉ aᵉ [precategory](category-theory.precategories.mdᵉ)
`C`ᵉ isᵉ aᵉ [subprecategory](category-theory.subprecategories.mdᵉ) thatᵉ containsᵉ allᵉ
theᵉ objectsᵉ ofᵉ `C`.ᵉ

## Definitions

### The predicate of being a wide subprecategory

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Pᵉ : Subprecategoryᵉ l3ᵉ l4ᵉ Cᵉ)
  where

  is-wide-prop-Subprecategoryᵉ : Propᵉ (l1ᵉ ⊔ l3ᵉ)
  is-wide-prop-Subprecategoryᵉ =
    Π-Propᵉ (obj-Precategoryᵉ Cᵉ) (subtype-obj-Subprecategoryᵉ Cᵉ Pᵉ)

  is-wide-Subprecategoryᵉ : UUᵉ (l1ᵉ ⊔ l3ᵉ)
  is-wide-Subprecategoryᵉ = type-Propᵉ is-wide-prop-Subprecategoryᵉ

  is-prop-is-wide-Subprecategoryᵉ : is-propᵉ (is-wide-Subprecategoryᵉ)
  is-prop-is-wide-Subprecategoryᵉ = is-prop-type-Propᵉ is-wide-prop-Subprecategoryᵉ
```

### Wide sub-hom-families of precategories

```agda
module _
  {l1ᵉ l2ᵉ : Level} (l3ᵉ : Level)
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  where

  subtype-hom-wide-Precategoryᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ lsuc l3ᵉ)
  subtype-hom-wide-Precategoryᵉ =
    (xᵉ yᵉ : obj-Precategoryᵉ Cᵉ) → subtypeᵉ l3ᵉ (hom-Precategoryᵉ Cᵉ xᵉ yᵉ)
```

### Categorical predicates on wide sub-hom-families

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (P₁ᵉ : subtype-hom-wide-Precategoryᵉ l3ᵉ Cᵉ)
  where

  contains-id-prop-subtype-hom-wide-Precategoryᵉ : Propᵉ (l1ᵉ ⊔ l3ᵉ)
  contains-id-prop-subtype-hom-wide-Precategoryᵉ =
    Π-Propᵉ (obj-Precategoryᵉ Cᵉ) (λ xᵉ → P₁ᵉ xᵉ xᵉ (id-hom-Precategoryᵉ Cᵉ))

  contains-id-subtype-hom-wide-Precategoryᵉ : UUᵉ (l1ᵉ ⊔ l3ᵉ)
  contains-id-subtype-hom-wide-Precategoryᵉ =
    type-Propᵉ contains-id-prop-subtype-hom-wide-Precategoryᵉ

  is-prop-contains-id-subtype-hom-wide-Precategoryᵉ :
    is-propᵉ contains-id-subtype-hom-wide-Precategoryᵉ
  is-prop-contains-id-subtype-hom-wide-Precategoryᵉ =
    is-prop-type-Propᵉ contains-id-prop-subtype-hom-wide-Precategoryᵉ

  is-closed-under-composition-subtype-hom-wide-Precategoryᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  is-closed-under-composition-subtype-hom-wide-Precategoryᵉ =
    (xᵉ yᵉ zᵉ : obj-Precategoryᵉ Cᵉ) →
    (gᵉ : hom-Precategoryᵉ Cᵉ yᵉ zᵉ) →
    (fᵉ : hom-Precategoryᵉ Cᵉ xᵉ yᵉ) →
    is-in-subtypeᵉ (P₁ᵉ yᵉ zᵉ) gᵉ →
    is-in-subtypeᵉ (P₁ᵉ xᵉ yᵉ) fᵉ →
    is-in-subtypeᵉ (P₁ᵉ xᵉ zᵉ) (comp-hom-Precategoryᵉ Cᵉ gᵉ fᵉ)

  is-prop-is-closed-under-composition-subtype-hom-wide-Precategoryᵉ :
    is-propᵉ is-closed-under-composition-subtype-hom-wide-Precategoryᵉ
  is-prop-is-closed-under-composition-subtype-hom-wide-Precategoryᵉ =
    is-prop-iterated-Πᵉ 7
      ( λ xᵉ yᵉ zᵉ gᵉ fᵉ _ _ →
        is-prop-is-in-subtypeᵉ (P₁ᵉ xᵉ zᵉ) (comp-hom-Precategoryᵉ Cᵉ gᵉ fᵉ))

  is-closed-under-composition-prop-subtype-hom-wide-Precategoryᵉ :
    Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  pr1ᵉ is-closed-under-composition-prop-subtype-hom-wide-Precategoryᵉ =
    is-closed-under-composition-subtype-hom-wide-Precategoryᵉ
  pr2ᵉ is-closed-under-composition-prop-subtype-hom-wide-Precategoryᵉ =
    is-prop-is-closed-under-composition-subtype-hom-wide-Precategoryᵉ
```

### The predicate on subtypes of hom-sets of being a wide subprecategory

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (P₁ᵉ : subtype-hom-wide-Precategoryᵉ l3ᵉ Cᵉ)
  where

  is-wide-subprecategory-Propᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  is-wide-subprecategory-Propᵉ =
    product-Propᵉ
      ( contains-id-prop-subtype-hom-wide-Precategoryᵉ Cᵉ P₁ᵉ)
      ( is-closed-under-composition-prop-subtype-hom-wide-Precategoryᵉ Cᵉ P₁ᵉ)

  is-wide-subprecategoryᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  is-wide-subprecategoryᵉ = type-Propᵉ is-wide-subprecategory-Propᵉ

  is-prop-is-wide-subprecategoryᵉ : is-propᵉ (is-wide-subprecategoryᵉ)
  is-prop-is-wide-subprecategoryᵉ = is-prop-type-Propᵉ is-wide-subprecategory-Propᵉ

  contains-id-is-wide-subprecategoryᵉ :
    is-wide-subprecategoryᵉ → contains-id-subtype-hom-wide-Precategoryᵉ Cᵉ P₁ᵉ
  contains-id-is-wide-subprecategoryᵉ = pr1ᵉ

  is-closed-under-composition-is-wide-subprecategoryᵉ :
    is-wide-subprecategoryᵉ →
    is-closed-under-composition-subtype-hom-wide-Precategoryᵉ Cᵉ P₁ᵉ
  is-closed-under-composition-is-wide-subprecategoryᵉ = pr2ᵉ
```

### Wide subprecategories

```agda
Wide-Subprecategoryᵉ :
  {l1ᵉ l2ᵉ : Level} (l3ᵉ : Level)
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ) →
  UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ lsuc l3ᵉ)
Wide-Subprecategoryᵉ l3ᵉ Cᵉ =
  Σᵉ (subtype-hom-wide-Precategoryᵉ l3ᵉ Cᵉ) (is-wide-subprecategoryᵉ Cᵉ)
```

#### Objects in wide subprecategories

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Pᵉ : Wide-Subprecategoryᵉ l3ᵉ Cᵉ)
  where

  subtype-obj-Wide-Subprecategoryᵉ : subtypeᵉ lzero (obj-Precategoryᵉ Cᵉ)
  subtype-obj-Wide-Subprecategoryᵉ _ = unit-Propᵉ

  obj-Wide-Subprecategoryᵉ : UUᵉ l1ᵉ
  obj-Wide-Subprecategoryᵉ = obj-Precategoryᵉ Cᵉ

  inclusion-obj-Wide-Subprecategoryᵉ :
    obj-Wide-Subprecategoryᵉ → obj-Precategoryᵉ Cᵉ
  inclusion-obj-Wide-Subprecategoryᵉ = idᵉ
```

#### Morphisms in wide subprecategories

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Pᵉ : Wide-Subprecategoryᵉ l3ᵉ Cᵉ)
  where

  subtype-hom-Wide-Subprecategoryᵉ : subtype-hom-wide-Precategoryᵉ l3ᵉ Cᵉ
  subtype-hom-Wide-Subprecategoryᵉ = pr1ᵉ Pᵉ

  hom-Wide-Subprecategoryᵉ : (xᵉ yᵉ : obj-Wide-Subprecategoryᵉ Cᵉ Pᵉ) → UUᵉ (l2ᵉ ⊔ l3ᵉ)
  hom-Wide-Subprecategoryᵉ xᵉ yᵉ =
    type-subtypeᵉ (subtype-hom-Wide-Subprecategoryᵉ xᵉ yᵉ)

  inclusion-hom-Wide-Subprecategoryᵉ :
    (xᵉ yᵉ : obj-Wide-Subprecategoryᵉ Cᵉ Pᵉ) →
    hom-Wide-Subprecategoryᵉ xᵉ yᵉ →
    hom-Precategoryᵉ Cᵉ
      ( inclusion-obj-Wide-Subprecategoryᵉ Cᵉ Pᵉ xᵉ)
      ( inclusion-obj-Wide-Subprecategoryᵉ Cᵉ Pᵉ yᵉ)
  inclusion-hom-Wide-Subprecategoryᵉ xᵉ yᵉ =
    inclusion-subtypeᵉ (subtype-hom-Wide-Subprecategoryᵉ xᵉ yᵉ)
```

Theᵉ predicateᵉ onᵉ morphismsᵉ betweenᵉ anyᵉ objectsᵉ ofᵉ beingᵉ containedᵉ in theᵉ wideᵉ
subprecategoryᵉ:

```agda
  is-in-hom-Wide-Subprecategoryᵉ :
    (xᵉ yᵉ : obj-Precategoryᵉ Cᵉ) (fᵉ : hom-Precategoryᵉ Cᵉ xᵉ yᵉ) → UUᵉ l3ᵉ
  is-in-hom-Wide-Subprecategoryᵉ xᵉ yᵉ =
    is-in-subtypeᵉ (subtype-hom-Wide-Subprecategoryᵉ xᵉ yᵉ)

  is-prop-is-in-hom-Wide-Subprecategoryᵉ :
    (xᵉ yᵉ : obj-Precategoryᵉ Cᵉ) (fᵉ : hom-Precategoryᵉ Cᵉ xᵉ yᵉ) →
    is-propᵉ (is-in-hom-Wide-Subprecategoryᵉ xᵉ yᵉ fᵉ)
  is-prop-is-in-hom-Wide-Subprecategoryᵉ xᵉ yᵉ =
    is-prop-is-in-subtypeᵉ (subtype-hom-Wide-Subprecategoryᵉ xᵉ yᵉ)

  is-in-hom-inclusion-hom-Wide-Subprecategoryᵉ :
    (xᵉ yᵉ : obj-Wide-Subprecategoryᵉ Cᵉ Pᵉ)
    (fᵉ : hom-Wide-Subprecategoryᵉ xᵉ yᵉ) →
    is-in-hom-Wide-Subprecategoryᵉ
      ( inclusion-obj-Wide-Subprecategoryᵉ Cᵉ Pᵉ xᵉ)
      ( inclusion-obj-Wide-Subprecategoryᵉ Cᵉ Pᵉ yᵉ)
      ( inclusion-hom-Wide-Subprecategoryᵉ xᵉ yᵉ fᵉ)
  is-in-hom-inclusion-hom-Wide-Subprecategoryᵉ xᵉ yᵉ =
    is-in-subtype-inclusion-subtypeᵉ (subtype-hom-Wide-Subprecategoryᵉ xᵉ yᵉ)
```

Wideᵉ subprecategoriesᵉ areᵉ wideᵉ subprecategoriesᵉ:

```agda
  is-wide-subprecategory-Wide-Subprecategoryᵉ :
    is-wide-subprecategoryᵉ Cᵉ subtype-hom-Wide-Subprecategoryᵉ
  is-wide-subprecategory-Wide-Subprecategoryᵉ = pr2ᵉ Pᵉ

  contains-id-Wide-Subprecategoryᵉ :
    contains-id-subtype-hom-wide-Precategoryᵉ Cᵉ
      ( subtype-hom-Wide-Subprecategoryᵉ)
  contains-id-Wide-Subprecategoryᵉ =
    contains-id-is-wide-subprecategoryᵉ Cᵉ
      ( subtype-hom-Wide-Subprecategoryᵉ)
      ( is-wide-subprecategory-Wide-Subprecategoryᵉ)

  is-closed-under-composition-Wide-Subprecategoryᵉ :
    is-closed-under-composition-subtype-hom-wide-Precategoryᵉ Cᵉ
      ( subtype-hom-Wide-Subprecategoryᵉ)
  is-closed-under-composition-Wide-Subprecategoryᵉ =
    is-closed-under-composition-is-wide-subprecategoryᵉ Cᵉ
      ( subtype-hom-Wide-Subprecategoryᵉ)
      ( is-wide-subprecategory-Wide-Subprecategoryᵉ)
```

Wideᵉ subprecategoriesᵉ areᵉ subprecategoriesᵉ:

```agda
  subtype-hom-subprecategory-Wide-Subprecategoryᵉ :
    subtype-hom-Precategoryᵉ l3ᵉ Cᵉ (subtype-obj-Wide-Subprecategoryᵉ Cᵉ Pᵉ)
  subtype-hom-subprecategory-Wide-Subprecategoryᵉ xᵉ yᵉ _ _ =
    subtype-hom-Wide-Subprecategoryᵉ xᵉ yᵉ

  is-subprecategory-Wide-Subprecategoryᵉ :
    is-subprecategoryᵉ Cᵉ
      ( subtype-obj-Wide-Subprecategoryᵉ Cᵉ Pᵉ)
      ( subtype-hom-subprecategory-Wide-Subprecategoryᵉ)
  pr1ᵉ is-subprecategory-Wide-Subprecategoryᵉ xᵉ _ =
    contains-id-Wide-Subprecategoryᵉ xᵉ
  pr2ᵉ is-subprecategory-Wide-Subprecategoryᵉ xᵉ yᵉ zᵉ gᵉ fᵉ _ _ _ =
    is-closed-under-composition-Wide-Subprecategoryᵉ xᵉ yᵉ zᵉ gᵉ fᵉ

  subprecategory-Wide-Subprecategoryᵉ : Subprecategoryᵉ lzero l3ᵉ Cᵉ
  pr1ᵉ subprecategory-Wide-Subprecategoryᵉ = subtype-obj-Wide-Subprecategoryᵉ Cᵉ Pᵉ
  pr1ᵉ (pr2ᵉ subprecategory-Wide-Subprecategoryᵉ) =
    subtype-hom-subprecategory-Wide-Subprecategoryᵉ
  pr2ᵉ (pr2ᵉ subprecategory-Wide-Subprecategoryᵉ) =
    is-subprecategory-Wide-Subprecategoryᵉ

  is-wide-Wide-Subprecategoryᵉ :
    is-wide-Subprecategoryᵉ Cᵉ (subprecategory-Wide-Subprecategoryᵉ)
  is-wide-Wide-Subprecategoryᵉ _ = starᵉ
```

### The underlying precategory of a wide subprecategory

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Pᵉ : Wide-Subprecategoryᵉ l3ᵉ Cᵉ)
  where

  hom-set-Wide-Subprecategoryᵉ :
    (xᵉ yᵉ : obj-Wide-Subprecategoryᵉ Cᵉ Pᵉ) → Setᵉ (l2ᵉ ⊔ l3ᵉ)
  hom-set-Wide-Subprecategoryᵉ xᵉ yᵉ =
    set-subsetᵉ
      ( hom-set-Precategoryᵉ Cᵉ xᵉ yᵉ)
      ( subtype-hom-Wide-Subprecategoryᵉ Cᵉ Pᵉ xᵉ yᵉ)

  is-set-hom-Wide-Subprecategoryᵉ :
    (xᵉ yᵉ : obj-Wide-Subprecategoryᵉ Cᵉ Pᵉ) →
    is-setᵉ (hom-Wide-Subprecategoryᵉ Cᵉ Pᵉ xᵉ yᵉ)
  is-set-hom-Wide-Subprecategoryᵉ xᵉ yᵉ =
    is-set-type-Setᵉ (hom-set-Wide-Subprecategoryᵉ xᵉ yᵉ)

  id-hom-Wide-Subprecategoryᵉ :
    {xᵉ : obj-Wide-Subprecategoryᵉ Cᵉ Pᵉ} → hom-Wide-Subprecategoryᵉ Cᵉ Pᵉ xᵉ xᵉ
  pr1ᵉ id-hom-Wide-Subprecategoryᵉ = id-hom-Precategoryᵉ Cᵉ
  pr2ᵉ (id-hom-Wide-Subprecategoryᵉ {xᵉ}) = contains-id-Wide-Subprecategoryᵉ Cᵉ Pᵉ xᵉ

  comp-hom-Wide-Subprecategoryᵉ :
    {xᵉ yᵉ zᵉ : obj-Wide-Subprecategoryᵉ Cᵉ Pᵉ} →
    hom-Wide-Subprecategoryᵉ Cᵉ Pᵉ yᵉ zᵉ →
    hom-Wide-Subprecategoryᵉ Cᵉ Pᵉ xᵉ yᵉ →
    hom-Wide-Subprecategoryᵉ Cᵉ Pᵉ xᵉ zᵉ
  pr1ᵉ (comp-hom-Wide-Subprecategoryᵉ {xᵉ} {yᵉ} {zᵉ} gᵉ fᵉ) =
    comp-hom-Precategoryᵉ Cᵉ
      ( inclusion-hom-Wide-Subprecategoryᵉ Cᵉ Pᵉ yᵉ zᵉ gᵉ)
      ( inclusion-hom-Wide-Subprecategoryᵉ Cᵉ Pᵉ xᵉ yᵉ fᵉ)
  pr2ᵉ (comp-hom-Wide-Subprecategoryᵉ {xᵉ} {yᵉ} {zᵉ} gᵉ fᵉ) =
    is-closed-under-composition-Wide-Subprecategoryᵉ Cᵉ Pᵉ xᵉ yᵉ zᵉ
      ( inclusion-hom-Wide-Subprecategoryᵉ Cᵉ Pᵉ yᵉ zᵉ gᵉ)
      ( inclusion-hom-Wide-Subprecategoryᵉ Cᵉ Pᵉ xᵉ yᵉ fᵉ)
      ( is-in-hom-inclusion-hom-Wide-Subprecategoryᵉ Cᵉ Pᵉ yᵉ zᵉ gᵉ)
      ( is-in-hom-inclusion-hom-Wide-Subprecategoryᵉ Cᵉ Pᵉ xᵉ yᵉ fᵉ)

  associative-comp-hom-Wide-Subprecategoryᵉ :
    {xᵉ yᵉ zᵉ wᵉ : obj-Wide-Subprecategoryᵉ Cᵉ Pᵉ}
    (hᵉ : hom-Wide-Subprecategoryᵉ Cᵉ Pᵉ zᵉ wᵉ)
    (gᵉ : hom-Wide-Subprecategoryᵉ Cᵉ Pᵉ yᵉ zᵉ)
    (fᵉ : hom-Wide-Subprecategoryᵉ Cᵉ Pᵉ xᵉ yᵉ) →
    comp-hom-Wide-Subprecategoryᵉ (comp-hom-Wide-Subprecategoryᵉ hᵉ gᵉ) fᵉ ＝ᵉ
    comp-hom-Wide-Subprecategoryᵉ hᵉ (comp-hom-Wide-Subprecategoryᵉ gᵉ fᵉ)
  associative-comp-hom-Wide-Subprecategoryᵉ {xᵉ} {yᵉ} {zᵉ} {wᵉ} hᵉ gᵉ fᵉ =
    eq-type-subtypeᵉ
      ( subtype-hom-Wide-Subprecategoryᵉ Cᵉ Pᵉ xᵉ wᵉ)
      ( associative-comp-hom-Precategoryᵉ Cᵉ
        ( inclusion-hom-Wide-Subprecategoryᵉ Cᵉ Pᵉ zᵉ wᵉ hᵉ)
        ( inclusion-hom-Wide-Subprecategoryᵉ Cᵉ Pᵉ yᵉ zᵉ gᵉ)
        ( inclusion-hom-Wide-Subprecategoryᵉ Cᵉ Pᵉ xᵉ yᵉ fᵉ))

  involutive-eq-associative-comp-hom-Wide-Subprecategoryᵉ :
    {xᵉ yᵉ zᵉ wᵉ : obj-Wide-Subprecategoryᵉ Cᵉ Pᵉ}
    (hᵉ : hom-Wide-Subprecategoryᵉ Cᵉ Pᵉ zᵉ wᵉ)
    (gᵉ : hom-Wide-Subprecategoryᵉ Cᵉ Pᵉ yᵉ zᵉ)
    (fᵉ : hom-Wide-Subprecategoryᵉ Cᵉ Pᵉ xᵉ yᵉ) →
    comp-hom-Wide-Subprecategoryᵉ (comp-hom-Wide-Subprecategoryᵉ hᵉ gᵉ) fᵉ ＝ⁱᵉ
    comp-hom-Wide-Subprecategoryᵉ hᵉ (comp-hom-Wide-Subprecategoryᵉ gᵉ fᵉ)
  involutive-eq-associative-comp-hom-Wide-Subprecategoryᵉ hᵉ gᵉ fᵉ =
    involutive-eq-eqᵉ (associative-comp-hom-Wide-Subprecategoryᵉ hᵉ gᵉ fᵉ)

  left-unit-law-comp-hom-Wide-Subprecategoryᵉ :
    {xᵉ yᵉ : obj-Wide-Subprecategoryᵉ Cᵉ Pᵉ}
    (fᵉ : hom-Wide-Subprecategoryᵉ Cᵉ Pᵉ xᵉ yᵉ) →
    comp-hom-Wide-Subprecategoryᵉ (id-hom-Wide-Subprecategoryᵉ) fᵉ ＝ᵉ fᵉ
  left-unit-law-comp-hom-Wide-Subprecategoryᵉ {xᵉ} {yᵉ} fᵉ =
    eq-type-subtypeᵉ
      ( subtype-hom-Wide-Subprecategoryᵉ Cᵉ Pᵉ xᵉ yᵉ)
      ( left-unit-law-comp-hom-Precategoryᵉ Cᵉ
        ( inclusion-hom-Wide-Subprecategoryᵉ Cᵉ Pᵉ xᵉ yᵉ fᵉ))

  right-unit-law-comp-hom-Wide-Subprecategoryᵉ :
    {xᵉ yᵉ : obj-Wide-Subprecategoryᵉ Cᵉ Pᵉ}
    (fᵉ : hom-Wide-Subprecategoryᵉ Cᵉ Pᵉ xᵉ yᵉ) →
    comp-hom-Wide-Subprecategoryᵉ fᵉ (id-hom-Wide-Subprecategoryᵉ) ＝ᵉ fᵉ
  right-unit-law-comp-hom-Wide-Subprecategoryᵉ {xᵉ} {yᵉ} fᵉ =
    eq-type-subtypeᵉ
      ( subtype-hom-Wide-Subprecategoryᵉ Cᵉ Pᵉ xᵉ yᵉ)
      ( right-unit-law-comp-hom-Precategoryᵉ Cᵉ
        ( inclusion-hom-Wide-Subprecategoryᵉ Cᵉ Pᵉ xᵉ yᵉ fᵉ))

  associative-composition-operation-Wide-Subprecategoryᵉ :
    associative-composition-operation-binary-family-Setᵉ
      ( hom-set-Wide-Subprecategoryᵉ)
  pr1ᵉ associative-composition-operation-Wide-Subprecategoryᵉ =
    comp-hom-Wide-Subprecategoryᵉ
  pr2ᵉ associative-composition-operation-Wide-Subprecategoryᵉ =
    involutive-eq-associative-comp-hom-Wide-Subprecategoryᵉ

  is-unital-composition-operation-Wide-Subprecategoryᵉ :
    is-unital-composition-operation-binary-family-Setᵉ
      ( hom-set-Wide-Subprecategoryᵉ)
      ( comp-hom-Wide-Subprecategoryᵉ)
  pr1ᵉ is-unital-composition-operation-Wide-Subprecategoryᵉ xᵉ =
    id-hom-Wide-Subprecategoryᵉ
  pr1ᵉ (pr2ᵉ is-unital-composition-operation-Wide-Subprecategoryᵉ) =
    left-unit-law-comp-hom-Wide-Subprecategoryᵉ
  pr2ᵉ (pr2ᵉ is-unital-composition-operation-Wide-Subprecategoryᵉ) =
    right-unit-law-comp-hom-Wide-Subprecategoryᵉ

  precategory-Wide-Subprecategoryᵉ : Precategoryᵉ l1ᵉ (l2ᵉ ⊔ l3ᵉ)
  pr1ᵉ precategory-Wide-Subprecategoryᵉ = obj-Wide-Subprecategoryᵉ Cᵉ Pᵉ
  pr1ᵉ (pr2ᵉ precategory-Wide-Subprecategoryᵉ) = hom-set-Wide-Subprecategoryᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ precategory-Wide-Subprecategoryᵉ)) =
    associative-composition-operation-Wide-Subprecategoryᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ precategory-Wide-Subprecategoryᵉ)) =
    is-unital-composition-operation-Wide-Subprecategoryᵉ
```

### The inclusion functor of a wide subprecategory

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Pᵉ : Wide-Subprecategoryᵉ l3ᵉ Cᵉ)
  where

  inclusion-map-Wide-Subprecategoryᵉ :
    map-Precategoryᵉ (precategory-Wide-Subprecategoryᵉ Cᵉ Pᵉ) Cᵉ
  pr1ᵉ inclusion-map-Wide-Subprecategoryᵉ = inclusion-obj-Wide-Subprecategoryᵉ Cᵉ Pᵉ
  pr2ᵉ inclusion-map-Wide-Subprecategoryᵉ {xᵉ} {yᵉ} =
    inclusion-hom-Wide-Subprecategoryᵉ Cᵉ Pᵉ xᵉ yᵉ

  is-functor-inclusion-Wide-Subprecategoryᵉ :
    is-functor-map-Precategoryᵉ
      ( precategory-Wide-Subprecategoryᵉ Cᵉ Pᵉ)
      ( Cᵉ)
      ( inclusion-map-Wide-Subprecategoryᵉ)
  pr1ᵉ is-functor-inclusion-Wide-Subprecategoryᵉ gᵉ fᵉ = reflᵉ
  pr2ᵉ is-functor-inclusion-Wide-Subprecategoryᵉ xᵉ = reflᵉ

  inclusion-Wide-Subprecategoryᵉ :
    functor-Precategoryᵉ (precategory-Wide-Subprecategoryᵉ Cᵉ Pᵉ) Cᵉ
  pr1ᵉ inclusion-Wide-Subprecategoryᵉ = inclusion-obj-Wide-Subprecategoryᵉ Cᵉ Pᵉ
  pr1ᵉ (pr2ᵉ inclusion-Wide-Subprecategoryᵉ) {xᵉ} {yᵉ} =
    inclusion-hom-Wide-Subprecategoryᵉ Cᵉ Pᵉ xᵉ yᵉ
  pr2ᵉ (pr2ᵉ inclusion-Wide-Subprecategoryᵉ) =
    is-functor-inclusion-Wide-Subprecategoryᵉ
```

## Properties

### The inclusion functor is faithful and an equivalence on objects

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Pᵉ : Wide-Subprecategoryᵉ l3ᵉ Cᵉ)
  where

  is-faithful-inclusion-Wide-Subprecategoryᵉ :
    is-faithful-functor-Precategoryᵉ
      ( precategory-Wide-Subprecategoryᵉ Cᵉ Pᵉ)
      ( Cᵉ)
      ( inclusion-Wide-Subprecategoryᵉ Cᵉ Pᵉ)
  is-faithful-inclusion-Wide-Subprecategoryᵉ xᵉ yᵉ =
    is-emb-inclusion-subtypeᵉ (subtype-hom-Wide-Subprecategoryᵉ Cᵉ Pᵉ xᵉ yᵉ)

  is-equiv-obj-inclusion-Wide-Subprecategoryᵉ :
    is-equivᵉ
      ( obj-functor-Precategoryᵉ
        ( precategory-Wide-Subprecategoryᵉ Cᵉ Pᵉ)
        ( Cᵉ)
        ( inclusion-Wide-Subprecategoryᵉ Cᵉ Pᵉ))
  is-equiv-obj-inclusion-Wide-Subprecategoryᵉ = is-equiv-idᵉ
```

## External links

-ᵉ [Wideᵉ subcategories](https://1lab.dev/Cat.Functor.WideSubcategory.htmlᵉ) atᵉ
  1labᵉ
-ᵉ [wideᵉ subcategory](https://ncatlab.org/nlab/show/wide+subcategoryᵉ) atᵉ $n$Labᵉ