# Subprecategories

```agda
module category-theory.subprecategoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.composition-operations-on-binary-families-of-setsᵉ
open import category-theory.faithful-functors-precategoriesᵉ
open import category-theory.functors-precategoriesᵉ
open import category-theory.maps-precategoriesᵉ
open import category-theory.precategoriesᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.embeddingsᵉ
open import foundation.identity-typesᵉ
open import foundation.iterated-dependent-product-typesᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.strictly-involutive-identity-typesᵉ
open import foundation.subtypesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Aᵉ **subprecategory**ᵉ ofᵉ aᵉ [precategory](category-theory.precategories.mdᵉ) `C`ᵉ
consistsᵉ ofᵉ aᵉ [subtype](foundation-core.subtypes.mdᵉ) `P₀`ᵉ ofᵉ theᵉ objectsᵉ ofᵉ `C`,ᵉ
andᵉ aᵉ familyᵉ ofᵉ subtypesᵉ `P₁`ᵉ

```text
  P₁ᵉ : (Xᵉ Yᵉ : objᵉ Cᵉ) → P₀ᵉ Xᵉ → P₀ᵉ Yᵉ → subtypeᵉ (homᵉ Xᵉ Yᵉ)
```

ofᵉ theᵉ morphismsᵉ ofᵉ `C`,ᵉ suchᵉ thatᵉ `P₁`ᵉ containsᵉ allᵉ identityᵉ morphismsᵉ ofᵉ
objectsᵉ in `P₀`ᵉ andᵉ isᵉ closedᵉ underᵉ composition.ᵉ

## Definition

### Sub-hom-families

```agda
subtype-hom-Precategoryᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} (l4ᵉ : Level)
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (P₀ᵉ : subtypeᵉ l3ᵉ (obj-Precategoryᵉ Cᵉ)) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ lsuc l4ᵉ)
subtype-hom-Precategoryᵉ l4ᵉ Cᵉ P₀ᵉ =
  (xᵉ yᵉ : obj-Precategoryᵉ Cᵉ) → is-in-subtypeᵉ P₀ᵉ xᵉ → is-in-subtypeᵉ P₀ᵉ yᵉ →
  subtypeᵉ l4ᵉ (hom-Precategoryᵉ Cᵉ xᵉ yᵉ)
```

### Categorical predicates on sub-hom-families

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (P₀ᵉ : subtypeᵉ l3ᵉ (obj-Precategoryᵉ Cᵉ))
  (P₁ᵉ : subtype-hom-Precategoryᵉ l4ᵉ Cᵉ P₀ᵉ)
  where

  contains-id-subtype-Precategoryᵉ : UUᵉ (l1ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  contains-id-subtype-Precategoryᵉ =
    (xᵉ : obj-Precategoryᵉ Cᵉ) →
    (x₀ᵉ : is-in-subtypeᵉ P₀ᵉ xᵉ) →
    is-in-subtypeᵉ (P₁ᵉ xᵉ xᵉ x₀ᵉ x₀ᵉ) (id-hom-Precategoryᵉ Cᵉ)

  is-prop-contains-id-subtype-Precategoryᵉ :
    is-propᵉ contains-id-subtype-Precategoryᵉ
  is-prop-contains-id-subtype-Precategoryᵉ =
    is-prop-iterated-Πᵉ 2
      ( λ xᵉ x₀ᵉ → is-prop-is-in-subtypeᵉ (P₁ᵉ xᵉ xᵉ x₀ᵉ x₀ᵉ) (id-hom-Precategoryᵉ Cᵉ))

  contains-id-prop-subtype-Precategoryᵉ : Propᵉ (l1ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  pr1ᵉ contains-id-prop-subtype-Precategoryᵉ =
    contains-id-subtype-Precategoryᵉ
  pr2ᵉ contains-id-prop-subtype-Precategoryᵉ =
    is-prop-contains-id-subtype-Precategoryᵉ

  is-closed-under-composition-subtype-Precategoryᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  is-closed-under-composition-subtype-Precategoryᵉ =
    (xᵉ yᵉ zᵉ : obj-Precategoryᵉ Cᵉ) →
    (gᵉ : hom-Precategoryᵉ Cᵉ yᵉ zᵉ) →
    (fᵉ : hom-Precategoryᵉ Cᵉ xᵉ yᵉ) →
    (x₀ᵉ : is-in-subtypeᵉ P₀ᵉ xᵉ) →
    (y₀ᵉ : is-in-subtypeᵉ P₀ᵉ yᵉ) →
    (z₀ᵉ : is-in-subtypeᵉ P₀ᵉ zᵉ) →
    is-in-subtypeᵉ (P₁ᵉ yᵉ zᵉ y₀ᵉ z₀ᵉ) gᵉ →
    is-in-subtypeᵉ (P₁ᵉ xᵉ yᵉ x₀ᵉ y₀ᵉ) fᵉ →
    is-in-subtypeᵉ (P₁ᵉ xᵉ zᵉ x₀ᵉ z₀ᵉ) (comp-hom-Precategoryᵉ Cᵉ gᵉ fᵉ)

  is-prop-is-closed-under-composition-subtype-Precategoryᵉ :
    is-propᵉ is-closed-under-composition-subtype-Precategoryᵉ
  is-prop-is-closed-under-composition-subtype-Precategoryᵉ =
    is-prop-iterated-Πᵉ 10
      ( λ xᵉ yᵉ zᵉ gᵉ fᵉ x₀ᵉ _ z₀ᵉ _ _ →
        is-prop-is-in-subtypeᵉ (P₁ᵉ xᵉ zᵉ x₀ᵉ z₀ᵉ) (comp-hom-Precategoryᵉ Cᵉ gᵉ fᵉ))

  is-closed-under-composition-prop-subtype-Precategoryᵉ :
    Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  pr1ᵉ is-closed-under-composition-prop-subtype-Precategoryᵉ =
    is-closed-under-composition-subtype-Precategoryᵉ
  pr2ᵉ is-closed-under-composition-prop-subtype-Precategoryᵉ =
    is-prop-is-closed-under-composition-subtype-Precategoryᵉ
```

### The predicate of being a subprecategory

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (P₀ᵉ : subtypeᵉ l3ᵉ (obj-Precategoryᵉ Cᵉ))
  (P₁ᵉ : subtype-hom-Precategoryᵉ l4ᵉ Cᵉ P₀ᵉ)
  where

  is-subprecategory-Propᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  is-subprecategory-Propᵉ =
    product-Propᵉ
      ( contains-id-prop-subtype-Precategoryᵉ Cᵉ P₀ᵉ P₁ᵉ)
      ( is-closed-under-composition-prop-subtype-Precategoryᵉ Cᵉ P₀ᵉ P₁ᵉ)

  is-subprecategoryᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  is-subprecategoryᵉ = type-Propᵉ is-subprecategory-Propᵉ

  is-prop-is-subprecategoryᵉ : is-propᵉ (is-subprecategoryᵉ)
  is-prop-is-subprecategoryᵉ = is-prop-type-Propᵉ is-subprecategory-Propᵉ

  contains-id-is-subprecategoryᵉ :
    is-subprecategoryᵉ → contains-id-subtype-Precategoryᵉ Cᵉ P₀ᵉ P₁ᵉ
  contains-id-is-subprecategoryᵉ = pr1ᵉ

  is-closed-under-composition-is-subprecategoryᵉ :
    is-subprecategoryᵉ → is-closed-under-composition-subtype-Precategoryᵉ Cᵉ P₀ᵉ P₁ᵉ
  is-closed-under-composition-is-subprecategoryᵉ = pr2ᵉ
```

### Subprecategories

```agda
Subprecategoryᵉ :
  {l1ᵉ l2ᵉ : Level} (l3ᵉ l4ᵉ : Level)
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ) →
  UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ lsuc l3ᵉ ⊔ lsuc l4ᵉ)
Subprecategoryᵉ l3ᵉ l4ᵉ Cᵉ =
  Σᵉ ( subtypeᵉ l3ᵉ (obj-Precategoryᵉ Cᵉ))
    ( λ P₀ᵉ →
      Σᵉ ( subtype-hom-Precategoryᵉ l4ᵉ Cᵉ P₀ᵉ)
        ( is-subprecategoryᵉ Cᵉ P₀ᵉ))
```

#### Objects in subprecategories

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Pᵉ : Subprecategoryᵉ l3ᵉ l4ᵉ Cᵉ)
  where

  subtype-obj-Subprecategoryᵉ : subtypeᵉ l3ᵉ (obj-Precategoryᵉ Cᵉ)
  subtype-obj-Subprecategoryᵉ = pr1ᵉ Pᵉ

  obj-Subprecategoryᵉ : UUᵉ (l1ᵉ ⊔ l3ᵉ)
  obj-Subprecategoryᵉ = type-subtypeᵉ subtype-obj-Subprecategoryᵉ

  inclusion-obj-Subprecategoryᵉ : obj-Subprecategoryᵉ → obj-Precategoryᵉ Cᵉ
  inclusion-obj-Subprecategoryᵉ = inclusion-subtypeᵉ subtype-obj-Subprecategoryᵉ

  is-in-obj-Subprecategoryᵉ : (xᵉ : obj-Precategoryᵉ Cᵉ) → UUᵉ l3ᵉ
  is-in-obj-Subprecategoryᵉ = is-in-subtypeᵉ subtype-obj-Subprecategoryᵉ

  is-prop-is-in-obj-Subprecategoryᵉ :
    (xᵉ : obj-Precategoryᵉ Cᵉ) → is-propᵉ (is-in-obj-Subprecategoryᵉ xᵉ)
  is-prop-is-in-obj-Subprecategoryᵉ =
    is-prop-is-in-subtypeᵉ subtype-obj-Subprecategoryᵉ

  is-in-obj-inclusion-obj-Subprecategoryᵉ :
    (xᵉ : obj-Subprecategoryᵉ) →
    is-in-obj-Subprecategoryᵉ (inclusion-obj-Subprecategoryᵉ xᵉ)
  is-in-obj-inclusion-obj-Subprecategoryᵉ =
    is-in-subtype-inclusion-subtypeᵉ subtype-obj-Subprecategoryᵉ
```

#### Morphisms in subprecategories

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Pᵉ : Subprecategoryᵉ l3ᵉ l4ᵉ Cᵉ)
  where

  subtype-hom-Subprecategoryᵉ :
    subtype-hom-Precategoryᵉ l4ᵉ Cᵉ (subtype-obj-Subprecategoryᵉ Cᵉ Pᵉ)
  subtype-hom-Subprecategoryᵉ = pr1ᵉ (pr2ᵉ Pᵉ)

  subtype-hom-obj-subprecategory-Subprecategoryᵉ :
    (xᵉ yᵉ : obj-Subprecategoryᵉ Cᵉ Pᵉ) →
    subtypeᵉ l4ᵉ
      ( hom-Precategoryᵉ Cᵉ
        ( inclusion-obj-Subprecategoryᵉ Cᵉ Pᵉ xᵉ)
        ( inclusion-obj-Subprecategoryᵉ Cᵉ Pᵉ yᵉ))
  subtype-hom-obj-subprecategory-Subprecategoryᵉ xᵉ yᵉ =
    subtype-hom-Subprecategoryᵉ
      ( inclusion-obj-Subprecategoryᵉ Cᵉ Pᵉ xᵉ)
      ( inclusion-obj-Subprecategoryᵉ Cᵉ Pᵉ yᵉ)
      ( is-in-obj-inclusion-obj-Subprecategoryᵉ Cᵉ Pᵉ xᵉ)
      ( is-in-obj-inclusion-obj-Subprecategoryᵉ Cᵉ Pᵉ yᵉ)

  hom-Subprecategoryᵉ : (xᵉ yᵉ : obj-Subprecategoryᵉ Cᵉ Pᵉ) → UUᵉ (l2ᵉ ⊔ l4ᵉ)
  hom-Subprecategoryᵉ xᵉ yᵉ =
    type-subtypeᵉ (subtype-hom-obj-subprecategory-Subprecategoryᵉ xᵉ yᵉ)

  inclusion-hom-Subprecategoryᵉ :
    (xᵉ yᵉ : obj-Subprecategoryᵉ Cᵉ Pᵉ) →
    hom-Subprecategoryᵉ xᵉ yᵉ →
    hom-Precategoryᵉ Cᵉ
      ( inclusion-obj-Subprecategoryᵉ Cᵉ Pᵉ xᵉ)
      ( inclusion-obj-Subprecategoryᵉ Cᵉ Pᵉ yᵉ)
  inclusion-hom-Subprecategoryᵉ xᵉ yᵉ =
    inclusion-subtypeᵉ (subtype-hom-obj-subprecategory-Subprecategoryᵉ xᵉ yᵉ)
```

Theᵉ predicateᵉ onᵉ morphismsᵉ betweenᵉ subobjectsᵉ ofᵉ beingᵉ containedᵉ in theᵉ
subprecategoryᵉ:

```agda
  is-in-hom-obj-subprecategory-Subprecategoryᵉ :
    ( xᵉ yᵉ : obj-Subprecategoryᵉ Cᵉ Pᵉ) →
    hom-Precategoryᵉ Cᵉ
      ( inclusion-obj-Subprecategoryᵉ Cᵉ Pᵉ xᵉ)
      ( inclusion-obj-Subprecategoryᵉ Cᵉ Pᵉ yᵉ) →
    UUᵉ l4ᵉ
  is-in-hom-obj-subprecategory-Subprecategoryᵉ xᵉ yᵉ =
    is-in-subtypeᵉ (subtype-hom-obj-subprecategory-Subprecategoryᵉ xᵉ yᵉ)

  is-prop-is-in-hom-obj-subprecategory-Subprecategoryᵉ :
    ( xᵉ yᵉ : obj-Subprecategoryᵉ Cᵉ Pᵉ)
    ( fᵉ :
      hom-Precategoryᵉ Cᵉ
        ( inclusion-obj-Subprecategoryᵉ Cᵉ Pᵉ xᵉ)
        ( inclusion-obj-Subprecategoryᵉ Cᵉ Pᵉ yᵉ)) →
    is-propᵉ (is-in-hom-obj-subprecategory-Subprecategoryᵉ xᵉ yᵉ fᵉ)
  is-prop-is-in-hom-obj-subprecategory-Subprecategoryᵉ xᵉ yᵉ =
    is-prop-is-in-subtypeᵉ (subtype-hom-obj-subprecategory-Subprecategoryᵉ xᵉ yᵉ)
```

Theᵉ predicateᵉ onᵉ morphismsᵉ betweenᵉ anyᵉ objectsᵉ ofᵉ beingᵉ containedᵉ in theᵉ
subprecategoryᵉ:

```agda
  is-in-hom-Subprecategoryᵉ :
    (xᵉ yᵉ : obj-Precategoryᵉ Cᵉ) (fᵉ : hom-Precategoryᵉ Cᵉ xᵉ yᵉ) → UUᵉ (l3ᵉ ⊔ l4ᵉ)
  is-in-hom-Subprecategoryᵉ xᵉ yᵉ fᵉ =
    Σᵉ ( is-in-obj-Subprecategoryᵉ Cᵉ Pᵉ xᵉ)
      ( λ x₀ᵉ →
        Σᵉ ( is-in-obj-Subprecategoryᵉ Cᵉ Pᵉ yᵉ)
          ( λ y₀ᵉ →
            is-in-hom-obj-subprecategory-Subprecategoryᵉ (xᵉ ,ᵉ x₀ᵉ) (yᵉ ,ᵉ y₀ᵉ) fᵉ))

  is-prop-is-in-hom-Subprecategoryᵉ :
    (xᵉ yᵉ : obj-Precategoryᵉ Cᵉ) (fᵉ : hom-Precategoryᵉ Cᵉ xᵉ yᵉ) →
    is-propᵉ (is-in-hom-Subprecategoryᵉ xᵉ yᵉ fᵉ)
  is-prop-is-in-hom-Subprecategoryᵉ xᵉ yᵉ fᵉ =
    is-prop-Σᵉ
      ( is-prop-is-in-obj-Subprecategoryᵉ Cᵉ Pᵉ xᵉ)
      ( λ x₀ᵉ →
        is-prop-Σᵉ
          ( is-prop-is-in-obj-Subprecategoryᵉ Cᵉ Pᵉ yᵉ)
          ( λ y₀ᵉ →
            is-prop-is-in-hom-obj-subprecategory-Subprecategoryᵉ
              ( xᵉ ,ᵉ x₀ᵉ) (yᵉ ,ᵉ y₀ᵉ) fᵉ))

  is-in-hom-obj-subprecategory-inclusion-hom-Subprecategoryᵉ :
    (xᵉ yᵉ : obj-Subprecategoryᵉ Cᵉ Pᵉ)
    (fᵉ : hom-Subprecategoryᵉ xᵉ yᵉ) →
    is-in-hom-obj-subprecategory-Subprecategoryᵉ xᵉ yᵉ
      ( inclusion-hom-Subprecategoryᵉ xᵉ yᵉ fᵉ)
  is-in-hom-obj-subprecategory-inclusion-hom-Subprecategoryᵉ xᵉ yᵉ fᵉ = pr2ᵉ fᵉ

  is-in-hom-inclusion-hom-Subprecategoryᵉ :
    (xᵉ yᵉ : obj-Subprecategoryᵉ Cᵉ Pᵉ)
    (fᵉ : hom-Subprecategoryᵉ xᵉ yᵉ) →
    is-in-hom-Subprecategoryᵉ
      ( inclusion-obj-Subprecategoryᵉ Cᵉ Pᵉ xᵉ)
      ( inclusion-obj-Subprecategoryᵉ Cᵉ Pᵉ yᵉ)
      ( inclusion-hom-Subprecategoryᵉ xᵉ yᵉ fᵉ)
  pr1ᵉ (is-in-hom-inclusion-hom-Subprecategoryᵉ xᵉ yᵉ fᵉ) =
    is-in-obj-inclusion-obj-Subprecategoryᵉ Cᵉ Pᵉ xᵉ
  pr1ᵉ (pr2ᵉ (is-in-hom-inclusion-hom-Subprecategoryᵉ xᵉ yᵉ fᵉ)) =
    is-in-obj-inclusion-obj-Subprecategoryᵉ Cᵉ Pᵉ yᵉ
  pr2ᵉ (pr2ᵉ (is-in-hom-inclusion-hom-Subprecategoryᵉ xᵉ yᵉ fᵉ)) =
    is-in-hom-obj-subprecategory-inclusion-hom-Subprecategoryᵉ xᵉ yᵉ fᵉ
```

#### Subprecategories are subprecategories

```agda
  is-subprecategory-Subprecategoryᵉ :
    is-subprecategoryᵉ Cᵉ
      ( subtype-obj-Subprecategoryᵉ Cᵉ Pᵉ) (subtype-hom-Subprecategoryᵉ)
  is-subprecategory-Subprecategoryᵉ = pr2ᵉ (pr2ᵉ Pᵉ)

  contains-id-Subprecategoryᵉ :
    contains-id-subtype-Precategoryᵉ Cᵉ
      ( subtype-obj-Subprecategoryᵉ Cᵉ Pᵉ)
      ( subtype-hom-Subprecategoryᵉ)
  contains-id-Subprecategoryᵉ =
    contains-id-is-subprecategoryᵉ Cᵉ
      ( subtype-obj-Subprecategoryᵉ Cᵉ Pᵉ)
      ( subtype-hom-Subprecategoryᵉ)
      ( is-subprecategory-Subprecategoryᵉ)

  is-closed-under-composition-Subprecategoryᵉ :
    is-closed-under-composition-subtype-Precategoryᵉ Cᵉ
      ( subtype-obj-Subprecategoryᵉ Cᵉ Pᵉ)
      ( subtype-hom-Subprecategoryᵉ)
  is-closed-under-composition-Subprecategoryᵉ =
    is-closed-under-composition-is-subprecategoryᵉ Cᵉ
      ( subtype-obj-Subprecategoryᵉ Cᵉ Pᵉ)
      ( subtype-hom-Subprecategoryᵉ)
      ( is-subprecategory-Subprecategoryᵉ)
```

### The underlying precategory of a subprecategory

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Pᵉ : Subprecategoryᵉ l3ᵉ l4ᵉ Cᵉ)
  where

  hom-set-Subprecategoryᵉ : (xᵉ yᵉ : obj-Subprecategoryᵉ Cᵉ Pᵉ) → Setᵉ (l2ᵉ ⊔ l4ᵉ)
  hom-set-Subprecategoryᵉ xᵉ yᵉ =
    set-subsetᵉ
      ( hom-set-Precategoryᵉ Cᵉ
        ( inclusion-obj-Subprecategoryᵉ Cᵉ Pᵉ xᵉ)
        ( inclusion-obj-Subprecategoryᵉ Cᵉ Pᵉ yᵉ))
      ( subtype-hom-obj-subprecategory-Subprecategoryᵉ Cᵉ Pᵉ xᵉ yᵉ)

  is-set-hom-Subprecategoryᵉ :
    (xᵉ yᵉ : obj-Subprecategoryᵉ Cᵉ Pᵉ) → is-setᵉ (hom-Subprecategoryᵉ Cᵉ Pᵉ xᵉ yᵉ)
  is-set-hom-Subprecategoryᵉ xᵉ yᵉ = is-set-type-Setᵉ (hom-set-Subprecategoryᵉ xᵉ yᵉ)

  id-hom-Subprecategoryᵉ :
    {xᵉ : obj-Subprecategoryᵉ Cᵉ Pᵉ} → hom-Subprecategoryᵉ Cᵉ Pᵉ xᵉ xᵉ
  pr1ᵉ (id-hom-Subprecategoryᵉ) = id-hom-Precategoryᵉ Cᵉ
  pr2ᵉ (id-hom-Subprecategoryᵉ {xᵉ}) =
    contains-id-Subprecategoryᵉ Cᵉ Pᵉ
      ( inclusion-obj-Subprecategoryᵉ Cᵉ Pᵉ xᵉ)
      ( is-in-obj-inclusion-obj-Subprecategoryᵉ Cᵉ Pᵉ xᵉ)

  comp-hom-Subprecategoryᵉ :
    {xᵉ yᵉ zᵉ : obj-Subprecategoryᵉ Cᵉ Pᵉ} →
    hom-Subprecategoryᵉ Cᵉ Pᵉ yᵉ zᵉ →
    hom-Subprecategoryᵉ Cᵉ Pᵉ xᵉ yᵉ →
    hom-Subprecategoryᵉ Cᵉ Pᵉ xᵉ zᵉ
  pr1ᵉ (comp-hom-Subprecategoryᵉ {xᵉ} {yᵉ} {zᵉ} gᵉ fᵉ) =
    comp-hom-Precategoryᵉ Cᵉ
      ( inclusion-hom-Subprecategoryᵉ Cᵉ Pᵉ yᵉ zᵉ gᵉ)
      ( inclusion-hom-Subprecategoryᵉ Cᵉ Pᵉ xᵉ yᵉ fᵉ)
  pr2ᵉ (comp-hom-Subprecategoryᵉ {xᵉ} {yᵉ} {zᵉ} gᵉ fᵉ) =
    is-closed-under-composition-Subprecategoryᵉ Cᵉ Pᵉ
      ( inclusion-obj-Subprecategoryᵉ Cᵉ Pᵉ xᵉ)
      ( inclusion-obj-Subprecategoryᵉ Cᵉ Pᵉ yᵉ)
      ( inclusion-obj-Subprecategoryᵉ Cᵉ Pᵉ zᵉ)
      ( inclusion-hom-Subprecategoryᵉ Cᵉ Pᵉ yᵉ zᵉ gᵉ)
      ( inclusion-hom-Subprecategoryᵉ Cᵉ Pᵉ xᵉ yᵉ fᵉ)
      ( is-in-obj-inclusion-obj-Subprecategoryᵉ Cᵉ Pᵉ xᵉ)
      ( is-in-obj-inclusion-obj-Subprecategoryᵉ Cᵉ Pᵉ yᵉ)
      ( is-in-obj-inclusion-obj-Subprecategoryᵉ Cᵉ Pᵉ zᵉ)
      ( pr2ᵉ gᵉ)
      ( pr2ᵉ fᵉ)

  associative-comp-hom-Subprecategoryᵉ :
    {xᵉ yᵉ zᵉ wᵉ : obj-Subprecategoryᵉ Cᵉ Pᵉ}
    (hᵉ : hom-Subprecategoryᵉ Cᵉ Pᵉ zᵉ wᵉ)
    (gᵉ : hom-Subprecategoryᵉ Cᵉ Pᵉ yᵉ zᵉ)
    (fᵉ : hom-Subprecategoryᵉ Cᵉ Pᵉ xᵉ yᵉ) →
    comp-hom-Subprecategoryᵉ {xᵉ} {yᵉ} {wᵉ}
      ( comp-hom-Subprecategoryᵉ {yᵉ} {zᵉ} {wᵉ} hᵉ gᵉ)
      ( fᵉ) ＝ᵉ
    comp-hom-Subprecategoryᵉ {xᵉ} {zᵉ} {wᵉ}
      ( hᵉ)
      ( comp-hom-Subprecategoryᵉ {xᵉ} {yᵉ} {zᵉ} gᵉ fᵉ)
  associative-comp-hom-Subprecategoryᵉ {xᵉ} {yᵉ} {zᵉ} {wᵉ} hᵉ gᵉ fᵉ =
    eq-type-subtypeᵉ
      ( subtype-hom-Subprecategoryᵉ Cᵉ Pᵉ
        ( inclusion-obj-Subprecategoryᵉ Cᵉ Pᵉ xᵉ)
        ( inclusion-obj-Subprecategoryᵉ Cᵉ Pᵉ wᵉ)
        ( is-in-obj-inclusion-obj-Subprecategoryᵉ Cᵉ Pᵉ xᵉ)
        ( is-in-obj-inclusion-obj-Subprecategoryᵉ Cᵉ Pᵉ wᵉ))
      ( associative-comp-hom-Precategoryᵉ Cᵉ
        ( inclusion-hom-Subprecategoryᵉ Cᵉ Pᵉ zᵉ wᵉ hᵉ)
        ( inclusion-hom-Subprecategoryᵉ Cᵉ Pᵉ yᵉ zᵉ gᵉ)
        ( inclusion-hom-Subprecategoryᵉ Cᵉ Pᵉ xᵉ yᵉ fᵉ))

  involutive-eq-associative-comp-hom-Subprecategoryᵉ :
    {xᵉ yᵉ zᵉ wᵉ : obj-Subprecategoryᵉ Cᵉ Pᵉ}
    (hᵉ : hom-Subprecategoryᵉ Cᵉ Pᵉ zᵉ wᵉ)
    (gᵉ : hom-Subprecategoryᵉ Cᵉ Pᵉ yᵉ zᵉ)
    (fᵉ : hom-Subprecategoryᵉ Cᵉ Pᵉ xᵉ yᵉ) →
    comp-hom-Subprecategoryᵉ {xᵉ} {yᵉ} {wᵉ}
      ( comp-hom-Subprecategoryᵉ {yᵉ} {zᵉ} {wᵉ} hᵉ gᵉ)
      ( fᵉ) ＝ⁱᵉ
    comp-hom-Subprecategoryᵉ {xᵉ} {zᵉ} {wᵉ}
      ( hᵉ)
      ( comp-hom-Subprecategoryᵉ {xᵉ} {yᵉ} {zᵉ} gᵉ fᵉ)
  involutive-eq-associative-comp-hom-Subprecategoryᵉ {xᵉ} {yᵉ} {zᵉ} {wᵉ} hᵉ gᵉ fᵉ =
    involutive-eq-eqᵉ (associative-comp-hom-Subprecategoryᵉ hᵉ gᵉ fᵉ)

  left-unit-law-comp-hom-Subprecategoryᵉ :
    {xᵉ yᵉ : obj-Subprecategoryᵉ Cᵉ Pᵉ}
    (fᵉ : hom-Subprecategoryᵉ Cᵉ Pᵉ xᵉ yᵉ) →
    comp-hom-Subprecategoryᵉ {xᵉ} {yᵉ} {yᵉ} (id-hom-Subprecategoryᵉ {yᵉ}) fᵉ ＝ᵉ fᵉ
  left-unit-law-comp-hom-Subprecategoryᵉ {xᵉ} {yᵉ} fᵉ =
    eq-type-subtypeᵉ
      ( subtype-hom-Subprecategoryᵉ Cᵉ Pᵉ
        ( inclusion-obj-Subprecategoryᵉ Cᵉ Pᵉ xᵉ)
        ( inclusion-obj-Subprecategoryᵉ Cᵉ Pᵉ yᵉ)
        ( is-in-obj-inclusion-obj-Subprecategoryᵉ Cᵉ Pᵉ xᵉ)
        ( is-in-obj-inclusion-obj-Subprecategoryᵉ Cᵉ Pᵉ yᵉ))
      ( left-unit-law-comp-hom-Precategoryᵉ Cᵉ
        ( inclusion-hom-Subprecategoryᵉ Cᵉ Pᵉ xᵉ yᵉ fᵉ))

  right-unit-law-comp-hom-Subprecategoryᵉ :
    {xᵉ yᵉ : obj-Subprecategoryᵉ Cᵉ Pᵉ}
    (fᵉ : hom-Subprecategoryᵉ Cᵉ Pᵉ xᵉ yᵉ) →
    comp-hom-Subprecategoryᵉ {xᵉ} {xᵉ} {yᵉ} fᵉ (id-hom-Subprecategoryᵉ {xᵉ}) ＝ᵉ fᵉ
  right-unit-law-comp-hom-Subprecategoryᵉ {xᵉ} {yᵉ} fᵉ =
    eq-type-subtypeᵉ
      ( subtype-hom-Subprecategoryᵉ Cᵉ Pᵉ
        ( inclusion-obj-Subprecategoryᵉ Cᵉ Pᵉ xᵉ)
        ( inclusion-obj-Subprecategoryᵉ Cᵉ Pᵉ yᵉ)
        ( is-in-obj-inclusion-obj-Subprecategoryᵉ Cᵉ Pᵉ xᵉ)
        ( is-in-obj-inclusion-obj-Subprecategoryᵉ Cᵉ Pᵉ yᵉ))
      ( right-unit-law-comp-hom-Precategoryᵉ Cᵉ
        ( inclusion-hom-Subprecategoryᵉ Cᵉ Pᵉ xᵉ yᵉ fᵉ))

  associative-composition-operation-Subprecategoryᵉ :
    associative-composition-operation-binary-family-Setᵉ hom-set-Subprecategoryᵉ
  pr1ᵉ associative-composition-operation-Subprecategoryᵉ {xᵉ} {yᵉ} {zᵉ} =
    comp-hom-Subprecategoryᵉ {xᵉ} {yᵉ} {zᵉ}
  pr2ᵉ associative-composition-operation-Subprecategoryᵉ =
    involutive-eq-associative-comp-hom-Subprecategoryᵉ

  is-unital-composition-operation-Subprecategoryᵉ :
    is-unital-composition-operation-binary-family-Setᵉ
      ( hom-set-Subprecategoryᵉ)
      ( comp-hom-Subprecategoryᵉ)
  pr1ᵉ is-unital-composition-operation-Subprecategoryᵉ xᵉ =
    id-hom-Subprecategoryᵉ {xᵉ}
  pr1ᵉ (pr2ᵉ is-unital-composition-operation-Subprecategoryᵉ) {xᵉ} {yᵉ} =
    left-unit-law-comp-hom-Subprecategoryᵉ {xᵉ} {yᵉ}
  pr2ᵉ (pr2ᵉ is-unital-composition-operation-Subprecategoryᵉ) {xᵉ} {yᵉ} =
    right-unit-law-comp-hom-Subprecategoryᵉ {xᵉ} {yᵉ}

  precategory-Subprecategoryᵉ : Precategoryᵉ (l1ᵉ ⊔ l3ᵉ) (l2ᵉ ⊔ l4ᵉ)
  pr1ᵉ precategory-Subprecategoryᵉ = obj-Subprecategoryᵉ Cᵉ Pᵉ
  pr1ᵉ (pr2ᵉ precategory-Subprecategoryᵉ) = hom-set-Subprecategoryᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ precategory-Subprecategoryᵉ)) =
    associative-composition-operation-Subprecategoryᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ precategory-Subprecategoryᵉ)) =
    is-unital-composition-operation-Subprecategoryᵉ
```

### The inclusion functor of a subprecategory

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Pᵉ : Subprecategoryᵉ l3ᵉ l4ᵉ Cᵉ)
  where

  inclusion-map-Subprecategoryᵉ :
    map-Precategoryᵉ (precategory-Subprecategoryᵉ Cᵉ Pᵉ) Cᵉ
  pr1ᵉ inclusion-map-Subprecategoryᵉ =
    inclusion-obj-Subprecategoryᵉ Cᵉ Pᵉ
  pr2ᵉ inclusion-map-Subprecategoryᵉ {xᵉ} {yᵉ} =
    inclusion-hom-Subprecategoryᵉ Cᵉ Pᵉ xᵉ yᵉ

  is-functor-inclusion-Subprecategoryᵉ :
    is-functor-map-Precategoryᵉ
      ( precategory-Subprecategoryᵉ Cᵉ Pᵉ)
      ( Cᵉ)
      ( inclusion-map-Subprecategoryᵉ)
  pr1ᵉ is-functor-inclusion-Subprecategoryᵉ gᵉ fᵉ = reflᵉ
  pr2ᵉ is-functor-inclusion-Subprecategoryᵉ xᵉ = reflᵉ

  inclusion-Subprecategoryᵉ :
    functor-Precategoryᵉ (precategory-Subprecategoryᵉ Cᵉ Pᵉ) Cᵉ
  pr1ᵉ inclusion-Subprecategoryᵉ =
    inclusion-obj-Subprecategoryᵉ Cᵉ Pᵉ
  pr1ᵉ (pr2ᵉ inclusion-Subprecategoryᵉ) {xᵉ} {yᵉ} =
    inclusion-hom-Subprecategoryᵉ Cᵉ Pᵉ xᵉ yᵉ
  pr2ᵉ (pr2ᵉ inclusion-Subprecategoryᵉ) =
    is-functor-inclusion-Subprecategoryᵉ
```

## Properties

### The inclusion functor is an embedding on objects and hom-sets

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Pᵉ : Subprecategoryᵉ l3ᵉ l4ᵉ Cᵉ)
  where

  is-faithful-inclusion-Subprecategoryᵉ :
    is-faithful-functor-Precategoryᵉ
      ( precategory-Subprecategoryᵉ Cᵉ Pᵉ)
      ( Cᵉ)
      ( inclusion-Subprecategoryᵉ Cᵉ Pᵉ)
  is-faithful-inclusion-Subprecategoryᵉ xᵉ yᵉ =
    is-emb-inclusion-subtypeᵉ
      ( subtype-hom-Subprecategoryᵉ Cᵉ Pᵉ
        ( inclusion-obj-Subprecategoryᵉ Cᵉ Pᵉ xᵉ)
        ( inclusion-obj-Subprecategoryᵉ Cᵉ Pᵉ yᵉ)
        ( is-in-obj-inclusion-obj-Subprecategoryᵉ Cᵉ Pᵉ xᵉ)
        ( is-in-obj-inclusion-obj-Subprecategoryᵉ Cᵉ Pᵉ yᵉ))

  is-emb-obj-inclusion-Subprecategoryᵉ :
    is-embᵉ
      ( obj-functor-Precategoryᵉ
        ( precategory-Subprecategoryᵉ Cᵉ Pᵉ)
        ( Cᵉ)
        ( inclusion-Subprecategoryᵉ Cᵉ Pᵉ))
  is-emb-obj-inclusion-Subprecategoryᵉ =
    is-emb-inclusion-subtypeᵉ (subtype-obj-Subprecategoryᵉ Cᵉ Pᵉ)
```

## See also

-ᵉ [Largeᵉ subprecategories](category-theory.large-subprecategories.mdᵉ)
-ᵉ [Subcategories](category-theory.subcategories.mdᵉ)

## External links

-ᵉ [subcategory](https://ncatlab.org/nlab/show/subcategoryᵉ) atᵉ $n$Labᵉ
-ᵉ [Subcategory](https://en.wikipedia.org/wiki/Subcategoryᵉ) atᵉ Wikipediaᵉ
-ᵉ [Subcategory](https://mathworld.wolfram.com/Subcategory.htmlᵉ) atᵉ Wolframᵉ
  MathWorldᵉ