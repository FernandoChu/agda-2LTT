# Isomorphisms in subprecategories

```agda
module category-theory.isomorphisms-in-subprecategoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.isomorphisms-in-precategoriesᵉ
open import category-theory.precategoriesᵉ
open import category-theory.subprecategoriesᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.subtypesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Definitions

### Isomorphisms in subprecategories

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Pᵉ : Subprecategoryᵉ l3ᵉ l4ᵉ Cᵉ)
  {xᵉ yᵉ : obj-Subprecategoryᵉ Cᵉ Pᵉ}
  (fᵉ : hom-Subprecategoryᵉ Cᵉ Pᵉ xᵉ yᵉ)
  where

  is-iso-prop-Subprecategoryᵉ : Propᵉ (l2ᵉ ⊔ l4ᵉ)
  is-iso-prop-Subprecategoryᵉ =
    is-iso-prop-Precategoryᵉ (precategory-Subprecategoryᵉ Cᵉ Pᵉ) {xᵉ} {yᵉ} fᵉ

  is-iso-Subprecategoryᵉ : UUᵉ (l2ᵉ ⊔ l4ᵉ)
  is-iso-Subprecategoryᵉ = type-Propᵉ is-iso-prop-Subprecategoryᵉ

  is-prop-is-iso-Subprecategoryᵉ : is-propᵉ is-iso-Subprecategoryᵉ
  is-prop-is-iso-Subprecategoryᵉ = is-prop-type-Propᵉ is-iso-prop-Subprecategoryᵉ
```

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Pᵉ : Subprecategoryᵉ l3ᵉ l4ᵉ Cᵉ)
  (xᵉ yᵉ : obj-Subprecategoryᵉ Cᵉ Pᵉ)
  where

  iso-set-Subprecategoryᵉ : Setᵉ (l2ᵉ ⊔ l4ᵉ)
  iso-set-Subprecategoryᵉ =
    iso-set-Precategoryᵉ (precategory-Subprecategoryᵉ Cᵉ Pᵉ) {xᵉ} {yᵉ}

  iso-Subprecategoryᵉ : UUᵉ (l2ᵉ ⊔ l4ᵉ)
  iso-Subprecategoryᵉ = type-Setᵉ iso-set-Subprecategoryᵉ

  is-set-iso-Subprecategoryᵉ : is-setᵉ iso-Subprecategoryᵉ
  is-set-iso-Subprecategoryᵉ = is-set-type-Setᵉ iso-set-Subprecategoryᵉ
```

#### The predicate on an isomorphism proof of being contained in a subprecategory

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Pᵉ : Subprecategoryᵉ l3ᵉ l4ᵉ Cᵉ)
  {xᵉ yᵉ : obj-Subprecategoryᵉ Cᵉ Pᵉ}
  (fᵉ : hom-Subprecategoryᵉ Cᵉ Pᵉ xᵉ yᵉ)
  (is-iso-fᵉ : is-iso-Precategoryᵉ Cᵉ (inclusion-hom-Subprecategoryᵉ Cᵉ Pᵉ xᵉ yᵉ fᵉ))
  where

  is-in-is-iso-prop-Subprecategoryᵉ : Propᵉ l4ᵉ
  is-in-is-iso-prop-Subprecategoryᵉ =
    subtype-hom-obj-subprecategory-Subprecategoryᵉ Cᵉ Pᵉ yᵉ xᵉ
      ( hom-inv-is-iso-Precategoryᵉ Cᵉ is-iso-fᵉ)

  is-in-is-iso-Subprecategoryᵉ : UUᵉ l4ᵉ
  is-in-is-iso-Subprecategoryᵉ =
    type-Propᵉ is-in-is-iso-prop-Subprecategoryᵉ

  is-prop-is-in-is-iso-Subprecategoryᵉ : is-propᵉ is-in-is-iso-Subprecategoryᵉ
  is-prop-is-in-is-iso-Subprecategoryᵉ =
    is-prop-type-Propᵉ is-in-is-iso-prop-Subprecategoryᵉ

  is-iso-is-in-is-iso-Subprecategoryᵉ :
    is-in-is-iso-Subprecategoryᵉ → is-iso-Subprecategoryᵉ Cᵉ Pᵉ fᵉ
  pr1ᵉ (pr1ᵉ (is-iso-is-in-is-iso-Subprecategoryᵉ is-in-is-iso-fᵉ)) =
    hom-inv-is-iso-Precategoryᵉ Cᵉ is-iso-fᵉ
  pr2ᵉ (pr1ᵉ (is-iso-is-in-is-iso-Subprecategoryᵉ is-in-is-iso-fᵉ)) =
    is-in-is-iso-fᵉ
  pr1ᵉ (pr2ᵉ (is-iso-is-in-is-iso-Subprecategoryᵉ is-in-is-iso-fᵉ)) =
    eq-type-subtypeᵉ
      ( subtype-hom-obj-subprecategory-Subprecategoryᵉ Cᵉ Pᵉ yᵉ yᵉ)
      ( pr1ᵉ (pr2ᵉ is-iso-fᵉ))
  pr2ᵉ (pr2ᵉ (is-iso-is-in-is-iso-Subprecategoryᵉ is-in-is-iso-fᵉ)) =
    eq-type-subtypeᵉ
      ( subtype-hom-obj-subprecategory-Subprecategoryᵉ Cᵉ Pᵉ xᵉ xᵉ)
      ( pr2ᵉ (pr2ᵉ is-iso-fᵉ))
```

#### The predicate on an isomorphism between objects in the subprecategory of being contained in the subprecategory

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Pᵉ : Subprecategoryᵉ l3ᵉ l4ᵉ Cᵉ)
  {xᵉ yᵉ : obj-Subprecategoryᵉ Cᵉ Pᵉ}
  (fᵉ :
    iso-Precategoryᵉ Cᵉ
      ( inclusion-obj-Subprecategoryᵉ Cᵉ Pᵉ xᵉ)
      ( inclusion-obj-Subprecategoryᵉ Cᵉ Pᵉ yᵉ))
  where

  is-in-iso-obj-subprecategory-prop-Subprecategoryᵉ : Propᵉ l4ᵉ
  is-in-iso-obj-subprecategory-prop-Subprecategoryᵉ =
    Σ-Propᵉ
      ( subtype-hom-obj-subprecategory-Subprecategoryᵉ Cᵉ Pᵉ xᵉ yᵉ
        ( hom-iso-Precategoryᵉ Cᵉ fᵉ))
      ( λ f₀ᵉ →
        is-in-is-iso-prop-Subprecategoryᵉ Cᵉ Pᵉ
          ( hom-iso-Precategoryᵉ Cᵉ fᵉ ,ᵉ f₀ᵉ)
          ( is-iso-iso-Precategoryᵉ Cᵉ fᵉ))

  is-in-iso-obj-subprecategory-Subprecategoryᵉ : UUᵉ l4ᵉ
  is-in-iso-obj-subprecategory-Subprecategoryᵉ =
    type-Propᵉ is-in-iso-obj-subprecategory-prop-Subprecategoryᵉ

  is-prop-is-in-iso-obj-subprecategory-Subprecategoryᵉ :
    is-propᵉ is-in-iso-obj-subprecategory-Subprecategoryᵉ
  is-prop-is-in-iso-obj-subprecategory-Subprecategoryᵉ =
    is-prop-type-Propᵉ is-in-iso-obj-subprecategory-prop-Subprecategoryᵉ

  is-iso-is-in-iso-obj-subprecategory-Subprecategoryᵉ :
    ((f₀ᵉ ,ᵉ f₁ᵉ) : is-in-iso-obj-subprecategory-Subprecategoryᵉ) →
    is-iso-Subprecategoryᵉ Cᵉ Pᵉ (hom-iso-Precategoryᵉ Cᵉ fᵉ ,ᵉ f₀ᵉ)
  is-iso-is-in-iso-obj-subprecategory-Subprecategoryᵉ (f₀ᵉ ,ᵉ f₁ᵉ) =
    is-iso-is-in-is-iso-Subprecategoryᵉ Cᵉ Pᵉ (pr1ᵉ fᵉ ,ᵉ f₀ᵉ) (pr2ᵉ fᵉ) f₁ᵉ

  iso-is-in-iso-obj-subprecategory-Subprecategoryᵉ :
    is-in-iso-obj-subprecategory-Subprecategoryᵉ → iso-Subprecategoryᵉ Cᵉ Pᵉ xᵉ yᵉ
  pr1ᵉ (pr1ᵉ (iso-is-in-iso-obj-subprecategory-Subprecategoryᵉ is-in-iso-fᵉ)) =
    hom-iso-Precategoryᵉ Cᵉ fᵉ
  pr2ᵉ (pr1ᵉ (iso-is-in-iso-obj-subprecategory-Subprecategoryᵉ is-in-iso-fᵉ)) =
    pr1ᵉ is-in-iso-fᵉ
  pr2ᵉ (iso-is-in-iso-obj-subprecategory-Subprecategoryᵉ is-in-iso-fᵉ) =
    is-iso-is-in-is-iso-Subprecategoryᵉ Cᵉ Pᵉ _
      ( is-iso-iso-Precategoryᵉ Cᵉ fᵉ)
      ( pr2ᵉ is-in-iso-fᵉ)
```

#### The predicate on an isomorphism between any objects of being contained in the subprecategory

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Pᵉ : Subprecategoryᵉ l3ᵉ l4ᵉ Cᵉ)
  {xᵉ yᵉ : obj-Precategoryᵉ Cᵉ}
  (fᵉ : iso-Precategoryᵉ Cᵉ xᵉ yᵉ)
  where

  is-in-iso-prop-Subprecategoryᵉ : Propᵉ (l3ᵉ ⊔ l4ᵉ)
  is-in-iso-prop-Subprecategoryᵉ =
    Σ-Propᵉ
      ( subtype-obj-Subprecategoryᵉ Cᵉ Pᵉ xᵉ)
      ( λ x₀ᵉ →
        Σ-Propᵉ
          ( subtype-obj-Subprecategoryᵉ Cᵉ Pᵉ yᵉ)
          ( λ y₀ᵉ →
            is-in-iso-obj-subprecategory-prop-Subprecategoryᵉ Cᵉ Pᵉ
              { xᵉ ,ᵉ x₀ᵉ} {yᵉ ,ᵉ y₀ᵉ} fᵉ))

  is-in-iso-Subprecategoryᵉ : UUᵉ (l3ᵉ ⊔ l4ᵉ)
  is-in-iso-Subprecategoryᵉ = type-Propᵉ is-in-iso-prop-Subprecategoryᵉ

  is-prop-is-in-iso-Subprecategoryᵉ : is-propᵉ is-in-iso-Subprecategoryᵉ
  is-prop-is-in-iso-Subprecategoryᵉ =
    is-prop-type-Propᵉ is-in-iso-prop-Subprecategoryᵉ

  iso-is-in-iso-Subprecategoryᵉ :
    (is-in-iso-fᵉ : is-in-iso-Subprecategoryᵉ) →
    iso-Subprecategoryᵉ Cᵉ Pᵉ (xᵉ ,ᵉ pr1ᵉ is-in-iso-fᵉ) (yᵉ ,ᵉ pr1ᵉ (pr2ᵉ is-in-iso-fᵉ))
  iso-is-in-iso-Subprecategoryᵉ is-in-iso-fᵉ =
    iso-is-in-iso-obj-subprecategory-Subprecategoryᵉ Cᵉ Pᵉ fᵉ
      ( pr2ᵉ (pr2ᵉ is-in-iso-fᵉ))

  is-iso-is-in-iso-Subprecategoryᵉ :
    ( is-in-iso-fᵉ : is-in-iso-Subprecategoryᵉ) →
    is-iso-Subprecategoryᵉ Cᵉ Pᵉ
      ( pr1ᵉ fᵉ ,ᵉ pr2ᵉ (pr1ᵉ (iso-is-in-iso-Subprecategoryᵉ is-in-iso-fᵉ)))
  is-iso-is-in-iso-Subprecategoryᵉ is-in-iso-fᵉ =
    pr2ᵉ (iso-is-in-iso-Subprecategoryᵉ is-in-iso-fᵉ)
```

### If a subprecategory contains an object, it contains its identity ismorphism

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Pᵉ : Subprecategoryᵉ l3ᵉ l4ᵉ Cᵉ)
  (xᵉ : obj-Subprecategoryᵉ Cᵉ Pᵉ)
  where

  is-iso-id-hom-Subprecategoryᵉ :
    is-iso-Subprecategoryᵉ Cᵉ Pᵉ (id-hom-Subprecategoryᵉ Cᵉ Pᵉ {xᵉ})
  is-iso-id-hom-Subprecategoryᵉ =
    is-iso-id-hom-Precategoryᵉ (precategory-Subprecategoryᵉ Cᵉ Pᵉ)

  is-in-is-iso-id-obj-subprecategory-Subprecategoryᵉ :
    is-in-is-iso-Subprecategoryᵉ Cᵉ Pᵉ {xᵉ}
      (id-hom-Subprecategoryᵉ Cᵉ Pᵉ) (is-iso-id-hom-Precategoryᵉ Cᵉ)
  is-in-is-iso-id-obj-subprecategory-Subprecategoryᵉ =
    contains-id-Subprecategoryᵉ Cᵉ Pᵉ
      ( inclusion-obj-Subprecategoryᵉ Cᵉ Pᵉ xᵉ)
      ( is-in-obj-inclusion-obj-Subprecategoryᵉ Cᵉ Pᵉ xᵉ)

  is-in-iso-id-obj-subprecategory-Subprecategoryᵉ :
    is-in-iso-obj-subprecategory-Subprecategoryᵉ Cᵉ Pᵉ (id-iso-Precategoryᵉ Cᵉ)
  pr1ᵉ is-in-iso-id-obj-subprecategory-Subprecategoryᵉ =
    is-in-is-iso-id-obj-subprecategory-Subprecategoryᵉ
  pr2ᵉ is-in-iso-id-obj-subprecategory-Subprecategoryᵉ =
    is-in-is-iso-id-obj-subprecategory-Subprecategoryᵉ

  is-in-iso-id-Subprecategoryᵉ :
    is-in-iso-Subprecategoryᵉ Cᵉ Pᵉ (id-iso-Precategoryᵉ Cᵉ)
  pr1ᵉ is-in-iso-id-Subprecategoryᵉ = is-in-obj-inclusion-obj-Subprecategoryᵉ Cᵉ Pᵉ xᵉ
  pr1ᵉ (pr2ᵉ is-in-iso-id-Subprecategoryᵉ) =
    is-in-obj-inclusion-obj-Subprecategoryᵉ Cᵉ Pᵉ xᵉ
  pr2ᵉ (pr2ᵉ is-in-iso-id-Subprecategoryᵉ) =
    is-in-iso-id-obj-subprecategory-Subprecategoryᵉ
```

## Properties

### Isomorphisms in a subprecategory are isomorphisms in the base category

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Pᵉ : Subprecategoryᵉ l3ᵉ l4ᵉ Cᵉ)
  {xᵉ yᵉ : obj-Subprecategoryᵉ Cᵉ Pᵉ}
  where

  is-iso-base-is-iso-Subprecategoryᵉ :
    {fᵉ : hom-Subprecategoryᵉ Cᵉ Pᵉ xᵉ yᵉ} →
    is-iso-Subprecategoryᵉ Cᵉ Pᵉ fᵉ →
    is-iso-Precategoryᵉ Cᵉ (inclusion-hom-Subprecategoryᵉ Cᵉ Pᵉ xᵉ yᵉ fᵉ)
  pr1ᵉ (is-iso-base-is-iso-Subprecategoryᵉ is-iso-fᵉ) =
    pr1ᵉ (pr1ᵉ is-iso-fᵉ)
  pr1ᵉ (pr2ᵉ (is-iso-base-is-iso-Subprecategoryᵉ is-iso-fᵉ)) =
    apᵉ pr1ᵉ (pr1ᵉ (pr2ᵉ (is-iso-fᵉ)))
  pr2ᵉ (pr2ᵉ (is-iso-base-is-iso-Subprecategoryᵉ is-iso-fᵉ)) =
    apᵉ pr1ᵉ (pr2ᵉ (pr2ᵉ (is-iso-fᵉ)))
```