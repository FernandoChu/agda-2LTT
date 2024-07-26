# Representations of monoids in precategories

```agda
module group-theory.representations-monoids-precategoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.endomorphisms-in-precategoriesᵉ
open import category-theory.functors-precategoriesᵉ
open import category-theory.one-object-precategoriesᵉ
open import category-theory.precategoriesᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import group-theory.monoidsᵉ
```

</details>

## Idea

Aᵉ **representation**ᵉ ofᵉ aᵉ [monoid](group-theory.monoids.mdᵉ) `M`ᵉ in aᵉ
[precategory](category-theory.precategories.mdᵉ) `C`ᵉ consistᵉ ofᵉ anᵉ objectᵉ `V`ᵉ in
`C`ᵉ [equipped](foundation.structure.mdᵉ) with aᵉ
[monoidᵉ homomorphism](group-theory.homomorphisms-monoids.mdᵉ) fromᵉ `M`ᵉ to theᵉ
monoidᵉ ofᵉ [endomorphisms](category-theory.endomorphisms-in-precategories.mdᵉ) onᵉ
`V`.ᵉ However,ᵉ sinceᵉ
[monoidsᵉ areᵉ one-objectᵉ precategories](category-theory.one-object-precategories.md),ᵉ
weᵉ canᵉ encodeᵉ thisᵉ asᵉ aᵉ functorᵉ ofᵉ categoriesᵉ `Mᵉ → C`.ᵉ

## Definition

### Representations of a monoid in a precategory

```agda
representation-precategory-Monoidᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Mᵉ : Monoidᵉ l1ᵉ) (Cᵉ : Precategoryᵉ l2ᵉ l3ᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
representation-precategory-Monoidᵉ Mᵉ Cᵉ =
  functor-Precategoryᵉ (precategory-one-object-precategory-Monoidᵉ Mᵉ) Cᵉ

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Mᵉ : Monoidᵉ l1ᵉ) (Cᵉ : Precategoryᵉ l2ᵉ l3ᵉ)
  (ρᵉ : representation-precategory-Monoidᵉ Mᵉ Cᵉ)
  where

  obj-representation-precategory-Monoidᵉ : obj-Precategoryᵉ Cᵉ
  obj-representation-precategory-Monoidᵉ = pr1ᵉ ρᵉ starᵉ

  action-representation-precategory-Monoidᵉ :
    type-Monoidᵉ Mᵉ →
    type-endo-Precategoryᵉ Cᵉ obj-representation-precategory-Monoidᵉ
  action-representation-precategory-Monoidᵉ = pr1ᵉ (pr2ᵉ ρᵉ)

  preserves-mul-action-representation-precategory-Monoidᵉ :
    ( xᵉ yᵉ : type-Monoidᵉ Mᵉ) →
    ( action-representation-precategory-Monoidᵉ (mul-Monoidᵉ Mᵉ xᵉ yᵉ)) ＝ᵉ
    ( comp-endo-Precategoryᵉ Cᵉ
      ( obj-representation-precategory-Monoidᵉ)
      ( action-representation-precategory-Monoidᵉ xᵉ)
      ( action-representation-precategory-Monoidᵉ yᵉ))
  preserves-mul-action-representation-precategory-Monoidᵉ =
    preserves-comp-functor-Precategoryᵉ
      ( precategory-one-object-precategory-Monoidᵉ Mᵉ) Cᵉ ρᵉ

  preserves-unit-action-representation-precategory-Monoidᵉ :
    action-representation-precategory-Monoidᵉ (unit-Monoidᵉ Mᵉ) ＝ᵉ
    id-endo-Precategoryᵉ Cᵉ obj-representation-precategory-Monoidᵉ
  preserves-unit-action-representation-precategory-Monoidᵉ =
    preserves-id-functor-Precategoryᵉ
      ( precategory-one-object-precategory-Monoidᵉ Mᵉ) Cᵉ ρᵉ starᵉ
```

### The total type of representations of a monoid

```agda
Representation-Precategory-Monoidᵉ :
  {l1ᵉ : Level} (Mᵉ : Monoidᵉ l1ᵉ) (l2ᵉ l3ᵉ : Level) → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ ⊔ lsuc l3ᵉ)
Representation-Precategory-Monoidᵉ Mᵉ l2ᵉ l3ᵉ =
  Σᵉ (Precategoryᵉ l2ᵉ l3ᵉ) (representation-precategory-Monoidᵉ Mᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Mᵉ : Monoidᵉ l1ᵉ)
  (ρᵉ : Representation-Precategory-Monoidᵉ Mᵉ l2ᵉ l3ᵉ)
  where

  precategory-Representation-Precategory-Monoidᵉ : Precategoryᵉ l2ᵉ l3ᵉ
  precategory-Representation-Precategory-Monoidᵉ = pr1ᵉ ρᵉ

  representation-precategory-Representation-Precategory-Monoidᵉ :
    representation-precategory-Monoidᵉ Mᵉ
      ( precategory-Representation-Precategory-Monoidᵉ)
  representation-precategory-Representation-Precategory-Monoidᵉ = pr2ᵉ ρᵉ

  obj-Representation-Precategory-Monoidᵉ :
    obj-Precategoryᵉ precategory-Representation-Precategory-Monoidᵉ
  obj-Representation-Precategory-Monoidᵉ =
    obj-representation-precategory-Monoidᵉ Mᵉ
      ( precategory-Representation-Precategory-Monoidᵉ)
      ( representation-precategory-Representation-Precategory-Monoidᵉ)

  action-Representation-Precategory-Monoidᵉ :
    type-Monoidᵉ Mᵉ →
    type-endo-Precategoryᵉ
      ( precategory-Representation-Precategory-Monoidᵉ)
      ( obj-Representation-Precategory-Monoidᵉ)
  action-Representation-Precategory-Monoidᵉ =
    action-representation-precategory-Monoidᵉ Mᵉ
      ( precategory-Representation-Precategory-Monoidᵉ)
      ( representation-precategory-Representation-Precategory-Monoidᵉ)

  preserves-mul-action-Representation-Precategory-Monoidᵉ :
    ( xᵉ yᵉ : type-Monoidᵉ Mᵉ) →
    ( action-Representation-Precategory-Monoidᵉ (mul-Monoidᵉ Mᵉ xᵉ yᵉ)) ＝ᵉ
    ( comp-endo-Precategoryᵉ
      ( precategory-Representation-Precategory-Monoidᵉ)
      ( obj-Representation-Precategory-Monoidᵉ)
      ( action-Representation-Precategory-Monoidᵉ xᵉ)
      ( action-Representation-Precategory-Monoidᵉ yᵉ))
  preserves-mul-action-Representation-Precategory-Monoidᵉ =
    preserves-mul-action-representation-precategory-Monoidᵉ Mᵉ
      ( precategory-Representation-Precategory-Monoidᵉ)
      ( representation-precategory-Representation-Precategory-Monoidᵉ)

  preserves-unit-action-Representation-Precategory-Monoidᵉ :
    action-Representation-Precategory-Monoidᵉ (unit-Monoidᵉ Mᵉ) ＝ᵉ
    id-endo-Precategoryᵉ
      ( precategory-Representation-Precategory-Monoidᵉ)
      ( obj-Representation-Precategory-Monoidᵉ)
  preserves-unit-action-Representation-Precategory-Monoidᵉ =
    preserves-unit-action-representation-precategory-Monoidᵉ Mᵉ
      ( precategory-Representation-Precategory-Monoidᵉ)
      ( representation-precategory-Representation-Precategory-Monoidᵉ)
```