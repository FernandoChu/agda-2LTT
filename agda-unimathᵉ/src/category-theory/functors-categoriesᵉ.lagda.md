# Functors between categories

```agda
module category-theory.functors-categoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categoriesᵉ
open import category-theory.functors-precategoriesᵉ
open import category-theory.isomorphisms-in-categoriesᵉ
open import category-theory.maps-categoriesᵉ

open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Aᵉ **functor**ᵉ betweenᵉ twoᵉ [categories](category-theory.categories.mdᵉ) isᵉ aᵉ
[functor](category-theory.functors-precategories.mdᵉ) betweenᵉ theᵉ underlyingᵉ
[precategories](category-theory.precategories.md).ᵉ

## Definition

### The predicate on maps between categories of being a functor

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Categoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ : map-Categoryᵉ Cᵉ Dᵉ)
  where

  preserves-comp-hom-map-Categoryᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l4ᵉ)
  preserves-comp-hom-map-Categoryᵉ =
    preserves-comp-hom-map-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( precategory-Categoryᵉ Dᵉ)
      ( Fᵉ)

  preserves-id-hom-map-Categoryᵉ : UUᵉ (l1ᵉ ⊔ l4ᵉ)
  preserves-id-hom-map-Categoryᵉ =
    preserves-id-hom-map-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( precategory-Categoryᵉ Dᵉ)
      ( Fᵉ)

  is-functor-map-Categoryᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l4ᵉ)
  is-functor-map-Categoryᵉ =
    is-functor-map-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( precategory-Categoryᵉ Dᵉ)
      ( Fᵉ)

  preserves-comp-is-functor-map-Categoryᵉ :
    is-functor-map-Categoryᵉ → preserves-comp-hom-map-Categoryᵉ
  preserves-comp-is-functor-map-Categoryᵉ =
    preserves-comp-is-functor-map-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( precategory-Categoryᵉ Dᵉ)
      ( Fᵉ)

  preserves-id-is-functor-map-Categoryᵉ :
    is-functor-map-Categoryᵉ → preserves-id-hom-map-Categoryᵉ
  preserves-id-is-functor-map-Categoryᵉ =
    preserves-id-is-functor-map-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( precategory-Categoryᵉ Dᵉ)
      ( Fᵉ)
```

### functors between categories

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Categoryᵉ l3ᵉ l4ᵉ)
  where

  functor-Categoryᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  functor-Categoryᵉ =
    functor-Precategoryᵉ (precategory-Categoryᵉ Cᵉ) (precategory-Categoryᵉ Dᵉ)

  obj-functor-Categoryᵉ : functor-Categoryᵉ → obj-Categoryᵉ Cᵉ → obj-Categoryᵉ Dᵉ
  obj-functor-Categoryᵉ =
    obj-functor-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( precategory-Categoryᵉ Dᵉ)

  hom-functor-Categoryᵉ :
    (Fᵉ : functor-Categoryᵉ) →
    {xᵉ yᵉ : obj-Categoryᵉ Cᵉ} →
    (fᵉ : hom-Categoryᵉ Cᵉ xᵉ yᵉ) →
    hom-Categoryᵉ Dᵉ
      ( obj-functor-Categoryᵉ Fᵉ xᵉ)
      ( obj-functor-Categoryᵉ Fᵉ yᵉ)
  hom-functor-Categoryᵉ =
    hom-functor-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( precategory-Categoryᵉ Dᵉ)

  map-functor-Categoryᵉ : functor-Categoryᵉ → map-Categoryᵉ Cᵉ Dᵉ
  map-functor-Categoryᵉ =
    map-functor-Precategoryᵉ (precategory-Categoryᵉ Cᵉ) (precategory-Categoryᵉ Dᵉ)

  is-functor-functor-Categoryᵉ :
    (Fᵉ : functor-Categoryᵉ) →
    is-functor-map-Categoryᵉ Cᵉ Dᵉ (map-functor-Categoryᵉ Fᵉ)
  is-functor-functor-Categoryᵉ =
    is-functor-functor-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( precategory-Categoryᵉ Dᵉ)

  preserves-comp-functor-Categoryᵉ :
    ( Fᵉ : functor-Categoryᵉ) {xᵉ yᵉ zᵉ : obj-Categoryᵉ Cᵉ}
    ( gᵉ : hom-Categoryᵉ Cᵉ yᵉ zᵉ) (fᵉ : hom-Categoryᵉ Cᵉ xᵉ yᵉ) →
    ( hom-functor-Categoryᵉ Fᵉ (comp-hom-Categoryᵉ Cᵉ gᵉ fᵉ)) ＝ᵉ
    ( comp-hom-Categoryᵉ Dᵉ
      ( hom-functor-Categoryᵉ Fᵉ gᵉ)
      ( hom-functor-Categoryᵉ Fᵉ fᵉ))
  preserves-comp-functor-Categoryᵉ =
    preserves-comp-functor-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( precategory-Categoryᵉ Dᵉ)

  preserves-id-functor-Categoryᵉ :
    (Fᵉ : functor-Categoryᵉ) (xᵉ : obj-Categoryᵉ Cᵉ) →
    hom-functor-Categoryᵉ Fᵉ (id-hom-Categoryᵉ Cᵉ {xᵉ}) ＝ᵉ
    id-hom-Categoryᵉ Dᵉ {obj-functor-Categoryᵉ Fᵉ xᵉ}
  preserves-id-functor-Categoryᵉ =
    preserves-id-functor-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( precategory-Categoryᵉ Dᵉ)
```

## Examples

### The identity functor

Thereᵉ isᵉ anᵉ identityᵉ functorᵉ onᵉ anyᵉ category.ᵉ

```agda
id-functor-Categoryᵉ :
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ) → functor-Categoryᵉ Cᵉ Cᵉ
id-functor-Categoryᵉ Cᵉ = id-functor-Precategoryᵉ (precategory-Categoryᵉ Cᵉ)
```

### Composition of functors

Anyᵉ twoᵉ compatibleᵉ functorsᵉ canᵉ beᵉ composedᵉ to aᵉ newᵉ functor.ᵉ

```agda
comp-functor-Categoryᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level}
  (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ) (Dᵉ : Categoryᵉ l3ᵉ l4ᵉ) (Eᵉ : Categoryᵉ l5ᵉ l6ᵉ) →
  functor-Categoryᵉ Dᵉ Eᵉ → functor-Categoryᵉ Cᵉ Dᵉ → functor-Categoryᵉ Cᵉ Eᵉ
comp-functor-Categoryᵉ Cᵉ Dᵉ Eᵉ =
  comp-functor-Precategoryᵉ
    ( precategory-Categoryᵉ Cᵉ)
    ( precategory-Categoryᵉ Dᵉ)
    ( precategory-Categoryᵉ Eᵉ)
```

## Properties

### Respecting identities and compositions are propositions

Thisᵉ followsᵉ fromᵉ theᵉ factᵉ thatᵉ theᵉ hom-typesᵉ areᵉ
[sets](foundation-core.sets.md).ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Categoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ : map-Categoryᵉ Cᵉ Dᵉ)
  where

  is-prop-preserves-comp-hom-map-Categoryᵉ :
    is-propᵉ (preserves-comp-hom-map-Categoryᵉ Cᵉ Dᵉ Fᵉ)
  is-prop-preserves-comp-hom-map-Categoryᵉ =
    is-prop-preserves-comp-hom-map-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( precategory-Categoryᵉ Dᵉ)
      ( Fᵉ)

  preserves-comp-hom-prop-map-Categoryᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l4ᵉ)
  preserves-comp-hom-prop-map-Categoryᵉ =
    preserves-comp-hom-prop-map-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( precategory-Categoryᵉ Dᵉ)
      ( Fᵉ)

  is-prop-preserves-id-hom-map-Categoryᵉ :
    is-propᵉ (preserves-id-hom-map-Categoryᵉ Cᵉ Dᵉ Fᵉ)
  is-prop-preserves-id-hom-map-Categoryᵉ =
    is-prop-preserves-id-hom-map-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( precategory-Categoryᵉ Dᵉ)
      ( Fᵉ)

  preserves-id-hom-prop-map-Categoryᵉ : Propᵉ (l1ᵉ ⊔ l4ᵉ)
  preserves-id-hom-prop-map-Categoryᵉ =
    preserves-id-hom-prop-map-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( precategory-Categoryᵉ Dᵉ)
      ( Fᵉ)

  is-prop-is-functor-map-Categoryᵉ :
    is-propᵉ (is-functor-map-Categoryᵉ Cᵉ Dᵉ Fᵉ)
  is-prop-is-functor-map-Categoryᵉ =
    is-prop-is-functor-map-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( precategory-Categoryᵉ Dᵉ)
      ( Fᵉ)

  is-functor-prop-map-Categoryᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l4ᵉ)
  is-functor-prop-map-Categoryᵉ =
    is-functor-prop-map-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( precategory-Categoryᵉ Dᵉ)
      ( Fᵉ)
```

### Extensionality of functors between categories

#### Equality of functors is equality of underlying maps

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Categoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ Gᵉ : functor-Categoryᵉ Cᵉ Dᵉ)
  where

  equiv-eq-map-eq-functor-Categoryᵉ :
    (Fᵉ ＝ᵉ Gᵉ) ≃ᵉ (map-functor-Categoryᵉ Cᵉ Dᵉ Fᵉ ＝ᵉ map-functor-Categoryᵉ Cᵉ Dᵉ Gᵉ)
  equiv-eq-map-eq-functor-Categoryᵉ =
    equiv-eq-map-eq-functor-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( precategory-Categoryᵉ Dᵉ)
      ( Fᵉ)
      ( Gᵉ)

  eq-map-eq-functor-Categoryᵉ :
    (Fᵉ ＝ᵉ Gᵉ) → (map-functor-Categoryᵉ Cᵉ Dᵉ Fᵉ ＝ᵉ map-functor-Categoryᵉ Cᵉ Dᵉ Gᵉ)
  eq-map-eq-functor-Categoryᵉ =
    map-equivᵉ equiv-eq-map-eq-functor-Categoryᵉ

  eq-eq-map-functor-Categoryᵉ :
    (map-functor-Categoryᵉ Cᵉ Dᵉ Fᵉ ＝ᵉ map-functor-Categoryᵉ Cᵉ Dᵉ Gᵉ) → (Fᵉ ＝ᵉ Gᵉ)
  eq-eq-map-functor-Categoryᵉ =
    map-inv-equivᵉ equiv-eq-map-eq-functor-Categoryᵉ

  is-section-eq-eq-map-functor-Categoryᵉ :
    eq-map-eq-functor-Categoryᵉ ∘ᵉ eq-eq-map-functor-Categoryᵉ ~ᵉ idᵉ
  is-section-eq-eq-map-functor-Categoryᵉ =
    is-section-map-inv-equivᵉ equiv-eq-map-eq-functor-Categoryᵉ

  is-retraction-eq-eq-map-functor-Categoryᵉ :
    eq-eq-map-functor-Categoryᵉ ∘ᵉ eq-map-eq-functor-Categoryᵉ ~ᵉ idᵉ
  is-retraction-eq-eq-map-functor-Categoryᵉ =
    is-retraction-map-inv-equivᵉ equiv-eq-map-eq-functor-Categoryᵉ
```

#### Equality of functors is homotopy of underlying maps

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Categoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ Gᵉ : functor-Categoryᵉ Cᵉ Dᵉ)
  where

  htpy-functor-Categoryᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  htpy-functor-Categoryᵉ =
    htpy-functor-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( precategory-Categoryᵉ Dᵉ)
      ( Fᵉ)
      ( Gᵉ)

  equiv-htpy-eq-functor-Categoryᵉ : (Fᵉ ＝ᵉ Gᵉ) ≃ᵉ htpy-functor-Categoryᵉ
  equiv-htpy-eq-functor-Categoryᵉ =
    equiv-htpy-eq-functor-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( precategory-Categoryᵉ Dᵉ)
      ( Fᵉ)
      ( Gᵉ)

  htpy-eq-functor-Categoryᵉ : Fᵉ ＝ᵉ Gᵉ → htpy-functor-Categoryᵉ
  htpy-eq-functor-Categoryᵉ =
    map-equivᵉ equiv-htpy-eq-functor-Categoryᵉ

  eq-htpy-functor-Categoryᵉ : htpy-functor-Categoryᵉ → Fᵉ ＝ᵉ Gᵉ
  eq-htpy-functor-Categoryᵉ =
    map-inv-equivᵉ equiv-htpy-eq-functor-Categoryᵉ

  is-section-eq-htpy-functor-Categoryᵉ :
    htpy-eq-functor-Categoryᵉ ∘ᵉ eq-htpy-functor-Categoryᵉ ~ᵉ idᵉ
  is-section-eq-htpy-functor-Categoryᵉ =
    is-section-map-inv-equivᵉ equiv-htpy-eq-functor-Categoryᵉ

  is-retraction-eq-htpy-functor-Categoryᵉ :
    eq-htpy-functor-Categoryᵉ ∘ᵉ htpy-eq-functor-Categoryᵉ ~ᵉ idᵉ
  is-retraction-eq-htpy-functor-Categoryᵉ =
    is-retraction-map-inv-equivᵉ equiv-htpy-eq-functor-Categoryᵉ
```

### Functors preserve isomorphisms

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Categoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ : functor-Categoryᵉ Cᵉ Dᵉ)
  {xᵉ yᵉ : obj-Categoryᵉ Cᵉ}
  where

  preserves-is-iso-functor-Categoryᵉ :
    (fᵉ : hom-Categoryᵉ Cᵉ xᵉ yᵉ) →
    is-iso-Categoryᵉ Cᵉ fᵉ →
    is-iso-Categoryᵉ Dᵉ (hom-functor-Categoryᵉ Cᵉ Dᵉ Fᵉ fᵉ)
  preserves-is-iso-functor-Categoryᵉ =
    preserves-is-iso-functor-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( precategory-Categoryᵉ Dᵉ)
      ( Fᵉ)

  preserves-iso-functor-Categoryᵉ :
    iso-Categoryᵉ Cᵉ xᵉ yᵉ →
    iso-Categoryᵉ Dᵉ
      ( obj-functor-Categoryᵉ Cᵉ Dᵉ Fᵉ xᵉ)
      ( obj-functor-Categoryᵉ Cᵉ Dᵉ Fᵉ yᵉ)
  preserves-iso-functor-Categoryᵉ =
    preserves-iso-functor-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( precategory-Categoryᵉ Dᵉ)
      ( Fᵉ)
```

## See also

-ᵉ [Theᵉ categoryᵉ ofᵉ functorsᵉ andᵉ naturalᵉ transformationsᵉ betweenᵉ categories](category-theory.category-of-functors.mdᵉ)