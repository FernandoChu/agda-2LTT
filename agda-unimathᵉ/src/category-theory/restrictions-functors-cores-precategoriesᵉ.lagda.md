# Restrictions of functors to cores of precategories

```agda
module category-theory.restrictions-functors-cores-precategoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.cores-precategoriesᵉ
open import category-theory.faithful-functors-precategoriesᵉ
open import category-theory.fully-faithful-functors-precategoriesᵉ
open import category-theory.functors-precategoriesᵉ
open import category-theory.isomorphisms-in-precategoriesᵉ
open import category-theory.maps-precategoriesᵉ
open import category-theory.precategoriesᵉ
open import category-theory.pseudomonic-functors-precategoriesᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.subtypesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Forᵉ everyᵉ [functor](category-theory.functors-precategories.mdᵉ) `Fᵉ : Cᵉ → D`ᵉ thereᵉ
isᵉ aᵉ restrictionᵉ functorᵉ betweenᵉ theirᵉ
[cores](category-theory.cores-precategories.mdᵉ)

```text
  coreᵉ Fᵉ : coreᵉ Cᵉ → coreᵉ Dᵉ
```

thatᵉ fitᵉ intoᵉ aᵉ naturalᵉ diagramᵉ

```text
          coreᵉ Fᵉ
  coreᵉ Cᵉ ------->ᵉ coreᵉ Dᵉ
    |               |
    |               |
    |               |
    |               |
    ∨ᵉ               ∨ᵉ
    Cᵉ ------------>ᵉ D.ᵉ
            Fᵉ
```

## Definitions

### Restrictions of functors to cores of precategories

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ) (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ : functor-Precategoryᵉ Cᵉ Dᵉ)
  where

  obj-functor-core-Precategoryᵉ :
    obj-Precategoryᵉ (core-precategory-Precategoryᵉ Cᵉ) →
    obj-Precategoryᵉ (core-precategory-Precategoryᵉ Dᵉ)
  obj-functor-core-Precategoryᵉ = obj-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ

  hom-functor-core-Precategoryᵉ :
    {xᵉ yᵉ : obj-Precategoryᵉ (core-precategory-Precategoryᵉ Cᵉ)} →
    hom-Precategoryᵉ (core-precategory-Precategoryᵉ Cᵉ) xᵉ yᵉ →
    hom-Precategoryᵉ
      ( core-precategory-Precategoryᵉ Dᵉ)
      ( obj-functor-core-Precategoryᵉ xᵉ)
      ( obj-functor-core-Precategoryᵉ yᵉ)
  hom-functor-core-Precategoryᵉ = preserves-iso-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ

  map-functor-core-Precategoryᵉ :
    map-Precategoryᵉ
      ( core-precategory-Precategoryᵉ Cᵉ)
      ( core-precategory-Precategoryᵉ Dᵉ)
  pr1ᵉ map-functor-core-Precategoryᵉ = obj-functor-core-Precategoryᵉ
  pr2ᵉ map-functor-core-Precategoryᵉ = hom-functor-core-Precategoryᵉ

  preserves-id-functor-core-Precategoryᵉ :
    preserves-id-hom-map-Precategoryᵉ
      ( core-precategory-Precategoryᵉ Cᵉ)
      ( core-precategory-Precategoryᵉ Dᵉ)
      ( map-functor-core-Precategoryᵉ)
  preserves-id-functor-core-Precategoryᵉ xᵉ =
    eq-type-subtypeᵉ
      ( is-iso-prop-Precategoryᵉ Dᵉ)
      ( preserves-id-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ xᵉ)

  preserves-comp-functor-core-Precategoryᵉ :
    preserves-comp-hom-map-Precategoryᵉ
      ( core-precategory-Precategoryᵉ Cᵉ)
      ( core-precategory-Precategoryᵉ Dᵉ)
      ( map-functor-core-Precategoryᵉ)
  preserves-comp-functor-core-Precategoryᵉ gᵉ fᵉ =
    eq-type-subtypeᵉ
      ( is-iso-prop-Precategoryᵉ Dᵉ)
      ( preserves-comp-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ
        ( hom-iso-Precategoryᵉ Cᵉ gᵉ)
        ( hom-iso-Precategoryᵉ Cᵉ fᵉ))

  is-functor-functor-core-Precategoryᵉ :
    is-functor-map-Precategoryᵉ
      ( core-precategory-Precategoryᵉ Cᵉ)
      ( core-precategory-Precategoryᵉ Dᵉ)
      map-functor-core-Precategoryᵉ
  pr1ᵉ is-functor-functor-core-Precategoryᵉ =
    preserves-comp-functor-core-Precategoryᵉ
  pr2ᵉ is-functor-functor-core-Precategoryᵉ =
    preserves-id-functor-core-Precategoryᵉ

  functor-core-Precategoryᵉ :
    functor-Precategoryᵉ
      ( core-precategory-Precategoryᵉ Cᵉ)
      ( core-precategory-Precategoryᵉ Dᵉ)
  pr1ᵉ functor-core-Precategoryᵉ = obj-functor-core-Precategoryᵉ
  pr1ᵉ (pr2ᵉ functor-core-Precategoryᵉ) = hom-functor-core-Precategoryᵉ
  pr2ᵉ (pr2ᵉ functor-core-Precategoryᵉ) = is-functor-functor-core-Precategoryᵉ
```

## Properties

### Faithful functors restrict to faithful functors on the core

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ) (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  where

  is-faithful-functor-core-is-faithful-functor-Precategoryᵉ :
    (Fᵉ : functor-Precategoryᵉ Cᵉ Dᵉ) →
    is-faithful-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ →
    is-faithful-functor-Precategoryᵉ
      ( core-precategory-Precategoryᵉ Cᵉ)
      ( core-precategory-Precategoryᵉ Dᵉ)
      ( functor-core-Precategoryᵉ Cᵉ Dᵉ Fᵉ)
  is-faithful-functor-core-is-faithful-functor-Precategoryᵉ =
    is-faithful-on-isos-is-faithful-functor-Precategoryᵉ Cᵉ Dᵉ
```

### Pseudomonic functors restrict to fully faithful functors on the core

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ) (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ : functor-Precategoryᵉ Cᵉ Dᵉ)
  (is-pseudomonic-Fᵉ : is-pseudomonic-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ)
  where

  is-fully-faithful-functor-core-is-pseudomonic-functor-Precategoryᵉ :
    is-fully-faithful-functor-Precategoryᵉ
      ( core-precategory-Precategoryᵉ Cᵉ)
      ( core-precategory-Precategoryᵉ Dᵉ)
      ( functor-core-Precategoryᵉ Cᵉ Dᵉ Fᵉ)
  is-fully-faithful-functor-core-is-pseudomonic-functor-Precategoryᵉ xᵉ yᵉ =
    is-equiv-preserves-iso-is-pseudomonic-functor-Precategoryᵉ
      Cᵉ Dᵉ Fᵉ is-pseudomonic-Fᵉ
```

### Fully faithful functors restrict to fully faithful functors on the core

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ) (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ : functor-Precategoryᵉ Cᵉ Dᵉ)
  (is-ff-Fᵉ : is-fully-faithful-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ)
  where

  is-fully-faithful-functor-core-is-fully-faithful-functor-Precategoryᵉ :
    is-fully-faithful-functor-Precategoryᵉ
      ( core-precategory-Precategoryᵉ Cᵉ)
      ( core-precategory-Precategoryᵉ Dᵉ)
      ( functor-core-Precategoryᵉ Cᵉ Dᵉ Fᵉ)
  is-fully-faithful-functor-core-is-fully-faithful-functor-Precategoryᵉ =
    is-fully-faithful-functor-core-is-pseudomonic-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ
      ( is-pseudomonic-is-fully-faithful-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ is-ff-Fᵉ)
```

## External links

-ᵉ [Theᵉ coreᵉ ofᵉ aᵉ category](https://1lab.dev/Cat.Instances.Core.htmlᵉ) atᵉ 1labᵉ
-ᵉ [coreᵉ groupoid](https://ncatlab.org/nlab/show/core+groupoidᵉ) atᵉ $n$Labᵉ