# Anafunctors between categories

```agda
module category-theory.anafunctors-categoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.anafunctors-precategoriesᵉ
open import category-theory.categoriesᵉ
open import category-theory.functors-categoriesᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Anᵉ **anafunctor**ᵉ isᵉ aᵉ [functor](category-theory.functors-categories.mdᵉ) thatᵉ isᵉ
onlyᵉ definedᵉ upᵉ to [isomorphism](category-theory.isomorphisms-in-categories.md).ᵉ

## Definition

```agda
anafunctor-Categoryᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (lᵉ : Level) →
  Categoryᵉ l1ᵉ l2ᵉ → Categoryᵉ l3ᵉ l4ᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ ⊔ lsuc lᵉ)
anafunctor-Categoryᵉ lᵉ Cᵉ Dᵉ =
  anafunctor-Precategoryᵉ lᵉ (precategory-Categoryᵉ Cᵉ) (precategory-Categoryᵉ Dᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level} (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ) (Dᵉ : Categoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ : anafunctor-Categoryᵉ l5ᵉ Cᵉ Dᵉ)
  where

  object-anafunctor-Categoryᵉ : obj-Categoryᵉ Cᵉ → obj-Categoryᵉ Dᵉ → UUᵉ l5ᵉ
  object-anafunctor-Categoryᵉ =
    object-anafunctor-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( precategory-Categoryᵉ Dᵉ)
      ( Fᵉ)

  hom-anafunctor-Categoryᵉ :
    (Xᵉ Yᵉ : obj-Categoryᵉ Cᵉ) (Uᵉ : obj-Categoryᵉ Dᵉ)
    (uᵉ : object-anafunctor-Categoryᵉ Xᵉ Uᵉ)
    (Vᵉ : obj-Categoryᵉ Dᵉ) (vᵉ : object-anafunctor-Categoryᵉ Yᵉ Vᵉ) →
    hom-Categoryᵉ Cᵉ Xᵉ Yᵉ → hom-Categoryᵉ Dᵉ Uᵉ Vᵉ
  hom-anafunctor-Categoryᵉ =
    hom-anafunctor-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( precategory-Categoryᵉ Dᵉ)
      ( Fᵉ)
```

## Properties

### Any functor between categories induces an anafunctor

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ) (Dᵉ : Categoryᵉ l3ᵉ l4ᵉ)
  where

  anafunctor-functor-Categoryᵉ :
    functor-Categoryᵉ Cᵉ Dᵉ → anafunctor-Categoryᵉ l4ᵉ Cᵉ Dᵉ
  anafunctor-functor-Categoryᵉ =
    anafunctor-functor-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( precategory-Categoryᵉ Dᵉ)
```

### The action on objects of an anafunctor between categories

```agda
image-object-anafunctor-Categoryᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level} (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ) (Dᵉ : Categoryᵉ l3ᵉ l4ᵉ) →
  anafunctor-Categoryᵉ l5ᵉ Cᵉ Dᵉ → obj-Categoryᵉ Cᵉ → UUᵉ (l3ᵉ ⊔ l5ᵉ)
image-object-anafunctor-Categoryᵉ Cᵉ Dᵉ Fᵉ Xᵉ =
  Σᵉ ( obj-Categoryᵉ Dᵉ)
    ( λ Uᵉ → type-trunc-Propᵉ (object-anafunctor-Categoryᵉ Cᵉ Dᵉ Fᵉ Xᵉ Uᵉ))
```