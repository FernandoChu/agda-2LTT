# Full functors between precategories

```agda
module category-theory.full-functors-precategoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.full-maps-precategoriesᵉ
open import category-theory.functors-precategoriesᵉ
open import category-theory.precategoriesᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.function-typesᵉ
open import foundation.propositionsᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Aᵉ [functor](category-theory.functors-precategories.mdᵉ) betweenᵉ
[precategories](category-theory.precategories.mdᵉ) `C`ᵉ andᵉ `D`ᵉ isᵉ **full**ᵉ ifᵉ
it'sᵉ [surjective](foundation.surjective-maps.mdᵉ) onᵉ
hom-[sets](foundation-core.sets.md).ᵉ

## Definition

### The predicate on functors between precategories of being full

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ : functor-Precategoryᵉ Cᵉ Dᵉ)
  where

  is-full-functor-Precategoryᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l4ᵉ)
  is-full-functor-Precategoryᵉ =
    is-full-map-Precategoryᵉ Cᵉ Dᵉ (map-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ)

  is-prop-is-full-functor-Precategoryᵉ :
    is-propᵉ is-full-functor-Precategoryᵉ
  is-prop-is-full-functor-Precategoryᵉ =
    is-prop-is-full-map-Precategoryᵉ Cᵉ Dᵉ (map-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ)

  is-full-prop-functor-Precategoryᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l4ᵉ)
  is-full-prop-functor-Precategoryᵉ =
    is-full-prop-map-Precategoryᵉ Cᵉ Dᵉ (map-functor-Precategoryᵉ Cᵉ Dᵉ Fᵉ)
```

### The type of full functors between two precategories

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  where

  full-functor-Precategoryᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  full-functor-Precategoryᵉ =
    Σᵉ (functor-Precategoryᵉ Cᵉ Dᵉ) (is-full-functor-Precategoryᵉ Cᵉ Dᵉ)

  functor-full-functor-Precategoryᵉ :
    full-functor-Precategoryᵉ → functor-Precategoryᵉ Cᵉ Dᵉ
  functor-full-functor-Precategoryᵉ = pr1ᵉ

  is-full-full-functor-Precategoryᵉ :
    (Fᵉ : full-functor-Precategoryᵉ) →
    is-full-functor-Precategoryᵉ Cᵉ Dᵉ (functor-full-functor-Precategoryᵉ Fᵉ)
  is-full-full-functor-Precategoryᵉ = pr2ᵉ

  obj-full-functor-Precategoryᵉ :
    full-functor-Precategoryᵉ → obj-Precategoryᵉ Cᵉ → obj-Precategoryᵉ Dᵉ
  obj-full-functor-Precategoryᵉ =
    obj-functor-Precategoryᵉ Cᵉ Dᵉ ∘ᵉ functor-full-functor-Precategoryᵉ

  hom-full-functor-Precategoryᵉ :
    (Fᵉ : full-functor-Precategoryᵉ) {xᵉ yᵉ : obj-Precategoryᵉ Cᵉ} →
    hom-Precategoryᵉ Cᵉ xᵉ yᵉ →
    hom-Precategoryᵉ Dᵉ
      ( obj-full-functor-Precategoryᵉ Fᵉ xᵉ)
      ( obj-full-functor-Precategoryᵉ Fᵉ yᵉ)
  hom-full-functor-Precategoryᵉ =
    hom-functor-Precategoryᵉ Cᵉ Dᵉ ∘ᵉ functor-full-functor-Precategoryᵉ
```