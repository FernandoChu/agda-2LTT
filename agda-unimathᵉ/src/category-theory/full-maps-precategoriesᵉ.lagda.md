# Full maps between precategories

```agda
module category-theory.full-maps-precategoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.maps-precategoriesᵉ
open import category-theory.precategoriesᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.function-typesᵉ
open import foundation.iterated-dependent-product-typesᵉ
open import foundation.propositionsᵉ
open import foundation.surjective-mapsᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Aᵉ [map](category-theory.maps-precategories.mdᵉ) betweenᵉ
[precategories](category-theory.precategories.mdᵉ) `C`ᵉ andᵉ `D`ᵉ isᵉ **full**ᵉ ifᵉ
it'sᵉ aᵉ [surjection](foundation.surjective-maps.mdᵉ) onᵉ
hom-[sets](foundation-core.sets.md).ᵉ

## Definition

### The predicate on maps between precategories of being full

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ : map-Precategoryᵉ Cᵉ Dᵉ)
  where

  is-full-map-Precategoryᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l4ᵉ)
  is-full-map-Precategoryᵉ =
    (xᵉ yᵉ : obj-Precategoryᵉ Cᵉ) →
    is-surjectiveᵉ (hom-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ {xᵉ} {yᵉ})

  is-prop-is-full-map-Precategoryᵉ : is-propᵉ is-full-map-Precategoryᵉ
  is-prop-is-full-map-Precategoryᵉ =
    is-prop-iterated-Πᵉ 2
      ( λ xᵉ yᵉ → is-prop-is-surjectiveᵉ (hom-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ {xᵉ} {yᵉ}))

  is-full-prop-map-Precategoryᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l4ᵉ)
  pr1ᵉ is-full-prop-map-Precategoryᵉ = is-full-map-Precategoryᵉ
  pr2ᵉ is-full-prop-map-Precategoryᵉ = is-prop-is-full-map-Precategoryᵉ
```

### The type of full maps between two precategories

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  where

  full-map-Precategoryᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  full-map-Precategoryᵉ =
    Σᵉ (map-Precategoryᵉ Cᵉ Dᵉ) (is-full-map-Precategoryᵉ Cᵉ Dᵉ)

  map-full-map-Precategoryᵉ :
    full-map-Precategoryᵉ → map-Precategoryᵉ Cᵉ Dᵉ
  map-full-map-Precategoryᵉ = pr1ᵉ

  is-full-full-map-Precategoryᵉ :
    (Fᵉ : full-map-Precategoryᵉ) →
    is-full-map-Precategoryᵉ Cᵉ Dᵉ (map-full-map-Precategoryᵉ Fᵉ)
  is-full-full-map-Precategoryᵉ = pr2ᵉ

  obj-full-map-Precategoryᵉ :
    full-map-Precategoryᵉ → obj-Precategoryᵉ Cᵉ → obj-Precategoryᵉ Dᵉ
  obj-full-map-Precategoryᵉ =
    obj-map-Precategoryᵉ Cᵉ Dᵉ ∘ᵉ map-full-map-Precategoryᵉ

  hom-full-map-Precategoryᵉ :
    (Fᵉ : full-map-Precategoryᵉ) {xᵉ yᵉ : obj-Precategoryᵉ Cᵉ} →
    hom-Precategoryᵉ Cᵉ xᵉ yᵉ →
    hom-Precategoryᵉ Dᵉ
      ( obj-full-map-Precategoryᵉ Fᵉ xᵉ)
      ( obj-full-map-Precategoryᵉ Fᵉ yᵉ)
  hom-full-map-Precategoryᵉ =
    hom-map-Precategoryᵉ Cᵉ Dᵉ ∘ᵉ map-full-map-Precategoryᵉ
```