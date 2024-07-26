# Maps between categories

```agda
module category-theory.maps-categoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categoriesᵉ
open import category-theory.maps-precategoriesᵉ

open import foundation.equivalencesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Aᵉ **map**ᵉ fromᵉ aᵉ [category](category-theory.categories.mdᵉ) `C`ᵉ to aᵉ categoryᵉ `D`ᵉ
consistsᵉ ofᵉ:

-ᵉ aᵉ mapᵉ `F₀ᵉ : Cᵉ → D`ᵉ onᵉ objects,ᵉ
-ᵉ aᵉ mapᵉ `F₁ᵉ : homᵉ xᵉ yᵉ → homᵉ (F₀ᵉ xᵉ) (F₀ᵉ y)`ᵉ onᵉ morphismsᵉ

## Definition

### Maps between categories

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Categoryᵉ l3ᵉ l4ᵉ)
  where

  map-Categoryᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  map-Categoryᵉ =
    map-Precategoryᵉ (precategory-Categoryᵉ Cᵉ) (precategory-Categoryᵉ Dᵉ)

  obj-map-Categoryᵉ :
    (Fᵉ : map-Categoryᵉ) → obj-Categoryᵉ Cᵉ → obj-Categoryᵉ Dᵉ
  obj-map-Categoryᵉ =
    obj-map-Precategoryᵉ (precategory-Categoryᵉ Cᵉ) (precategory-Categoryᵉ Dᵉ)

  hom-map-Categoryᵉ :
    (Fᵉ : map-Categoryᵉ)
    {xᵉ yᵉ : obj-Categoryᵉ Cᵉ} →
    hom-Categoryᵉ Cᵉ xᵉ yᵉ →
    hom-Categoryᵉ Dᵉ
      ( obj-map-Categoryᵉ Fᵉ xᵉ)
      ( obj-map-Categoryᵉ Fᵉ yᵉ)
  hom-map-Categoryᵉ =
    hom-map-Precategoryᵉ (precategory-Categoryᵉ Cᵉ) (precategory-Categoryᵉ Dᵉ)
```

## Properties

### Characterization of equality of maps between categories

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Categoryᵉ l3ᵉ l4ᵉ)
  where

  coherence-htpy-map-Categoryᵉ :
    (fᵉ gᵉ : map-Categoryᵉ Cᵉ Dᵉ) →
    (obj-map-Categoryᵉ Cᵉ Dᵉ fᵉ ~ᵉ obj-map-Categoryᵉ Cᵉ Dᵉ gᵉ) →
    UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l4ᵉ)
  coherence-htpy-map-Categoryᵉ =
    coherence-htpy-map-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( precategory-Categoryᵉ Dᵉ)

  htpy-map-Categoryᵉ :
    (fᵉ gᵉ : map-Categoryᵉ Cᵉ Dᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  htpy-map-Categoryᵉ =
    htpy-map-Precategoryᵉ (precategory-Categoryᵉ Cᵉ) (precategory-Categoryᵉ Dᵉ)

  refl-htpy-map-Categoryᵉ :
    (fᵉ : map-Categoryᵉ Cᵉ Dᵉ) → htpy-map-Categoryᵉ fᵉ fᵉ
  refl-htpy-map-Categoryᵉ =
    refl-htpy-map-Precategoryᵉ (precategory-Categoryᵉ Cᵉ) (precategory-Categoryᵉ Dᵉ)

  htpy-eq-map-Categoryᵉ :
    (fᵉ gᵉ : map-Categoryᵉ Cᵉ Dᵉ) → (fᵉ ＝ᵉ gᵉ) → htpy-map-Categoryᵉ fᵉ gᵉ
  htpy-eq-map-Categoryᵉ =
    htpy-eq-map-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( precategory-Categoryᵉ Dᵉ)

  is-torsorial-htpy-map-Categoryᵉ :
    (fᵉ : map-Categoryᵉ Cᵉ Dᵉ) → is-torsorialᵉ (htpy-map-Categoryᵉ fᵉ)
  is-torsorial-htpy-map-Categoryᵉ =
    is-torsorial-htpy-map-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( precategory-Categoryᵉ Dᵉ)

  is-equiv-htpy-eq-map-Categoryᵉ :
    (fᵉ gᵉ : map-Categoryᵉ Cᵉ Dᵉ) → is-equivᵉ (htpy-eq-map-Categoryᵉ fᵉ gᵉ)
  is-equiv-htpy-eq-map-Categoryᵉ =
    is-equiv-htpy-eq-map-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( precategory-Categoryᵉ Dᵉ)

  equiv-htpy-eq-map-Categoryᵉ :
    (fᵉ gᵉ : map-Categoryᵉ Cᵉ Dᵉ) → (fᵉ ＝ᵉ gᵉ) ≃ᵉ htpy-map-Categoryᵉ fᵉ gᵉ
  equiv-htpy-eq-map-Categoryᵉ =
    equiv-htpy-eq-map-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( precategory-Categoryᵉ Dᵉ)

  eq-htpy-map-Categoryᵉ :
    (fᵉ gᵉ : map-Categoryᵉ Cᵉ Dᵉ) → htpy-map-Categoryᵉ fᵉ gᵉ → (fᵉ ＝ᵉ gᵉ)
  eq-htpy-map-Categoryᵉ =
    eq-htpy-map-Precategoryᵉ (precategory-Categoryᵉ Cᵉ) (precategory-Categoryᵉ Dᵉ)
```

## See also

-ᵉ [Functorsᵉ betweenᵉ categories](category-theory.functors-categories.mdᵉ)
-ᵉ [Theᵉ categoryᵉ ofᵉ mapsᵉ andᵉ naturalᵉ transformationsᵉ betweenᵉ categories](category-theory.category-of-maps-categories.mdᵉ)