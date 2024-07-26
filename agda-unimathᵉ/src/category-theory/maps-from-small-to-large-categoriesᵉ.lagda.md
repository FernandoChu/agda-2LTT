# Maps from small to large categories

```agda
module category-theory.maps-from-small-to-large-categoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categoriesᵉ
open import category-theory.large-categoriesᵉ
open import category-theory.maps-from-small-to-large-precategoriesᵉ

open import foundation.equivalencesᵉ
open import foundation.identity-typesᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Aᵉ **map**ᵉ fromᵉ aᵉ [(smallᵉ) category](category-theory.categories.mdᵉ) `C`ᵉ to aᵉ
[largeᵉ category](category-theory.large-categories.mdᵉ) `D`ᵉ consistsᵉ ofᵉ:

-ᵉ aᵉ mapᵉ `F₀ᵉ : Cᵉ → D`ᵉ onᵉ objectsᵉ atᵉ aᵉ chosenᵉ universeᵉ levelᵉ `γ`,ᵉ
-ᵉ aᵉ mapᵉ `F₁ᵉ : homᵉ xᵉ yᵉ → homᵉ (F₀ᵉ xᵉ) (F₀ᵉ y)`ᵉ onᵉ morphisms.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ) (Dᵉ : Large-Categoryᵉ αᵉ βᵉ)
  where

  map-Small-Large-Categoryᵉ : (γᵉ : Level) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ αᵉ γᵉ ⊔ βᵉ γᵉ γᵉ)
  map-Small-Large-Categoryᵉ =
    map-Small-Large-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( large-precategory-Large-Categoryᵉ Dᵉ)

  obj-map-Small-Large-Categoryᵉ :
    {γᵉ : Level} → map-Small-Large-Categoryᵉ γᵉ →
    obj-Categoryᵉ Cᵉ → obj-Large-Categoryᵉ Dᵉ γᵉ
  obj-map-Small-Large-Categoryᵉ {γᵉ} =
    obj-map-Small-Large-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( large-precategory-Large-Categoryᵉ Dᵉ)

  hom-map-Small-Large-Categoryᵉ :
    {γᵉ : Level} →
    (Fᵉ : map-Small-Large-Categoryᵉ γᵉ) →
    { Xᵉ Yᵉ : obj-Categoryᵉ Cᵉ} →
    hom-Categoryᵉ Cᵉ Xᵉ Yᵉ →
    hom-Large-Categoryᵉ Dᵉ
      ( obj-map-Small-Large-Categoryᵉ Fᵉ Xᵉ)
      ( obj-map-Small-Large-Categoryᵉ Fᵉ Yᵉ)
  hom-map-Small-Large-Categoryᵉ {γᵉ} =
    hom-map-Small-Large-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( large-precategory-Large-Categoryᵉ Dᵉ)
```

## Properties

### Characterization of equality of maps from small to large categories

```agda
module _
  {l1ᵉ l2ᵉ γᵉ : Level} {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ) (Dᵉ : Large-Categoryᵉ αᵉ βᵉ)
  where

  htpy-map-Small-Large-Categoryᵉ :
    (fᵉ gᵉ : map-Small-Large-Categoryᵉ Cᵉ Dᵉ γᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ αᵉ γᵉ ⊔ βᵉ γᵉ γᵉ)
  htpy-map-Small-Large-Categoryᵉ =
    htpy-map-Small-Large-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( large-precategory-Large-Categoryᵉ Dᵉ)

  htpy-eq-map-Small-Large-Categoryᵉ :
    (fᵉ gᵉ : map-Small-Large-Categoryᵉ Cᵉ Dᵉ γᵉ) →
    (fᵉ ＝ᵉ gᵉ) → htpy-map-Small-Large-Categoryᵉ fᵉ gᵉ
  htpy-eq-map-Small-Large-Categoryᵉ =
    htpy-eq-map-Small-Large-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( large-precategory-Large-Categoryᵉ Dᵉ)

  is-torsorial-htpy-map-Small-Large-Categoryᵉ :
    (fᵉ : map-Small-Large-Categoryᵉ Cᵉ Dᵉ γᵉ) →
    is-torsorialᵉ (htpy-map-Small-Large-Categoryᵉ fᵉ)
  is-torsorial-htpy-map-Small-Large-Categoryᵉ =
    is-torsorial-htpy-map-Small-Large-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( large-precategory-Large-Categoryᵉ Dᵉ)

  is-equiv-htpy-eq-map-Small-Large-Categoryᵉ :
    (fᵉ gᵉ : map-Small-Large-Categoryᵉ Cᵉ Dᵉ γᵉ) →
    is-equivᵉ (htpy-eq-map-Small-Large-Categoryᵉ fᵉ gᵉ)
  is-equiv-htpy-eq-map-Small-Large-Categoryᵉ =
    is-equiv-htpy-eq-map-Small-Large-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( large-precategory-Large-Categoryᵉ Dᵉ)

  equiv-htpy-eq-map-Small-Large-Categoryᵉ :
    (fᵉ gᵉ : map-Small-Large-Categoryᵉ Cᵉ Dᵉ γᵉ) →
    (fᵉ ＝ᵉ gᵉ) ≃ᵉ htpy-map-Small-Large-Categoryᵉ fᵉ gᵉ
  equiv-htpy-eq-map-Small-Large-Categoryᵉ =
    equiv-htpy-eq-map-Small-Large-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( large-precategory-Large-Categoryᵉ Dᵉ)

  eq-htpy-map-Small-Large-Categoryᵉ :
    (fᵉ gᵉ : map-Small-Large-Categoryᵉ Cᵉ Dᵉ γᵉ) →
    htpy-map-Small-Large-Categoryᵉ fᵉ gᵉ → (fᵉ ＝ᵉ gᵉ)
  eq-htpy-map-Small-Large-Categoryᵉ =
    eq-htpy-map-Small-Large-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( large-precategory-Large-Categoryᵉ Dᵉ)
```

## See also

-ᵉ [Functorsᵉ fromᵉ smallᵉ to largeᵉ categories](category-theory.functors-from-small-to-large-categories.mdᵉ)
-ᵉ [Theᵉ categoryᵉ ofᵉ mapsᵉ andᵉ naturalᵉ transformationsᵉ fromᵉ smallᵉ to largeᵉ categories](category-theory.category-of-maps-from-small-to-large-categories.mdᵉ)