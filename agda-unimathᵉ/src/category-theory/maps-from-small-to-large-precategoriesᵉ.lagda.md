# Maps from small to large precategories

```agda
module category-theory.maps-from-small-to-large-precategoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.large-precategoriesᵉ
open import category-theory.maps-precategoriesᵉ
open import category-theory.precategoriesᵉ

open import foundation.equivalencesᵉ
open import foundation.identity-typesᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Aᵉ **map**ᵉ fromᵉ aᵉ [(smallᵉ) precategory](category-theory.precategories.mdᵉ) `C`ᵉ to
aᵉ [largeᵉ precategory](category-theory.large-precategories.mdᵉ) `D`ᵉ consistsᵉ ofᵉ:

-ᵉ aᵉ mapᵉ `F₀ᵉ : Cᵉ → D`ᵉ onᵉ objectsᵉ atᵉ aᵉ chosenᵉ universeᵉ levelᵉ `γ`,ᵉ
-ᵉ aᵉ mapᵉ `F₁ᵉ : homᵉ xᵉ yᵉ → homᵉ (F₀ᵉ xᵉ) (F₀ᵉ y)`ᵉ onᵉ morphisms.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ) (Dᵉ : Large-Precategoryᵉ αᵉ βᵉ)
  where

  map-Small-Large-Precategoryᵉ : (γᵉ : Level) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ αᵉ γᵉ ⊔ βᵉ γᵉ γᵉ)
  map-Small-Large-Precategoryᵉ γᵉ =
    map-Precategoryᵉ Cᵉ (precategory-Large-Precategoryᵉ Dᵉ γᵉ)

  obj-map-Small-Large-Precategoryᵉ :
    {γᵉ : Level} → map-Small-Large-Precategoryᵉ γᵉ →
    obj-Precategoryᵉ Cᵉ → obj-Large-Precategoryᵉ Dᵉ γᵉ
  obj-map-Small-Large-Precategoryᵉ {γᵉ} =
    obj-map-Precategoryᵉ Cᵉ (precategory-Large-Precategoryᵉ Dᵉ γᵉ)

  hom-map-Small-Large-Precategoryᵉ :
    {γᵉ : Level} →
    (Fᵉ : map-Small-Large-Precategoryᵉ γᵉ) →
    { Xᵉ Yᵉ : obj-Precategoryᵉ Cᵉ} →
    hom-Precategoryᵉ Cᵉ Xᵉ Yᵉ →
    hom-Large-Precategoryᵉ Dᵉ
      ( obj-map-Small-Large-Precategoryᵉ Fᵉ Xᵉ)
      ( obj-map-Small-Large-Precategoryᵉ Fᵉ Yᵉ)
  hom-map-Small-Large-Precategoryᵉ {γᵉ} =
    hom-map-Precategoryᵉ Cᵉ (precategory-Large-Precategoryᵉ Dᵉ γᵉ)
```

## Properties

### Characterization of equality of maps from small to large precategories

```agda
module _
  {l1ᵉ l2ᵉ γᵉ : Level} {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ) (Dᵉ : Large-Precategoryᵉ αᵉ βᵉ)
  where

  htpy-map-Small-Large-Precategoryᵉ :
    (fᵉ gᵉ : map-Small-Large-Precategoryᵉ Cᵉ Dᵉ γᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ αᵉ γᵉ ⊔ βᵉ γᵉ γᵉ)
  htpy-map-Small-Large-Precategoryᵉ =
    htpy-map-Precategoryᵉ Cᵉ (precategory-Large-Precategoryᵉ Dᵉ γᵉ)

  htpy-eq-map-Small-Large-Precategoryᵉ :
    (fᵉ gᵉ : map-Small-Large-Precategoryᵉ Cᵉ Dᵉ γᵉ) →
    (fᵉ ＝ᵉ gᵉ) → htpy-map-Small-Large-Precategoryᵉ fᵉ gᵉ
  htpy-eq-map-Small-Large-Precategoryᵉ =
    htpy-eq-map-Precategoryᵉ Cᵉ (precategory-Large-Precategoryᵉ Dᵉ γᵉ)

  is-torsorial-htpy-map-Small-Large-Precategoryᵉ :
    (fᵉ : map-Small-Large-Precategoryᵉ Cᵉ Dᵉ γᵉ) →
    is-torsorialᵉ (htpy-map-Small-Large-Precategoryᵉ fᵉ)
  is-torsorial-htpy-map-Small-Large-Precategoryᵉ =
    is-torsorial-htpy-map-Precategoryᵉ Cᵉ (precategory-Large-Precategoryᵉ Dᵉ γᵉ)

  is-equiv-htpy-eq-map-Small-Large-Precategoryᵉ :
    (fᵉ gᵉ : map-Small-Large-Precategoryᵉ Cᵉ Dᵉ γᵉ) →
    is-equivᵉ (htpy-eq-map-Small-Large-Precategoryᵉ fᵉ gᵉ)
  is-equiv-htpy-eq-map-Small-Large-Precategoryᵉ =
    is-equiv-htpy-eq-map-Precategoryᵉ Cᵉ (precategory-Large-Precategoryᵉ Dᵉ γᵉ)

  equiv-htpy-eq-map-Small-Large-Precategoryᵉ :
    (fᵉ gᵉ : map-Small-Large-Precategoryᵉ Cᵉ Dᵉ γᵉ) →
    (fᵉ ＝ᵉ gᵉ) ≃ᵉ htpy-map-Small-Large-Precategoryᵉ fᵉ gᵉ
  equiv-htpy-eq-map-Small-Large-Precategoryᵉ =
    equiv-htpy-eq-map-Precategoryᵉ Cᵉ (precategory-Large-Precategoryᵉ Dᵉ γᵉ)

  eq-htpy-map-Small-Large-Precategoryᵉ :
    (fᵉ gᵉ : map-Small-Large-Precategoryᵉ Cᵉ Dᵉ γᵉ) →
    htpy-map-Small-Large-Precategoryᵉ fᵉ gᵉ → (fᵉ ＝ᵉ gᵉ)
  eq-htpy-map-Small-Large-Precategoryᵉ =
    eq-htpy-map-Precategoryᵉ Cᵉ (precategory-Large-Precategoryᵉ Dᵉ γᵉ)
```

## See also

-ᵉ [Functorsᵉ fromᵉ smallᵉ to largeᵉ precategories](category-theory.functors-from-small-to-large-precategories.mdᵉ)
-ᵉ [Theᵉ precategoryᵉ ofᵉ mapsᵉ andᵉ naturalᵉ transformationsᵉ fromᵉ smallᵉ to largeᵉ precategories](category-theory.precategory-of-maps-from-small-to-large-precategories.mdᵉ)