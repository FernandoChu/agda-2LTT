# Functors from small to large categories

```agda
module category-theory.functors-from-small-to-large-categoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categoriesᵉ
open import category-theory.functors-from-small-to-large-precategoriesᵉ
open import category-theory.large-categoriesᵉ
open import category-theory.maps-from-small-to-large-categoriesᵉ

open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Aᵉ **functor**ᵉ fromᵉ aᵉ [(smallᵉ) category](category-theory.categories.mdᵉ) `C`ᵉ to aᵉ
[largeᵉ category](category-theory.large-categories.mdᵉ) `D`ᵉ consistsᵉ ofᵉ:

-ᵉ aᵉ mapᵉ `Cᵉ → D`ᵉ onᵉ objectsᵉ atᵉ someᵉ chosenᵉ universeᵉ levelᵉ `γ`,ᵉ
-ᵉ aᵉ mapᵉ `homᵉ xᵉ yᵉ → homᵉ (Fᵉ xᵉ) (Fᵉ y)`ᵉ onᵉ morphisms,ᵉ suchᵉ thatᵉ theᵉ followingᵉ
  identitiesᵉ holdᵉ:
-ᵉ `Fᵉ id_xᵉ = id_(Fᵉ x)`,ᵉ
-ᵉ `Fᵉ (gᵉ ∘ᵉ fᵉ) = Fᵉ gᵉ ∘ᵉ Fᵉ f`.ᵉ

## Definition

### The predicate on maps from small to large categories of being a functor

```agda
module _
  {l1ᵉ l2ᵉ γᵉ : Level} {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ) (Dᵉ : Large-Categoryᵉ αᵉ βᵉ)
  (Fᵉ : map-Small-Large-Categoryᵉ Cᵉ Dᵉ γᵉ)
  where

  preserves-comp-hom-map-Small-Large-Categoryᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ βᵉ γᵉ γᵉ)
  preserves-comp-hom-map-Small-Large-Categoryᵉ =
    preserves-comp-hom-map-Small-Large-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( large-precategory-Large-Categoryᵉ Dᵉ)
      ( Fᵉ)

  preserves-id-hom-map-Small-Large-Categoryᵉ : UUᵉ (l1ᵉ ⊔ βᵉ γᵉ γᵉ)
  preserves-id-hom-map-Small-Large-Categoryᵉ =
    preserves-id-hom-map-Small-Large-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( large-precategory-Large-Categoryᵉ Dᵉ)
      ( Fᵉ)

  is-functor-map-Small-Large-Categoryᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ βᵉ γᵉ γᵉ)
  is-functor-map-Small-Large-Categoryᵉ =
    is-functor-map-Small-Large-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( large-precategory-Large-Categoryᵉ Dᵉ)
      ( Fᵉ)

  preserves-comp-is-functor-map-Small-Large-Categoryᵉ :
    is-functor-map-Small-Large-Categoryᵉ →
    preserves-comp-hom-map-Small-Large-Categoryᵉ
  preserves-comp-is-functor-map-Small-Large-Categoryᵉ =
    preserves-comp-is-functor-map-Small-Large-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( large-precategory-Large-Categoryᵉ Dᵉ)
      ( Fᵉ)

  preserves-id-is-functor-map-Small-Large-Categoryᵉ :
    is-functor-map-Small-Large-Categoryᵉ →
    preserves-id-hom-map-Small-Large-Categoryᵉ
  preserves-id-is-functor-map-Small-Large-Categoryᵉ =
    preserves-id-is-functor-map-Small-Large-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( large-precategory-Large-Categoryᵉ Dᵉ)
      ( Fᵉ)
```

### Functors from small to large categories

```agda
module _
  {l1ᵉ l2ᵉ : Level} {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ) (Dᵉ : Large-Categoryᵉ αᵉ βᵉ)
  where

  functor-Small-Large-Categoryᵉ :
    (γᵉ : Level) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ αᵉ γᵉ ⊔ βᵉ γᵉ γᵉ)
  functor-Small-Large-Categoryᵉ =
    functor-Small-Large-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( large-precategory-Large-Categoryᵉ Dᵉ)

module _
  {l1ᵉ l2ᵉ : Level} {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ) (Dᵉ : Large-Categoryᵉ αᵉ βᵉ)
  {γᵉ : Level} (Fᵉ : functor-Small-Large-Categoryᵉ Cᵉ Dᵉ γᵉ)
  where

  obj-functor-Small-Large-Categoryᵉ :
    obj-Categoryᵉ Cᵉ → obj-Large-Categoryᵉ Dᵉ γᵉ
  obj-functor-Small-Large-Categoryᵉ =
    obj-functor-Small-Large-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( large-precategory-Large-Categoryᵉ Dᵉ)
      ( Fᵉ)

  hom-functor-Small-Large-Categoryᵉ :
    {xᵉ yᵉ : obj-Categoryᵉ Cᵉ} →
    (fᵉ : hom-Categoryᵉ Cᵉ xᵉ yᵉ) →
    hom-Large-Categoryᵉ Dᵉ
      ( obj-functor-Small-Large-Categoryᵉ xᵉ)
      ( obj-functor-Small-Large-Categoryᵉ yᵉ)
  hom-functor-Small-Large-Categoryᵉ =
    hom-functor-Small-Large-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( large-precategory-Large-Categoryᵉ Dᵉ)
      ( Fᵉ)

  map-functor-Small-Large-Categoryᵉ :
    map-Small-Large-Categoryᵉ Cᵉ Dᵉ γᵉ
  map-functor-Small-Large-Categoryᵉ =
    map-functor-Small-Large-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( large-precategory-Large-Categoryᵉ Dᵉ)
      ( Fᵉ)

  is-functor-functor-Small-Large-Categoryᵉ :
    is-functor-map-Small-Large-Categoryᵉ Cᵉ Dᵉ
      ( map-functor-Small-Large-Categoryᵉ)
  is-functor-functor-Small-Large-Categoryᵉ =
    is-functor-functor-Small-Large-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( large-precategory-Large-Categoryᵉ Dᵉ)
      ( Fᵉ)

  preserves-comp-functor-Small-Large-Categoryᵉ :
    {xᵉ yᵉ zᵉ : obj-Categoryᵉ Cᵉ}
    (gᵉ : hom-Categoryᵉ Cᵉ yᵉ zᵉ) (fᵉ : hom-Categoryᵉ Cᵉ xᵉ yᵉ) →
    ( hom-functor-Small-Large-Categoryᵉ (comp-hom-Categoryᵉ Cᵉ gᵉ fᵉ)) ＝ᵉ
    ( comp-hom-Large-Categoryᵉ Dᵉ
      ( hom-functor-Small-Large-Categoryᵉ gᵉ)
      ( hom-functor-Small-Large-Categoryᵉ fᵉ))
  preserves-comp-functor-Small-Large-Categoryᵉ =
    preserves-comp-is-functor-map-Small-Large-Categoryᵉ Cᵉ Dᵉ
      ( map-functor-Small-Large-Categoryᵉ)
      ( is-functor-functor-Small-Large-Categoryᵉ)

  preserves-id-functor-Small-Large-Categoryᵉ :
    (xᵉ : obj-Categoryᵉ Cᵉ) →
    ( hom-functor-Small-Large-Categoryᵉ (id-hom-Categoryᵉ Cᵉ {xᵉ})) ＝ᵉ
    ( id-hom-Large-Categoryᵉ Dᵉ {γᵉ} {obj-functor-Small-Large-Categoryᵉ xᵉ})
  preserves-id-functor-Small-Large-Categoryᵉ =
    preserves-id-is-functor-map-Small-Large-Categoryᵉ Cᵉ Dᵉ
      ( map-functor-Small-Large-Categoryᵉ)
      ( is-functor-functor-Small-Large-Categoryᵉ)
```

## Properties

### Characterizing equality of functors from small to large categories

#### Equality of functors is equality of underlying maps

```agda
module _
  {l1ᵉ l2ᵉ γᵉ : Level} {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ) (Dᵉ : Large-Categoryᵉ αᵉ βᵉ)
  (Fᵉ Gᵉ : functor-Small-Large-Categoryᵉ Cᵉ Dᵉ γᵉ)
  where

  equiv-eq-map-eq-functor-Small-Large-Categoryᵉ :
    ( Fᵉ ＝ᵉ Gᵉ) ≃ᵉ
    ( map-functor-Small-Large-Categoryᵉ Cᵉ Dᵉ Fᵉ ＝ᵉ
      map-functor-Small-Large-Categoryᵉ Cᵉ Dᵉ Gᵉ)
  equiv-eq-map-eq-functor-Small-Large-Categoryᵉ =
    equiv-eq-map-eq-functor-Small-Large-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( large-precategory-Large-Categoryᵉ Dᵉ)
      ( Fᵉ)
      ( Gᵉ)

  eq-map-eq-functor-Small-Large-Categoryᵉ :
    (Fᵉ ＝ᵉ Gᵉ) →
    ( map-functor-Small-Large-Categoryᵉ Cᵉ Dᵉ Fᵉ ＝ᵉ
      map-functor-Small-Large-Categoryᵉ Cᵉ Dᵉ Gᵉ)
  eq-map-eq-functor-Small-Large-Categoryᵉ =
    map-equivᵉ equiv-eq-map-eq-functor-Small-Large-Categoryᵉ

  eq-eq-map-functor-Small-Large-Categoryᵉ :
    ( map-functor-Small-Large-Categoryᵉ Cᵉ Dᵉ Fᵉ ＝ᵉ
      map-functor-Small-Large-Categoryᵉ Cᵉ Dᵉ Gᵉ) →
    ( Fᵉ ＝ᵉ Gᵉ)
  eq-eq-map-functor-Small-Large-Categoryᵉ =
    map-inv-equivᵉ equiv-eq-map-eq-functor-Small-Large-Categoryᵉ

  is-section-eq-eq-map-functor-Small-Large-Categoryᵉ :
    ( eq-map-eq-functor-Small-Large-Categoryᵉ ∘ᵉ
      eq-eq-map-functor-Small-Large-Categoryᵉ) ~ᵉ
    idᵉ
  is-section-eq-eq-map-functor-Small-Large-Categoryᵉ =
    is-section-map-inv-equivᵉ equiv-eq-map-eq-functor-Small-Large-Categoryᵉ

  is-retraction-eq-eq-map-functor-Small-Large-Categoryᵉ :
    ( eq-eq-map-functor-Small-Large-Categoryᵉ ∘ᵉ
      eq-map-eq-functor-Small-Large-Categoryᵉ) ~ᵉ
    idᵉ
  is-retraction-eq-eq-map-functor-Small-Large-Categoryᵉ =
    is-retraction-map-inv-equivᵉ equiv-eq-map-eq-functor-Small-Large-Categoryᵉ
```

#### Equality of functors is homotopy of underlying maps

```agda
module _
  {l1ᵉ l2ᵉ γᵉ : Level} {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ) (Dᵉ : Large-Categoryᵉ αᵉ βᵉ)
  (Fᵉ Gᵉ : functor-Small-Large-Categoryᵉ Cᵉ Dᵉ γᵉ)
  where

  htpy-functor-Small-Large-Categoryᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ αᵉ γᵉ ⊔ βᵉ γᵉ γᵉ)
  htpy-functor-Small-Large-Categoryᵉ =
    htpy-functor-Small-Large-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( large-precategory-Large-Categoryᵉ Dᵉ)
      ( Fᵉ)
      ( Gᵉ)

  equiv-htpy-eq-functor-Small-Large-Categoryᵉ :
    (Fᵉ ＝ᵉ Gᵉ) ≃ᵉ htpy-functor-Small-Large-Categoryᵉ
  equiv-htpy-eq-functor-Small-Large-Categoryᵉ =
    equiv-htpy-eq-functor-Small-Large-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( large-precategory-Large-Categoryᵉ Dᵉ)
      ( Fᵉ)
      ( Gᵉ)

  htpy-eq-functor-Small-Large-Categoryᵉ :
    (Fᵉ ＝ᵉ Gᵉ) → htpy-functor-Small-Large-Categoryᵉ
  htpy-eq-functor-Small-Large-Categoryᵉ =
    map-equivᵉ equiv-htpy-eq-functor-Small-Large-Categoryᵉ

  eq-htpy-functor-Small-Large-Categoryᵉ :
    htpy-functor-Small-Large-Categoryᵉ → Fᵉ ＝ᵉ Gᵉ
  eq-htpy-functor-Small-Large-Categoryᵉ =
    map-inv-equivᵉ equiv-htpy-eq-functor-Small-Large-Categoryᵉ

  is-section-eq-htpy-functor-Small-Large-Categoryᵉ :
    ( htpy-eq-functor-Small-Large-Categoryᵉ ∘ᵉ
      eq-htpy-functor-Small-Large-Categoryᵉ) ~ᵉ
    idᵉ
  is-section-eq-htpy-functor-Small-Large-Categoryᵉ =
    is-section-map-inv-equivᵉ equiv-htpy-eq-functor-Small-Large-Categoryᵉ

  is-retraction-eq-htpy-functor-Small-Large-Categoryᵉ :
    ( eq-htpy-functor-Small-Large-Categoryᵉ ∘ᵉ
      htpy-eq-functor-Small-Large-Categoryᵉ) ~ᵉ
    idᵉ
  is-retraction-eq-htpy-functor-Small-Large-Categoryᵉ =
    is-retraction-map-inv-equivᵉ
      equiv-htpy-eq-functor-Small-Large-Categoryᵉ
```

## See also

-ᵉ [Theᵉ categoryᵉ ofᵉ functorsᵉ andᵉ naturalᵉ transformationsᵉ fromᵉ smallᵉ to largeᵉ categories](category-theory.category-of-functors-from-small-to-large-categories.mdᵉ)