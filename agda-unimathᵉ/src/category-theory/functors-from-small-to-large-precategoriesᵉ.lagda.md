# Functors from small to large precategories

```agda
module category-theory.functors-from-small-to-large-precategoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.functors-precategoriesᵉ
open import category-theory.large-precategoriesᵉ
open import category-theory.maps-from-small-to-large-precategoriesᵉ
open import category-theory.precategoriesᵉ

open import foundation.cartesian-product-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Aᵉ **functor**ᵉ fromᵉ aᵉ [(smallᵉ) precategory](category-theory.precategories.mdᵉ) `C`ᵉ
to aᵉ [largeᵉ precategory](category-theory.large-precategories.mdᵉ) `D`ᵉ consistsᵉ
ofᵉ:

-ᵉ aᵉ mapᵉ `F₀ᵉ : Cᵉ → D`ᵉ onᵉ objectsᵉ atᵉ someᵉ chosenᵉ universeᵉ levelᵉ `γ`,ᵉ
-ᵉ aᵉ mapᵉ `F₁ᵉ : homᵉ xᵉ yᵉ → homᵉ (F₀ᵉ xᵉ) (F₀ᵉ y)`ᵉ onᵉ morphisms,ᵉ suchᵉ thatᵉ theᵉ followingᵉ
  identitiesᵉ holdᵉ:
-ᵉ `Fᵉ id_xᵉ = id_(Fᵉ x)`,ᵉ
-ᵉ `Fᵉ (gᵉ ∘ᵉ fᵉ) = Fᵉ gᵉ ∘ᵉ Fᵉ f`.ᵉ

## Definition

### The predicate on maps from small to large precategories of being a functor

```agda
module _
  {l1ᵉ l2ᵉ γᵉ : Level} {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ) (Dᵉ : Large-Precategoryᵉ αᵉ βᵉ)
  (Fᵉ : map-Small-Large-Precategoryᵉ Cᵉ Dᵉ γᵉ)
  where

  preserves-comp-hom-map-Small-Large-Precategoryᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ βᵉ γᵉ γᵉ)
  preserves-comp-hom-map-Small-Large-Precategoryᵉ =
    {xᵉ yᵉ zᵉ : obj-Precategoryᵉ Cᵉ}
    (gᵉ : hom-Precategoryᵉ Cᵉ yᵉ zᵉ) (fᵉ : hom-Precategoryᵉ Cᵉ xᵉ yᵉ) →
    ( hom-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ (comp-hom-Precategoryᵉ Cᵉ gᵉ fᵉ)) ＝ᵉ
    ( comp-hom-Large-Precategoryᵉ Dᵉ
      ( hom-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ gᵉ)
      ( hom-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ fᵉ))

  preserves-id-hom-map-Small-Large-Precategoryᵉ : UUᵉ (l1ᵉ ⊔ βᵉ γᵉ γᵉ)
  preserves-id-hom-map-Small-Large-Precategoryᵉ =
    (xᵉ : obj-Precategoryᵉ Cᵉ) →
    ( hom-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ (id-hom-Precategoryᵉ Cᵉ {xᵉ})) ＝ᵉ
    ( id-hom-Large-Precategoryᵉ Dᵉ {γᵉ} {obj-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ xᵉ})

  is-functor-map-Small-Large-Precategoryᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ βᵉ γᵉ γᵉ)
  is-functor-map-Small-Large-Precategoryᵉ =
    preserves-comp-hom-map-Small-Large-Precategoryᵉ ×ᵉ
    preserves-id-hom-map-Small-Large-Precategoryᵉ

  preserves-comp-is-functor-map-Small-Large-Precategoryᵉ :
    is-functor-map-Small-Large-Precategoryᵉ →
    preserves-comp-hom-map-Small-Large-Precategoryᵉ
  preserves-comp-is-functor-map-Small-Large-Precategoryᵉ = pr1ᵉ

  preserves-id-is-functor-map-Small-Large-Precategoryᵉ :
    is-functor-map-Small-Large-Precategoryᵉ →
    preserves-id-hom-map-Small-Large-Precategoryᵉ
  preserves-id-is-functor-map-Small-Large-Precategoryᵉ = pr2ᵉ
```

### Functors from small to large precategories

```agda
module _
  {l1ᵉ l2ᵉ : Level} {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ) (Dᵉ : Large-Precategoryᵉ αᵉ βᵉ)
  where

  functor-Small-Large-Precategoryᵉ :
    (γᵉ : Level) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ αᵉ γᵉ ⊔ βᵉ γᵉ γᵉ)
  functor-Small-Large-Precategoryᵉ γᵉ =
    functor-Precategoryᵉ Cᵉ (precategory-Large-Precategoryᵉ Dᵉ γᵉ)

module _
  {l1ᵉ l2ᵉ : Level} {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ) (Dᵉ : Large-Precategoryᵉ αᵉ βᵉ)
  {γᵉ : Level} (Fᵉ : functor-Small-Large-Precategoryᵉ Cᵉ Dᵉ γᵉ)
  where

  obj-functor-Small-Large-Precategoryᵉ :
    obj-Precategoryᵉ Cᵉ → obj-Large-Precategoryᵉ Dᵉ γᵉ
  obj-functor-Small-Large-Precategoryᵉ =
    obj-functor-Precategoryᵉ Cᵉ (precategory-Large-Precategoryᵉ Dᵉ γᵉ) Fᵉ

  hom-functor-Small-Large-Precategoryᵉ :
    {xᵉ yᵉ : obj-Precategoryᵉ Cᵉ} →
    (fᵉ : hom-Precategoryᵉ Cᵉ xᵉ yᵉ) →
    hom-Large-Precategoryᵉ Dᵉ
      ( obj-functor-Small-Large-Precategoryᵉ xᵉ)
      ( obj-functor-Small-Large-Precategoryᵉ yᵉ)
  hom-functor-Small-Large-Precategoryᵉ =
    hom-functor-Precategoryᵉ Cᵉ (precategory-Large-Precategoryᵉ Dᵉ γᵉ) Fᵉ

  map-functor-Small-Large-Precategoryᵉ :
    map-Small-Large-Precategoryᵉ Cᵉ Dᵉ γᵉ
  map-functor-Small-Large-Precategoryᵉ =
    map-functor-Precategoryᵉ Cᵉ (precategory-Large-Precategoryᵉ Dᵉ γᵉ) Fᵉ

  is-functor-functor-Small-Large-Precategoryᵉ :
    is-functor-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ
      ( map-functor-Small-Large-Precategoryᵉ)
  is-functor-functor-Small-Large-Precategoryᵉ =
    is-functor-functor-Precategoryᵉ Cᵉ (precategory-Large-Precategoryᵉ Dᵉ γᵉ) Fᵉ

  preserves-comp-functor-Small-Large-Precategoryᵉ :
    {xᵉ yᵉ zᵉ : obj-Precategoryᵉ Cᵉ}
    (gᵉ : hom-Precategoryᵉ Cᵉ yᵉ zᵉ) (fᵉ : hom-Precategoryᵉ Cᵉ xᵉ yᵉ) →
    ( hom-functor-Small-Large-Precategoryᵉ (comp-hom-Precategoryᵉ Cᵉ gᵉ fᵉ)) ＝ᵉ
    ( comp-hom-Large-Precategoryᵉ Dᵉ
      ( hom-functor-Small-Large-Precategoryᵉ gᵉ)
      ( hom-functor-Small-Large-Precategoryᵉ fᵉ))
  preserves-comp-functor-Small-Large-Precategoryᵉ =
    preserves-comp-is-functor-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ
      ( map-functor-Small-Large-Precategoryᵉ)
      ( is-functor-functor-Small-Large-Precategoryᵉ)

  preserves-id-functor-Small-Large-Precategoryᵉ :
    (xᵉ : obj-Precategoryᵉ Cᵉ) →
    ( hom-functor-Small-Large-Precategoryᵉ (id-hom-Precategoryᵉ Cᵉ {xᵉ})) ＝ᵉ
    ( id-hom-Large-Precategoryᵉ Dᵉ {γᵉ} {obj-functor-Small-Large-Precategoryᵉ xᵉ})
  preserves-id-functor-Small-Large-Precategoryᵉ =
    preserves-id-is-functor-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ
      ( map-functor-Small-Large-Precategoryᵉ)
      ( is-functor-functor-Small-Large-Precategoryᵉ)
```

## Properties

### Characterizing equality of functors from small to large precategories

#### Equality of functors is equality of underlying maps

```agda
module _
  {l1ᵉ l2ᵉ γᵉ : Level} {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ) (Dᵉ : Large-Precategoryᵉ αᵉ βᵉ)
  (Fᵉ Gᵉ : functor-Small-Large-Precategoryᵉ Cᵉ Dᵉ γᵉ)
  where

  equiv-eq-map-eq-functor-Small-Large-Precategoryᵉ :
    ( Fᵉ ＝ᵉ Gᵉ) ≃ᵉ
    ( map-functor-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ ＝ᵉ
      map-functor-Small-Large-Precategoryᵉ Cᵉ Dᵉ Gᵉ)
  equiv-eq-map-eq-functor-Small-Large-Precategoryᵉ =
    equiv-eq-map-eq-functor-Precategoryᵉ
      Cᵉ (precategory-Large-Precategoryᵉ Dᵉ γᵉ) Fᵉ Gᵉ

  eq-map-eq-functor-Small-Large-Precategoryᵉ :
    (Fᵉ ＝ᵉ Gᵉ) →
    ( map-functor-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ ＝ᵉ
      map-functor-Small-Large-Precategoryᵉ Cᵉ Dᵉ Gᵉ)
  eq-map-eq-functor-Small-Large-Precategoryᵉ =
    map-equivᵉ equiv-eq-map-eq-functor-Small-Large-Precategoryᵉ

  eq-eq-map-functor-Small-Large-Precategoryᵉ :
    ( map-functor-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ ＝ᵉ
      map-functor-Small-Large-Precategoryᵉ Cᵉ Dᵉ Gᵉ) →
    ( Fᵉ ＝ᵉ Gᵉ)
  eq-eq-map-functor-Small-Large-Precategoryᵉ =
    map-inv-equivᵉ equiv-eq-map-eq-functor-Small-Large-Precategoryᵉ

  is-section-eq-eq-map-functor-Small-Large-Precategoryᵉ :
    ( eq-map-eq-functor-Small-Large-Precategoryᵉ ∘ᵉ
      eq-eq-map-functor-Small-Large-Precategoryᵉ) ~ᵉ
    idᵉ
  is-section-eq-eq-map-functor-Small-Large-Precategoryᵉ =
    is-section-map-inv-equivᵉ equiv-eq-map-eq-functor-Small-Large-Precategoryᵉ

  is-retraction-eq-eq-map-functor-Small-Large-Precategoryᵉ :
    ( eq-eq-map-functor-Small-Large-Precategoryᵉ ∘ᵉ
      eq-map-eq-functor-Small-Large-Precategoryᵉ) ~ᵉ
    idᵉ
  is-retraction-eq-eq-map-functor-Small-Large-Precategoryᵉ =
    is-retraction-map-inv-equivᵉ equiv-eq-map-eq-functor-Small-Large-Precategoryᵉ
```

#### Equality of functors is homotopy of underlying maps

```agda
module _
  {l1ᵉ l2ᵉ γᵉ : Level} {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ) (Dᵉ : Large-Precategoryᵉ αᵉ βᵉ)
  (Fᵉ Gᵉ : functor-Small-Large-Precategoryᵉ Cᵉ Dᵉ γᵉ)
  where

  htpy-functor-Small-Large-Precategoryᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ αᵉ γᵉ ⊔ βᵉ γᵉ γᵉ)
  htpy-functor-Small-Large-Precategoryᵉ =
    htpy-map-Small-Large-Precategoryᵉ Cᵉ Dᵉ
      ( map-functor-Small-Large-Precategoryᵉ Cᵉ Dᵉ Fᵉ)
      ( map-functor-Small-Large-Precategoryᵉ Cᵉ Dᵉ Gᵉ)

  equiv-htpy-eq-functor-Small-Large-Precategoryᵉ :
    (Fᵉ ＝ᵉ Gᵉ) ≃ᵉ htpy-functor-Small-Large-Precategoryᵉ
  equiv-htpy-eq-functor-Small-Large-Precategoryᵉ =
    equiv-htpy-eq-functor-Precategoryᵉ
      Cᵉ (precategory-Large-Precategoryᵉ Dᵉ γᵉ) Fᵉ Gᵉ

  htpy-eq-functor-Small-Large-Precategoryᵉ :
    Fᵉ ＝ᵉ Gᵉ → htpy-functor-Small-Large-Precategoryᵉ
  htpy-eq-functor-Small-Large-Precategoryᵉ =
    map-equivᵉ equiv-htpy-eq-functor-Small-Large-Precategoryᵉ

  eq-htpy-functor-Small-Large-Precategoryᵉ :
    htpy-functor-Small-Large-Precategoryᵉ → Fᵉ ＝ᵉ Gᵉ
  eq-htpy-functor-Small-Large-Precategoryᵉ =
    map-inv-equivᵉ equiv-htpy-eq-functor-Small-Large-Precategoryᵉ

  is-section-eq-htpy-functor-Small-Large-Precategoryᵉ :
    ( htpy-eq-functor-Small-Large-Precategoryᵉ ∘ᵉ
      eq-htpy-functor-Small-Large-Precategoryᵉ) ~ᵉ
    idᵉ
  is-section-eq-htpy-functor-Small-Large-Precategoryᵉ =
    is-section-map-inv-equivᵉ equiv-htpy-eq-functor-Small-Large-Precategoryᵉ

  is-retraction-eq-htpy-functor-Small-Large-Precategoryᵉ :
    ( eq-htpy-functor-Small-Large-Precategoryᵉ ∘ᵉ
      htpy-eq-functor-Small-Large-Precategoryᵉ) ~ᵉ
    idᵉ
  is-retraction-eq-htpy-functor-Small-Large-Precategoryᵉ =
    is-retraction-map-inv-equivᵉ
      equiv-htpy-eq-functor-Small-Large-Precategoryᵉ
```

## See also

-ᵉ [Theᵉ precategoryᵉ ofᵉ functorsᵉ andᵉ naturalᵉ transformationsᵉ fromᵉ smallᵉ to largeᵉ precategories](category-theory.precategory-of-functors-from-small-to-large-precategories.mdᵉ)