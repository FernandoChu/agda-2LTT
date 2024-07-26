# Fully faithful maps between precategories

```agda
module category-theory.fully-faithful-maps-precategoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.faithful-maps-precategoriesᵉ
open import category-theory.full-maps-precategoriesᵉ
open import category-theory.maps-precategoriesᵉ
open import category-theory.precategoriesᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.iterated-dependent-product-typesᵉ
open import foundation.propositionsᵉ
open import foundation.surjective-mapsᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Aᵉ [map](category-theory.maps-precategories.mdᵉ) betweenᵉ
[precategories](category-theory.precategories.mdᵉ) `C`ᵉ andᵉ `D`ᵉ isᵉ **fullyᵉ
faithful**ᵉ ifᵉ it'sᵉ anᵉ [equivalence](foundation-core.equivalences.mdᵉ) onᵉ
hom-sets,ᵉ orᵉ equivalently,ᵉ aᵉ [full](category-theory.full-maps-precategories.mdᵉ)
andᵉ [faithful](category-theory.faithful-maps-precategories.mdᵉ) mapᵉ onᵉ
precategories.ᵉ

## Definition

### The predicate on maps between precategories of being fully faithful

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ : map-Precategoryᵉ Cᵉ Dᵉ)
  where

  is-fully-faithful-map-Precategoryᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l4ᵉ)
  is-fully-faithful-map-Precategoryᵉ =
    (xᵉ yᵉ : obj-Precategoryᵉ Cᵉ) → is-equivᵉ (hom-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ {xᵉ} {yᵉ})

  is-prop-is-fully-faithful-map-Precategoryᵉ :
    is-propᵉ is-fully-faithful-map-Precategoryᵉ
  is-prop-is-fully-faithful-map-Precategoryᵉ =
    is-prop-iterated-Πᵉ 2
      ( λ xᵉ yᵉ → is-property-is-equivᵉ (hom-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ {xᵉ} {yᵉ}))

  is-fully-faithful-prop-map-Precategoryᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l4ᵉ)
  pr1ᵉ is-fully-faithful-prop-map-Precategoryᵉ = is-fully-faithful-map-Precategoryᵉ
  pr2ᵉ is-fully-faithful-prop-map-Precategoryᵉ =
    is-prop-is-fully-faithful-map-Precategoryᵉ

  equiv-hom-is-fully-faithful-map-Precategoryᵉ :
    is-fully-faithful-map-Precategoryᵉ → {xᵉ yᵉ : obj-Precategoryᵉ Cᵉ} →
    hom-Precategoryᵉ Cᵉ xᵉ yᵉ ≃ᵉ
    hom-Precategoryᵉ Dᵉ
      ( obj-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ xᵉ)
      ( obj-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ yᵉ)
  pr1ᵉ (equiv-hom-is-fully-faithful-map-Precategoryᵉ is-ff-Fᵉ) =
    hom-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ
  pr2ᵉ (equiv-hom-is-fully-faithful-map-Precategoryᵉ is-ff-Fᵉ {xᵉ} {yᵉ}) =
    is-ff-Fᵉ xᵉ yᵉ

  inv-equiv-hom-is-fully-faithful-map-Precategoryᵉ :
    is-fully-faithful-map-Precategoryᵉ → {xᵉ yᵉ : obj-Precategoryᵉ Cᵉ} →
    hom-Precategoryᵉ Dᵉ
      ( obj-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ xᵉ)
      ( obj-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ yᵉ) ≃ᵉ
    hom-Precategoryᵉ Cᵉ xᵉ yᵉ
  inv-equiv-hom-is-fully-faithful-map-Precategoryᵉ is-ff-Fᵉ =
    inv-equivᵉ (equiv-hom-is-fully-faithful-map-Precategoryᵉ is-ff-Fᵉ)

  map-inv-hom-is-fully-faithful-map-Precategoryᵉ :
    is-fully-faithful-map-Precategoryᵉ → {xᵉ yᵉ : obj-Precategoryᵉ Cᵉ} →
    hom-Precategoryᵉ Dᵉ
      ( obj-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ xᵉ)
      ( obj-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ yᵉ) →
    hom-Precategoryᵉ Cᵉ xᵉ yᵉ
  map-inv-hom-is-fully-faithful-map-Precategoryᵉ is-ff-Fᵉ =
    map-equivᵉ (inv-equiv-hom-is-fully-faithful-map-Precategoryᵉ is-ff-Fᵉ)
```

### The type of fully faithful maps between two precategories

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  where

  fully-faithful-map-Precategoryᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  fully-faithful-map-Precategoryᵉ =
    Σᵉ (map-Precategoryᵉ Cᵉ Dᵉ) (is-fully-faithful-map-Precategoryᵉ Cᵉ Dᵉ)

  map-fully-faithful-map-Precategoryᵉ :
    fully-faithful-map-Precategoryᵉ → map-Precategoryᵉ Cᵉ Dᵉ
  map-fully-faithful-map-Precategoryᵉ = pr1ᵉ

  is-fully-faithful-fully-faithful-map-Precategoryᵉ :
    (Fᵉ : fully-faithful-map-Precategoryᵉ) →
    is-fully-faithful-map-Precategoryᵉ Cᵉ Dᵉ (map-fully-faithful-map-Precategoryᵉ Fᵉ)
  is-fully-faithful-fully-faithful-map-Precategoryᵉ = pr2ᵉ

  obj-fully-faithful-map-Precategoryᵉ :
    fully-faithful-map-Precategoryᵉ → obj-Precategoryᵉ Cᵉ → obj-Precategoryᵉ Dᵉ
  obj-fully-faithful-map-Precategoryᵉ =
    obj-map-Precategoryᵉ Cᵉ Dᵉ ∘ᵉ map-fully-faithful-map-Precategoryᵉ

  hom-fully-faithful-map-Precategoryᵉ :
    (Fᵉ : fully-faithful-map-Precategoryᵉ) {xᵉ yᵉ : obj-Precategoryᵉ Cᵉ} →
    hom-Precategoryᵉ Cᵉ xᵉ yᵉ →
    hom-Precategoryᵉ Dᵉ
      ( obj-fully-faithful-map-Precategoryᵉ Fᵉ xᵉ)
      ( obj-fully-faithful-map-Precategoryᵉ Fᵉ yᵉ)
  hom-fully-faithful-map-Precategoryᵉ =
    hom-map-Precategoryᵉ Cᵉ Dᵉ ∘ᵉ map-fully-faithful-map-Precategoryᵉ

  equiv-hom-fully-faithful-map-Precategoryᵉ :
    (Fᵉ : fully-faithful-map-Precategoryᵉ) {xᵉ yᵉ : obj-Precategoryᵉ Cᵉ} →
    hom-Precategoryᵉ Cᵉ xᵉ yᵉ ≃ᵉ
    hom-Precategoryᵉ Dᵉ
      ( obj-fully-faithful-map-Precategoryᵉ Fᵉ xᵉ)
      ( obj-fully-faithful-map-Precategoryᵉ Fᵉ yᵉ)
  equiv-hom-fully-faithful-map-Precategoryᵉ Fᵉ =
    equiv-hom-is-fully-faithful-map-Precategoryᵉ Cᵉ Dᵉ
      ( map-fully-faithful-map-Precategoryᵉ Fᵉ)
      ( is-fully-faithful-fully-faithful-map-Precategoryᵉ Fᵉ)

  inv-equiv-hom-fully-faithful-map-Precategoryᵉ :
    (Fᵉ : fully-faithful-map-Precategoryᵉ) {xᵉ yᵉ : obj-Precategoryᵉ Cᵉ} →
    hom-Precategoryᵉ Dᵉ
      ( obj-fully-faithful-map-Precategoryᵉ Fᵉ xᵉ)
      ( obj-fully-faithful-map-Precategoryᵉ Fᵉ yᵉ) ≃ᵉ
    hom-Precategoryᵉ Cᵉ xᵉ yᵉ
  inv-equiv-hom-fully-faithful-map-Precategoryᵉ Fᵉ =
    inv-equivᵉ (equiv-hom-fully-faithful-map-Precategoryᵉ Fᵉ)

  map-inv-hom-fully-faithful-map-Precategoryᵉ :
    (Fᵉ : fully-faithful-map-Precategoryᵉ) {xᵉ yᵉ : obj-Precategoryᵉ Cᵉ} →
    hom-Precategoryᵉ Dᵉ
      ( obj-fully-faithful-map-Precategoryᵉ Fᵉ xᵉ)
      ( obj-fully-faithful-map-Precategoryᵉ Fᵉ yᵉ) →
    hom-Precategoryᵉ Cᵉ xᵉ yᵉ
  map-inv-hom-fully-faithful-map-Precategoryᵉ Fᵉ =
    map-equivᵉ (inv-equiv-hom-fully-faithful-map-Precategoryᵉ Fᵉ)
```

## Properties

### Fully faithful maps are the same as full and faithful maps

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ : map-Precategoryᵉ Cᵉ Dᵉ)
  where

  is-full-is-fully-faithful-map-Precategoryᵉ :
    is-fully-faithful-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ → is-full-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ
  is-full-is-fully-faithful-map-Precategoryᵉ is-ff-Fᵉ xᵉ yᵉ =
    is-surjective-is-equivᵉ (is-ff-Fᵉ xᵉ yᵉ)

  full-map-is-fully-faithful-map-Precategoryᵉ :
    is-fully-faithful-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ → full-map-Precategoryᵉ Cᵉ Dᵉ
  pr1ᵉ (full-map-is-fully-faithful-map-Precategoryᵉ is-ff-Fᵉ) = Fᵉ
  pr2ᵉ (full-map-is-fully-faithful-map-Precategoryᵉ is-ff-Fᵉ) =
    is-full-is-fully-faithful-map-Precategoryᵉ is-ff-Fᵉ

  is-faithful-is-fully-faithful-map-Precategoryᵉ :
    is-fully-faithful-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ → is-faithful-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ
  is-faithful-is-fully-faithful-map-Precategoryᵉ is-ff-Fᵉ xᵉ yᵉ =
    is-emb-is-equivᵉ (is-ff-Fᵉ xᵉ yᵉ)

  faithful-map-is-fully-faithful-map-Precategoryᵉ :
    is-fully-faithful-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ → faithful-map-Precategoryᵉ Cᵉ Dᵉ
  pr1ᵉ (faithful-map-is-fully-faithful-map-Precategoryᵉ is-ff-Fᵉ) = Fᵉ
  pr2ᵉ (faithful-map-is-fully-faithful-map-Precategoryᵉ is-ff-Fᵉ) =
    is-faithful-is-fully-faithful-map-Precategoryᵉ is-ff-Fᵉ

  is-fully-faithful-is-full-is-faithful-map-Precategoryᵉ :
    is-full-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ →
    is-faithful-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ →
    is-fully-faithful-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ
  is-fully-faithful-is-full-is-faithful-map-Precategoryᵉ
    is-full-Fᵉ is-faithful-Fᵉ xᵉ yᵉ =
    is-equiv-is-emb-is-surjectiveᵉ (is-full-Fᵉ xᵉ yᵉ) (is-faithful-Fᵉ xᵉ yᵉ)

  fully-faithful-map-is-full-is-faithful-map-Precategoryᵉ :
    is-full-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ →
    is-faithful-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ →
    fully-faithful-map-Precategoryᵉ Cᵉ Dᵉ
  pr1ᵉ
    ( fully-faithful-map-is-full-is-faithful-map-Precategoryᵉ
      is-full-Fᵉ is-faithful-Fᵉ) =
    Fᵉ
  pr2ᵉ
    ( fully-faithful-map-is-full-is-faithful-map-Precategoryᵉ
      is-full-Fᵉ is-faithful-Fᵉ) =
    is-fully-faithful-is-full-is-faithful-map-Precategoryᵉ
      ( is-full-Fᵉ) (is-faithful-Fᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Precategoryᵉ l3ᵉ l4ᵉ)
  (Fᵉ : fully-faithful-map-Precategoryᵉ Cᵉ Dᵉ)
  where

  full-map-fully-faithful-map-Precategoryᵉ : full-map-Precategoryᵉ Cᵉ Dᵉ
  full-map-fully-faithful-map-Precategoryᵉ =
    full-map-is-fully-faithful-map-Precategoryᵉ Cᵉ Dᵉ
      ( map-fully-faithful-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ)
      ( is-fully-faithful-fully-faithful-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ)

  faithful-map-fully-faithful-map-Precategoryᵉ : faithful-map-Precategoryᵉ Cᵉ Dᵉ
  faithful-map-fully-faithful-map-Precategoryᵉ =
    faithful-map-is-fully-faithful-map-Precategoryᵉ Cᵉ Dᵉ
      ( map-fully-faithful-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ)
      ( is-fully-faithful-fully-faithful-map-Precategoryᵉ Cᵉ Dᵉ Fᵉ)
```

## See also

-ᵉ [Fullyᵉ faithfulᵉ functorsᵉ betweenᵉ precategories](category-theory.fully-faithful-functors-precategories.mdᵉ)