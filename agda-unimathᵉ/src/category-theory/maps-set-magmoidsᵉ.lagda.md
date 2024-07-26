# Maps between set-magmoids

```agda
module category-theory.maps-set-magmoidsᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.set-magmoidsᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.commuting-pentagons-of-identificationsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.function-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Aᵉ **map**ᵉ fromᵉ aᵉ [set-magmoid](category-theory.set-magmoids.mdᵉ) `C`ᵉ to aᵉ setᵉ
magmoidᵉ `D`ᵉ consistsᵉ ofᵉ:

-ᵉ aᵉ mapᵉ `F₀ᵉ : Cᵉ → D`ᵉ onᵉ objects,ᵉ andᵉ
-ᵉ aᵉ mapᵉ `F₁ᵉ : homᵉ xᵉ yᵉ → homᵉ (F₀ᵉ xᵉ) (F₀ᵉ y)`ᵉ onᵉ morphisms.ᵉ

## Definitions

### Maps between set-magmoids

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Cᵉ : Set-Magmoidᵉ l1ᵉ l2ᵉ)
  (Dᵉ : Set-Magmoidᵉ l3ᵉ l4ᵉ)
  where

  map-Set-Magmoidᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  map-Set-Magmoidᵉ =
    Σᵉ ( obj-Set-Magmoidᵉ Cᵉ → obj-Set-Magmoidᵉ Dᵉ)
      ( λ F₀ᵉ →
        {xᵉ yᵉ : obj-Set-Magmoidᵉ Cᵉ} →
        hom-Set-Magmoidᵉ Cᵉ xᵉ yᵉ →
        hom-Set-Magmoidᵉ Dᵉ (F₀ᵉ xᵉ) (F₀ᵉ yᵉ))

  obj-map-Set-Magmoidᵉ :
    (Fᵉ : map-Set-Magmoidᵉ) → obj-Set-Magmoidᵉ Cᵉ → obj-Set-Magmoidᵉ Dᵉ
  obj-map-Set-Magmoidᵉ = pr1ᵉ

  hom-map-Set-Magmoidᵉ :
    (Fᵉ : map-Set-Magmoidᵉ) {xᵉ yᵉ : obj-Set-Magmoidᵉ Cᵉ} →
    hom-Set-Magmoidᵉ Cᵉ xᵉ yᵉ →
    hom-Set-Magmoidᵉ Dᵉ (obj-map-Set-Magmoidᵉ Fᵉ xᵉ) (obj-map-Set-Magmoidᵉ Fᵉ yᵉ)
  hom-map-Set-Magmoidᵉ = pr2ᵉ
```

### The identity map on a set-magmoid

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Set-Magmoidᵉ l1ᵉ l2ᵉ)
  where

  id-map-Set-Magmoidᵉ : map-Set-Magmoidᵉ Aᵉ Aᵉ
  pr1ᵉ id-map-Set-Magmoidᵉ = idᵉ
  pr2ᵉ id-map-Set-Magmoidᵉ = idᵉ
```

### Composition of maps on set-magmoids

Anyᵉ twoᵉ compatibleᵉ mapsᵉ canᵉ beᵉ composedᵉ to aᵉ newᵉ map.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level}
  (Aᵉ : Set-Magmoidᵉ l1ᵉ l2ᵉ)
  (Bᵉ : Set-Magmoidᵉ l3ᵉ l4ᵉ)
  (Cᵉ : Set-Magmoidᵉ l5ᵉ l6ᵉ)
  (Gᵉ : map-Set-Magmoidᵉ Bᵉ Cᵉ)
  (Fᵉ : map-Set-Magmoidᵉ Aᵉ Bᵉ)
  where

  obj-comp-map-Set-Magmoidᵉ : obj-Set-Magmoidᵉ Aᵉ → obj-Set-Magmoidᵉ Cᵉ
  obj-comp-map-Set-Magmoidᵉ =
    obj-map-Set-Magmoidᵉ Bᵉ Cᵉ Gᵉ ∘ᵉ obj-map-Set-Magmoidᵉ Aᵉ Bᵉ Fᵉ

  hom-comp-map-Set-Magmoidᵉ :
    {xᵉ yᵉ : obj-Set-Magmoidᵉ Aᵉ} →
    hom-Set-Magmoidᵉ Aᵉ xᵉ yᵉ →
    hom-Set-Magmoidᵉ Cᵉ (obj-comp-map-Set-Magmoidᵉ xᵉ) (obj-comp-map-Set-Magmoidᵉ yᵉ)
  hom-comp-map-Set-Magmoidᵉ =
    hom-map-Set-Magmoidᵉ Bᵉ Cᵉ Gᵉ ∘ᵉ hom-map-Set-Magmoidᵉ Aᵉ Bᵉ Fᵉ

  comp-map-Set-Magmoidᵉ : map-Set-Magmoidᵉ Aᵉ Cᵉ
  pr1ᵉ comp-map-Set-Magmoidᵉ = obj-comp-map-Set-Magmoidᵉ
  pr2ᵉ comp-map-Set-Magmoidᵉ = hom-comp-map-Set-Magmoidᵉ
```

## Properties

### Categorical laws for map composition

#### Unit laws for map composition

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  (Aᵉ : Set-Magmoidᵉ l1ᵉ l2ᵉ) (Bᵉ : Set-Magmoidᵉ l3ᵉ l4ᵉ)
  (Fᵉ : map-Set-Magmoidᵉ Aᵉ Bᵉ)
  where

  left-unit-law-comp-map-Set-Magmoidᵉ :
    comp-map-Set-Magmoidᵉ Aᵉ Bᵉ Bᵉ (id-map-Set-Magmoidᵉ Bᵉ) Fᵉ ＝ᵉ Fᵉ
  left-unit-law-comp-map-Set-Magmoidᵉ = reflᵉ

  right-unit-law-comp-map-Set-Magmoidᵉ :
    comp-map-Set-Magmoidᵉ Aᵉ Aᵉ Bᵉ Fᵉ (id-map-Set-Magmoidᵉ Aᵉ) ＝ᵉ Fᵉ
  right-unit-law-comp-map-Set-Magmoidᵉ = reflᵉ
```

#### Associativity of map composition

```agda
module _
  {l1ᵉ l1'ᵉ l2ᵉ l2'ᵉ l3ᵉ l3'ᵉ l4ᵉ l4'ᵉ : Level}
  (Aᵉ : Set-Magmoidᵉ l1ᵉ l1'ᵉ)
  (Bᵉ : Set-Magmoidᵉ l2ᵉ l2'ᵉ)
  (Cᵉ : Set-Magmoidᵉ l3ᵉ l3'ᵉ)
  (Dᵉ : Set-Magmoidᵉ l4ᵉ l4'ᵉ)
  (Fᵉ : map-Set-Magmoidᵉ Aᵉ Bᵉ)
  (Gᵉ : map-Set-Magmoidᵉ Bᵉ Cᵉ)
  (Hᵉ : map-Set-Magmoidᵉ Cᵉ Dᵉ)
  where

  associative-comp-map-Set-Magmoidᵉ :
    comp-map-Set-Magmoidᵉ Aᵉ Bᵉ Dᵉ (comp-map-Set-Magmoidᵉ Bᵉ Cᵉ Dᵉ Hᵉ Gᵉ) Fᵉ ＝ᵉ
    comp-map-Set-Magmoidᵉ Aᵉ Cᵉ Dᵉ Hᵉ (comp-map-Set-Magmoidᵉ Aᵉ Bᵉ Cᵉ Gᵉ Fᵉ)
  associative-comp-map-Set-Magmoidᵉ = reflᵉ
```

#### Mac Lane pentagon for map composition

Theᵉ Macᵉ Laneᵉ pentagonᵉ isᵉ aᵉ higherᵉ coherenceᵉ ofᵉ theᵉ associatorᵉ forᵉ mapᵉ
composition.ᵉ Sinceᵉ mapᵉ compositionᵉ isᵉ strictlyᵉ associative,ᵉ theᵉ Macᵉ Laneᵉ
pentagonᵉ alsoᵉ followsᵉ byᵉ reflexivity.ᵉ

```text
    (I(GH))Fᵉ ----ᵉ I((GH)Fᵉ)
          /ᵉ        \ᵉ
         /ᵉ          \ᵉ
  ((IH)G)Fᵉ          I(H(GFᵉ))
          \ᵉ        /ᵉ
            \ᵉ    /ᵉ
           (IH)(GFᵉ)
```

```agda
module _
  {l1ᵉ l1'ᵉ l2ᵉ l2'ᵉ l3ᵉ l3'ᵉ l4ᵉ l4'ᵉ : Level}
  (Aᵉ : Set-Magmoidᵉ l1ᵉ l1'ᵉ)
  (Bᵉ : Set-Magmoidᵉ l2ᵉ l2'ᵉ)
  (Cᵉ : Set-Magmoidᵉ l3ᵉ l3'ᵉ)
  (Dᵉ : Set-Magmoidᵉ l4ᵉ l4'ᵉ)
  (Eᵉ : Set-Magmoidᵉ l4ᵉ l4'ᵉ)
  (Fᵉ : map-Set-Magmoidᵉ Aᵉ Bᵉ)
  (Gᵉ : map-Set-Magmoidᵉ Bᵉ Cᵉ)
  (Hᵉ : map-Set-Magmoidᵉ Cᵉ Dᵉ)
  (Iᵉ : map-Set-Magmoidᵉ Dᵉ Eᵉ)
  where

  mac-lane-pentagon-comp-map-Set-Magmoidᵉ :
    coherence-pentagon-identificationsᵉ
      { xᵉ =
        comp-map-Set-Magmoidᵉ Aᵉ Bᵉ Eᵉ
        ( comp-map-Set-Magmoidᵉ Bᵉ Dᵉ Eᵉ Iᵉ
          ( comp-map-Set-Magmoidᵉ Bᵉ Cᵉ Dᵉ Hᵉ Gᵉ))
        ( Fᵉ)}
      { comp-map-Set-Magmoidᵉ Aᵉ Dᵉ Eᵉ Iᵉ
        ( comp-map-Set-Magmoidᵉ Aᵉ Bᵉ Dᵉ
          ( comp-map-Set-Magmoidᵉ Bᵉ Cᵉ Dᵉ Hᵉ Gᵉ)
          ( Fᵉ))}
      { comp-map-Set-Magmoidᵉ Aᵉ Bᵉ Eᵉ
        ( comp-map-Set-Magmoidᵉ Bᵉ Cᵉ Eᵉ
          ( comp-map-Set-Magmoidᵉ Cᵉ Dᵉ Eᵉ Iᵉ Hᵉ)
          ( Gᵉ))
        ( Fᵉ)}
      { comp-map-Set-Magmoidᵉ Aᵉ Dᵉ Eᵉ
        ( Iᵉ)
        ( comp-map-Set-Magmoidᵉ Aᵉ Cᵉ Dᵉ
          ( Hᵉ)
          ( comp-map-Set-Magmoidᵉ Aᵉ Bᵉ Cᵉ Gᵉ Fᵉ))}
      { comp-map-Set-Magmoidᵉ Aᵉ Cᵉ Eᵉ
        ( comp-map-Set-Magmoidᵉ Cᵉ Dᵉ Eᵉ Iᵉ Hᵉ)
        ( comp-map-Set-Magmoidᵉ Aᵉ Bᵉ Cᵉ Gᵉ Fᵉ)}
      ( associative-comp-map-Set-Magmoidᵉ Aᵉ Bᵉ Dᵉ Eᵉ
        ( Fᵉ) (comp-map-Set-Magmoidᵉ Bᵉ Cᵉ Dᵉ Hᵉ Gᵉ) (Iᵉ))
      ( apᵉ
        ( λ pᵉ → comp-map-Set-Magmoidᵉ Aᵉ Bᵉ Eᵉ pᵉ Fᵉ)
        ( invᵉ (associative-comp-map-Set-Magmoidᵉ Bᵉ Cᵉ Dᵉ Eᵉ Gᵉ Hᵉ Iᵉ)))
      ( apᵉ
        ( λ pᵉ → comp-map-Set-Magmoidᵉ Aᵉ Dᵉ Eᵉ Iᵉ pᵉ)
        ( associative-comp-map-Set-Magmoidᵉ Aᵉ Bᵉ Cᵉ Dᵉ Fᵉ Gᵉ Hᵉ))
      ( associative-comp-map-Set-Magmoidᵉ Aᵉ Bᵉ Cᵉ Eᵉ
        ( Fᵉ) (Gᵉ) (comp-map-Set-Magmoidᵉ Cᵉ Dᵉ Eᵉ Iᵉ Hᵉ))
      ( invᵉ
        ( associative-comp-map-Set-Magmoidᵉ Aᵉ Cᵉ Dᵉ Eᵉ
          (comp-map-Set-Magmoidᵉ Aᵉ Bᵉ Cᵉ Gᵉ Fᵉ) Hᵉ Iᵉ))
  mac-lane-pentagon-comp-map-Set-Magmoidᵉ = reflᵉ
```

## See also

-ᵉ [Functorsᵉ betweenᵉ set-magmoids](category-theory.maps-set-magmoids.mdᵉ)
-ᵉ [Theᵉ precategoryᵉ ofᵉ mapsᵉ andᵉ naturalᵉ transformationsᵉ betweenᵉ precategories](category-theory.precategory-of-maps-precategories.mdᵉ)

## External links

Aᵉ wikidataᵉ identifierᵉ wasᵉ notᵉ availableᵉ forᵉ thisᵉ concept.ᵉ