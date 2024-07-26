# Opposite precategories

```agda
module category-theory.opposite-precategoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.isomorphisms-in-precategoriesᵉ
open import category-theory.precategoriesᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.involutionsᵉ
open import foundation.setsᵉ
open import foundation.strictly-involutive-identity-typesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Letᵉ `C`ᵉ beᵉ aᵉ [precategory](category-theory.precategories.md),ᵉ itsᵉ **oppositeᵉ
precategory**ᵉ `Cᵒᵖ`ᵉ isᵉ givenᵉ byᵉ reversingᵉ everyᵉ morphism.ᵉ

## Definition

### The opposite precategory

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  where

  obj-opposite-Precategoryᵉ : UUᵉ l1ᵉ
  obj-opposite-Precategoryᵉ = obj-Precategoryᵉ Cᵉ

  hom-set-opposite-Precategoryᵉ : (xᵉ yᵉ : obj-opposite-Precategoryᵉ) → Setᵉ l2ᵉ
  hom-set-opposite-Precategoryᵉ xᵉ yᵉ = hom-set-Precategoryᵉ Cᵉ yᵉ xᵉ

  hom-opposite-Precategoryᵉ : (xᵉ yᵉ : obj-opposite-Precategoryᵉ) → UUᵉ l2ᵉ
  hom-opposite-Precategoryᵉ xᵉ yᵉ = type-Setᵉ (hom-set-opposite-Precategoryᵉ xᵉ yᵉ)

  comp-hom-opposite-Precategoryᵉ :
    {xᵉ yᵉ zᵉ : obj-opposite-Precategoryᵉ} →
    hom-opposite-Precategoryᵉ yᵉ zᵉ →
    hom-opposite-Precategoryᵉ xᵉ yᵉ →
    hom-opposite-Precategoryᵉ xᵉ zᵉ
  comp-hom-opposite-Precategoryᵉ gᵉ fᵉ = comp-hom-Precategoryᵉ Cᵉ fᵉ gᵉ

  involutive-eq-associative-comp-hom-opposite-Precategoryᵉ :
    {xᵉ yᵉ zᵉ wᵉ : obj-opposite-Precategoryᵉ}
    (hᵉ : hom-opposite-Precategoryᵉ zᵉ wᵉ)
    (gᵉ : hom-opposite-Precategoryᵉ yᵉ zᵉ)
    (fᵉ : hom-opposite-Precategoryᵉ xᵉ yᵉ) →
    ( comp-hom-opposite-Precategoryᵉ (comp-hom-opposite-Precategoryᵉ hᵉ gᵉ) fᵉ) ＝ⁱᵉ
    ( comp-hom-opposite-Precategoryᵉ hᵉ (comp-hom-opposite-Precategoryᵉ gᵉ fᵉ))
  involutive-eq-associative-comp-hom-opposite-Precategoryᵉ hᵉ gᵉ fᵉ =
    invⁱᵉ (involutive-eq-associative-comp-hom-Precategoryᵉ Cᵉ fᵉ gᵉ hᵉ)

  associative-comp-hom-opposite-Precategoryᵉ :
    {xᵉ yᵉ zᵉ wᵉ : obj-opposite-Precategoryᵉ}
    (hᵉ : hom-opposite-Precategoryᵉ zᵉ wᵉ)
    (gᵉ : hom-opposite-Precategoryᵉ yᵉ zᵉ)
    (fᵉ : hom-opposite-Precategoryᵉ xᵉ yᵉ) →
    ( comp-hom-opposite-Precategoryᵉ (comp-hom-opposite-Precategoryᵉ hᵉ gᵉ) fᵉ) ＝ᵉ
    ( comp-hom-opposite-Precategoryᵉ hᵉ (comp-hom-opposite-Precategoryᵉ gᵉ fᵉ))
  associative-comp-hom-opposite-Precategoryᵉ hᵉ gᵉ fᵉ =
    eq-involutive-eqᵉ
      ( involutive-eq-associative-comp-hom-opposite-Precategoryᵉ hᵉ gᵉ fᵉ)

  id-hom-opposite-Precategoryᵉ :
    {xᵉ : obj-opposite-Precategoryᵉ} → hom-opposite-Precategoryᵉ xᵉ xᵉ
  id-hom-opposite-Precategoryᵉ = id-hom-Precategoryᵉ Cᵉ

  left-unit-law-comp-hom-opposite-Precategoryᵉ :
    {xᵉ yᵉ : obj-opposite-Precategoryᵉ}
    (fᵉ : hom-opposite-Precategoryᵉ xᵉ yᵉ) →
    comp-hom-opposite-Precategoryᵉ id-hom-opposite-Precategoryᵉ fᵉ ＝ᵉ fᵉ
  left-unit-law-comp-hom-opposite-Precategoryᵉ =
    right-unit-law-comp-hom-Precategoryᵉ Cᵉ

  right-unit-law-comp-hom-opposite-Precategoryᵉ :
    {xᵉ yᵉ : obj-opposite-Precategoryᵉ} (fᵉ : hom-opposite-Precategoryᵉ xᵉ yᵉ) →
    comp-hom-opposite-Precategoryᵉ fᵉ id-hom-opposite-Precategoryᵉ ＝ᵉ fᵉ
  right-unit-law-comp-hom-opposite-Precategoryᵉ =
    left-unit-law-comp-hom-Precategoryᵉ Cᵉ

  opposite-Precategoryᵉ : Precategoryᵉ l1ᵉ l2ᵉ
  pr1ᵉ opposite-Precategoryᵉ = obj-opposite-Precategoryᵉ
  pr1ᵉ (pr2ᵉ opposite-Precategoryᵉ) = hom-set-opposite-Precategoryᵉ
  pr1ᵉ (pr1ᵉ (pr2ᵉ (pr2ᵉ opposite-Precategoryᵉ))) = comp-hom-opposite-Precategoryᵉ
  pr2ᵉ (pr1ᵉ (pr2ᵉ (pr2ᵉ opposite-Precategoryᵉ))) =
    involutive-eq-associative-comp-hom-opposite-Precategoryᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ opposite-Precategoryᵉ))) xᵉ = id-hom-opposite-Precategoryᵉ {xᵉ}
  pr1ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ opposite-Precategoryᵉ)))) =
    left-unit-law-comp-hom-opposite-Precategoryᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ opposite-Precategoryᵉ)))) =
    right-unit-law-comp-hom-opposite-Precategoryᵉ
```

## Properties

### The opposite construction is a definitional involution on the type of precategories

```agda
is-involution-opposite-Precategoryᵉ :
  {l1ᵉ l2ᵉ : Level} → is-involutionᵉ (opposite-Precategoryᵉ {l1ᵉ} {l2ᵉ})
is-involution-opposite-Precategoryᵉ Cᵉ = reflᵉ

involution-opposite-Precategoryᵉ :
  (l1ᵉ l2ᵉ : Level) → involutionᵉ (Precategoryᵉ l1ᵉ l2ᵉ)
pr1ᵉ (involution-opposite-Precategoryᵉ l1ᵉ l2ᵉ) = opposite-Precategoryᵉ
pr2ᵉ (involution-opposite-Precategoryᵉ l1ᵉ l2ᵉ) = is-involution-opposite-Precategoryᵉ

is-equiv-opposite-Precategoryᵉ :
  {l1ᵉ l2ᵉ : Level} → is-equivᵉ (opposite-Precategoryᵉ {l1ᵉ} {l2ᵉ})
is-equiv-opposite-Precategoryᵉ =
  is-equiv-is-involutionᵉ is-involution-opposite-Precategoryᵉ

equiv-opposite-Precategoryᵉ :
  (l1ᵉ l2ᵉ : Level) → Precategoryᵉ l1ᵉ l2ᵉ ≃ᵉ Precategoryᵉ l1ᵉ l2ᵉ
equiv-opposite-Precategoryᵉ l1ᵉ l2ᵉ =
  equiv-involutionᵉ (involution-opposite-Precategoryᵉ l1ᵉ l2ᵉ)
```

### Computing the isomorphism sets of the opposite precategory

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ) {xᵉ yᵉ : obj-Precategoryᵉ Cᵉ}
  where

  map-compute-iso-opposite-Precategoryᵉ :
    iso-Precategoryᵉ Cᵉ xᵉ yᵉ → iso-Precategoryᵉ (opposite-Precategoryᵉ Cᵉ) yᵉ xᵉ
  pr1ᵉ (map-compute-iso-opposite-Precategoryᵉ fᵉ) =
    hom-iso-Precategoryᵉ Cᵉ fᵉ
  pr1ᵉ (pr2ᵉ (map-compute-iso-opposite-Precategoryᵉ fᵉ)) =
    hom-inv-iso-Precategoryᵉ Cᵉ fᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ (map-compute-iso-opposite-Precategoryᵉ fᵉ))) =
    is-retraction-hom-inv-iso-Precategoryᵉ Cᵉ fᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ (map-compute-iso-opposite-Precategoryᵉ fᵉ))) =
    is-section-hom-inv-iso-Precategoryᵉ Cᵉ fᵉ

  map-inv-compute-iso-opposite-Precategoryᵉ :
    iso-Precategoryᵉ (opposite-Precategoryᵉ Cᵉ) yᵉ xᵉ → iso-Precategoryᵉ Cᵉ xᵉ yᵉ
  pr1ᵉ (map-inv-compute-iso-opposite-Precategoryᵉ fᵉ) =
    hom-iso-Precategoryᵉ (opposite-Precategoryᵉ Cᵉ) fᵉ
  pr1ᵉ (pr2ᵉ (map-inv-compute-iso-opposite-Precategoryᵉ fᵉ)) =
    hom-inv-iso-Precategoryᵉ (opposite-Precategoryᵉ Cᵉ) fᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ (map-inv-compute-iso-opposite-Precategoryᵉ fᵉ))) =
    is-retraction-hom-inv-iso-Precategoryᵉ (opposite-Precategoryᵉ Cᵉ) fᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ (map-inv-compute-iso-opposite-Precategoryᵉ fᵉ))) =
    is-section-hom-inv-iso-Precategoryᵉ (opposite-Precategoryᵉ Cᵉ) fᵉ

  is-equiv-map-compute-iso-opposite-Precategoryᵉ :
    is-equivᵉ (map-compute-iso-opposite-Precategoryᵉ)
  pr1ᵉ (pr1ᵉ is-equiv-map-compute-iso-opposite-Precategoryᵉ) =
    map-inv-compute-iso-opposite-Precategoryᵉ
  pr2ᵉ (pr1ᵉ is-equiv-map-compute-iso-opposite-Precategoryᵉ) = refl-htpyᵉ
  pr1ᵉ (pr2ᵉ is-equiv-map-compute-iso-opposite-Precategoryᵉ) =
    map-inv-compute-iso-opposite-Precategoryᵉ
  pr2ᵉ (pr2ᵉ is-equiv-map-compute-iso-opposite-Precategoryᵉ) = refl-htpyᵉ

  compute-iso-opposite-Precategoryᵉ :
    iso-Precategoryᵉ Cᵉ xᵉ yᵉ ≃ᵉ iso-Precategoryᵉ (opposite-Precategoryᵉ Cᵉ) yᵉ xᵉ
  pr1ᵉ compute-iso-opposite-Precategoryᵉ =
    map-compute-iso-opposite-Precategoryᵉ
  pr2ᵉ compute-iso-opposite-Precategoryᵉ =
    is-equiv-map-compute-iso-opposite-Precategoryᵉ
```

## External links

-ᵉ [Precategoriesᵉ -ᵉ opposites](https://1lab.dev/Cat.Base.html#oppositesᵉ) atᵉ 1labᵉ
-ᵉ [oppositeᵉ category](https://ncatlab.org/nlab/show/opposite+categoryᵉ) atᵉ $n$Labᵉ
-ᵉ [Oppositeᵉ category](https://en.wikipedia.org/wiki/Opposite_categoryᵉ) atᵉ
  Wikipediaᵉ
-ᵉ [oppositeᵉ category](https://www.wikidata.org/wiki/Q7098616ᵉ) atᵉ Wikidataᵉ