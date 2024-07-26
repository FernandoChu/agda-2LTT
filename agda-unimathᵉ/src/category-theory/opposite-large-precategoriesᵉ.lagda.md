# Opposite large precategories

```agda
module category-theory.opposite-large-precategoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.isomorphisms-in-large-precategoriesᵉ
open import category-theory.large-precategoriesᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.setsᵉ
open import foundation.strictly-involutive-identity-typesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Letᵉ `C`ᵉ beᵉ aᵉ [largeᵉ precategory](category-theory.large-precategories.md),ᵉ itsᵉ
**oppositeᵉ largeᵉ precategory**ᵉ `Cᵒᵖ`ᵉ isᵉ givenᵉ byᵉ reversingᵉ everyᵉ morphism.ᵉ

## Definition

### The opposite large precategory

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level} (Cᵉ : Large-Precategoryᵉ αᵉ βᵉ)
  where

  obj-opposite-Large-Precategoryᵉ : (lᵉ : Level) → UUᵉ (αᵉ lᵉ)
  obj-opposite-Large-Precategoryᵉ = obj-Large-Precategoryᵉ Cᵉ

  hom-set-opposite-Large-Precategoryᵉ :
    {l1ᵉ l2ᵉ : Level}
    (Xᵉ : obj-opposite-Large-Precategoryᵉ l1ᵉ)
    (Yᵉ : obj-opposite-Large-Precategoryᵉ l2ᵉ) → Setᵉ (βᵉ l2ᵉ l1ᵉ)
  hom-set-opposite-Large-Precategoryᵉ Xᵉ Yᵉ = hom-set-Large-Precategoryᵉ Cᵉ Yᵉ Xᵉ

  hom-opposite-Large-Precategoryᵉ :
    {l1ᵉ l2ᵉ : Level}
    (Xᵉ : obj-opposite-Large-Precategoryᵉ l1ᵉ)
    (Yᵉ : obj-opposite-Large-Precategoryᵉ l2ᵉ) → UUᵉ (βᵉ l2ᵉ l1ᵉ)
  hom-opposite-Large-Precategoryᵉ Xᵉ Yᵉ =
    type-Setᵉ (hom-set-opposite-Large-Precategoryᵉ Xᵉ Yᵉ)

  comp-hom-opposite-Large-Precategoryᵉ :
    {l1ᵉ l2ᵉ l3ᵉ : Level}
    {Xᵉ : obj-opposite-Large-Precategoryᵉ l1ᵉ}
    {Yᵉ : obj-opposite-Large-Precategoryᵉ l2ᵉ}
    {Zᵉ : obj-opposite-Large-Precategoryᵉ l3ᵉ} →
    hom-opposite-Large-Precategoryᵉ Yᵉ Zᵉ →
    hom-opposite-Large-Precategoryᵉ Xᵉ Yᵉ →
    hom-opposite-Large-Precategoryᵉ Xᵉ Zᵉ
  comp-hom-opposite-Large-Precategoryᵉ gᵉ fᵉ = comp-hom-Large-Precategoryᵉ Cᵉ fᵉ gᵉ

  involutive-eq-associative-comp-hom-opposite-Large-Precategoryᵉ :
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
    {Xᵉ : obj-opposite-Large-Precategoryᵉ l1ᵉ}
    {Yᵉ : obj-opposite-Large-Precategoryᵉ l2ᵉ}
    {Zᵉ : obj-opposite-Large-Precategoryᵉ l3ᵉ}
    {Wᵉ : obj-opposite-Large-Precategoryᵉ l4ᵉ}
    (hᵉ : hom-opposite-Large-Precategoryᵉ Zᵉ Wᵉ)
    (gᵉ : hom-opposite-Large-Precategoryᵉ Yᵉ Zᵉ)
    (fᵉ : hom-opposite-Large-Precategoryᵉ Xᵉ Yᵉ) →
    comp-hom-opposite-Large-Precategoryᵉ
      ( comp-hom-opposite-Large-Precategoryᵉ hᵉ gᵉ)
      ( fᵉ) ＝ⁱᵉ
    comp-hom-opposite-Large-Precategoryᵉ
      ( hᵉ)
      ( comp-hom-opposite-Large-Precategoryᵉ gᵉ fᵉ)
  involutive-eq-associative-comp-hom-opposite-Large-Precategoryᵉ hᵉ gᵉ fᵉ =
    invⁱᵉ (involutive-eq-associative-comp-hom-Large-Precategoryᵉ Cᵉ fᵉ gᵉ hᵉ)

  associative-comp-hom-opposite-Large-Precategoryᵉ :
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
    {Xᵉ : obj-opposite-Large-Precategoryᵉ l1ᵉ}
    {Yᵉ : obj-opposite-Large-Precategoryᵉ l2ᵉ}
    {Zᵉ : obj-opposite-Large-Precategoryᵉ l3ᵉ}
    {Wᵉ : obj-opposite-Large-Precategoryᵉ l4ᵉ}
    (hᵉ : hom-opposite-Large-Precategoryᵉ Zᵉ Wᵉ)
    (gᵉ : hom-opposite-Large-Precategoryᵉ Yᵉ Zᵉ)
    (fᵉ : hom-opposite-Large-Precategoryᵉ Xᵉ Yᵉ) →
    comp-hom-opposite-Large-Precategoryᵉ
      ( comp-hom-opposite-Large-Precategoryᵉ hᵉ gᵉ)
      ( fᵉ) ＝ᵉ
    comp-hom-opposite-Large-Precategoryᵉ
      ( hᵉ)
      ( comp-hom-opposite-Large-Precategoryᵉ gᵉ fᵉ)
  associative-comp-hom-opposite-Large-Precategoryᵉ hᵉ gᵉ fᵉ =
    eq-involutive-eqᵉ
      ( involutive-eq-associative-comp-hom-opposite-Large-Precategoryᵉ hᵉ gᵉ fᵉ)

  id-hom-opposite-Large-Precategoryᵉ :
    {l1ᵉ : Level} {Xᵉ : obj-opposite-Large-Precategoryᵉ l1ᵉ} →
    hom-opposite-Large-Precategoryᵉ Xᵉ Xᵉ
  id-hom-opposite-Large-Precategoryᵉ = id-hom-Large-Precategoryᵉ Cᵉ

  left-unit-law-comp-hom-opposite-Large-Precategoryᵉ :
    {l1ᵉ l2ᵉ : Level}
    {Xᵉ : obj-opposite-Large-Precategoryᵉ l1ᵉ}
    {Yᵉ : obj-opposite-Large-Precategoryᵉ l2ᵉ}
    (fᵉ : hom-opposite-Large-Precategoryᵉ Xᵉ Yᵉ) →
    comp-hom-opposite-Large-Precategoryᵉ id-hom-opposite-Large-Precategoryᵉ fᵉ ＝ᵉ fᵉ
  left-unit-law-comp-hom-opposite-Large-Precategoryᵉ =
    right-unit-law-comp-hom-Large-Precategoryᵉ Cᵉ

  right-unit-law-comp-hom-opposite-Large-Precategoryᵉ :
    {l1ᵉ l2ᵉ : Level}
    {Xᵉ : obj-opposite-Large-Precategoryᵉ l1ᵉ}
    {Yᵉ : obj-opposite-Large-Precategoryᵉ l2ᵉ}
    (fᵉ : hom-opposite-Large-Precategoryᵉ Xᵉ Yᵉ) →
    comp-hom-opposite-Large-Precategoryᵉ fᵉ id-hom-opposite-Large-Precategoryᵉ ＝ᵉ fᵉ
  right-unit-law-comp-hom-opposite-Large-Precategoryᵉ =
    left-unit-law-comp-hom-Large-Precategoryᵉ Cᵉ

  opposite-Large-Precategoryᵉ : Large-Precategoryᵉ αᵉ (λ l1ᵉ l2ᵉ → βᵉ l2ᵉ l1ᵉ)
  obj-Large-Precategoryᵉ opposite-Large-Precategoryᵉ =
    obj-opposite-Large-Precategoryᵉ
  hom-set-Large-Precategoryᵉ opposite-Large-Precategoryᵉ =
    hom-set-opposite-Large-Precategoryᵉ
  comp-hom-Large-Precategoryᵉ opposite-Large-Precategoryᵉ =
    comp-hom-opposite-Large-Precategoryᵉ
  id-hom-Large-Precategoryᵉ opposite-Large-Precategoryᵉ =
    id-hom-opposite-Large-Precategoryᵉ
  involutive-eq-associative-comp-hom-Large-Precategoryᵉ
    opposite-Large-Precategoryᵉ =
    involutive-eq-associative-comp-hom-opposite-Large-Precategoryᵉ
  left-unit-law-comp-hom-Large-Precategoryᵉ opposite-Large-Precategoryᵉ =
    left-unit-law-comp-hom-opposite-Large-Precategoryᵉ
  right-unit-law-comp-hom-Large-Precategoryᵉ opposite-Large-Precategoryᵉ =
    right-unit-law-comp-hom-opposite-Large-Precategoryᵉ
```

## Properties

### Computing the isomorphism sets of the opposite large precategory

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level} {l1ᵉ l2ᵉ : Level}
  (Cᵉ : Large-Precategoryᵉ αᵉ βᵉ)
  {Xᵉ : obj-Large-Precategoryᵉ Cᵉ l1ᵉ} {Yᵉ : obj-Large-Precategoryᵉ Cᵉ l2ᵉ}
  where

  map-compute-iso-opposite-Large-Precategoryᵉ :
    iso-Large-Precategoryᵉ Cᵉ Xᵉ Yᵉ →
    iso-Large-Precategoryᵉ (opposite-Large-Precategoryᵉ Cᵉ) Yᵉ Xᵉ
  pr1ᵉ (map-compute-iso-opposite-Large-Precategoryᵉ fᵉ) =
    hom-iso-Large-Precategoryᵉ Cᵉ fᵉ
  pr1ᵉ (pr2ᵉ (map-compute-iso-opposite-Large-Precategoryᵉ fᵉ)) =
    hom-inv-iso-Large-Precategoryᵉ Cᵉ fᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ (map-compute-iso-opposite-Large-Precategoryᵉ fᵉ))) =
    is-retraction-hom-inv-iso-Large-Precategoryᵉ Cᵉ fᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ (map-compute-iso-opposite-Large-Precategoryᵉ fᵉ))) =
    is-section-hom-inv-iso-Large-Precategoryᵉ Cᵉ fᵉ

  map-inv-compute-iso-opposite-Large-Precategoryᵉ :
    iso-Large-Precategoryᵉ (opposite-Large-Precategoryᵉ Cᵉ) Yᵉ Xᵉ →
    iso-Large-Precategoryᵉ Cᵉ Xᵉ Yᵉ
  pr1ᵉ (map-inv-compute-iso-opposite-Large-Precategoryᵉ fᵉ) =
    hom-iso-Large-Precategoryᵉ (opposite-Large-Precategoryᵉ Cᵉ) fᵉ
  pr1ᵉ (pr2ᵉ (map-inv-compute-iso-opposite-Large-Precategoryᵉ fᵉ)) =
    hom-inv-iso-Large-Precategoryᵉ (opposite-Large-Precategoryᵉ Cᵉ) fᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ (map-inv-compute-iso-opposite-Large-Precategoryᵉ fᵉ))) =
    is-retraction-hom-inv-iso-Large-Precategoryᵉ (opposite-Large-Precategoryᵉ Cᵉ) fᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ (map-inv-compute-iso-opposite-Large-Precategoryᵉ fᵉ))) =
    is-section-hom-inv-iso-Large-Precategoryᵉ (opposite-Large-Precategoryᵉ Cᵉ) fᵉ

  is-equiv-map-compute-iso-opposite-Large-Precategoryᵉ :
    is-equivᵉ (map-compute-iso-opposite-Large-Precategoryᵉ)
  pr1ᵉ (pr1ᵉ is-equiv-map-compute-iso-opposite-Large-Precategoryᵉ) =
    map-inv-compute-iso-opposite-Large-Precategoryᵉ
  pr2ᵉ (pr1ᵉ is-equiv-map-compute-iso-opposite-Large-Precategoryᵉ) = refl-htpyᵉ
  pr1ᵉ (pr2ᵉ is-equiv-map-compute-iso-opposite-Large-Precategoryᵉ) =
    map-inv-compute-iso-opposite-Large-Precategoryᵉ
  pr2ᵉ (pr2ᵉ is-equiv-map-compute-iso-opposite-Large-Precategoryᵉ) = refl-htpyᵉ

  compute-iso-opposite-Large-Precategoryᵉ :
    iso-Large-Precategoryᵉ Cᵉ Xᵉ Yᵉ ≃ᵉ
    iso-Large-Precategoryᵉ (opposite-Large-Precategoryᵉ Cᵉ) Yᵉ Xᵉ
  pr1ᵉ compute-iso-opposite-Large-Precategoryᵉ =
    map-compute-iso-opposite-Large-Precategoryᵉ
  pr2ᵉ compute-iso-opposite-Large-Precategoryᵉ =
    is-equiv-map-compute-iso-opposite-Large-Precategoryᵉ
```

## External links

-ᵉ [Precategoriesᵉ -ᵉ opposites](https://1lab.dev/Cat.Base.html#oppositesᵉ) atᵉ 1labᵉ
-ᵉ [oppositeᵉ category](https://ncatlab.org/nlab/show/opposite+categoryᵉ) atᵉ $n$Labᵉ
-ᵉ [Oppositeᵉ category](https://en.wikipedia.org/wiki/Opposite_categoryᵉ) atᵉ
  Wikipediaᵉ
-ᵉ [oppositeᵉ category](https://www.wikidata.org/wiki/Q7098616ᵉ) atᵉ Wikidataᵉ