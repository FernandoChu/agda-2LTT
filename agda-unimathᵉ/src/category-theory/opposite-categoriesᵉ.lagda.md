# Opposite categories

```agda
module category-theory.opposite-categoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categoriesᵉ
open import category-theory.isomorphisms-in-precategoriesᵉ
open import category-theory.opposite-precategoriesᵉ
open import category-theory.precategoriesᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.identity-typesᵉ
open import foundation.involutionsᵉ
open import foundation.setsᵉ
open import foundation.strictly-involutive-identity-typesᵉ
open import foundation.subtypesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Letᵉ `C`ᵉ beᵉ aᵉ [category](category-theory.categories.md),ᵉ itsᵉ **oppositeᵉ
category**ᵉ `Cᵒᵖ`ᵉ isᵉ givenᵉ byᵉ reversingᵉ everyᵉ morphism.ᵉ

## Lemma

### The underlying precategory is a category if and only if the opposite is a category

```agda
abstract
  is-category-opposite-is-category-Precategoryᵉ :
    {l1ᵉ l2ᵉ : Level} (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ) →
    is-category-Precategoryᵉ Cᵉ →
    is-category-Precategoryᵉ (opposite-Precategoryᵉ Cᵉ)
  is-category-opposite-is-category-Precategoryᵉ Cᵉ is-category-Cᵉ xᵉ yᵉ =
    is-equiv-htpy-equivᵉ
      ( compute-iso-opposite-Precategoryᵉ Cᵉ ∘eᵉ
        equiv-inv-iso-Precategoryᵉ Cᵉ ∘eᵉ
        (ᵉ_ ,ᵉ is-category-Cᵉ xᵉ yᵉ))
      ( λ where
        reflᵉ →
          eq-type-subtypeᵉ
            ( is-iso-prop-Precategoryᵉ (opposite-Precategoryᵉ Cᵉ))
            ( reflᵉ))

abstract
  is-category-is-category-opposite-Precategoryᵉ :
    {l1ᵉ l2ᵉ : Level} (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ) →
    is-category-Precategoryᵉ (opposite-Precategoryᵉ Cᵉ) →
    is-category-Precategoryᵉ Cᵉ
  is-category-is-category-opposite-Precategoryᵉ Cᵉ =
    is-category-opposite-is-category-Precategoryᵉ (opposite-Precategoryᵉ Cᵉ)
```

## Definitions

### The opposite category

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ)
  where

  obj-opposite-Categoryᵉ : UUᵉ l1ᵉ
  obj-opposite-Categoryᵉ = obj-opposite-Precategoryᵉ (precategory-Categoryᵉ Cᵉ)

  hom-set-opposite-Categoryᵉ : (xᵉ yᵉ : obj-opposite-Categoryᵉ) → Setᵉ l2ᵉ
  hom-set-opposite-Categoryᵉ =
    hom-set-opposite-Precategoryᵉ (precategory-Categoryᵉ Cᵉ)

  hom-opposite-Categoryᵉ : (xᵉ yᵉ : obj-opposite-Categoryᵉ) → UUᵉ l2ᵉ
  hom-opposite-Categoryᵉ = hom-opposite-Precategoryᵉ (precategory-Categoryᵉ Cᵉ)

  comp-hom-opposite-Categoryᵉ :
    {xᵉ yᵉ zᵉ : obj-opposite-Categoryᵉ} →
    hom-opposite-Categoryᵉ yᵉ zᵉ →
    hom-opposite-Categoryᵉ xᵉ yᵉ →
    hom-opposite-Categoryᵉ xᵉ zᵉ
  comp-hom-opposite-Categoryᵉ =
    comp-hom-opposite-Precategoryᵉ (precategory-Categoryᵉ Cᵉ)

  associative-comp-hom-opposite-Categoryᵉ :
    {xᵉ yᵉ zᵉ wᵉ : obj-opposite-Categoryᵉ}
    (hᵉ : hom-opposite-Categoryᵉ zᵉ wᵉ)
    (gᵉ : hom-opposite-Categoryᵉ yᵉ zᵉ)
    (fᵉ : hom-opposite-Categoryᵉ xᵉ yᵉ) →
    comp-hom-opposite-Categoryᵉ (comp-hom-opposite-Categoryᵉ hᵉ gᵉ) fᵉ ＝ᵉ
    comp-hom-opposite-Categoryᵉ hᵉ (comp-hom-opposite-Categoryᵉ gᵉ fᵉ)
  associative-comp-hom-opposite-Categoryᵉ =
    associative-comp-hom-opposite-Precategoryᵉ (precategory-Categoryᵉ Cᵉ)

  involutive-eq-associative-comp-hom-opposite-Categoryᵉ :
    {xᵉ yᵉ zᵉ wᵉ : obj-opposite-Categoryᵉ}
    (hᵉ : hom-opposite-Categoryᵉ zᵉ wᵉ)
    (gᵉ : hom-opposite-Categoryᵉ yᵉ zᵉ)
    (fᵉ : hom-opposite-Categoryᵉ xᵉ yᵉ) →
    comp-hom-opposite-Categoryᵉ (comp-hom-opposite-Categoryᵉ hᵉ gᵉ) fᵉ ＝ⁱᵉ
    comp-hom-opposite-Categoryᵉ hᵉ (comp-hom-opposite-Categoryᵉ gᵉ fᵉ)
  involutive-eq-associative-comp-hom-opposite-Categoryᵉ =
    involutive-eq-associative-comp-hom-opposite-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)

  id-hom-opposite-Categoryᵉ :
    {xᵉ : obj-opposite-Categoryᵉ} → hom-opposite-Categoryᵉ xᵉ xᵉ
  id-hom-opposite-Categoryᵉ =
    id-hom-opposite-Precategoryᵉ (precategory-Categoryᵉ Cᵉ)

  left-unit-law-comp-hom-opposite-Categoryᵉ :
    {xᵉ yᵉ : obj-opposite-Categoryᵉ}
    (fᵉ : hom-opposite-Categoryᵉ xᵉ yᵉ) →
    comp-hom-opposite-Categoryᵉ id-hom-opposite-Categoryᵉ fᵉ ＝ᵉ fᵉ
  left-unit-law-comp-hom-opposite-Categoryᵉ =
    left-unit-law-comp-hom-opposite-Precategoryᵉ (precategory-Categoryᵉ Cᵉ)

  right-unit-law-comp-hom-opposite-Categoryᵉ :
    {xᵉ yᵉ : obj-opposite-Categoryᵉ} (fᵉ : hom-opposite-Categoryᵉ xᵉ yᵉ) →
    comp-hom-opposite-Categoryᵉ fᵉ id-hom-opposite-Categoryᵉ ＝ᵉ fᵉ
  right-unit-law-comp-hom-opposite-Categoryᵉ =
    right-unit-law-comp-hom-opposite-Precategoryᵉ (precategory-Categoryᵉ Cᵉ)

  precategory-opposite-Categoryᵉ : Precategoryᵉ l1ᵉ l2ᵉ
  precategory-opposite-Categoryᵉ = opposite-Precategoryᵉ (precategory-Categoryᵉ Cᵉ)

  opposite-Categoryᵉ : Categoryᵉ l1ᵉ l2ᵉ
  pr1ᵉ opposite-Categoryᵉ = precategory-opposite-Categoryᵉ
  pr2ᵉ opposite-Categoryᵉ =
    is-category-opposite-is-category-Precategoryᵉ
      ( precategory-Categoryᵉ Cᵉ)
      ( is-category-Categoryᵉ Cᵉ)
```

## Properties

### The opposite construction is an involution on the type of categories

```agda
is-involution-opposite-Categoryᵉ :
  {l1ᵉ l2ᵉ : Level} → is-involutionᵉ (opposite-Categoryᵉ {l1ᵉ} {l2ᵉ})
is-involution-opposite-Categoryᵉ Cᵉ =
  eq-type-subtypeᵉ
    ( is-category-prop-Precategoryᵉ)
    ( is-involution-opposite-Precategoryᵉ (precategory-Categoryᵉ Cᵉ))

involution-opposite-Categoryᵉ :
  (l1ᵉ l2ᵉ : Level) → involutionᵉ (Categoryᵉ l1ᵉ l2ᵉ)
pr1ᵉ (involution-opposite-Categoryᵉ l1ᵉ l2ᵉ) = opposite-Categoryᵉ
pr2ᵉ (involution-opposite-Categoryᵉ l1ᵉ l2ᵉ) = is-involution-opposite-Categoryᵉ

is-equiv-opposite-Categoryᵉ :
  {l1ᵉ l2ᵉ : Level} → is-equivᵉ (opposite-Categoryᵉ {l1ᵉ} {l2ᵉ})
is-equiv-opposite-Categoryᵉ =
  is-equiv-is-involutionᵉ is-involution-opposite-Categoryᵉ

equiv-opposite-Categoryᵉ :
  (l1ᵉ l2ᵉ : Level) → Categoryᵉ l1ᵉ l2ᵉ ≃ᵉ Categoryᵉ l1ᵉ l2ᵉ
equiv-opposite-Categoryᵉ l1ᵉ l2ᵉ =
  equiv-involutionᵉ (involution-opposite-Categoryᵉ l1ᵉ l2ᵉ)
```

## External links

-ᵉ [Precategoriesᵉ -ᵉ opposites](https://1lab.dev/Cat.Base.html#oppositesᵉ) atᵉ 1labᵉ
-ᵉ [oppositeᵉ category](https://ncatlab.org/nlab/show/opposite+categoryᵉ) atᵉ $n$Labᵉ
-ᵉ [Oppositeᵉ category](https://en.wikipedia.org/wiki/Opposite_categoryᵉ) atᵉ
  Wikipediaᵉ
-ᵉ [oppositeᵉ category](https://www.wikidata.org/wiki/Q7098616ᵉ) atᵉ Wikidataᵉ