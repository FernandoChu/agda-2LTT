# Opposite preunivalent categories

```agda
module category-theory.opposite-preunivalent-categoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.isomorphisms-in-precategoriesᵉ
open import category-theory.opposite-precategoriesᵉ
open import category-theory.precategoriesᵉ
open import category-theory.preunivalent-categoriesᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.embeddingsᵉ
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

Letᵉ `C`ᵉ beᵉ aᵉ
[preunivalentᵉ category](category-theory.preunivalent-categories.md),ᵉ itsᵉ
**oppositeᵉ preunivalentᵉ category**ᵉ `Cᵒᵖ`ᵉ isᵉ givenᵉ byᵉ reversingᵉ everyᵉ morphism.ᵉ

## Lemma

### A precategory is preunivalent if and only if the opposite is preunivalent

```agda
abstract
  is-preunivalent-opposite-is-preunivalent-Precategoryᵉ :
    {l1ᵉ l2ᵉ : Level} (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ) →
    is-preunivalent-Precategoryᵉ Cᵉ →
    is-preunivalent-Precategoryᵉ (opposite-Precategoryᵉ Cᵉ)
  is-preunivalent-opposite-is-preunivalent-Precategoryᵉ Cᵉ is-preunivalent-Cᵉ xᵉ yᵉ =
    is-emb-htpy-embᵉ
      ( comp-embᵉ
        ( emb-equivᵉ
          ( compute-iso-opposite-Precategoryᵉ Cᵉ ∘eᵉ equiv-inv-iso-Precategoryᵉ Cᵉ))
        ( _ ,ᵉ is-preunivalent-Cᵉ xᵉ yᵉ))
      ( λ where
        reflᵉ →
          eq-type-subtypeᵉ
            ( is-iso-prop-Precategoryᵉ (opposite-Precategoryᵉ Cᵉ))
            ( reflᵉ))

abstract
  is-preunivalent-is-preunivalent-opposite-Precategoryᵉ :
    {l1ᵉ l2ᵉ : Level} (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ) →
    is-preunivalent-Precategoryᵉ (opposite-Precategoryᵉ Cᵉ) →
    is-preunivalent-Precategoryᵉ Cᵉ
  is-preunivalent-is-preunivalent-opposite-Precategoryᵉ Cᵉ =
    is-preunivalent-opposite-is-preunivalent-Precategoryᵉ
      ( opposite-Precategoryᵉ Cᵉ)
```

## Definitions

### The opposite preunivalent category

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Preunivalent-Categoryᵉ l1ᵉ l2ᵉ)
  where

  obj-opposite-Preunivalent-Categoryᵉ : UUᵉ l1ᵉ
  obj-opposite-Preunivalent-Categoryᵉ =
    obj-opposite-Precategoryᵉ (precategory-Preunivalent-Categoryᵉ Cᵉ)

  hom-set-opposite-Preunivalent-Categoryᵉ :
    (xᵉ yᵉ : obj-opposite-Preunivalent-Categoryᵉ) → Setᵉ l2ᵉ
  hom-set-opposite-Preunivalent-Categoryᵉ =
    hom-set-opposite-Precategoryᵉ (precategory-Preunivalent-Categoryᵉ Cᵉ)

  hom-opposite-Preunivalent-Categoryᵉ :
    (xᵉ yᵉ : obj-opposite-Preunivalent-Categoryᵉ) → UUᵉ l2ᵉ
  hom-opposite-Preunivalent-Categoryᵉ =
    hom-opposite-Precategoryᵉ (precategory-Preunivalent-Categoryᵉ Cᵉ)

  comp-hom-opposite-Preunivalent-Categoryᵉ :
    {xᵉ yᵉ zᵉ : obj-opposite-Preunivalent-Categoryᵉ} →
    hom-opposite-Preunivalent-Categoryᵉ yᵉ zᵉ →
    hom-opposite-Preunivalent-Categoryᵉ xᵉ yᵉ →
    hom-opposite-Preunivalent-Categoryᵉ xᵉ zᵉ
  comp-hom-opposite-Preunivalent-Categoryᵉ =
    comp-hom-opposite-Precategoryᵉ (precategory-Preunivalent-Categoryᵉ Cᵉ)

  involutive-eq-associative-comp-hom-opposite-Preunivalent-Categoryᵉ :
    {xᵉ yᵉ zᵉ wᵉ : obj-opposite-Preunivalent-Categoryᵉ}
    (hᵉ : hom-opposite-Preunivalent-Categoryᵉ zᵉ wᵉ)
    (gᵉ : hom-opposite-Preunivalent-Categoryᵉ yᵉ zᵉ)
    (fᵉ : hom-opposite-Preunivalent-Categoryᵉ xᵉ yᵉ) →
    comp-hom-opposite-Preunivalent-Categoryᵉ
      ( comp-hom-opposite-Preunivalent-Categoryᵉ hᵉ gᵉ)
      ( fᵉ) ＝ⁱᵉ
    comp-hom-opposite-Preunivalent-Categoryᵉ
      ( hᵉ)
      ( comp-hom-opposite-Preunivalent-Categoryᵉ gᵉ fᵉ)
  involutive-eq-associative-comp-hom-opposite-Preunivalent-Categoryᵉ =
    involutive-eq-associative-comp-hom-opposite-Precategoryᵉ
      ( precategory-Preunivalent-Categoryᵉ Cᵉ)

  associative-comp-hom-opposite-Preunivalent-Categoryᵉ :
    {xᵉ yᵉ zᵉ wᵉ : obj-opposite-Preunivalent-Categoryᵉ}
    (hᵉ : hom-opposite-Preunivalent-Categoryᵉ zᵉ wᵉ)
    (gᵉ : hom-opposite-Preunivalent-Categoryᵉ yᵉ zᵉ)
    (fᵉ : hom-opposite-Preunivalent-Categoryᵉ xᵉ yᵉ) →
    comp-hom-opposite-Preunivalent-Categoryᵉ
      ( comp-hom-opposite-Preunivalent-Categoryᵉ hᵉ gᵉ)
      ( fᵉ) ＝ᵉ
    comp-hom-opposite-Preunivalent-Categoryᵉ
      ( hᵉ)
      ( comp-hom-opposite-Preunivalent-Categoryᵉ gᵉ fᵉ)
  associative-comp-hom-opposite-Preunivalent-Categoryᵉ =
    associative-comp-hom-opposite-Precategoryᵉ
      ( precategory-Preunivalent-Categoryᵉ Cᵉ)

  id-hom-opposite-Preunivalent-Categoryᵉ :
    {xᵉ : obj-opposite-Preunivalent-Categoryᵉ} →
    hom-opposite-Preunivalent-Categoryᵉ xᵉ xᵉ
  id-hom-opposite-Preunivalent-Categoryᵉ =
    id-hom-opposite-Precategoryᵉ (precategory-Preunivalent-Categoryᵉ Cᵉ)

  left-unit-law-comp-hom-opposite-Preunivalent-Categoryᵉ :
    {xᵉ yᵉ : obj-opposite-Preunivalent-Categoryᵉ}
    (fᵉ : hom-opposite-Preunivalent-Categoryᵉ xᵉ yᵉ) →
    comp-hom-opposite-Preunivalent-Categoryᵉ
      ( id-hom-opposite-Preunivalent-Categoryᵉ)
      ( fᵉ) ＝ᵉ
    fᵉ
  left-unit-law-comp-hom-opposite-Preunivalent-Categoryᵉ =
    left-unit-law-comp-hom-opposite-Precategoryᵉ
      ( precategory-Preunivalent-Categoryᵉ Cᵉ)

  right-unit-law-comp-hom-opposite-Preunivalent-Categoryᵉ :
    {xᵉ yᵉ : obj-opposite-Preunivalent-Categoryᵉ}
    (fᵉ : hom-opposite-Preunivalent-Categoryᵉ xᵉ yᵉ) →
    comp-hom-opposite-Preunivalent-Categoryᵉ
      ( fᵉ) (id-hom-opposite-Preunivalent-Categoryᵉ) ＝ᵉ
    ( fᵉ)
  right-unit-law-comp-hom-opposite-Preunivalent-Categoryᵉ =
    right-unit-law-comp-hom-opposite-Precategoryᵉ
      ( precategory-Preunivalent-Categoryᵉ Cᵉ)

  precategory-opposite-Preunivalent-Categoryᵉ : Precategoryᵉ l1ᵉ l2ᵉ
  precategory-opposite-Preunivalent-Categoryᵉ =
    opposite-Precategoryᵉ (precategory-Preunivalent-Categoryᵉ Cᵉ)

  opposite-Preunivalent-Categoryᵉ : Preunivalent-Categoryᵉ l1ᵉ l2ᵉ
  pr1ᵉ opposite-Preunivalent-Categoryᵉ =
    precategory-opposite-Preunivalent-Categoryᵉ
  pr2ᵉ opposite-Preunivalent-Categoryᵉ =
    is-preunivalent-opposite-is-preunivalent-Precategoryᵉ
      ( precategory-Preunivalent-Categoryᵉ Cᵉ)
      ( is-preunivalent-Preunivalent-Categoryᵉ Cᵉ)
```

## Properties

### The opposite construction is an involution on the type of preunivalent categories

```agda
is-involution-opposite-Preunivalent-Categoryᵉ :
  {l1ᵉ l2ᵉ : Level} → is-involutionᵉ (opposite-Preunivalent-Categoryᵉ {l1ᵉ} {l2ᵉ})
is-involution-opposite-Preunivalent-Categoryᵉ Cᵉ =
  eq-type-subtypeᵉ
    ( is-preunivalent-prop-Precategoryᵉ)
    ( is-involution-opposite-Precategoryᵉ (precategory-Preunivalent-Categoryᵉ Cᵉ))

involution-opposite-Preunivalent-Categoryᵉ :
  (l1ᵉ l2ᵉ : Level) → involutionᵉ (Preunivalent-Categoryᵉ l1ᵉ l2ᵉ)
pr1ᵉ (involution-opposite-Preunivalent-Categoryᵉ l1ᵉ l2ᵉ) =
  opposite-Preunivalent-Categoryᵉ
pr2ᵉ (involution-opposite-Preunivalent-Categoryᵉ l1ᵉ l2ᵉ) =
  is-involution-opposite-Preunivalent-Categoryᵉ

is-equiv-opposite-Preunivalent-Categoryᵉ :
  {l1ᵉ l2ᵉ : Level} → is-equivᵉ (opposite-Preunivalent-Categoryᵉ {l1ᵉ} {l2ᵉ})
is-equiv-opposite-Preunivalent-Categoryᵉ =
  is-equiv-is-involutionᵉ is-involution-opposite-Preunivalent-Categoryᵉ

equiv-opposite-Preunivalent-Categoryᵉ :
  (l1ᵉ l2ᵉ : Level) → Preunivalent-Categoryᵉ l1ᵉ l2ᵉ ≃ᵉ Preunivalent-Categoryᵉ l1ᵉ l2ᵉ
equiv-opposite-Preunivalent-Categoryᵉ l1ᵉ l2ᵉ =
  equiv-involutionᵉ (involution-opposite-Preunivalent-Categoryᵉ l1ᵉ l2ᵉ)
```

## External links

-ᵉ [Precategoriesᵉ -ᵉ opposites](https://1lab.dev/Cat.Base.html#oppositesᵉ) atᵉ 1labᵉ
-ᵉ [oppositeᵉ category](https://ncatlab.org/nlab/show/opposite+categoryᵉ) atᵉ $n$Labᵉ
-ᵉ [Oppositeᵉ category](https://en.wikipedia.org/wiki/Opposite_categoryᵉ) atᵉ
  Wikipediaᵉ
-ᵉ [oppositeᵉ category](https://www.wikidata.org/wiki/Q7098616ᵉ) atᵉ Wikidataᵉ