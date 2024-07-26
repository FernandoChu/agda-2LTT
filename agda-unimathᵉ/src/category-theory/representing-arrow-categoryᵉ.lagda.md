# The representing arrow category

```agda
module category-theory.representing-arrow-categoryᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categoriesᵉ
open import category-theory.isomorphisms-in-precategoriesᵉ
open import category-theory.precategoriesᵉ

open import foundation.booleansᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.empty-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.subtypesᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Theᵉ **representingᵉ arrow**ᵉ isᵉ theᵉ [category](category-theory.categories.mdᵉ) thatᵉ
[represents](category-theory.representable-functors-categories.mdᵉ) arrowsᵉ in aᵉ
([pre-](category-theory.precategories.md))category.ᵉ Weᵉ modelᵉ itᵉ afterᵉ
implicationᵉ onᵉ theᵉ [booleans](foundation.booleans.md).ᵉ

## Definition

### The objects and hom-sets of the representing arrow

```agda
obj-representing-arrow-Categoryᵉ : UUᵉ lzero
obj-representing-arrow-Categoryᵉ = boolᵉ

hom-set-representing-arrow-Categoryᵉ :
  obj-representing-arrow-Categoryᵉ → obj-representing-arrow-Categoryᵉ → Setᵉ lzero
hom-set-representing-arrow-Categoryᵉ trueᵉ trueᵉ = unit-Setᵉ
hom-set-representing-arrow-Categoryᵉ trueᵉ falseᵉ = empty-Setᵉ
hom-set-representing-arrow-Categoryᵉ falseᵉ _ = unit-Setᵉ

hom-representing-arrow-Categoryᵉ :
  obj-representing-arrow-Categoryᵉ → obj-representing-arrow-Categoryᵉ → UUᵉ lzero
hom-representing-arrow-Categoryᵉ xᵉ yᵉ =
  type-Setᵉ (hom-set-representing-arrow-Categoryᵉ xᵉ yᵉ)
```

### The underlying precategory of the representing arrow

```agda
comp-hom-representing-arrow-Categoryᵉ :
  {xᵉ yᵉ zᵉ : obj-representing-arrow-Categoryᵉ} →
  hom-representing-arrow-Categoryᵉ yᵉ zᵉ →
  hom-representing-arrow-Categoryᵉ xᵉ yᵉ →
  hom-representing-arrow-Categoryᵉ xᵉ zᵉ
comp-hom-representing-arrow-Categoryᵉ {trueᵉ} {trueᵉ} {trueᵉ} _ _ = starᵉ
comp-hom-representing-arrow-Categoryᵉ {falseᵉ} _ _ = starᵉ

associative-comp-hom-representing-arrow-Categoryᵉ :
  {xᵉ yᵉ zᵉ wᵉ : obj-representing-arrow-Categoryᵉ} →
  (hᵉ : hom-representing-arrow-Categoryᵉ zᵉ wᵉ)
  (gᵉ : hom-representing-arrow-Categoryᵉ yᵉ zᵉ)
  (fᵉ : hom-representing-arrow-Categoryᵉ xᵉ yᵉ) →
  ( comp-hom-representing-arrow-Categoryᵉ
    { xᵉ} (comp-hom-representing-arrow-Categoryᵉ {yᵉ} hᵉ gᵉ) fᵉ) ＝ᵉ
  ( comp-hom-representing-arrow-Categoryᵉ
    { xᵉ} hᵉ (comp-hom-representing-arrow-Categoryᵉ {xᵉ} gᵉ fᵉ))
associative-comp-hom-representing-arrow-Categoryᵉ
  { trueᵉ} {trueᵉ} {trueᵉ} {trueᵉ} hᵉ gᵉ fᵉ =
  reflᵉ
associative-comp-hom-representing-arrow-Categoryᵉ {falseᵉ} hᵉ gᵉ fᵉ = reflᵉ

id-hom-representing-arrow-Categoryᵉ :
  {xᵉ : obj-representing-arrow-Categoryᵉ} → hom-representing-arrow-Categoryᵉ xᵉ xᵉ
id-hom-representing-arrow-Categoryᵉ {trueᵉ} = starᵉ
id-hom-representing-arrow-Categoryᵉ {falseᵉ} = starᵉ

left-unit-law-comp-hom-representing-arrow-Categoryᵉ :
  {xᵉ yᵉ : obj-representing-arrow-Categoryᵉ} →
  (fᵉ : hom-representing-arrow-Categoryᵉ xᵉ yᵉ) →
  comp-hom-representing-arrow-Categoryᵉ
    { xᵉ} (id-hom-representing-arrow-Categoryᵉ {yᵉ}) fᵉ ＝ᵉ
  fᵉ
left-unit-law-comp-hom-representing-arrow-Categoryᵉ {trueᵉ} {trueᵉ} fᵉ = reflᵉ
left-unit-law-comp-hom-representing-arrow-Categoryᵉ {falseᵉ} fᵉ = reflᵉ

right-unit-law-comp-hom-representing-arrow-Categoryᵉ :
  {xᵉ yᵉ : obj-representing-arrow-Categoryᵉ} →
  (fᵉ : hom-representing-arrow-Categoryᵉ xᵉ yᵉ) →
  comp-hom-representing-arrow-Categoryᵉ
    { xᵉ} fᵉ (id-hom-representing-arrow-Categoryᵉ {xᵉ}) ＝ᵉ
  fᵉ
right-unit-law-comp-hom-representing-arrow-Categoryᵉ {trueᵉ} {trueᵉ} fᵉ = reflᵉ
right-unit-law-comp-hom-representing-arrow-Categoryᵉ {falseᵉ} fᵉ = reflᵉ

representing-arrow-Precategoryᵉ : Precategoryᵉ lzero lzero
representing-arrow-Precategoryᵉ =
  make-Precategoryᵉ
    ( obj-representing-arrow-Categoryᵉ)
    ( hom-set-representing-arrow-Categoryᵉ)
    ( λ {xᵉ} {yᵉ} {zᵉ} → comp-hom-representing-arrow-Categoryᵉ {xᵉ} {yᵉ} {zᵉ})
    ( λ xᵉ → id-hom-representing-arrow-Categoryᵉ {xᵉ})
    ( λ {xᵉ} {yᵉ} {zᵉ} {wᵉ} →
      associative-comp-hom-representing-arrow-Categoryᵉ {xᵉ} {yᵉ} {zᵉ} {wᵉ})
    ( λ {xᵉ} {yᵉ} → left-unit-law-comp-hom-representing-arrow-Categoryᵉ {xᵉ} {yᵉ})
    ( λ {xᵉ} {yᵉ} → right-unit-law-comp-hom-representing-arrow-Categoryᵉ {xᵉ} {yᵉ})
```

### The representing arrow category

```agda
is-category-representing-arrow-Categoryᵉ :
  is-category-Precategoryᵉ representing-arrow-Precategoryᵉ
is-category-representing-arrow-Categoryᵉ trueᵉ trueᵉ =
    is-equiv-has-converse-is-propᵉ
    ( is-set-boolᵉ trueᵉ trueᵉ)
    ( is-prop-type-subtypeᵉ
      ( is-iso-prop-Precategoryᵉ representing-arrow-Precategoryᵉ {trueᵉ} {trueᵉ})
      ( is-prop-unitᵉ))
    ( λ _ → reflᵉ)
is-category-representing-arrow-Categoryᵉ trueᵉ falseᵉ =
  is-equiv-is-emptyᵉ
    ( iso-eq-Precategoryᵉ representing-arrow-Precategoryᵉ trueᵉ falseᵉ)
    ( hom-iso-Precategoryᵉ representing-arrow-Precategoryᵉ)
is-category-representing-arrow-Categoryᵉ falseᵉ trueᵉ =
  is-equiv-is-emptyᵉ
    ( iso-eq-Precategoryᵉ representing-arrow-Precategoryᵉ falseᵉ trueᵉ)
    ( hom-inv-iso-Precategoryᵉ representing-arrow-Precategoryᵉ)
is-category-representing-arrow-Categoryᵉ falseᵉ falseᵉ =
  is-equiv-has-converse-is-propᵉ
    ( is-set-boolᵉ falseᵉ falseᵉ)
    ( is-prop-type-subtypeᵉ
      ( is-iso-prop-Precategoryᵉ representing-arrow-Precategoryᵉ {falseᵉ} {falseᵉ})
      ( is-prop-unitᵉ))
    ( λ _ → reflᵉ)

representing-arrow-Categoryᵉ : Categoryᵉ lzero lzero
pr1ᵉ representing-arrow-Categoryᵉ = representing-arrow-Precategoryᵉ
pr2ᵉ representing-arrow-Categoryᵉ = is-category-representing-arrow-Categoryᵉ
```

## Properties

### The representing arrow represents arrows in a category

Thisᵉ remainsᵉ to beᵉ formalized.ᵉ

## External links

-ᵉ [Intervalᵉ category](https://1lab.dev/Cat.Instances.Shape.Interval.html#interval-categoryᵉ)
  atᵉ 1labᵉ
-ᵉ [intervalᵉ category](https://ncatlab.org/nlab/show/interval+categoryᵉ) atᵉ $n$Labᵉ

Aᵉ wikidataᵉ identifierᵉ wasᵉ notᵉ availableᵉ forᵉ thisᵉ concept.ᵉ