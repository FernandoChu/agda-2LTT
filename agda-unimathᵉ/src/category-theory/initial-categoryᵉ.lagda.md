# The initial category

```agda
module category-theory.initial-categoryᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categoriesᵉ
open import category-theory.functors-precategoriesᵉ
open import category-theory.gaunt-categoriesᵉ
open import category-theory.indiscrete-precategoriesᵉ
open import category-theory.precategoriesᵉ
open import category-theory.preunivalent-categoriesᵉ
open import category-theory.strict-categoriesᵉ

open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.empty-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.setsᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Theᵉ **initialᵉ category**ᵉ isᵉ theᵉ [category](category-theory.categories.mdᵉ) with
noᵉ objects.ᵉ

## Definition

### The objects and hom-sets of the initial category

```agda
obj-initial-Categoryᵉ : UUᵉ lzero
obj-initial-Categoryᵉ = emptyᵉ

hom-set-initial-Categoryᵉ :
  obj-initial-Categoryᵉ → obj-initial-Categoryᵉ → Setᵉ lzero
hom-set-initial-Categoryᵉ _ _ = unit-Setᵉ

hom-initial-Categoryᵉ :
  obj-initial-Categoryᵉ → obj-initial-Categoryᵉ → UUᵉ lzero
hom-initial-Categoryᵉ xᵉ yᵉ = type-Setᵉ (hom-set-initial-Categoryᵉ xᵉ yᵉ)
```

### The underlying precategory of the initial category

```agda
comp-hom-initial-Categoryᵉ :
  {xᵉ yᵉ zᵉ : obj-initial-Categoryᵉ} →
  hom-initial-Categoryᵉ yᵉ zᵉ → hom-initial-Categoryᵉ xᵉ yᵉ → hom-initial-Categoryᵉ xᵉ zᵉ
comp-hom-initial-Categoryᵉ {xᵉ} {yᵉ} {zᵉ} =
  comp-hom-indiscrete-Precategoryᵉ emptyᵉ {xᵉ} {yᵉ} {zᵉ}

associative-comp-hom-initial-Categoryᵉ :
  {xᵉ yᵉ zᵉ wᵉ : obj-initial-Categoryᵉ}
  (hᵉ : hom-initial-Categoryᵉ zᵉ wᵉ)
  (gᵉ : hom-initial-Categoryᵉ yᵉ zᵉ)
  (fᵉ : hom-initial-Categoryᵉ xᵉ yᵉ) →
  comp-hom-initial-Categoryᵉ {xᵉ} {yᵉ} {wᵉ}
    ( comp-hom-initial-Categoryᵉ {yᵉ} {zᵉ} {wᵉ} hᵉ gᵉ)
    ( fᵉ) ＝ᵉ
  comp-hom-initial-Categoryᵉ {xᵉ} {zᵉ} {wᵉ}
    ( hᵉ)
    ( comp-hom-initial-Categoryᵉ {xᵉ} {yᵉ} {zᵉ} gᵉ fᵉ)
associative-comp-hom-initial-Categoryᵉ {xᵉ} {yᵉ} {zᵉ} {wᵉ} =
  associative-comp-hom-indiscrete-Precategoryᵉ emptyᵉ {xᵉ} {yᵉ} {zᵉ} {wᵉ}

id-hom-initial-Categoryᵉ : {xᵉ : obj-initial-Categoryᵉ} → hom-initial-Categoryᵉ xᵉ xᵉ
id-hom-initial-Categoryᵉ {xᵉ} = id-hom-indiscrete-Precategoryᵉ emptyᵉ {xᵉ}

left-unit-law-comp-hom-initial-Categoryᵉ :
  {xᵉ yᵉ : obj-initial-Categoryᵉ}
  (fᵉ : hom-initial-Categoryᵉ xᵉ yᵉ) →
  comp-hom-initial-Categoryᵉ {xᵉ} {yᵉ} {yᵉ} (id-hom-initial-Categoryᵉ {yᵉ}) fᵉ ＝ᵉ fᵉ
left-unit-law-comp-hom-initial-Categoryᵉ {xᵉ} {yᵉ} =
  left-unit-law-comp-hom-indiscrete-Precategoryᵉ emptyᵉ {xᵉ} {yᵉ}

right-unit-law-comp-hom-initial-Categoryᵉ :
  {xᵉ yᵉ : obj-initial-Categoryᵉ}
  (fᵉ : hom-initial-Categoryᵉ xᵉ yᵉ) →
  comp-hom-initial-Categoryᵉ {xᵉ} {xᵉ} {yᵉ} fᵉ (id-hom-initial-Categoryᵉ {xᵉ}) ＝ᵉ fᵉ
right-unit-law-comp-hom-initial-Categoryᵉ {xᵉ} {yᵉ} =
  right-unit-law-comp-hom-indiscrete-Precategoryᵉ emptyᵉ {xᵉ} {yᵉ}

initial-Precategoryᵉ : Precategoryᵉ lzero lzero
initial-Precategoryᵉ = indiscrete-Precategoryᵉ emptyᵉ
```

### The initial category

```agda
is-category-initial-Categoryᵉ :
  is-category-Precategoryᵉ initial-Precategoryᵉ
is-category-initial-Categoryᵉ ()

initial-Categoryᵉ : Categoryᵉ lzero lzero
pr1ᵉ initial-Categoryᵉ = initial-Precategoryᵉ
pr2ᵉ initial-Categoryᵉ = is-category-initial-Categoryᵉ
```

### The initial preunivalent category

```agda
is-preunivalent-initial-Categoryᵉ :
  is-preunivalent-Precategoryᵉ initial-Precategoryᵉ
is-preunivalent-initial-Categoryᵉ ()

initial-Preunivalent-Categoryᵉ : Preunivalent-Categoryᵉ lzero lzero
initial-Preunivalent-Categoryᵉ =
  preunivalent-category-Categoryᵉ initial-Categoryᵉ
```

### The initial strict category

```agda
is-strict-category-initial-Categoryᵉ :
  is-strict-category-Precategoryᵉ initial-Precategoryᵉ
is-strict-category-initial-Categoryᵉ ()

initial-Strict-Categoryᵉ : Strict-Categoryᵉ lzero lzero
pr1ᵉ initial-Strict-Categoryᵉ = initial-Precategoryᵉ
pr2ᵉ initial-Strict-Categoryᵉ = is-strict-category-initial-Categoryᵉ
```

### The initial gaunt category

```agda
is-gaunt-initial-Categoryᵉ : is-gaunt-Categoryᵉ initial-Categoryᵉ
is-gaunt-initial-Categoryᵉ ()

initial-Gaunt-Categoryᵉ : Gaunt-Categoryᵉ lzero lzero
pr1ᵉ initial-Gaunt-Categoryᵉ = initial-Categoryᵉ
pr2ᵉ initial-Gaunt-Categoryᵉ = is-gaunt-initial-Categoryᵉ
```

## Properties

### The initial category is initial

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  where

  initial-functor-Precategoryᵉ : functor-Precategoryᵉ initial-Precategoryᵉ Cᵉ
  pr1ᵉ initial-functor-Precategoryᵉ ()
  pr1ᵉ (pr2ᵉ initial-functor-Precategoryᵉ) {()}
  pr1ᵉ (pr2ᵉ (pr2ᵉ initial-functor-Precategoryᵉ)) {()}
  pr2ᵉ (pr2ᵉ (pr2ᵉ initial-functor-Precategoryᵉ)) ()

  abstract
    uniqueness-initial-functor-Precategoryᵉ :
      (Fᵉ : functor-Precategoryᵉ initial-Precategoryᵉ Cᵉ) →
      initial-functor-Precategoryᵉ ＝ᵉ Fᵉ
    uniqueness-initial-functor-Precategoryᵉ Fᵉ =
      eq-htpy-functor-Precategoryᵉ
        ( initial-Precategoryᵉ)
        ( Cᵉ)
        ( initial-functor-Precategoryᵉ)
        ( Fᵉ)
        ( (λ where ()) ,ᵉ (λ where {()}))

  abstract
    is-contr-functor-initial-Precategoryᵉ :
      is-contrᵉ (functor-Precategoryᵉ initial-Precategoryᵉ Cᵉ)
    pr1ᵉ is-contr-functor-initial-Precategoryᵉ =
      initial-functor-Precategoryᵉ
    pr2ᵉ is-contr-functor-initial-Precategoryᵉ =
      uniqueness-initial-functor-Precategoryᵉ
```

## See also

-ᵉ [Theᵉ terminalᵉ category](category-theory.terminal-category.mdᵉ)

## External links

-ᵉ [emptyᵉ category](https://ncatlab.org/nlab/show/empty+categoryᵉ) atᵉ $n$Labᵉ

Aᵉ wikidataᵉ identifierᵉ wasᵉ notᵉ availableᵉ forᵉ thisᵉ concept.ᵉ