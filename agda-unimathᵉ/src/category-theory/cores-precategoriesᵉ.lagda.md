# Cores of precategories

```agda
module category-theory.cores-precategoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categoriesᵉ
open import category-theory.isomorphisms-in-categoriesᵉ
open import category-theory.isomorphisms-in-precategoriesᵉ
open import category-theory.precategoriesᵉ
open import category-theory.pregroupoidsᵉ
open import category-theory.replete-subprecategoriesᵉ
open import category-theory.subprecategoriesᵉ
open import category-theory.wide-subprecategoriesᵉ

open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.subtypesᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Theᵉ **coreᵉ ofᵉ aᵉ [precategory](category-theory.precategories.md)**ᵉ `C`ᵉ isᵉ theᵉ
maximalᵉ subpregroupoidᵉ ofᵉ it.ᵉ Itᵉ consistsᵉ ofᵉ allᵉ objectsᵉ andᵉ
[isomorphisms](category-theory.isomorphisms-in-precategories.mdᵉ) in `C`.ᵉ

## Definitions

### The core wide subprecategory

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  where

  core-wide-subprecategory-Precategoryᵉ : Wide-Subprecategoryᵉ l2ᵉ Cᵉ
  pr1ᵉ core-wide-subprecategory-Precategoryᵉ xᵉ yᵉ = is-iso-prop-Precategoryᵉ Cᵉ
  pr1ᵉ (pr2ᵉ core-wide-subprecategory-Precategoryᵉ) xᵉ = is-iso-id-hom-Precategoryᵉ Cᵉ
  pr2ᵉ (pr2ᵉ core-wide-subprecategory-Precategoryᵉ) xᵉ yᵉ zᵉ gᵉ fᵉ =
    is-iso-comp-is-iso-Precategoryᵉ Cᵉ
```

### The core subprecategory

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  where

  core-subprecategory-Precategoryᵉ : Subprecategoryᵉ lzero l2ᵉ Cᵉ
  core-subprecategory-Precategoryᵉ =
    subprecategory-Wide-Subprecategoryᵉ Cᵉ
      ( core-wide-subprecategory-Precategoryᵉ Cᵉ)

  is-wide-core-Precategoryᵉ :
    is-wide-Subprecategoryᵉ Cᵉ core-subprecategory-Precategoryᵉ
  is-wide-core-Precategoryᵉ =
    is-wide-Wide-Subprecategoryᵉ Cᵉ (core-wide-subprecategory-Precategoryᵉ Cᵉ)
```

### The core precategory

```agda
core-precategory-Precategoryᵉ :
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ) → Precategoryᵉ l1ᵉ l2ᵉ
core-precategory-Precategoryᵉ Cᵉ =
  precategory-Wide-Subprecategoryᵉ Cᵉ (core-wide-subprecategory-Precategoryᵉ Cᵉ)
```

### The core pregroupoid

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  where

  is-pregroupoid-core-Precategoryᵉ :
    is-pregroupoid-Precategoryᵉ (core-precategory-Precategoryᵉ Cᵉ)
  pr1ᵉ (pr1ᵉ (is-pregroupoid-core-Precategoryᵉ xᵉ yᵉ (fᵉ ,ᵉ f'ᵉ ,ᵉ lᵉ ,ᵉ rᵉ))) = f'ᵉ
  pr1ᵉ (pr2ᵉ (pr1ᵉ (is-pregroupoid-core-Precategoryᵉ xᵉ yᵉ (fᵉ ,ᵉ f'ᵉ ,ᵉ lᵉ ,ᵉ rᵉ)))) = fᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ (pr1ᵉ (is-pregroupoid-core-Precategoryᵉ xᵉ yᵉ (fᵉ ,ᵉ f'ᵉ ,ᵉ lᵉ ,ᵉ rᵉ))))) =
    rᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ (pr1ᵉ (is-pregroupoid-core-Precategoryᵉ xᵉ yᵉ (fᵉ ,ᵉ f'ᵉ ,ᵉ lᵉ ,ᵉ rᵉ))))) =
    lᵉ
  pr1ᵉ (pr2ᵉ (is-pregroupoid-core-Precategoryᵉ xᵉ yᵉ (fᵉ ,ᵉ f'ᵉ ,ᵉ lᵉ ,ᵉ rᵉ))) =
    eq-type-subtypeᵉ (is-iso-prop-Precategoryᵉ Cᵉ) lᵉ
  pr2ᵉ (pr2ᵉ (is-pregroupoid-core-Precategoryᵉ xᵉ yᵉ (fᵉ ,ᵉ f'ᵉ ,ᵉ lᵉ ,ᵉ rᵉ))) =
    eq-type-subtypeᵉ (is-iso-prop-Precategoryᵉ Cᵉ) rᵉ

  core-pregroupoid-Precategoryᵉ : Pregroupoidᵉ l1ᵉ l2ᵉ
  pr1ᵉ core-pregroupoid-Precategoryᵉ = core-precategory-Precategoryᵉ Cᵉ
  pr2ᵉ core-pregroupoid-Precategoryᵉ = is-pregroupoid-core-Precategoryᵉ
```

## Properties

### Computing isomorphisms in the core

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ) {xᵉ yᵉ : obj-Precategoryᵉ Cᵉ}
  where

  compute-iso-core-Precategoryᵉ :
    iso-Precategoryᵉ Cᵉ xᵉ yᵉ ≃ᵉ iso-Precategoryᵉ (core-precategory-Precategoryᵉ Cᵉ) xᵉ yᵉ
  compute-iso-core-Precategoryᵉ =
    compute-iso-Pregroupoidᵉ (core-pregroupoid-Precategoryᵉ Cᵉ)

  inv-compute-iso-core-Precategoryᵉ :
    iso-Precategoryᵉ (core-precategory-Precategoryᵉ Cᵉ) xᵉ yᵉ ≃ᵉ iso-Precategoryᵉ Cᵉ xᵉ yᵉ
  inv-compute-iso-core-Precategoryᵉ =
    inv-compute-iso-Pregroupoidᵉ (core-pregroupoid-Precategoryᵉ Cᵉ)
```

### The core is replete

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  where

  is-replete-core-Precategoryᵉ :
    is-replete-Subprecategoryᵉ Cᵉ (core-subprecategory-Precategoryᵉ Cᵉ)
  pr1ᵉ (is-replete-core-Precategoryᵉ xᵉ yᵉ (fᵉ ,ᵉ is-iso-fᵉ)) = starᵉ
  pr1ᵉ (pr2ᵉ (is-replete-core-Precategoryᵉ xᵉ yᵉ (fᵉ ,ᵉ is-iso-fᵉ))) = is-iso-fᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ (is-replete-core-Precategoryᵉ xᵉ yᵉ (fᵉ ,ᵉ is-iso-fᵉ)))) = fᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ (is-replete-core-Precategoryᵉ xᵉ yᵉ (fᵉ ,ᵉ f'ᵉ ,ᵉ lᵉ ,ᵉ rᵉ))))) = rᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ (is-replete-core-Precategoryᵉ xᵉ yᵉ (fᵉ ,ᵉ f'ᵉ ,ᵉ lᵉ ,ᵉ rᵉ))))) = lᵉ
```

### The base precategory is a category if and only if the core is

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  where

  is-torsorial-iso-core-is-category-Precategoryᵉ :
    is-category-Precategoryᵉ Cᵉ →
    (xᵉ : obj-Precategoryᵉ Cᵉ) →
    is-torsorialᵉ (iso-Precategoryᵉ (core-precategory-Precategoryᵉ Cᵉ) xᵉ)
  is-torsorial-iso-core-is-category-Precategoryᵉ is-category-Cᵉ xᵉ =
    is-contr-equivᵉ
      ( Σᵉ (obj-Categoryᵉ (Cᵉ ,ᵉ is-category-Cᵉ)) (iso-Precategoryᵉ Cᵉ xᵉ))
      ( equiv-totᵉ (λ yᵉ → inv-compute-iso-core-Precategoryᵉ Cᵉ))
      ( is-torsorial-iso-Categoryᵉ (Cᵉ ,ᵉ is-category-Cᵉ) xᵉ)

  is-category-core-is-category-Precategoryᵉ :
    is-category-Precategoryᵉ Cᵉ →
    is-category-Precategoryᵉ (core-precategory-Precategoryᵉ Cᵉ)
  is-category-core-is-category-Precategoryᵉ is-category-Cᵉ xᵉ =
    fundamental-theorem-idᵉ
      ( is-torsorial-iso-core-is-category-Precategoryᵉ is-category-Cᵉ xᵉ)
      ( iso-eq-Precategoryᵉ (core-precategory-Precategoryᵉ Cᵉ) xᵉ)

  is-torsorial-iso-is-category-core-Precategoryᵉ :
    is-category-Precategoryᵉ (core-precategory-Precategoryᵉ Cᵉ) →
    (xᵉ : obj-Precategoryᵉ Cᵉ) →
    is-torsorialᵉ (iso-Precategoryᵉ Cᵉ xᵉ)
  is-torsorial-iso-is-category-core-Precategoryᵉ is-category-core-Cᵉ xᵉ =
    is-contr-equivᵉ
      ( Σᵉ ( obj-Categoryᵉ (core-precategory-Precategoryᵉ Cᵉ ,ᵉ is-category-core-Cᵉ))
          ( iso-Precategoryᵉ (core-precategory-Precategoryᵉ Cᵉ) xᵉ))
      ( equiv-totᵉ (λ yᵉ → compute-iso-core-Precategoryᵉ Cᵉ))
      ( is-torsorial-iso-Categoryᵉ
        ( core-precategory-Precategoryᵉ Cᵉ ,ᵉ is-category-core-Cᵉ)
        ( xᵉ))

  is-category-is-category-core-Precategoryᵉ :
    is-category-Precategoryᵉ (core-precategory-Precategoryᵉ Cᵉ) →
    is-category-Precategoryᵉ Cᵉ
  is-category-is-category-core-Precategoryᵉ is-category-core-Cᵉ xᵉ =
    fundamental-theorem-idᵉ
      ( is-torsorial-iso-is-category-core-Precategoryᵉ is-category-core-Cᵉ xᵉ)
      ( iso-eq-Precategoryᵉ Cᵉ xᵉ)
```

### The construction of the core is idempotent

```text
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  where

  is-idempotent-core-Precategoryᵉ :
    ( core-precategory-Precategoryᵉ (core-precategory-Precategoryᵉ Cᵉ)) ＝ᵉ
    ( core-precategory-Precategoryᵉ Cᵉ)
  is-idempotent-core-Precategoryᵉ = {!ᵉ   !ᵉ}
```

## See also

-ᵉ [Coresᵉ ofᵉ monoids](group-theory.cores-monoids.mdᵉ)
-ᵉ [Restrictionsᵉ ofᵉ functorsᵉ to coresᵉ ofᵉ precategories](category-theory.restrictions-functors-cores-precategories.mdᵉ)

## External links

-ᵉ [Theᵉ coreᵉ ofᵉ aᵉ category](https://1lab.dev/Cat.Instances.Core.htmlᵉ) atᵉ 1labᵉ
-ᵉ [coreᵉ groupoid](https://ncatlab.org/nlab/show/core+groupoidᵉ) atᵉ $n$Labᵉ