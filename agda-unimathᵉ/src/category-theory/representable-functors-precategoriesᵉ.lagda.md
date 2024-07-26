# Representable functors between precategories

```agda
module category-theory.representable-functors-precategoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.copresheaf-categoriesᵉ
open import category-theory.functors-precategoriesᵉ
open import category-theory.maps-precategoriesᵉ
open import category-theory.natural-transformations-functors-precategoriesᵉ
open import category-theory.opposite-precategoriesᵉ
open import category-theory.precategoriesᵉ

open import foundation.category-of-setsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.homotopiesᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Givenᵉ aᵉ [precategory](category-theory.precategories.mdᵉ) `C`ᵉ andᵉ anᵉ objectᵉ `c`,ᵉ
thereᵉ isᵉ aᵉ [functor](category-theory.functors-precategories.mdᵉ) fromᵉ `C`ᵉ to theᵉ
[precategoryᵉ ofᵉ sets](foundation.category-of-sets.mdᵉ) **represented**ᵉ byᵉ `c`ᵉ
thatᵉ:

-ᵉ sendsᵉ anᵉ objectᵉ `x`ᵉ ofᵉ `C`ᵉ to theᵉ [set](foundation-core.sets.mdᵉ) `homᵉ cᵉ x`ᵉ andᵉ
-ᵉ sendsᵉ aᵉ morphismᵉ `fᵉ : homᵉ xᵉ y`ᵉ ofᵉ `C`ᵉ to theᵉ functionᵉ `homᵉ cᵉ xᵉ → homᵉ cᵉ y`ᵉ
  definedᵉ byᵉ postcompositionᵉ with `f`.ᵉ

Theᵉ functorialityᵉ axiomsᵉ follow,ᵉ byᵉ
[functionᵉ extensionality](foundation.function-extensionality.md),ᵉ fromᵉ
associativityᵉ andᵉ theᵉ leftᵉ unitᵉ lawᵉ forᵉ theᵉ precategoryᵉ `C`.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ) (cᵉ : obj-Precategoryᵉ Cᵉ)
  where

  obj-representable-functor-Precategoryᵉ : obj-Precategoryᵉ Cᵉ → Setᵉ l2ᵉ
  obj-representable-functor-Precategoryᵉ = hom-set-Precategoryᵉ Cᵉ cᵉ

  hom-representable-functor-Precategoryᵉ :
    {xᵉ yᵉ : obj-Precategoryᵉ Cᵉ} (fᵉ : hom-Precategoryᵉ Cᵉ xᵉ yᵉ) →
    hom-Precategoryᵉ Cᵉ cᵉ xᵉ → hom-Precategoryᵉ Cᵉ cᵉ yᵉ
  hom-representable-functor-Precategoryᵉ fᵉ = postcomp-hom-Precategoryᵉ Cᵉ fᵉ cᵉ

  representable-map-Precategoryᵉ : map-Precategoryᵉ Cᵉ (Set-Precategoryᵉ l2ᵉ)
  pr1ᵉ representable-map-Precategoryᵉ = obj-representable-functor-Precategoryᵉ
  pr2ᵉ representable-map-Precategoryᵉ = hom-representable-functor-Precategoryᵉ

  preserves-comp-representable-functor-Precategoryᵉ :
    preserves-comp-hom-map-Precategoryᵉ
      ( Cᵉ)
      ( Set-Precategoryᵉ l2ᵉ)
      ( representable-map-Precategoryᵉ)
  preserves-comp-representable-functor-Precategoryᵉ gᵉ fᵉ =
    eq-htpyᵉ (associative-comp-hom-Precategoryᵉ Cᵉ gᵉ fᵉ)

  preserves-id-representable-functor-Precategoryᵉ :
    preserves-id-hom-map-Precategoryᵉ
      ( Cᵉ)
      ( Set-Precategoryᵉ l2ᵉ)
      ( representable-map-Precategoryᵉ)
  preserves-id-representable-functor-Precategoryᵉ xᵉ =
    eq-htpyᵉ (left-unit-law-comp-hom-Precategoryᵉ Cᵉ)

  representable-functor-Precategoryᵉ : functor-Precategoryᵉ Cᵉ (Set-Precategoryᵉ l2ᵉ)
  pr1ᵉ representable-functor-Precategoryᵉ =
    obj-representable-functor-Precategoryᵉ
  pr1ᵉ (pr2ᵉ representable-functor-Precategoryᵉ) =
    hom-representable-functor-Precategoryᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ representable-functor-Precategoryᵉ)) =
    preserves-comp-representable-functor-Precategoryᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ representable-functor-Precategoryᵉ)) =
    preserves-id-representable-functor-Precategoryᵉ
```

## Natural transformations between representable functors

Aᵉ morphismᵉ `fᵉ : homᵉ bᵉ c`ᵉ in aᵉ precategoryᵉ `C`ᵉ definesᵉ aᵉ
[naturalᵉ transformation](category-theory.natural-transformations-functors-precategories.mdᵉ)
fromᵉ theᵉ functorᵉ representedᵉ byᵉ `c`ᵉ to theᵉ functorᵉ representedᵉ byᵉ `b`.ᵉ Itsᵉ
componentsᵉ `homᵉ cᵉ xᵉ → homᵉ bᵉ x`ᵉ areᵉ definedᵉ byᵉ precompositionᵉ with `f`.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  {bᵉ cᵉ : obj-Precategoryᵉ Cᵉ} (fᵉ : hom-Precategoryᵉ Cᵉ bᵉ cᵉ)
  where

  hom-family-representable-natural-transformation-Precategoryᵉ :
    hom-family-functor-Precategoryᵉ
      ( Cᵉ)
      ( Set-Precategoryᵉ l2ᵉ)
      ( representable-functor-Precategoryᵉ Cᵉ cᵉ)
      ( representable-functor-Precategoryᵉ Cᵉ bᵉ)
  hom-family-representable-natural-transformation-Precategoryᵉ =
    precomp-hom-Precategoryᵉ Cᵉ fᵉ

  is-natural-transformation-representable-natural-transformation-Precategoryᵉ :
    is-natural-transformation-Precategoryᵉ
      ( Cᵉ)
      ( Set-Precategoryᵉ l2ᵉ)
      ( representable-functor-Precategoryᵉ Cᵉ cᵉ)
      ( representable-functor-Precategoryᵉ Cᵉ bᵉ)
      ( hom-family-representable-natural-transformation-Precategoryᵉ)
  is-natural-transformation-representable-natural-transformation-Precategoryᵉ hᵉ =
    eq-htpyᵉ (inv-htpyᵉ (λ gᵉ → associative-comp-hom-Precategoryᵉ Cᵉ hᵉ gᵉ fᵉ))

  representable-natural-transformation-Precategoryᵉ :
    natural-transformation-Precategoryᵉ
      ( Cᵉ)
      ( Set-Precategoryᵉ l2ᵉ)
      ( representable-functor-Precategoryᵉ Cᵉ cᵉ)
      ( representable-functor-Precategoryᵉ Cᵉ bᵉ)
  pr1ᵉ (representable-natural-transformation-Precategoryᵉ) =
    hom-family-representable-natural-transformation-Precategoryᵉ
  pr2ᵉ (representable-natural-transformation-Precategoryᵉ) =
    is-natural-transformation-representable-natural-transformation-Precategoryᵉ
```

## Properties

### Taking representable functors defines a functor into the presheaf category

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  where

  map-representable-functor-copresheaf-Precategoryᵉ :
    map-Precategoryᵉ
      ( opposite-Precategoryᵉ Cᵉ)
      ( copresheaf-precategory-Precategoryᵉ Cᵉ l2ᵉ)
  pr1ᵉ map-representable-functor-copresheaf-Precategoryᵉ =
    representable-functor-Precategoryᵉ Cᵉ
  pr2ᵉ map-representable-functor-copresheaf-Precategoryᵉ =
    representable-natural-transformation-Precategoryᵉ Cᵉ
```

Itᵉ remainsᵉ to showᵉ thatᵉ thisᵉ mapᵉ isᵉ functorial.ᵉ