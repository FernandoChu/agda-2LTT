# Representable functors between categories

```agda
module category-theory.representable-functors-categoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categoriesᵉ
open import category-theory.functors-categoriesᵉ
open import category-theory.natural-transformations-functors-categoriesᵉ
open import category-theory.representable-functors-precategoriesᵉ

open import foundation.category-of-setsᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Givenᵉ aᵉ [category](category-theory.categories.mdᵉ) `C`ᵉ andᵉ anᵉ objectᵉ `c`,ᵉ thereᵉ
isᵉ aᵉ [functor](category-theory.functors-categories.mdᵉ) fromᵉ `C`ᵉ to theᵉ
[categoryᵉ ofᵉ sets](foundation.category-of-sets.mdᵉ) **represented**ᵉ byᵉ `c`ᵉ thatᵉ:

-ᵉ sendsᵉ anᵉ objectᵉ `x`ᵉ ofᵉ `C`ᵉ to theᵉ [set](foundation-core.sets.mdᵉ) `homᵉ cᵉ x`ᵉ andᵉ
-ᵉ sendsᵉ aᵉ morphismᵉ `gᵉ : homᵉ xᵉ y`ᵉ ofᵉ `C`ᵉ to theᵉ functionᵉ `homᵉ cᵉ xᵉ → homᵉ cᵉ y`ᵉ
  definedᵉ byᵉ postcompositionᵉ with `g`.ᵉ

Theᵉ functorialityᵉ axiomsᵉ follow,ᵉ byᵉ
[functionᵉ extensionality](foundation.function-extensionality.md),ᵉ fromᵉ
associativityᵉ andᵉ theᵉ leftᵉ unitᵉ lawᵉ forᵉ theᵉ categoryᵉ `C`.ᵉ

## Definition

```agda
representable-functor-Categoryᵉ :
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ) (cᵉ : obj-Categoryᵉ Cᵉ) →
  functor-Categoryᵉ Cᵉ (Set-Categoryᵉ l2ᵉ)
representable-functor-Categoryᵉ Cᵉ =
  representable-functor-Precategoryᵉ (precategory-Categoryᵉ Cᵉ)
```

## Natural transformations between representable functors

Aᵉ morphismᵉ `fᵉ : homᵉ bᵉ c`ᵉ in aᵉ categoryᵉ `C`ᵉ definesᵉ aᵉ
[naturalᵉ transformation](category-theory.natural-transformations-functors-categories.mdᵉ)
fromᵉ theᵉ functorᵉ representedᵉ byᵉ `c`ᵉ to theᵉ functorᵉ representedᵉ byᵉ `b`.ᵉ Itsᵉ
componentsᵉ `homᵉ cᵉ xᵉ → homᵉ bᵉ x`ᵉ areᵉ definedᵉ byᵉ precompositionᵉ with `f`.ᵉ

```agda
representable-natural-transformation-Categoryᵉ :
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Categoryᵉ l1ᵉ l2ᵉ) {bᵉ cᵉ : obj-Categoryᵉ Cᵉ}
  (fᵉ : hom-Categoryᵉ Cᵉ bᵉ cᵉ) →
  natural-transformation-Categoryᵉ
    ( Cᵉ)
    ( Set-Categoryᵉ l2ᵉ)
    ( representable-functor-Categoryᵉ Cᵉ cᵉ)
    ( representable-functor-Categoryᵉ Cᵉ bᵉ)
representable-natural-transformation-Categoryᵉ Cᵉ =
  representable-natural-transformation-Precategoryᵉ (precategory-Categoryᵉ Cᵉ)
```