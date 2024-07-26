# Subterminal precategories

```agda
module category-theory.subterminal-precategoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.composition-operations-on-binary-families-of-setsᵉ
open import category-theory.fully-faithful-functors-precategoriesᵉ
open import category-theory.isomorphisms-in-precategoriesᵉ
open import category-theory.precategoriesᵉ
open import category-theory.pregroupoidsᵉ
open import category-theory.preunivalent-categoriesᵉ
open import category-theory.strict-categoriesᵉ
open import category-theory.terminal-categoryᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.embeddingsᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.iterated-dependent-product-typesᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.subtype-identity-principleᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Aᵉ [precategory](category-theory.precategories.mdᵉ) isᵉ **subterminal**ᵉ ifᵉ itsᵉ
[terminalᵉ projectionᵉ functor](category-theory.terminal-category.mdᵉ) isᵉ
[fullyᵉ faithful](category-theory.fully-faithful-functors-precategories.md).ᵉ

## Definitions

### The predicate on precategories of being subterminal

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  where

  is-subterminal-Precategoryᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-subterminal-Precategoryᵉ =
    is-fully-faithful-functor-Precategoryᵉ Cᵉ terminal-Precategoryᵉ
      ( terminal-functor-Precategoryᵉ Cᵉ)

  is-subterminal-prop-Precategoryᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  is-subterminal-prop-Precategoryᵉ =
    is-fully-faithful-prop-functor-Precategoryᵉ Cᵉ terminal-Precategoryᵉ
      ( terminal-functor-Precategoryᵉ Cᵉ)

  is-prop-is-subterminal-Precategoryᵉ : is-propᵉ is-subterminal-Precategoryᵉ
  is-prop-is-subterminal-Precategoryᵉ =
    is-prop-is-fully-faithful-functor-Precategoryᵉ Cᵉ terminal-Precategoryᵉ
      ( terminal-functor-Precategoryᵉ Cᵉ)
```