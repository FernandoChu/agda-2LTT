# Empty multisets

```agda
module trees.empty-multisetsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.empty-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.universe-levelsᵉ

open import trees.elementhood-relation-w-typesᵉ
open import trees.multisetsᵉ
open import trees.w-typesᵉ
```

</details>

## Idea

Aᵉ [multiset](trees.multisets.mdᵉ) isᵉ saidᵉ to beᵉ **empty**ᵉ ifᵉ itᵉ hasᵉ noᵉ
[elements](trees.elementhood-relation-w-types.md).ᵉ

## Definition

### The predicate of being an empty multiset

```agda
module _
  {lᵉ : Level}
  where

  is-empty-𝕍ᵉ : 𝕍ᵉ lᵉ → UUᵉ lᵉ
  is-empty-𝕍ᵉ (tree-𝕎ᵉ Xᵉ Yᵉ) = is-emptyᵉ Xᵉ

  is-property-is-empty-𝕍ᵉ : (Xᵉ : 𝕍ᵉ lᵉ) → is-propᵉ (is-empty-𝕍ᵉ Xᵉ)
  is-property-is-empty-𝕍ᵉ (tree-𝕎ᵉ Xᵉ Yᵉ) = is-property-is-emptyᵉ

  is-empty-prop-𝕍ᵉ : 𝕍ᵉ lᵉ → Propᵉ lᵉ
  is-empty-prop-𝕍ᵉ Xᵉ = is-empty-𝕍ᵉ Xᵉ ,ᵉ is-property-is-empty-𝕍ᵉ Xᵉ
```

### The predicate of being a multiset with no elements

However,ᵉ noteᵉ thatᵉ thisᵉ predicateᵉ returnsᵉ aᵉ typeᵉ ofᵉ universeᵉ levelᵉ `lsucᵉ l`.ᵉ

```agda
module _
  {lᵉ : Level}
  where

  has-no-elements-𝕍ᵉ : 𝕍ᵉ lᵉ → UUᵉ (lsuc lᵉ)
  has-no-elements-𝕍ᵉ Xᵉ = (Yᵉ : 𝕍ᵉ lᵉ) → Yᵉ ∉-𝕎ᵉ Xᵉ
```

## Properties

### A multiset `X` is empty if and only if it has no elements

```agda
module _
  {lᵉ : Level}
  where

  is-empty-has-no-elements-𝕍ᵉ :
    (Xᵉ : 𝕍ᵉ lᵉ) → has-no-elements-𝕍ᵉ Xᵉ → is-empty-𝕍ᵉ Xᵉ
  is-empty-has-no-elements-𝕍ᵉ (tree-𝕎ᵉ Xᵉ Yᵉ) Hᵉ xᵉ = Hᵉ (Yᵉ xᵉ) (xᵉ ,ᵉ reflᵉ)

  has-no-elements-is-empty-𝕍ᵉ :
    (Xᵉ : 𝕍ᵉ lᵉ) → is-empty-𝕍ᵉ Xᵉ → has-no-elements-𝕍ᵉ Xᵉ
  has-no-elements-is-empty-𝕍ᵉ (tree-𝕎ᵉ Xᵉ Yᵉ) Hᵉ ._ (xᵉ ,ᵉ reflᵉ) = Hᵉ xᵉ
```