# Top elements in large posets

```agda
module order-theory.top-elements-large-posetsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levelsᵉ

open import order-theory.dependent-products-large-posetsᵉ
open import order-theory.large-posetsᵉ
```

</details>

## Idea

Weᵉ sayᵉ thatᵉ aᵉ [largeᵉ poset](order-theory.large-posets.mdᵉ) `P`ᵉ hasᵉ aᵉ **largestᵉ
element**ᵉ ifᵉ itᵉ comesᵉ equippedᵉ with anᵉ elementᵉ `tᵉ : type-Large-Posetᵉ Pᵉ lzero`ᵉ
suchᵉ thatᵉ `xᵉ ≤ᵉ t`ᵉ holdsᵉ forᵉ everyᵉ `xᵉ : P`ᵉ

## Definition

### The predicate on elements of posets of being a top element

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level} (Pᵉ : Large-Posetᵉ αᵉ βᵉ)
  where

  is-top-element-Large-Posetᵉ :
    {l1ᵉ : Level} → type-Large-Posetᵉ Pᵉ l1ᵉ → UUωᵉ
  is-top-element-Large-Posetᵉ xᵉ =
    {lᵉ : Level} (yᵉ : type-Large-Posetᵉ Pᵉ lᵉ) → leq-Large-Posetᵉ Pᵉ yᵉ xᵉ
```

### The predicate on posets of having a top element

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Pᵉ : Large-Posetᵉ αᵉ βᵉ)
  where

  record
    has-top-element-Large-Posetᵉ : UUωᵉ
    where
    field
      top-has-top-element-Large-Posetᵉ :
        type-Large-Posetᵉ Pᵉ lzero
      is-top-element-top-has-top-element-Large-Posetᵉ :
        is-top-element-Large-Posetᵉ Pᵉ top-has-top-element-Large-Posetᵉ

  open has-top-element-Large-Posetᵉ public
```

## Properties

### If `P` is a family of large posets, then `Π-Large-Poset P` has a largest element

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  {l1ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ} (Pᵉ : Iᵉ → Large-Posetᵉ αᵉ βᵉ)
  where

  has-top-element-Π-Large-Posetᵉ :
    ((iᵉ : Iᵉ) → has-top-element-Large-Posetᵉ (Pᵉ iᵉ)) →
    has-top-element-Large-Posetᵉ (Π-Large-Posetᵉ Pᵉ)
  top-has-top-element-Large-Posetᵉ
    ( has-top-element-Π-Large-Posetᵉ Hᵉ) iᵉ =
    top-has-top-element-Large-Posetᵉ (Hᵉ iᵉ)
  is-top-element-top-has-top-element-Large-Posetᵉ
    ( has-top-element-Π-Large-Posetᵉ Hᵉ) xᵉ iᵉ =
    is-top-element-top-has-top-element-Large-Posetᵉ (Hᵉ iᵉ) (xᵉ iᵉ)
```