# Lower bounds in large posets

```agda
module order-theory.lower-bounds-large-posetsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.universe-levelsᵉ

open import order-theory.dependent-products-large-posetsᵉ
open import order-theory.large-posetsᵉ
```

</details>

## Idea

Aᵉ **binaryᵉ lowerᵉ bound**ᵉ ofᵉ twoᵉ elementsᵉ `a`ᵉ andᵉ `b`ᵉ in aᵉ largeᵉ posetᵉ `P`ᵉ isᵉ anᵉ
elementᵉ `x`ᵉ suchᵉ thatᵉ bothᵉ `xᵉ ≤ᵉ a`ᵉ andᵉ `xᵉ ≤ᵉ b`ᵉ hold.ᵉ Similarly,ᵉ aᵉ **lowerᵉ
bound**ᵉ ofᵉ aᵉ familyᵉ ofᵉ elementsᵉ `aᵉ : Iᵉ → P`ᵉ in aᵉ largeᵉ posetᵉ `P`ᵉ isᵉ anᵉ elementᵉ
`x`ᵉ suchᵉ thatᵉ `xᵉ ≤ᵉ aᵉ i`ᵉ holdsᵉ forᵉ everyᵉ `iᵉ : I`.ᵉ

## Definitions

### The predicate that an element of a large poset is a lower bound of two elements

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level} (Pᵉ : Large-Posetᵉ αᵉ βᵉ)
  {l1ᵉ l2ᵉ : Level} (aᵉ : type-Large-Posetᵉ Pᵉ l1ᵉ) (bᵉ : type-Large-Posetᵉ Pᵉ l2ᵉ)
  where

  is-binary-lower-bound-Large-Posetᵉ :
    {l3ᵉ : Level} → type-Large-Posetᵉ Pᵉ l3ᵉ → UUᵉ (βᵉ l3ᵉ l1ᵉ ⊔ βᵉ l3ᵉ l2ᵉ)
  is-binary-lower-bound-Large-Posetᵉ xᵉ =
    leq-Large-Posetᵉ Pᵉ xᵉ aᵉ ×ᵉ leq-Large-Posetᵉ Pᵉ xᵉ bᵉ
```

## Properties

### An element of a dependent product of large posets is a binary lower bound of two elements if and only if it is a pointwise binary lower bound

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  {lᵉ : Level} {Iᵉ : UUᵉ lᵉ} (Pᵉ : Iᵉ → Large-Posetᵉ αᵉ βᵉ)
  {l1ᵉ l2ᵉ : Level} (xᵉ : type-Π-Large-Posetᵉ Pᵉ l1ᵉ) (yᵉ : type-Π-Large-Posetᵉ Pᵉ l2ᵉ)
  where

  is-binary-lower-bound-Π-Large-Posetᵉ :
    {l3ᵉ : Level} (zᵉ : type-Π-Large-Posetᵉ Pᵉ l3ᵉ) →
    ((iᵉ : Iᵉ) → is-binary-lower-bound-Large-Posetᵉ (Pᵉ iᵉ) (xᵉ iᵉ) (yᵉ iᵉ) (zᵉ iᵉ)) →
    is-binary-lower-bound-Large-Posetᵉ (Π-Large-Posetᵉ Pᵉ) xᵉ yᵉ zᵉ
  pr1ᵉ (is-binary-lower-bound-Π-Large-Posetᵉ zᵉ Hᵉ) iᵉ = pr1ᵉ (Hᵉ iᵉ)
  pr2ᵉ (is-binary-lower-bound-Π-Large-Posetᵉ zᵉ Hᵉ) iᵉ = pr2ᵉ (Hᵉ iᵉ)

  is-binary-lower-bound-is-binary-lower-bound-Π-Large-Posetᵉ :
    {l3ᵉ : Level} (zᵉ : type-Π-Large-Posetᵉ Pᵉ l3ᵉ) →
    is-binary-lower-bound-Large-Posetᵉ (Π-Large-Posetᵉ Pᵉ) xᵉ yᵉ zᵉ →
    (iᵉ : Iᵉ) → is-binary-lower-bound-Large-Posetᵉ (Pᵉ iᵉ) (xᵉ iᵉ) (yᵉ iᵉ) (zᵉ iᵉ)
  pr1ᵉ (is-binary-lower-bound-is-binary-lower-bound-Π-Large-Posetᵉ zᵉ Hᵉ iᵉ) =
    pr1ᵉ Hᵉ iᵉ
  pr2ᵉ (is-binary-lower-bound-is-binary-lower-bound-Π-Large-Posetᵉ zᵉ Hᵉ iᵉ) =
    pr2ᵉ Hᵉ iᵉ

  logical-equivalence-is-binary-lower-bound-Π-Large-Posetᵉ :
    {l3ᵉ : Level} (zᵉ : type-Π-Large-Posetᵉ Pᵉ l3ᵉ) →
    ((iᵉ : Iᵉ) → is-binary-lower-bound-Large-Posetᵉ (Pᵉ iᵉ) (xᵉ iᵉ) (yᵉ iᵉ) (zᵉ iᵉ)) ↔ᵉ
    is-binary-lower-bound-Large-Posetᵉ (Π-Large-Posetᵉ Pᵉ) xᵉ yᵉ zᵉ
  pr1ᵉ (logical-equivalence-is-binary-lower-bound-Π-Large-Posetᵉ zᵉ) =
    is-binary-lower-bound-Π-Large-Posetᵉ zᵉ
  pr2ᵉ (logical-equivalence-is-binary-lower-bound-Π-Large-Posetᵉ zᵉ) =
    is-binary-lower-bound-is-binary-lower-bound-Π-Large-Posetᵉ zᵉ
```