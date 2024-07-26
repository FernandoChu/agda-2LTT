# Upper bounds in large posets

```agda
module order-theory.upper-bounds-large-posetsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.propositionsᵉ
open import foundation.universe-levelsᵉ

open import order-theory.dependent-products-large-posetsᵉ
open import order-theory.large-posetsᵉ
```

</details>

## Idea

Aᵉ **binaryᵉ upperᵉ bound**ᵉ ofᵉ twoᵉ elementsᵉ `a`ᵉ andᵉ `b`ᵉ ofᵉ aᵉ largeᵉ posetᵉ `P`ᵉ isᵉ anᵉ
elementᵉ `x`ᵉ ofᵉ `P`ᵉ suchᵉ thatᵉ `aᵉ ≤ᵉ x`ᵉ andᵉ `bᵉ ≤ᵉ x`ᵉ bothᵉ hold.ᵉ Similarly,ᵉ anᵉ
**upperᵉ bound**ᵉ ofᵉ aᵉ familyᵉ `aᵉ : Iᵉ → P`ᵉ ofᵉ elementsᵉ ofᵉ `P`ᵉ isᵉ anᵉ elementᵉ `x`ᵉ ofᵉ
`P`ᵉ suchᵉ thatᵉ theᵉ inequalityᵉ `(aᵉ iᵉ) ≤ᵉ x`ᵉ holdsᵉ forᵉ everyᵉ `iᵉ : I`.ᵉ

## Definitions

### The predicate of being an upper bound of a family of elements

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  (Pᵉ : Large-Posetᵉ αᵉ βᵉ)
  {l1ᵉ l2ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ} (xᵉ : Iᵉ → type-Large-Posetᵉ Pᵉ l2ᵉ)
  where

  is-upper-bound-prop-family-of-elements-Large-Posetᵉ :
    {l3ᵉ : Level} (yᵉ : type-Large-Posetᵉ Pᵉ l3ᵉ) → Propᵉ (βᵉ l2ᵉ l3ᵉ ⊔ l1ᵉ)
  is-upper-bound-prop-family-of-elements-Large-Posetᵉ yᵉ =
    Π-Propᵉ Iᵉ (λ iᵉ → leq-prop-Large-Posetᵉ Pᵉ (xᵉ iᵉ) yᵉ)

  is-upper-bound-family-of-elements-Large-Posetᵉ :
    {l3ᵉ : Level} (yᵉ : type-Large-Posetᵉ Pᵉ l3ᵉ) → UUᵉ (βᵉ l2ᵉ l3ᵉ ⊔ l1ᵉ)
  is-upper-bound-family-of-elements-Large-Posetᵉ yᵉ =
    type-Propᵉ (is-upper-bound-prop-family-of-elements-Large-Posetᵉ yᵉ)

  is-prop-is-upper-bound-family-of-elements-Large-Posetᵉ :
    {l3ᵉ : Level} (yᵉ : type-Large-Posetᵉ Pᵉ l3ᵉ) →
    is-propᵉ (is-upper-bound-family-of-elements-Large-Posetᵉ yᵉ)
  is-prop-is-upper-bound-family-of-elements-Large-Posetᵉ yᵉ =
    is-prop-type-Propᵉ (is-upper-bound-prop-family-of-elements-Large-Posetᵉ yᵉ)
```

## Properties

### An element `x : Π-Large-Poset P` of a dependent product of large posets `P i` indexed by `i : I` is an upper bound of a family `a : J → Π-Large-Poset P` if and only if `x i` is an upper bound of the family `(j ↦ a j i) : J → P i` of elements of `P i`

```agda
module _
  {αᵉ : Level → Level} {βᵉ : Level → Level → Level}
  {l1ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ} (Pᵉ : Iᵉ → Large-Posetᵉ αᵉ βᵉ)
  {l2ᵉ l3ᵉ : Level} {Jᵉ : UUᵉ l2ᵉ} (aᵉ : Jᵉ → type-Π-Large-Posetᵉ Pᵉ l3ᵉ)
  {l4ᵉ : Level} (xᵉ : type-Π-Large-Posetᵉ Pᵉ l4ᵉ)
  where

  is-upper-bound-family-of-elements-Π-Large-Posetᵉ :
    ( (iᵉ : Iᵉ) →
      is-upper-bound-family-of-elements-Large-Posetᵉ (Pᵉ iᵉ) (λ jᵉ → aᵉ jᵉ iᵉ) (xᵉ iᵉ)) →
    is-upper-bound-family-of-elements-Large-Posetᵉ (Π-Large-Posetᵉ Pᵉ) aᵉ xᵉ
  is-upper-bound-family-of-elements-Π-Large-Posetᵉ Hᵉ jᵉ iᵉ = Hᵉ iᵉ jᵉ

  map-inv-is-upper-bound-family-of-elements-Π-Large-Posetᵉ :
    is-upper-bound-family-of-elements-Large-Posetᵉ (Π-Large-Posetᵉ Pᵉ) aᵉ xᵉ →
    (iᵉ : Iᵉ) →
    is-upper-bound-family-of-elements-Large-Posetᵉ (Pᵉ iᵉ) (λ jᵉ → aᵉ jᵉ iᵉ) (xᵉ iᵉ)
  map-inv-is-upper-bound-family-of-elements-Π-Large-Posetᵉ Hᵉ iᵉ jᵉ = Hᵉ jᵉ iᵉ

  logical-equivalence-is-upper-bound-family-of-elements-Π-Large-Posetᵉ :
    ( (iᵉ : Iᵉ) →
      is-upper-bound-family-of-elements-Large-Posetᵉ (Pᵉ iᵉ) (λ jᵉ → aᵉ jᵉ iᵉ) (xᵉ iᵉ)) ↔ᵉ
    is-upper-bound-family-of-elements-Large-Posetᵉ (Π-Large-Posetᵉ Pᵉ) aᵉ xᵉ
  pr1ᵉ logical-equivalence-is-upper-bound-family-of-elements-Π-Large-Posetᵉ =
    is-upper-bound-family-of-elements-Π-Large-Posetᵉ
  pr2ᵉ logical-equivalence-is-upper-bound-family-of-elements-Π-Large-Posetᵉ =
    map-inv-is-upper-bound-family-of-elements-Π-Large-Posetᵉ
```