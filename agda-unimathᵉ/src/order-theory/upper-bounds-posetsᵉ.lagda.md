# Upper bounds in posets

```agda
module order-theory.upper-bounds-posetsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.propositionsᵉ
open import foundation.universe-levelsᵉ

open import order-theory.posetsᵉ
```

</details>

## Idea

Anᵉ **upperᵉ bound**ᵉ ofᵉ twoᵉ elementsᵉ `x`ᵉ andᵉ `y`ᵉ in aᵉ posetᵉ `P`ᵉ isᵉ anᵉ elementᵉ `z`ᵉ
suchᵉ thatᵉ bothᵉ `xᵉ ≤ᵉ z`ᵉ andᵉ `yᵉ ≤ᵉ z`ᵉ hold.ᵉ Similaryly,ᵉ anᵉ **upperᵉ bound**ᵉ ofᵉ aᵉ
familyᵉ `xᵉ : Iᵉ → P`ᵉ ofᵉ elementsᵉ in `P`ᵉ isᵉ anᵉ elementᵉ `z`ᵉ suchᵉ thatᵉ `xᵉ iᵉ ≤ᵉ z`ᵉ
holdsᵉ forᵉ everyᵉ `iᵉ : I`.ᵉ

## Definitions

### Binary upper bounds

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Pᵉ : Posetᵉ l1ᵉ l2ᵉ)
  where

  is-binary-upper-bound-Poset-Propᵉ :
    (xᵉ yᵉ zᵉ : type-Posetᵉ Pᵉ) → Propᵉ l2ᵉ
  is-binary-upper-bound-Poset-Propᵉ xᵉ yᵉ zᵉ =
    product-Propᵉ (leq-Poset-Propᵉ Pᵉ xᵉ zᵉ) (leq-Poset-Propᵉ Pᵉ yᵉ zᵉ)

  is-binary-upper-bound-Posetᵉ :
    (xᵉ yᵉ zᵉ : type-Posetᵉ Pᵉ) → UUᵉ l2ᵉ
  is-binary-upper-bound-Posetᵉ xᵉ yᵉ zᵉ =
    type-Propᵉ (is-binary-upper-bound-Poset-Propᵉ xᵉ yᵉ zᵉ)

  is-prop-is-binary-upper-bound-Posetᵉ :
    (xᵉ yᵉ zᵉ : type-Posetᵉ Pᵉ) → is-propᵉ (is-binary-upper-bound-Posetᵉ xᵉ yᵉ zᵉ)
  is-prop-is-binary-upper-bound-Posetᵉ xᵉ yᵉ zᵉ =
    is-prop-type-Propᵉ (is-binary-upper-bound-Poset-Propᵉ xᵉ yᵉ zᵉ)

module _
  {l1ᵉ l2ᵉ : Level} (Pᵉ : Posetᵉ l1ᵉ l2ᵉ) {aᵉ bᵉ xᵉ : type-Posetᵉ Pᵉ}
  (Hᵉ : is-binary-upper-bound-Posetᵉ Pᵉ aᵉ bᵉ xᵉ)
  where

  leq-left-is-binary-upper-bound-Posetᵉ : leq-Posetᵉ Pᵉ aᵉ xᵉ
  leq-left-is-binary-upper-bound-Posetᵉ = pr1ᵉ Hᵉ

  leq-right-is-binary-upper-bound-Posetᵉ : leq-Posetᵉ Pᵉ bᵉ xᵉ
  leq-right-is-binary-upper-bound-Posetᵉ = pr2ᵉ Hᵉ
```

### Upper bounds of families of elements

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Pᵉ : Posetᵉ l1ᵉ l2ᵉ)
  where

  is-upper-bound-family-of-elements-Poset-Propᵉ :
    {lᵉ : Level} {Iᵉ : UUᵉ lᵉ} → (Iᵉ → type-Posetᵉ Pᵉ) → type-Posetᵉ Pᵉ →
    Propᵉ (l2ᵉ ⊔ lᵉ)
  is-upper-bound-family-of-elements-Poset-Propᵉ {lᵉ} {Iᵉ} fᵉ zᵉ =
    Π-Propᵉ Iᵉ (λ iᵉ → leq-Poset-Propᵉ Pᵉ (fᵉ iᵉ) zᵉ)

  is-upper-bound-family-of-elements-Posetᵉ :
    {lᵉ : Level} {Iᵉ : UUᵉ lᵉ} → (Iᵉ → type-Posetᵉ Pᵉ) → type-Posetᵉ Pᵉ →
    UUᵉ (l2ᵉ ⊔ lᵉ)
  is-upper-bound-family-of-elements-Posetᵉ fᵉ zᵉ =
    type-Propᵉ (is-upper-bound-family-of-elements-Poset-Propᵉ fᵉ zᵉ)

  is-prop-is-upper-bound-family-of-elements-Posetᵉ :
    {lᵉ : Level} {Iᵉ : UUᵉ lᵉ} (fᵉ : Iᵉ → type-Posetᵉ Pᵉ) (zᵉ : type-Posetᵉ Pᵉ) →
    is-propᵉ (is-upper-bound-family-of-elements-Posetᵉ fᵉ zᵉ)
  is-prop-is-upper-bound-family-of-elements-Posetᵉ fᵉ zᵉ =
    is-prop-type-Propᵉ (is-upper-bound-family-of-elements-Poset-Propᵉ fᵉ zᵉ)
```

## Properties

### Any element greater than an upper bound of `a` and `b` is an upper bound of `a` and `b`

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Pᵉ : Posetᵉ l1ᵉ l2ᵉ) {aᵉ bᵉ xᵉ : type-Posetᵉ Pᵉ}
  (Hᵉ : is-binary-upper-bound-Posetᵉ Pᵉ aᵉ bᵉ xᵉ)
  where

  is-binary-upper-bound-leq-Posetᵉ :
    {yᵉ : type-Posetᵉ Pᵉ} →
    leq-Posetᵉ Pᵉ xᵉ yᵉ → is-binary-upper-bound-Posetᵉ Pᵉ aᵉ bᵉ yᵉ
  pr1ᵉ (is-binary-upper-bound-leq-Posetᵉ Kᵉ) =
    transitive-leq-Posetᵉ Pᵉ aᵉ xᵉ _
      ( Kᵉ)
      ( leq-left-is-binary-upper-bound-Posetᵉ Pᵉ Hᵉ)
  pr2ᵉ (is-binary-upper-bound-leq-Posetᵉ Kᵉ) =
    transitive-leq-Posetᵉ Pᵉ bᵉ xᵉ _
      ( Kᵉ)
      ( leq-right-is-binary-upper-bound-Posetᵉ Pᵉ Hᵉ)
```

### Any element greater than an upper bound of a family of elements `a` is an upper bound of `a`

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Pᵉ : Posetᵉ l1ᵉ l2ᵉ) {Iᵉ : UUᵉ l3ᵉ} {aᵉ : Iᵉ → type-Posetᵉ Pᵉ}
  {xᵉ : type-Posetᵉ Pᵉ} (Hᵉ : is-upper-bound-family-of-elements-Posetᵉ Pᵉ aᵉ xᵉ)
  where

  is-upper-bound-family-of-elements-leq-Posetᵉ :
    {yᵉ : type-Posetᵉ Pᵉ} → leq-Posetᵉ Pᵉ xᵉ yᵉ →
    is-upper-bound-family-of-elements-Posetᵉ Pᵉ aᵉ yᵉ
  is-upper-bound-family-of-elements-leq-Posetᵉ Kᵉ iᵉ =
    transitive-leq-Posetᵉ Pᵉ (aᵉ iᵉ) xᵉ _ Kᵉ (Hᵉ iᵉ)
```