# Lower bounds in posets

```agda
module order-theory.lower-bounds-posetsᵉ where
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

Aᵉ **lowerᵉ bound**ᵉ ofᵉ twoᵉ elementsᵉ `a`ᵉ andᵉ `b`ᵉ in aᵉ posetᵉ `P`ᵉ isᵉ anᵉ elementᵉ `x`ᵉ
suchᵉ thatᵉ bothᵉ `xᵉ ≤ᵉ a`ᵉ andᵉ `xᵉ ≤ᵉ b`ᵉ hold.ᵉ Similarly,ᵉ aᵉ **lowerᵉ bound**ᵉ ofᵉ aᵉ
familyᵉ `aᵉ : Iᵉ → P`ᵉ ofᵉ elementsᵉ in `P`ᵉ isᵉ anᵉ elementᵉ `x`ᵉ suchᵉ thatᵉ `xᵉ ≤ᵉ aᵉ i`ᵉ
holdsᵉ forᵉ everyᵉ `iᵉ : I`.ᵉ

## Definitions

### Binary lower bounds

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Pᵉ : Posetᵉ l1ᵉ l2ᵉ) (aᵉ bᵉ xᵉ : type-Posetᵉ Pᵉ)
  where

  is-binary-lower-bound-Poset-Propᵉ : Propᵉ l2ᵉ
  is-binary-lower-bound-Poset-Propᵉ =
    product-Propᵉ (leq-Poset-Propᵉ Pᵉ xᵉ aᵉ) (leq-Poset-Propᵉ Pᵉ xᵉ bᵉ)

  is-binary-lower-bound-Posetᵉ : UUᵉ l2ᵉ
  is-binary-lower-bound-Posetᵉ =
    type-Propᵉ is-binary-lower-bound-Poset-Propᵉ

  is-prop-is-binary-lower-bound-Posetᵉ : is-propᵉ is-binary-lower-bound-Posetᵉ
  is-prop-is-binary-lower-bound-Posetᵉ =
    is-prop-type-Propᵉ is-binary-lower-bound-Poset-Propᵉ

module _
  {l1ᵉ l2ᵉ : Level} (Pᵉ : Posetᵉ l1ᵉ l2ᵉ) {aᵉ bᵉ xᵉ : type-Posetᵉ Pᵉ}
  (Hᵉ : is-binary-lower-bound-Posetᵉ Pᵉ aᵉ bᵉ xᵉ)
  where

  leq-left-is-binary-lower-bound-Posetᵉ : leq-Posetᵉ Pᵉ xᵉ aᵉ
  leq-left-is-binary-lower-bound-Posetᵉ = pr1ᵉ Hᵉ

  leq-right-is-binary-lower-bound-Posetᵉ : leq-Posetᵉ Pᵉ xᵉ bᵉ
  leq-right-is-binary-lower-bound-Posetᵉ = pr2ᵉ Hᵉ
```

### Lower bounds of families of elements

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Pᵉ : Posetᵉ l1ᵉ l2ᵉ) {Iᵉ : UUᵉ l3ᵉ} (xᵉ : Iᵉ → type-Posetᵉ Pᵉ)
  where

  is-lower-bound-family-of-elements-Poset-Propᵉ : type-Posetᵉ Pᵉ → Propᵉ (l2ᵉ ⊔ l3ᵉ)
  is-lower-bound-family-of-elements-Poset-Propᵉ zᵉ =
    Π-Propᵉ Iᵉ (λ iᵉ → leq-Poset-Propᵉ Pᵉ zᵉ (xᵉ iᵉ))

  is-lower-bound-family-of-elements-Posetᵉ : type-Posetᵉ Pᵉ → UUᵉ (l2ᵉ ⊔ l3ᵉ)
  is-lower-bound-family-of-elements-Posetᵉ zᵉ =
    type-Propᵉ (is-lower-bound-family-of-elements-Poset-Propᵉ zᵉ)

  is-prop-is-lower-bound-family-of-elements-Posetᵉ :
    (zᵉ : type-Posetᵉ Pᵉ) → is-propᵉ (is-lower-bound-family-of-elements-Posetᵉ zᵉ)
  is-prop-is-lower-bound-family-of-elements-Posetᵉ zᵉ =
    is-prop-type-Propᵉ (is-lower-bound-family-of-elements-Poset-Propᵉ zᵉ)
```

## Properties

### Any element less than a lower bound of `a` and `b` is a lower bound of `a` and `b`

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Pᵉ : Posetᵉ l1ᵉ l2ᵉ) {aᵉ bᵉ xᵉ : type-Posetᵉ Pᵉ}
  (Hᵉ : is-binary-lower-bound-Posetᵉ Pᵉ aᵉ bᵉ xᵉ)
  where

  is-binary-lower-bound-leq-Posetᵉ :
    {yᵉ : type-Posetᵉ Pᵉ} →
    leq-Posetᵉ Pᵉ yᵉ xᵉ → is-binary-lower-bound-Posetᵉ Pᵉ aᵉ bᵉ yᵉ
  pr1ᵉ (is-binary-lower-bound-leq-Posetᵉ Kᵉ) =
    transitive-leq-Posetᵉ Pᵉ _ xᵉ aᵉ
      ( leq-left-is-binary-lower-bound-Posetᵉ Pᵉ Hᵉ)
      ( Kᵉ)
  pr2ᵉ (is-binary-lower-bound-leq-Posetᵉ Kᵉ) =
    transitive-leq-Posetᵉ Pᵉ _ xᵉ bᵉ
      ( leq-right-is-binary-lower-bound-Posetᵉ Pᵉ Hᵉ)
      ( Kᵉ)
```

### Any element less than a lower bound of a family of elements `a` is a lower bound of `a`

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Pᵉ : Posetᵉ l1ᵉ l2ᵉ) {Iᵉ : UUᵉ l3ᵉ} {aᵉ : Iᵉ → type-Posetᵉ Pᵉ}
  {xᵉ : type-Posetᵉ Pᵉ} (Hᵉ : is-lower-bound-family-of-elements-Posetᵉ Pᵉ aᵉ xᵉ)
  where

  is-lower-bound-family-of-elements-leq-Posetᵉ :
    {yᵉ : type-Posetᵉ Pᵉ} → leq-Posetᵉ Pᵉ yᵉ xᵉ →
    is-lower-bound-family-of-elements-Posetᵉ Pᵉ aᵉ yᵉ
  is-lower-bound-family-of-elements-leq-Posetᵉ Kᵉ iᵉ =
    transitive-leq-Posetᵉ Pᵉ _ xᵉ (aᵉ iᵉ) (Hᵉ iᵉ) Kᵉ
```