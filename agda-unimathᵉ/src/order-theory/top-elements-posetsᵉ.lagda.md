# Top elements in posets

```agda
module order-theory.top-elements-posetsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.propositionsᵉ
open import foundation.subtypesᵉ
open import foundation.universe-levelsᵉ

open import order-theory.posetsᵉ
open import order-theory.top-elements-preordersᵉ
```

</details>

## Idea

Aᵉ **largestᵉ element**ᵉ in aᵉ posetᵉ isᵉ anᵉ elementᵉ `t`ᵉ suchᵉ thatᵉ `xᵉ ≤ᵉ t`ᵉ holdsᵉ forᵉ
everyᵉ `xᵉ : P`.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Xᵉ : Posetᵉ l1ᵉ l2ᵉ)
  where

  is-top-element-Poset-Propᵉ : type-Posetᵉ Xᵉ → Propᵉ (l1ᵉ ⊔ l2ᵉ)
  is-top-element-Poset-Propᵉ =
    is-top-element-Preorder-Propᵉ (preorder-Posetᵉ Xᵉ)

  is-top-element-Posetᵉ : type-Posetᵉ Xᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-top-element-Posetᵉ = is-top-element-Preorderᵉ (preorder-Posetᵉ Xᵉ)

  is-prop-is-top-element-Posetᵉ :
    (xᵉ : type-Posetᵉ Xᵉ) → is-propᵉ (is-top-element-Posetᵉ xᵉ)
  is-prop-is-top-element-Posetᵉ =
    is-prop-is-top-element-Preorderᵉ (preorder-Posetᵉ Xᵉ)

  has-top-element-Posetᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  has-top-element-Posetᵉ = has-top-element-Preorderᵉ (preorder-Posetᵉ Xᵉ)

  all-elements-equal-has-top-element-Posetᵉ :
    all-elements-equalᵉ has-top-element-Posetᵉ
  all-elements-equal-has-top-element-Posetᵉ (pairᵉ xᵉ Hᵉ) (pairᵉ yᵉ Kᵉ) =
    eq-type-subtypeᵉ
      ( is-top-element-Poset-Propᵉ)
      ( antisymmetric-leq-Posetᵉ Xᵉ xᵉ yᵉ (Kᵉ xᵉ) (Hᵉ yᵉ))

  is-prop-has-top-element-Posetᵉ : is-propᵉ has-top-element-Posetᵉ
  is-prop-has-top-element-Posetᵉ =
    is-prop-all-elements-equalᵉ all-elements-equal-has-top-element-Posetᵉ

  has-top-element-Poset-Propᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ has-top-element-Poset-Propᵉ = has-top-element-Posetᵉ
  pr2ᵉ has-top-element-Poset-Propᵉ = is-prop-has-top-element-Posetᵉ
```