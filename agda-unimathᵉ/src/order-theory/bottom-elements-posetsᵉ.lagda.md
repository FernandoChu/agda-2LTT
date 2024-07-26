# Bottom elements in posets

```agda
module order-theory.bottom-elements-posetsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.propositionsᵉ
open import foundation.subtypesᵉ
open import foundation.universe-levelsᵉ

open import order-theory.bottom-elements-preordersᵉ
open import order-theory.posetsᵉ
```

</details>

## Idea

Aᵉ **bottomᵉ element**ᵉ in aᵉ posetᵉ `P`ᵉ isᵉ anᵉ elementᵉ `b`ᵉ suchᵉ thatᵉ `bᵉ ≤ᵉ x`ᵉ holdsᵉ
forᵉ everyᵉ elementᵉ `xᵉ : P`.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Xᵉ : Posetᵉ l1ᵉ l2ᵉ)
  where

  is-bottom-element-Poset-Propᵉ : type-Posetᵉ Xᵉ → Propᵉ (l1ᵉ ⊔ l2ᵉ)
  is-bottom-element-Poset-Propᵉ =
    is-bottom-element-Preorder-Propᵉ (preorder-Posetᵉ Xᵉ)

  is-bottom-element-Posetᵉ : type-Posetᵉ Xᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-bottom-element-Posetᵉ = is-bottom-element-Preorderᵉ (preorder-Posetᵉ Xᵉ)

  is-prop-is-bottom-element-Posetᵉ :
    (xᵉ : type-Posetᵉ Xᵉ) → is-propᵉ (is-bottom-element-Posetᵉ xᵉ)
  is-prop-is-bottom-element-Posetᵉ =
    is-prop-is-bottom-element-Preorderᵉ (preorder-Posetᵉ Xᵉ)

  has-bottom-element-Posetᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  has-bottom-element-Posetᵉ = has-bottom-element-Preorderᵉ (preorder-Posetᵉ Xᵉ)

  all-elements-equal-has-bottom-element-Posetᵉ :
    all-elements-equalᵉ has-bottom-element-Posetᵉ
  all-elements-equal-has-bottom-element-Posetᵉ (pairᵉ xᵉ Hᵉ) (pairᵉ yᵉ Kᵉ) =
    eq-type-subtypeᵉ
      ( is-bottom-element-Poset-Propᵉ)
      ( antisymmetric-leq-Posetᵉ Xᵉ xᵉ yᵉ (Hᵉ yᵉ) (Kᵉ xᵉ))

  is-prop-has-bottom-element-Posetᵉ : is-propᵉ has-bottom-element-Posetᵉ
  is-prop-has-bottom-element-Posetᵉ =
    is-prop-all-elements-equalᵉ all-elements-equal-has-bottom-element-Posetᵉ

  has-bottom-element-Poset-Propᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ has-bottom-element-Poset-Propᵉ = has-bottom-element-Posetᵉ
  pr2ᵉ has-bottom-element-Poset-Propᵉ = is-prop-has-bottom-element-Posetᵉ
```