# Bottom elements in preorders

```agda
module order-theory.bottom-elements-preordersᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.propositionsᵉ
open import foundation.universe-levelsᵉ

open import order-theory.preordersᵉ
```

</details>

## Idea

Aᵉ **bottomᵉ element**ᵉ in aᵉ preorderᵉ `P`ᵉ isᵉ anᵉ elementᵉ `b`ᵉ suchᵉ thatᵉ `bᵉ ≤ᵉ x`ᵉ holdsᵉ
forᵉ everyᵉ elementᵉ `xᵉ : P`.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Xᵉ : Preorderᵉ l1ᵉ l2ᵉ)
  where

  is-bottom-element-Preorder-Propᵉ : type-Preorderᵉ Xᵉ → Propᵉ (l1ᵉ ⊔ l2ᵉ)
  is-bottom-element-Preorder-Propᵉ xᵉ =
    Π-Propᵉ (type-Preorderᵉ Xᵉ) (leq-Preorder-Propᵉ Xᵉ xᵉ)

  is-bottom-element-Preorderᵉ : type-Preorderᵉ Xᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-bottom-element-Preorderᵉ xᵉ = type-Propᵉ (is-bottom-element-Preorder-Propᵉ xᵉ)

  is-prop-is-bottom-element-Preorderᵉ :
    (xᵉ : type-Preorderᵉ Xᵉ) → is-propᵉ (is-bottom-element-Preorderᵉ xᵉ)
  is-prop-is-bottom-element-Preorderᵉ xᵉ =
    is-prop-type-Propᵉ (is-bottom-element-Preorder-Propᵉ xᵉ)

  has-bottom-element-Preorderᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  has-bottom-element-Preorderᵉ = Σᵉ (type-Preorderᵉ Xᵉ) is-bottom-element-Preorderᵉ
```