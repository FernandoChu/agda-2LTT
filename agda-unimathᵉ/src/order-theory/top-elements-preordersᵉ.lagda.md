# Top elements in preorders

```agda
module order-theory.top-elements-preordersᵉ where
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

Aᵉ **largestᵉ element**ᵉ in aᵉ preorderᵉ `P`ᵉ isᵉ anᵉ elementᵉ `t`ᵉ suchᵉ thatᵉ `xᵉ ≤ᵉ t`ᵉ
holdsᵉ forᵉ everyᵉ `xᵉ : P`.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Xᵉ : Preorderᵉ l1ᵉ l2ᵉ)
  where

  is-top-element-Preorder-Propᵉ : type-Preorderᵉ Xᵉ → Propᵉ (l1ᵉ ⊔ l2ᵉ)
  is-top-element-Preorder-Propᵉ xᵉ =
    Π-Propᵉ (type-Preorderᵉ Xᵉ) (λ yᵉ → leq-Preorder-Propᵉ Xᵉ yᵉ xᵉ)

  is-top-element-Preorderᵉ : type-Preorderᵉ Xᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-top-element-Preorderᵉ xᵉ = type-Propᵉ (is-top-element-Preorder-Propᵉ xᵉ)

  is-prop-is-top-element-Preorderᵉ :
    (xᵉ : type-Preorderᵉ Xᵉ) → is-propᵉ (is-top-element-Preorderᵉ xᵉ)
  is-prop-is-top-element-Preorderᵉ xᵉ =
    is-prop-type-Propᵉ (is-top-element-Preorder-Propᵉ xᵉ)

  has-top-element-Preorderᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  has-top-element-Preorderᵉ = Σᵉ (type-Preorderᵉ Xᵉ) is-top-element-Preorderᵉ
```