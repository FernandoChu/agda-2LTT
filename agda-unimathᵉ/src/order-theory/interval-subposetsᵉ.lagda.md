# Interval subposets

```agda
module order-theory.interval-subposetsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.propositionsᵉ
open import foundation.universe-levelsᵉ

open import order-theory.posetsᵉ
open import order-theory.subposetsᵉ
```

</details>

## Idea

Givenᵉ twoᵉ elementsᵉ `x`ᵉ andᵉ `y`ᵉ in aᵉ posetᵉ `X`,ᵉ theᵉ **intervalᵉ subposet**ᵉ
`[x,ᵉ y]`ᵉ isᵉ theᵉ subposetᵉ ofᵉ `X`ᵉ consistingᵉ ofᵉ allᵉ elementsᵉ `z`ᵉ in `X`ᵉ suchᵉ thatᵉ
`xᵉ ≤ᵉ z`ᵉ andᵉ `zᵉ ≤ᵉ y`.ᵉ Noteᵉ thatᵉ intervalᵉ subposetsᵉ needᵉ notᵉ beᵉ linearlyᵉ ordered.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Xᵉ : Posetᵉ l1ᵉ l2ᵉ) (xᵉ yᵉ : type-Posetᵉ Xᵉ)
  where

  is-in-interval-Posetᵉ : (zᵉ : type-Posetᵉ Xᵉ) → Propᵉ l2ᵉ
  is-in-interval-Posetᵉ zᵉ =
    product-Propᵉ (leq-Poset-Propᵉ Xᵉ xᵉ zᵉ) (leq-Poset-Propᵉ Xᵉ zᵉ yᵉ)

  poset-interval-Subposetᵉ : Posetᵉ (l1ᵉ ⊔ l2ᵉ) l2ᵉ
  poset-interval-Subposetᵉ = poset-Subposetᵉ Xᵉ is-in-interval-Posetᵉ
```