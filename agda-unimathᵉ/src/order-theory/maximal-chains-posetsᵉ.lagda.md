# Maximal chains in posets

```agda
module order-theory.maximal-chains-posetsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.propositionsᵉ
open import foundation.universe-levelsᵉ

open import order-theory.chains-posetsᵉ
open import order-theory.maximal-chains-preordersᵉ
open import order-theory.posetsᵉ
```

</details>

## Idea

Aᵉ **maximalᵉ chain**ᵉ in aᵉ posetᵉ `P`ᵉ isᵉ aᵉ chainᵉ `C`ᵉ in `P`ᵉ suchᵉ thatᵉ forᵉ anyᵉ chainᵉ
`D`ᵉ weᵉ haveᵉ `Cᵉ ⊆ᵉ Dᵉ ⇒ᵉ Cᵉ ＝ᵉ D`.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Xᵉ : Posetᵉ l1ᵉ l2ᵉ)
  where

  is-maximal-chain-Poset-Propᵉ :
    {l3ᵉ : Level} → chain-Posetᵉ l3ᵉ Xᵉ → Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ lsuc l3ᵉ)
  is-maximal-chain-Poset-Propᵉ =
    is-maximal-chain-Preorder-Propᵉ (preorder-Posetᵉ Xᵉ)

  is-maximal-chain-Posetᵉ :
    {l3ᵉ : Level} → chain-Posetᵉ l3ᵉ Xᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ lsuc l3ᵉ)
  is-maximal-chain-Posetᵉ = is-maximal-chain-Preorderᵉ (preorder-Posetᵉ Xᵉ)

  is-prop-is-maximal-chain-Posetᵉ :
    {l3ᵉ : Level} (Cᵉ : chain-Posetᵉ l3ᵉ Xᵉ) → is-propᵉ (is-maximal-chain-Posetᵉ Cᵉ)
  is-prop-is-maximal-chain-Posetᵉ =
    is-prop-is-maximal-chain-Preorderᵉ (preorder-Posetᵉ Xᵉ)

maximal-chain-Posetᵉ :
  {l1ᵉ l2ᵉ : Level} (l3ᵉ : Level) (Xᵉ : Posetᵉ l1ᵉ l2ᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ lsuc l3ᵉ)
maximal-chain-Posetᵉ l3ᵉ Xᵉ = maximal-chain-Preorderᵉ l3ᵉ (preorder-Posetᵉ Xᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Xᵉ : Posetᵉ l1ᵉ l2ᵉ) (Cᵉ : maximal-chain-Posetᵉ l3ᵉ Xᵉ)
  where

  chain-maximal-chain-Posetᵉ : chain-Posetᵉ l3ᵉ Xᵉ
  chain-maximal-chain-Posetᵉ = chain-maximal-chain-Preorderᵉ (preorder-Posetᵉ Xᵉ) Cᵉ

  is-maximal-chain-maximal-chain-Posetᵉ :
    is-maximal-chain-Posetᵉ Xᵉ chain-maximal-chain-Posetᵉ
  is-maximal-chain-maximal-chain-Posetᵉ =
    is-maximal-chain-maximal-chain-Preorderᵉ (preorder-Posetᵉ Xᵉ) Cᵉ

  type-maximal-chain-Posetᵉ : UUᵉ (l1ᵉ ⊔ l3ᵉ)
  type-maximal-chain-Posetᵉ =
    type-maximal-chain-Preorderᵉ (preorder-Posetᵉ Xᵉ) Cᵉ
```