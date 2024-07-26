# Chains in posets

```agda
module order-theory.chains-posetsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.propositionsᵉ
open import foundation.universe-levelsᵉ

open import order-theory.chains-preordersᵉ
open import order-theory.posetsᵉ
```

</details>

## Idea

Aᵉ **chain**ᵉ in aᵉ posetᵉ `P`ᵉ isᵉ aᵉ subtypeᵉ `S`ᵉ ofᵉ `P`ᵉ suchᵉ thatᵉ theᵉ orderingᵉ ofᵉ `P`ᵉ
restrictedᵉ to `S`ᵉ isᵉ linear.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Xᵉ : Posetᵉ l1ᵉ l2ᵉ)
  where

  is-chain-Subposet-Propᵉ :
    {l3ᵉ : Level} (Sᵉ : type-Posetᵉ Xᵉ → Propᵉ l3ᵉ) → Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  is-chain-Subposet-Propᵉ = is-chain-Subpreorder-Propᵉ (preorder-Posetᵉ Xᵉ)

  is-chain-Subposetᵉ :
    {l3ᵉ : Level} (Sᵉ : type-Posetᵉ Xᵉ → Propᵉ l3ᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  is-chain-Subposetᵉ = is-chain-Subpreorderᵉ (preorder-Posetᵉ Xᵉ)

  is-prop-is-chain-Subposetᵉ :
    {l3ᵉ : Level} (Sᵉ : type-Posetᵉ Xᵉ → Propᵉ l3ᵉ) →
    is-propᵉ (is-chain-Subposetᵉ Sᵉ)
  is-prop-is-chain-Subposetᵉ = is-prop-is-chain-Subpreorderᵉ (preorder-Posetᵉ Xᵉ)

chain-Posetᵉ :
  {l1ᵉ l2ᵉ : Level} (lᵉ : Level) (Xᵉ : Posetᵉ l1ᵉ l2ᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ lsuc lᵉ)
chain-Posetᵉ lᵉ Xᵉ = chain-Preorderᵉ lᵉ (preorder-Posetᵉ Xᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Xᵉ : Posetᵉ l1ᵉ l2ᵉ) (Cᵉ : chain-Posetᵉ l3ᵉ Xᵉ)
  where

  sub-preorder-chain-Posetᵉ : type-Posetᵉ Xᵉ → Propᵉ l3ᵉ
  sub-preorder-chain-Posetᵉ =
    sub-preorder-chain-Preorderᵉ (preorder-Posetᵉ Xᵉ) Cᵉ

  type-chain-Posetᵉ : UUᵉ (l1ᵉ ⊔ l3ᵉ)
  type-chain-Posetᵉ = type-chain-Preorderᵉ (preorder-Posetᵉ Xᵉ) Cᵉ

module _
  {l1ᵉ l2ᵉ : Level} (Xᵉ : Posetᵉ l1ᵉ l2ᵉ)
  where

  inclusion-chain-Poset-Propᵉ :
    {l3ᵉ l4ᵉ : Level} → chain-Posetᵉ l3ᵉ Xᵉ → chain-Posetᵉ l4ᵉ Xᵉ →
    Propᵉ (l1ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  inclusion-chain-Poset-Propᵉ = inclusion-chain-Preorder-Propᵉ (preorder-Posetᵉ Xᵉ)

  inclusion-chain-Posetᵉ :
    {l3ᵉ l4ᵉ : Level} → chain-Posetᵉ l3ᵉ Xᵉ → chain-Posetᵉ l4ᵉ Xᵉ → UUᵉ (l1ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  inclusion-chain-Posetᵉ = inclusion-chain-Preorderᵉ (preorder-Posetᵉ Xᵉ)

  is-prop-inclusion-chain-Posetᵉ :
    {l3ᵉ l4ᵉ : Level} (Cᵉ : chain-Posetᵉ l3ᵉ Xᵉ) (Dᵉ : chain-Posetᵉ l4ᵉ Xᵉ) →
    is-propᵉ (inclusion-chain-Posetᵉ Cᵉ Dᵉ)
  is-prop-inclusion-chain-Posetᵉ =
    is-prop-inclusion-chain-Preorderᵉ (preorder-Posetᵉ Xᵉ)
```