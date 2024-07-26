# Chains in preorders

```agda
module order-theory.chains-preordersᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.propositionsᵉ
open import foundation.subtypesᵉ
open import foundation.universe-levelsᵉ

open import order-theory.preordersᵉ
open import order-theory.subpreordersᵉ
open import order-theory.total-preordersᵉ
```

</details>

## Idea

Aᵉ **chain**ᵉ in aᵉ preorderᵉ `P`ᵉ isᵉ aᵉ subtypeᵉ `S`ᵉ ofᵉ `P`ᵉ suchᵉ thatᵉ theᵉ orderingᵉ ofᵉ
`P`ᵉ restrictedᵉ to `S`ᵉ isᵉ linear.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Xᵉ : Preorderᵉ l1ᵉ l2ᵉ)
  where

  is-chain-Subpreorder-Propᵉ :
    {l3ᵉ : Level} (Sᵉ : type-Preorderᵉ Xᵉ → Propᵉ l3ᵉ) → Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  is-chain-Subpreorder-Propᵉ Sᵉ =
    is-total-Preorder-Propᵉ (preorder-Subpreorderᵉ Xᵉ Sᵉ)

  is-chain-Subpreorderᵉ :
    {l3ᵉ : Level} (Sᵉ : type-Preorderᵉ Xᵉ → Propᵉ l3ᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  is-chain-Subpreorderᵉ Sᵉ = type-Propᵉ (is-chain-Subpreorder-Propᵉ Sᵉ)

  is-prop-is-chain-Subpreorderᵉ :
    {l3ᵉ : Level} (Sᵉ : type-Preorderᵉ Xᵉ → Propᵉ l3ᵉ) →
    is-propᵉ (is-chain-Subpreorderᵉ Sᵉ)
  is-prop-is-chain-Subpreorderᵉ Sᵉ =
    is-prop-type-Propᵉ (is-chain-Subpreorder-Propᵉ Sᵉ)

chain-Preorderᵉ :
  {l1ᵉ l2ᵉ : Level} (lᵉ : Level) (Xᵉ : Preorderᵉ l1ᵉ l2ᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ lsuc lᵉ)
chain-Preorderᵉ lᵉ Xᵉ =
  Σᵉ (type-Preorderᵉ Xᵉ → Propᵉ lᵉ) (is-chain-Subpreorderᵉ Xᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Xᵉ : Preorderᵉ l1ᵉ l2ᵉ) (Cᵉ : chain-Preorderᵉ l3ᵉ Xᵉ)
  where

  sub-preorder-chain-Preorderᵉ : type-Preorderᵉ Xᵉ → Propᵉ l3ᵉ
  sub-preorder-chain-Preorderᵉ = pr1ᵉ Cᵉ

  type-chain-Preorderᵉ : UUᵉ (l1ᵉ ⊔ l3ᵉ)
  type-chain-Preorderᵉ = type-subtypeᵉ sub-preorder-chain-Preorderᵉ

module _
  {l1ᵉ l2ᵉ : Level} (Xᵉ : Preorderᵉ l1ᵉ l2ᵉ)
  where

  inclusion-chain-Preorder-Propᵉ :
    {l3ᵉ l4ᵉ : Level} → chain-Preorderᵉ l3ᵉ Xᵉ → chain-Preorderᵉ l4ᵉ Xᵉ →
    Propᵉ (l1ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  inclusion-chain-Preorder-Propᵉ Cᵉ Dᵉ =
    inclusion-Subpreorder-Propᵉ Xᵉ
      ( sub-preorder-chain-Preorderᵉ Xᵉ Cᵉ)
      ( sub-preorder-chain-Preorderᵉ Xᵉ Dᵉ)

  inclusion-chain-Preorderᵉ :
    {l3ᵉ l4ᵉ : Level} → chain-Preorderᵉ l3ᵉ Xᵉ → chain-Preorderᵉ l4ᵉ Xᵉ →
    UUᵉ (l1ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  inclusion-chain-Preorderᵉ Cᵉ Dᵉ = type-Propᵉ (inclusion-chain-Preorder-Propᵉ Cᵉ Dᵉ)

  is-prop-inclusion-chain-Preorderᵉ :
    {l3ᵉ l4ᵉ : Level} (Cᵉ : chain-Preorderᵉ l3ᵉ Xᵉ) (Dᵉ : chain-Preorderᵉ l4ᵉ Xᵉ) →
    is-propᵉ (inclusion-chain-Preorderᵉ Cᵉ Dᵉ)
  is-prop-inclusion-chain-Preorderᵉ Cᵉ Dᵉ =
    is-prop-type-Propᵉ (inclusion-chain-Preorder-Propᵉ Cᵉ Dᵉ)
```