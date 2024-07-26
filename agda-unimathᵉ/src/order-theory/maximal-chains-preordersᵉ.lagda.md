# Maximal chains in preorders

```agda
module order-theory.maximal-chains-preordersᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.propositionsᵉ
open import foundation.universe-levelsᵉ

open import order-theory.chains-preordersᵉ
open import order-theory.preordersᵉ
```

</details>

## Idea

Aᵉ **maximalᵉ chain**ᵉ in aᵉ preorderᵉ `P`ᵉ isᵉ aᵉ chainᵉ `C`ᵉ in `P`ᵉ suchᵉ thatᵉ forᵉ everyᵉ
chainᵉ `D`ᵉ in `P`ᵉ weᵉ haveᵉ `Cᵉ ⊆ᵉ Dᵉ ⇒ᵉ Dᵉ ⊆ᵉ C`.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Xᵉ : Preorderᵉ l1ᵉ l2ᵉ)
  where

  is-maximal-chain-Preorder-Propᵉ :
    {l3ᵉ : Level} → chain-Preorderᵉ l3ᵉ Xᵉ → Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ lsuc l3ᵉ)
  is-maximal-chain-Preorder-Propᵉ {l3ᵉ} Cᵉ =
    Π-Propᵉ
      ( chain-Preorderᵉ l3ᵉ Xᵉ)
      ( λ Dᵉ →
        function-Propᵉ
          ( inclusion-chain-Preorderᵉ Xᵉ Cᵉ Dᵉ)
          ( inclusion-chain-Preorder-Propᵉ Xᵉ Dᵉ Cᵉ))

  is-maximal-chain-Preorderᵉ :
    {l3ᵉ : Level} → chain-Preorderᵉ l3ᵉ Xᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ lsuc l3ᵉ)
  is-maximal-chain-Preorderᵉ Cᵉ = type-Propᵉ (is-maximal-chain-Preorder-Propᵉ Cᵉ)

  is-prop-is-maximal-chain-Preorderᵉ :
    {l3ᵉ : Level} (Cᵉ : chain-Preorderᵉ l3ᵉ Xᵉ) →
    is-propᵉ (is-maximal-chain-Preorderᵉ Cᵉ)
  is-prop-is-maximal-chain-Preorderᵉ Cᵉ =
    is-prop-type-Propᵉ (is-maximal-chain-Preorder-Propᵉ Cᵉ)

maximal-chain-Preorderᵉ :
  {l1ᵉ l2ᵉ : Level} (l3ᵉ : Level) (Xᵉ : Preorderᵉ l1ᵉ l2ᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ lsuc l3ᵉ)
maximal-chain-Preorderᵉ l3ᵉ Xᵉ =
  Σᵉ (chain-Preorderᵉ l3ᵉ Xᵉ) (is-maximal-chain-Preorderᵉ Xᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Xᵉ : Preorderᵉ l1ᵉ l2ᵉ) (Cᵉ : maximal-chain-Preorderᵉ l3ᵉ Xᵉ)
  where

  chain-maximal-chain-Preorderᵉ : chain-Preorderᵉ l3ᵉ Xᵉ
  chain-maximal-chain-Preorderᵉ = pr1ᵉ Cᵉ

  is-maximal-chain-maximal-chain-Preorderᵉ :
    is-maximal-chain-Preorderᵉ Xᵉ chain-maximal-chain-Preorderᵉ
  is-maximal-chain-maximal-chain-Preorderᵉ = pr2ᵉ Cᵉ

  type-maximal-chain-Preorderᵉ : UUᵉ (l1ᵉ ⊔ l3ᵉ)
  type-maximal-chain-Preorderᵉ =
    type-chain-Preorderᵉ Xᵉ chain-maximal-chain-Preorderᵉ
```