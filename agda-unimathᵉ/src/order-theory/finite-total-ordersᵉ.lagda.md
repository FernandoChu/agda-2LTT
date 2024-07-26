# Finite total orders

```agda
module order-theory.finite-total-ordersᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.decidable-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.function-typesᵉ
open import foundation.propositionsᵉ
open import foundation.universe-levelsᵉ

open import order-theory.finite-posetsᵉ
open import order-theory.posetsᵉ
open import order-theory.total-ordersᵉ

open import univalent-combinatorics.finite-typesᵉ
```

</details>

## Definitions

Aᵉ **finiteᵉ totalᵉ order**ᵉ isᵉ aᵉ [totalᵉ order](order-theory.total-orders.mdᵉ) ofᵉ
whichᵉ theᵉ underlyingᵉ typeᵉ isᵉ [finite](univalent-combinatorics.finite-types.md),ᵉ
andᵉ ofᵉ whichᵉ theᵉ orderingᵉ relationᵉ isᵉ
[decidable](foundation.decidable-relations.md).ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Pᵉ : Total-Orderᵉ l1ᵉ l2ᵉ)
  where

  is-finite-Total-Order-Propᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  is-finite-Total-Order-Propᵉ = is-finite-Poset-Propᵉ (poset-Total-Orderᵉ Pᵉ)

  is-finite-Total-Orderᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-finite-Total-Orderᵉ = is-finite-Posetᵉ (poset-Total-Orderᵉ Pᵉ)

  is-prop-is-finite-Total-Orderᵉ : is-propᵉ is-finite-Total-Orderᵉ
  is-prop-is-finite-Total-Orderᵉ =
    is-prop-is-finite-Posetᵉ (poset-Total-Orderᵉ Pᵉ)

  is-finite-type-is-finite-Total-Orderᵉ :
    is-finite-Total-Orderᵉ → is-finiteᵉ (type-Total-Orderᵉ Pᵉ)
  is-finite-type-is-finite-Total-Orderᵉ =
    is-finite-type-is-finite-Posetᵉ (poset-Total-Orderᵉ Pᵉ)

  is-decidable-leq-is-finite-Total-Orderᵉ :
    is-finite-Total-Orderᵉ →
    (xᵉ yᵉ : type-Total-Orderᵉ Pᵉ) → is-decidableᵉ (leq-Total-Orderᵉ Pᵉ xᵉ yᵉ)
  is-decidable-leq-is-finite-Total-Orderᵉ =
    is-decidable-leq-is-finite-Posetᵉ (poset-Total-Orderᵉ Pᵉ)

is-finite-total-order-Poset-Propᵉ :
  {l1ᵉ l2ᵉ : Level} (Pᵉ : Posetᵉ l1ᵉ l2ᵉ) → Propᵉ (l1ᵉ ⊔ l2ᵉ)
is-finite-total-order-Poset-Propᵉ Pᵉ =
  product-Propᵉ
    ( is-total-Poset-Propᵉ Pᵉ)
    ( is-finite-Poset-Propᵉ Pᵉ)

Total-Order-𝔽ᵉ : (l1ᵉ l2ᵉ : Level) → UUᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ)
Total-Order-𝔽ᵉ l1ᵉ l2ᵉ =
  Σᵉ ( Poset-𝔽ᵉ l1ᵉ l2ᵉ)
    ( λ Pᵉ → is-total-Posetᵉ (poset-Poset-𝔽ᵉ Pᵉ))

poset-𝔽-Total-Order-𝔽ᵉ : {l1ᵉ l2ᵉ : Level} → Total-Order-𝔽ᵉ l1ᵉ l2ᵉ → Poset-𝔽ᵉ l1ᵉ l2ᵉ
poset-𝔽-Total-Order-𝔽ᵉ = pr1ᵉ

poset-Total-Order-𝔽ᵉ : {l1ᵉ l2ᵉ : Level} → Total-Order-𝔽ᵉ l1ᵉ l2ᵉ → Posetᵉ l1ᵉ l2ᵉ
poset-Total-Order-𝔽ᵉ = poset-Poset-𝔽ᵉ ∘ᵉ poset-𝔽-Total-Order-𝔽ᵉ

is-total-Total-Order-𝔽ᵉ :
  {l1ᵉ l2ᵉ : Level} (Pᵉ : Total-Order-𝔽ᵉ l1ᵉ l2ᵉ) →
  is-total-Posetᵉ (poset-Total-Order-𝔽ᵉ Pᵉ)
is-total-Total-Order-𝔽ᵉ = pr2ᵉ

total-order-Total-Order-𝔽ᵉ :
  {l1ᵉ l2ᵉ : Level} → Total-Order-𝔽ᵉ l1ᵉ l2ᵉ → Total-Orderᵉ l1ᵉ l2ᵉ
pr1ᵉ (total-order-Total-Order-𝔽ᵉ Pᵉ) = poset-Total-Order-𝔽ᵉ Pᵉ
pr2ᵉ (total-order-Total-Order-𝔽ᵉ Pᵉ) = is-total-Total-Order-𝔽ᵉ Pᵉ

type-Total-Order-𝔽ᵉ :
  {l1ᵉ l2ᵉ : Level} → Total-Order-𝔽ᵉ l1ᵉ l2ᵉ → UUᵉ l1ᵉ
type-Total-Order-𝔽ᵉ = type-Posetᵉ ∘ᵉ poset-Total-Order-𝔽ᵉ
```