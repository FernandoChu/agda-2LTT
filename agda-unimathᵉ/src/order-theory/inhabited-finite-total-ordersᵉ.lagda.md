# Inhabited finite total orders

```agda
module order-theory.inhabited-finite-total-ordersᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.inhabited-typesᵉ
open import foundation.propositionsᵉ
open import foundation.universe-levelsᵉ

open import order-theory.finite-posetsᵉ
open import order-theory.finite-total-ordersᵉ
open import order-theory.posetsᵉ
open import order-theory.total-ordersᵉ

open import univalent-combinatorics.finite-typesᵉ
```

</details>

## Definitions

Anᵉ **inhabitedᵉ finiteᵉ totalᵉ order**ᵉ isᵉ aᵉ
[finiteᵉ totalᵉ order](order-theory.finite-total-orders.mdᵉ) ofᵉ whichᵉ theᵉ
underlyingᵉ typeᵉ isᵉ [inhabited](foundation.inhabited-types.md).ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Pᵉ : Total-Order-𝔽ᵉ l1ᵉ l2ᵉ)
  where

  is-inhabited-Total-Order-𝔽-Propᵉ : Propᵉ l1ᵉ
  is-inhabited-Total-Order-𝔽-Propᵉ = is-inhabited-Propᵉ (type-Total-Order-𝔽ᵉ Pᵉ)

  is-inhabited-Total-Order-𝔽ᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-inhabited-Total-Order-𝔽ᵉ = is-finite-Posetᵉ (poset-Total-Order-𝔽ᵉ Pᵉ)

  is-property-is-inhabited-Total-Order-𝔽ᵉ : is-propᵉ is-inhabited-Total-Order-𝔽ᵉ
  is-property-is-inhabited-Total-Order-𝔽ᵉ =
    is-prop-is-finite-Posetᵉ (poset-Total-Order-𝔽ᵉ Pᵉ)

  is-finite-type-is-inhabited-Total-Order-𝔽ᵉ :
    is-inhabited-Total-Order-𝔽ᵉ → is-finiteᵉ (type-Total-Order-𝔽ᵉ Pᵉ)
  is-finite-type-is-inhabited-Total-Order-𝔽ᵉ =
    is-finite-type-is-finite-Posetᵉ (poset-Total-Order-𝔽ᵉ Pᵉ)

is-inhabited-finite-total-order-Poset-Propᵉ :
  {l1ᵉ l2ᵉ : Level} (Pᵉ : Posetᵉ l1ᵉ l2ᵉ) → Propᵉ (l1ᵉ ⊔ l2ᵉ)
is-inhabited-finite-total-order-Poset-Propᵉ Pᵉ =
  product-Propᵉ
    ( is-total-Poset-Propᵉ Pᵉ)
    ( product-Propᵉ
      ( is-finite-Poset-Propᵉ Pᵉ)
      ( is-inhabited-Propᵉ (type-Posetᵉ Pᵉ)))
```