# The decidable total order of integers

```agda
module elementary-number-theory.decidable-total-order-integersᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-integersᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.universe-levelsᵉ

open import order-theory.decidable-total-ordersᵉ
open import order-theory.total-ordersᵉ
```

</details>

## Idea

Theᵉ typeᵉ ofᵉ [integers](elementary-number-theory.integers.mdᵉ)
[equipped](foundation.structure.mdᵉ) with itsᵉ
[standardᵉ orderingᵉ relation](elementary-number-theory.inequality-integers.mdᵉ)
formsᵉ aᵉ [decidableᵉ totalᵉ order](order-theory.decidable-total-orders.md).ᵉ

## Definition

```agda
is-total-leq-ℤᵉ : is-total-Posetᵉ ℤ-Posetᵉ
is-total-leq-ℤᵉ xᵉ yᵉ = unit-trunc-Propᵉ (linear-leq-ℤᵉ xᵉ yᵉ)

ℤ-Total-Orderᵉ : Total-Orderᵉ lzero lzero
pr1ᵉ ℤ-Total-Orderᵉ = ℤ-Posetᵉ
pr2ᵉ ℤ-Total-Orderᵉ = is-total-leq-ℤᵉ

ℤ-Decidable-Total-Orderᵉ : Decidable-Total-Orderᵉ lzero lzero
pr1ᵉ ℤ-Decidable-Total-Orderᵉ = ℤ-Posetᵉ
pr1ᵉ (pr2ᵉ ℤ-Decidable-Total-Orderᵉ) = is-total-leq-ℤᵉ
pr2ᵉ (pr2ᵉ ℤ-Decidable-Total-Orderᵉ) = is-decidable-leq-ℤᵉ
```