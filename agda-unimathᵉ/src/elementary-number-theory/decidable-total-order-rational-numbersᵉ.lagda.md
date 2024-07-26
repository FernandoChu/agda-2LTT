# The decidable total order of rational numbers

```agda
module elementary-number-theory.decidable-total-order-rational-numbersᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-rational-numbersᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.universe-levelsᵉ

open import order-theory.decidable-total-ordersᵉ
open import order-theory.total-ordersᵉ
```

</details>

## Idea

Theᵉ typeᵉ ofᵉ [rationalᵉ numbers](elementary-number-theory.rational-numbers.mdᵉ)
[equipped](foundation.structure.mdᵉ) with itsᵉ
[standardᵉ orderingᵉ relation](elementary-number-theory.inequality-rational-numbers.mdᵉ)
formsᵉ aᵉ [decidableᵉ totalᵉ order](order-theory.decidable-total-orders.md).ᵉ

## Definition

```agda
is-total-leq-ℚᵉ : is-total-Posetᵉ ℚ-Posetᵉ
is-total-leq-ℚᵉ xᵉ yᵉ = unit-trunc-Propᵉ (linear-leq-ℚᵉ xᵉ yᵉ)

ℚ-Total-Orderᵉ : Total-Orderᵉ lzero lzero
pr1ᵉ ℚ-Total-Orderᵉ = ℚ-Posetᵉ
pr2ᵉ ℚ-Total-Orderᵉ = is-total-leq-ℚᵉ

ℚ-Decidable-Total-Orderᵉ : Decidable-Total-Orderᵉ lzero lzero
pr1ᵉ ℚ-Decidable-Total-Orderᵉ = ℚ-Posetᵉ
pr1ᵉ (pr2ᵉ ℚ-Decidable-Total-Orderᵉ) = is-total-leq-ℚᵉ
pr2ᵉ (pr2ᵉ ℚ-Decidable-Total-Orderᵉ) = is-decidable-leq-ℚᵉ
```