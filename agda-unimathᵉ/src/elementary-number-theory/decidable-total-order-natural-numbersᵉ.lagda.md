# The decidable total order of natural numbers

```agda
module elementary-number-theory.decidable-total-order-natural-numbersᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-natural-numbersᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.universe-levelsᵉ

open import order-theory.decidable-total-ordersᵉ
open import order-theory.total-ordersᵉ
```

</details>

## Idea

Theᵉ typeᵉ ofᵉ [naturalᵉ numbers](elementary-number-theory.natural-numbers.mdᵉ)
[equipped](foundation.structure.mdᵉ) with itsᵉ
[standardᵉ orderingᵉ relation](elementary-number-theory.inequality-natural-numbers.mdᵉ)
formsᵉ aᵉ [decidableᵉ totalᵉ order](order-theory.decidable-total-orders.md).ᵉ

## Definition

```agda
is-total-leq-ℕᵉ : is-total-Posetᵉ ℕ-Posetᵉ
is-total-leq-ℕᵉ nᵉ mᵉ = unit-trunc-Propᵉ (linear-leq-ℕᵉ nᵉ mᵉ)

ℕ-Total-Orderᵉ : Total-Orderᵉ lzero lzero
pr1ᵉ ℕ-Total-Orderᵉ = ℕ-Posetᵉ
pr2ᵉ ℕ-Total-Orderᵉ = is-total-leq-ℕᵉ

ℕ-Decidable-Total-Orderᵉ : Decidable-Total-Orderᵉ lzero lzero
pr1ᵉ ℕ-Decidable-Total-Orderᵉ = ℕ-Posetᵉ
pr1ᵉ (pr2ᵉ ℕ-Decidable-Total-Orderᵉ) = is-total-leq-ℕᵉ
pr2ᵉ (pr2ᵉ ℕ-Decidable-Total-Orderᵉ) = is-decidable-leq-ℕᵉ
```