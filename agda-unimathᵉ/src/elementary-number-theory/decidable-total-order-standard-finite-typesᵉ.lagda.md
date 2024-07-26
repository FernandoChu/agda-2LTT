# The decidable total order of a standard finite type

```agda
module elementary-number-theory.decidable-total-order-standard-finite-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-standard-finite-typesᵉ
open import elementary-number-theory.natural-numbersᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.universe-levelsᵉ

open import order-theory.decidable-total-ordersᵉ
open import order-theory.total-ordersᵉ
```

</details>

## Idea

Theᵉ [standardᵉ finiteᵉ type](univalent-combinatorics.standard-finite-types.mdᵉ) ofᵉ
orderᵉ `k`ᵉ [equipped](foundation.structure.mdᵉ) with itsᵉ
[standardᵉ orderingᵉ relation](elementary-number-theory.inequality-standard-finite-types.mdᵉ)
formsᵉ aᵉ [decidableᵉ totalᵉ order](order-theory.decidable-total-orders.md).ᵉ

## Definition

```agda
is-total-leq-Finᵉ : (kᵉ : ℕᵉ) → is-total-Posetᵉ (Fin-Posetᵉ kᵉ)
is-total-leq-Finᵉ kᵉ nᵉ mᵉ = unit-trunc-Propᵉ (linear-leq-Finᵉ kᵉ nᵉ mᵉ)

Fin-Total-Orderᵉ : ℕᵉ → Total-Orderᵉ lzero lzero
pr1ᵉ (Fin-Total-Orderᵉ kᵉ) = Fin-Posetᵉ kᵉ
pr2ᵉ (Fin-Total-Orderᵉ kᵉ) = is-total-leq-Finᵉ kᵉ

Fin-Decidable-Total-Orderᵉ : ℕᵉ → Decidable-Total-Orderᵉ lzero lzero
pr1ᵉ (Fin-Decidable-Total-Orderᵉ kᵉ) = Fin-Posetᵉ kᵉ
pr1ᵉ (pr2ᵉ (Fin-Decidable-Total-Orderᵉ kᵉ)) = is-total-leq-Finᵉ kᵉ
pr2ᵉ (pr2ᵉ (Fin-Decidable-Total-Orderᵉ kᵉ)) = is-decidable-leq-Finᵉ kᵉ
```