# An involution on the standard finite types

```agda
module univalent-combinatorics.involution-standard-finite-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.modular-arithmetic-standard-finite-typesᵉ
open import elementary-number-theory.natural-numbersᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.identity-typesᵉ
open import foundation.involutionsᵉ

open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Everyᵉ standardᵉ finiteᵉ typeᵉ `Finᵉ k`ᵉ hasᵉ anᵉ involutionᵉ operationᵉ givenᵉ byᵉ
`xᵉ ↦ᵉ -xᵉ -ᵉ 1`,ᵉ using theᵉ groupᵉ operationsᵉ onᵉ `Finᵉ k`.ᵉ

## Definition

```agda
opposite-Finᵉ : (kᵉ : ℕᵉ) → Finᵉ kᵉ → Finᵉ kᵉ
opposite-Finᵉ kᵉ xᵉ = pred-Finᵉ kᵉ (neg-Finᵉ kᵉ xᵉ)
```

## Properties

### The opposite function on `Fin k` is an involution

```agda
is-involution-opposite-Finᵉ : (kᵉ : ℕᵉ) → is-involutionᵉ (opposite-Finᵉ kᵉ)
is-involution-opposite-Finᵉ kᵉ xᵉ =
  ( apᵉ (pred-Finᵉ kᵉ) (neg-pred-Finᵉ kᵉ (neg-Finᵉ kᵉ xᵉ))) ∙ᵉ
  ( ( is-retraction-pred-Finᵉ kᵉ (neg-Finᵉ kᵉ (neg-Finᵉ kᵉ xᵉ))) ∙ᵉ
    ( neg-neg-Finᵉ kᵉ xᵉ))
```