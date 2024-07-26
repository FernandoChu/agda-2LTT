# Arithmetic functions

```agda
module elementary-number-theory.arithmetic-functionsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.nonzero-natural-numbersᵉ

open import foundation.universe-levelsᵉ

open import ring-theory.ringsᵉ
```

</details>

## Idea

Anᵉ arithmeticᵉ functionᵉ isᵉ aᵉ functionᵉ fromᵉ theᵉ nonzeroᵉ naturalᵉ numbersᵉ intoᵉ aᵉ
(commutativeᵉ) ring.ᵉ Theᵉ arithmeticᵉ functionsᵉ formᵉ aᵉ ringᵉ underᵉ pointwiseᵉ
additionᵉ andᵉ dirichletᵉ convolution.ᵉ

## Definition

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  type-arithmetic-functions-Ringᵉ : UUᵉ lᵉ
  type-arithmetic-functions-Ringᵉ = nonzero-ℕᵉ → type-Ringᵉ Rᵉ
```