# The Collatz conjecture

```agda
module elementary-number-theory.collatz-conjectureᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.modular-arithmetic-standard-finite-typesᵉ
open import elementary-number-theory.multiplication-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ

open import foundation.coproduct-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Statement

```agda
collatzᵉ : ℕᵉ → ℕᵉ
collatzᵉ nᵉ with is-decidable-div-ℕᵉ 2 nᵉ
... | inlᵉ (pairᵉ yᵉ pᵉ) = yᵉ
... | inrᵉ fᵉ = succ-ℕᵉ (3ᵉ *ℕᵉ nᵉ)

iterate-collatzᵉ : ℕᵉ → ℕᵉ → ℕᵉ
iterate-collatzᵉ zero-ℕᵉ nᵉ = nᵉ
iterate-collatzᵉ (succ-ℕᵉ kᵉ) nᵉ = collatzᵉ (iterate-collatzᵉ kᵉ nᵉ)

Collatz-conjectureᵉ : UUᵉ lzero
Collatz-conjectureᵉ =
  (nᵉ : ℕᵉ) → is-nonzero-ℕᵉ nᵉ → Σᵉ ℕᵉ (λ kᵉ → is-one-ℕᵉ (iterate-collatzᵉ kᵉ nᵉ))
```