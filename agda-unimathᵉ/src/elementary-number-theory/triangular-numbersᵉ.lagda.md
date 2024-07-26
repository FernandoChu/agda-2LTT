# The triangular numbers

```agda
module elementary-number-theory.triangular-numbersᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ
```

</details>

## Definition

```agda
triangular-number-ℕᵉ : ℕᵉ → ℕᵉ
triangular-number-ℕᵉ 0 = 0
triangular-number-ℕᵉ (succ-ℕᵉ nᵉ) = (triangular-number-ℕᵉ nᵉ) +ℕᵉ (succ-ℕᵉ nᵉ)
```