# The Ackermann function

```agda
module elementary-number-theory.ackermann-functionᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ
```

</details>

## Idea

Theᵉ Ackermannᵉ functionᵉ isᵉ aᵉ fastᵉ growingᵉ binaryᵉ operationᵉ onᵉ theᵉ naturalᵉ
numbers.ᵉ

## Definition

```agda
ackermannᵉ : ℕᵉ → ℕᵉ → ℕᵉ
ackermannᵉ zero-ℕᵉ nᵉ = succ-ℕᵉ nᵉ
ackermannᵉ (succ-ℕᵉ mᵉ) zero-ℕᵉ = ackermannᵉ mᵉ 1
ackermannᵉ (succ-ℕᵉ mᵉ) (succ-ℕᵉ nᵉ) = ackermannᵉ mᵉ (ackermannᵉ (succ-ℕᵉ mᵉ) nᵉ)
```