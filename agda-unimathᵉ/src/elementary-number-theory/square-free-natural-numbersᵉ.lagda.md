# Square-free natural numbers

```agda
module elementary-number-theory.square-free-natural-numbersᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.divisibility-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ
open import elementary-number-theory.squares-natural-numbersᵉ

open import foundation.universe-levelsᵉ
```

</details>

## Idea

Aᵉ naturalᵉ numberᵉ `n`ᵉ isᵉ saidᵉ to beᵉ square-freeᵉ ifᵉ `x²ᵉ | nᵉ ⇒ᵉ xᵉ = 1`ᵉ forᵉ anyᵉ
naturalᵉ numberᵉ `x`.ᵉ

## Definition

```agda
is-square-free-ℕᵉ : ℕᵉ → UUᵉ lzero
is-square-free-ℕᵉ nᵉ = (xᵉ : ℕᵉ) → div-ℕᵉ (square-ℕᵉ xᵉ) nᵉ → is-one-ℕᵉ xᵉ
```