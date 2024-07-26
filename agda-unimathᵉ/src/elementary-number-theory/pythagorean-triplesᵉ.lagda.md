# Pythagorean triples

```agda
module elementary-number-theory.pythagorean-triplesᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ
open import elementary-number-theory.squares-natural-numbersᵉ

open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Aᵉ Pythagoreanᵉ tripleᵉ isᵉ aᵉ tripleᵉ `(a,b,c)`ᵉ ofᵉ naturalᵉ numbersᵉ suchᵉ thatᵉ
`a²ᵉ +ᵉ b²ᵉ = c²`.ᵉ

## Definition

```agda
is-pythagorean-tripleᵉ : ℕᵉ → ℕᵉ → ℕᵉ → UUᵉ lzero
is-pythagorean-tripleᵉ aᵉ bᵉ cᵉ = ((square-ℕᵉ aᵉ) +ℕᵉ (square-ℕᵉ bᵉ) ＝ᵉ square-ℕᵉ cᵉ)
```