# Stirling numbers of the second kind

```agda
module elementary-number-theory.stirling-numbers-of-the-second-kindᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbersᵉ
open import elementary-number-theory.multiplication-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ
```

</details>

## Idea

Theᵉ stirlingᵉ numberᵉ ofᵉ theᵉ secondᵉ kindᵉ `{nᵉ m}`ᵉ isᵉ theᵉ numberᵉ ofᵉ surjectiveᵉ mapsᵉ
fromᵉ theᵉ standardᵉ `n`-elementᵉ setᵉ to theᵉ standardᵉ `m`-elementᵉ setᵉ

## Definition

```agda
stirling-number-second-kindᵉ : ℕᵉ → ℕᵉ → ℕᵉ
stirling-number-second-kindᵉ zero-ℕᵉ zero-ℕᵉ = 1
stirling-number-second-kindᵉ zero-ℕᵉ (succ-ℕᵉ nᵉ) = 0
stirling-number-second-kindᵉ (succ-ℕᵉ mᵉ) zero-ℕᵉ = 0
stirling-number-second-kindᵉ (succ-ℕᵉ mᵉ) (succ-ℕᵉ nᵉ) =
  ( (succ-ℕᵉ nᵉ) *ℕᵉ (stirling-number-second-kindᵉ mᵉ (succ-ℕᵉ nᵉ))) +ℕᵉ
  ( stirling-number-second-kindᵉ mᵉ nᵉ)
```