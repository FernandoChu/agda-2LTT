# The Collatz bijection

```agda
module elementary-number-theory.collatz-bijectionᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.distance-natural-numbersᵉ
open import elementary-number-theory.euclidean-division-natural-numbersᵉ
open import elementary-number-theory.modular-arithmeticᵉ
open import elementary-number-theory.multiplication-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ

open import foundation.coproduct-typesᵉ
open import foundation.identity-typesᵉ
```

</details>

## Idea

Weᵉ defineᵉ aᵉ bijectionᵉ ofᵉ Collatzᵉ

## Definition

```agda
cases-map-collatz-bijectionᵉ : (nᵉ : ℕᵉ) (xᵉ : ℤ-Modᵉ 3ᵉ) (pᵉ : mod-ℕᵉ 3 nᵉ ＝ᵉ xᵉ) → ℕᵉ
cases-map-collatz-bijectionᵉ nᵉ (inlᵉ (inlᵉ (inrᵉ _))) pᵉ =
  quotient-euclidean-division-ℕᵉ 3 (2ᵉ *ℕᵉ nᵉ)
cases-map-collatz-bijectionᵉ nᵉ (inlᵉ (inrᵉ _)) pᵉ =
  quotient-euclidean-division-ℕᵉ 3 (dist-ℕᵉ (4ᵉ *ℕᵉ nᵉ) 1ᵉ)
cases-map-collatz-bijectionᵉ nᵉ (inrᵉ _) pᵉ =
  quotient-euclidean-division-ℕᵉ 3 (succ-ℕᵉ (4ᵉ *ℕᵉ nᵉ))

map-collatz-bijectionᵉ : ℕᵉ → ℕᵉ
map-collatz-bijectionᵉ nᵉ = cases-map-collatz-bijectionᵉ nᵉ (mod-ℕᵉ 3 nᵉ) reflᵉ
```