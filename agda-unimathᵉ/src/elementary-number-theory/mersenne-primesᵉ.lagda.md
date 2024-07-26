# Mersenne primes

```agda
module elementary-number-theory.mersenne-primesᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.distance-natural-numbersᵉ
open import elementary-number-theory.exponentiation-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ
open import elementary-number-theory.prime-numbersᵉ

open import foundation.cartesian-product-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Aᵉ Mersenneᵉ primeᵉ isᵉ aᵉ primeᵉ numberᵉ thatᵉ isᵉ oneᵉ lessᵉ thanᵉ aᵉ powerᵉ ofᵉ two.ᵉ

## Definition

```agda
is-mersenne-primeᵉ : ℕᵉ → UUᵉ lzero
is-mersenne-primeᵉ nᵉ = is-prime-ℕᵉ nᵉ ×ᵉ Σᵉ ℕᵉ (λ kᵉ → dist-ℕᵉ (exp-ℕᵉ 2 kᵉ) 1 ＝ᵉ nᵉ)

is-mersenne-prime-powerᵉ : ℕᵉ → UUᵉ lzero
is-mersenne-prime-powerᵉ kᵉ = is-prime-ℕᵉ (dist-ℕᵉ (exp-ℕᵉ 2 kᵉ) 1ᵉ)
```