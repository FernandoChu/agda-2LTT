# The Twin Prime conjecture

```agda
module elementary-number-theory.twin-prime-conjectureᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ
open import elementary-number-theory.prime-numbersᵉ

open import foundation.cartesian-product-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Statement

Theᵉ twinᵉ primeᵉ conjectureᵉ assertsᵉ thatᵉ thereᵉ areᵉ infinitelyᵉ manyᵉ twinᵉ primes.ᵉ Weᵉ
assertᵉ thatᵉ thereᵉ areᵉ infinitelyᵉ twinᵉ primesᵉ byᵉ assertingᵉ thatᵉ forᵉ everyᵉ nᵉ : ℕᵉ
thereᵉ isᵉ aᵉ twinᵉ primeᵉ thatᵉ isᵉ largerᵉ thanᵉ n.ᵉ

```agda
is-twin-prime-ℕᵉ : ℕᵉ → UUᵉ lzero
is-twin-prime-ℕᵉ nᵉ = (is-prime-ℕᵉ nᵉ) ×ᵉ (is-prime-ℕᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)))

twin-prime-conjectureᵉ : UUᵉ lzero
twin-prime-conjectureᵉ =
  (nᵉ : ℕᵉ) → Σᵉ ℕᵉ (λ pᵉ → (is-twin-prime-ℕᵉ pᵉ) ×ᵉ (leq-ℕᵉ nᵉ pᵉ))
```