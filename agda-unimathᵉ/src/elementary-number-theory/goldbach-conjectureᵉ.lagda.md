# The Goldbach conjecture

```agda
module elementary-number-theory.goldbach-conjectureᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ
open import elementary-number-theory.parity-natural-numbersᵉ
open import elementary-number-theory.prime-numbersᵉ
open import elementary-number-theory.strict-inequality-natural-numbersᵉ

open import foundation.cartesian-product-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Conjecture

```agda
Goldbach-conjectureᵉ : UUᵉ lzero
Goldbach-conjectureᵉ =
  ( nᵉ : ℕᵉ) → (le-ℕᵉ 2 nᵉ) → (is-even-ℕᵉ nᵉ) →
    Σᵉ ℕᵉ (λ pᵉ → (is-prime-ℕᵉ pᵉ) ×ᵉ (Σᵉ ℕᵉ (λ qᵉ → (is-prime-ℕᵉ qᵉ) ×ᵉ (pᵉ +ℕᵉ qᵉ ＝ᵉ nᵉ))))
```