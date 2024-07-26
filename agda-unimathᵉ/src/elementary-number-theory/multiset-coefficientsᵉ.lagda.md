# Multiset coefficients

```agda
module elementary-number-theory.multiset-coefficientsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ
```

</details>

## Idea

Theᵉ multisetᵉ coefficientsᵉ countᵉ theᵉ numberᵉ ofᵉ multisetsᵉ ofᵉ sizeᵉ `k`ᵉ ofᵉ elementsᵉ
ofᵉ aᵉ setᵉ ofᵉ sizeᵉ `n`.ᵉ Inᵉ oterᵉ words,ᵉ itᵉ countsᵉ theᵉ numberᵉ ofᵉ connectedᵉ componetsᵉ
ofᵉ theᵉ typeᵉ

```text
  Σᵉ (Aᵉ : Finᵉ nᵉ → 𝔽),ᵉ ∥ᵉ Finᵉ kᵉ ≃ᵉ Σᵉ (iᵉ : Finᵉ n),ᵉ Aᵉ iᵉ ∥.ᵉ
```

## Definition

```agda
multiset-coefficientᵉ : ℕᵉ → ℕᵉ → ℕᵉ
multiset-coefficientᵉ zero-ℕᵉ zero-ℕᵉ = 1
multiset-coefficientᵉ zero-ℕᵉ (succ-ℕᵉ kᵉ) = 0
multiset-coefficientᵉ (succ-ℕᵉ nᵉ) zero-ℕᵉ = 1
multiset-coefficientᵉ (succ-ℕᵉ nᵉ) (succ-ℕᵉ kᵉ) =
  (multiset-coefficientᵉ (succ-ℕᵉ nᵉ) kᵉ) +ℕᵉ (multiset-coefficientᵉ nᵉ (succ-ℕᵉ kᵉ))
```