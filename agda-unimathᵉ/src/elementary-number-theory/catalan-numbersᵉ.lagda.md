# Catalan numbers

```agda
module elementary-number-theory.catalan-numbersᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.binomial-coefficientsᵉ
open import elementary-number-theory.distance-natural-numbersᵉ
open import elementary-number-theory.multiplication-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ
open import elementary-number-theory.strict-inequality-natural-numbersᵉ
open import elementary-number-theory.strong-induction-natural-numbersᵉ
open import elementary-number-theory.sums-of-natural-numbersᵉ

open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Theᵉ Catalanᵉ numbersᵉ areᵉ aᵉ sequenceᵉ ofᵉ naturalᵉ numbersᵉ thatᵉ occurᵉ in severalᵉ
combinatoricsᵉ problems.ᵉ

## Definitions

```agda
catalan-numbersᵉ : ℕᵉ → ℕᵉ
catalan-numbersᵉ =
  strong-ind-ℕᵉ (λ _ → ℕᵉ) (succ-ℕᵉ zero-ℕᵉ)
    ( λ kᵉ Cᵉ →
      sum-Fin-ℕᵉ kᵉ
        ( λ iᵉ →
          mul-ℕᵉ
            ( Cᵉ ( nat-Finᵉ kᵉ iᵉ)
                ( leq-le-ℕᵉ (nat-Finᵉ kᵉ iᵉ) kᵉ (strict-upper-bound-nat-Finᵉ kᵉ iᵉ)))
            ( Cᵉ ( dist-ℕᵉ (nat-Finᵉ kᵉ iᵉ) kᵉ)
                ( leq-dist-ℕᵉ
                  ( nat-Finᵉ kᵉ iᵉ)
                  ( kᵉ)
                  ( leq-le-ℕᵉ
                    ( nat-Finᵉ kᵉ iᵉ)
                    ( kᵉ)
                    ( strict-upper-bound-nat-Finᵉ kᵉ iᵉ))))))

catalan-numbers-binomialᵉ : ℕᵉ → ℕᵉ
catalan-numbers-binomialᵉ nᵉ =
  dist-ℕᵉ
    ( binomial-coefficient-ℕᵉ (2ᵉ *ℕᵉ nᵉ) nᵉ)
    ( binomial-coefficient-ℕᵉ (2ᵉ *ℕᵉ nᵉ) (succ-ℕᵉ nᵉ))
```