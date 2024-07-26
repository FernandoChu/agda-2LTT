# Combinatorial identities of sums of natural numbers

```agda
module univalent-combinatorics.sums-of-natural-numbersᵉ where

open import elementary-number-theory.sums-of-natural-numbersᵉ public
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import univalent-combinatorics.countingᵉ
open import univalent-combinatorics.counting-dependent-pair-typesᵉ
open import univalent-combinatorics.double-countingᵉ
open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Weᵉ useᵉ countingᵉ methodsᵉ to proveᵉ identitiesᵉ ofᵉ sumsᵉ ofᵉ naturalᵉ numbersᵉ

### Finite sums are associative

```agda
abstract
  associative-sum-count-ℕᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} (count-Aᵉ : countᵉ Aᵉ)
    (count-Bᵉ : (xᵉ : Aᵉ) → countᵉ (Bᵉ xᵉ)) (fᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ → ℕᵉ) →
    Idᵉ
      ( sum-count-ℕᵉ count-Aᵉ (λ xᵉ → sum-count-ℕᵉ (count-Bᵉ xᵉ) (fᵉ xᵉ)))
      ( sum-count-ℕᵉ (count-Σᵉ count-Aᵉ count-Bᵉ) (ind-Σᵉ fᵉ))
  associative-sum-count-ℕᵉ {l1ᵉ} {l2ᵉ} {Aᵉ} {Bᵉ} count-Aᵉ count-Bᵉ fᵉ =
    ( ( htpy-sum-count-ℕᵉ count-Aᵉ
        ( λ xᵉ →
          invᵉ
          ( number-of-elements-count-Σᵉ
            ( count-Bᵉ xᵉ)
            ( λ yᵉ → count-Finᵉ (fᵉ xᵉ yᵉ))))) ∙ᵉ
      ( invᵉ
        ( number-of-elements-count-Σᵉ count-Aᵉ
          ( λ xᵉ → count-Σᵉ (count-Bᵉ xᵉ) (λ yᵉ → count-Finᵉ (fᵉ xᵉ yᵉ)))))) ∙ᵉ
    ( ( double-counting-equivᵉ
        ( count-Σᵉ count-Aᵉ (λ xᵉ → count-Σᵉ (count-Bᵉ xᵉ) (λ yᵉ → count-Finᵉ (fᵉ xᵉ yᵉ))))
        ( count-Σᵉ (count-Σᵉ count-Aᵉ count-Bᵉ) (λ xᵉ → count-Finᵉ (ind-Σᵉ fᵉ xᵉ)))
        ( inv-associative-Σᵉ Aᵉ Bᵉ (λ xᵉ → Finᵉ (ind-Σᵉ fᵉ xᵉ)))) ∙ᵉ
      ( number-of-elements-count-Σᵉ
        ( count-Σᵉ count-Aᵉ count-Bᵉ)
        ( λ xᵉ → (count-Finᵉ (ind-Σᵉ fᵉ xᵉ)))))
```