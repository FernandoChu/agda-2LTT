# Repetitions of values in sequences

```agda
module univalent-combinatorics.repetitions-of-values-sequencesᵉ where
```

<details><summary>Imports</summary>

```agda

```

</details>

## Properties

```text
is-decidable-is-ordered-repetition-of-values-ℕ-Finᵉ :
  (kᵉ : ℕᵉ) (fᵉ : ℕᵉ → Finᵉ kᵉ) (xᵉ : ℕᵉ) →
  is-decidableᵉ (is-ordered-repetition-of-values-ℕᵉ fᵉ xᵉ)
is-decidable-is-ordered-repetition-of-values-ℕ-Finᵉ kᵉ fᵉ xᵉ = {!!ᵉ}

{-ᵉ
  is-decidable-strictly-bounded-Σ-ℕ'ᵉ xᵉ
    ( λ yᵉ → Idᵉ (fᵉ yᵉ) (fᵉ xᵉ))
    ( λ yᵉ → has-decidable-equality-Finᵉ kᵉ (fᵉ yᵉ) (fᵉ xᵉ))
-ᵉ}

is-decidable-is-ordered-repetition-of-values-ℕ-countᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} (eᵉ : countᵉ Aᵉ) (fᵉ : ℕᵉ → Aᵉ) (xᵉ : ℕᵉ) →
  is-decidableᵉ (is-ordered-repetition-of-values-ℕᵉ fᵉ xᵉ)
is-decidable-is-ordered-repetition-of-values-ℕ-countᵉ eᵉ fᵉ xᵉ = {!!ᵉ}

{-ᵉ
  is-decidable-strictly-bounded-Σ-ℕ'ᵉ xᵉ
    ( λ yᵉ → Idᵉ (fᵉ yᵉ) (fᵉ xᵉ))
    ( λ yᵉ → has-decidable-equality-countᵉ eᵉ (fᵉ yᵉ) (fᵉ xᵉ))
  -ᵉ}
```