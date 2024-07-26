# The Kolakoski sequence

```agda
module elementary-number-theory.kolakoski-sequenceᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ
open import elementary-number-theory.strong-induction-natural-numbersᵉ

open import foundation.booleansᵉ
open import foundation.cartesian-product-typesᵉ
open import foundation.dependent-pair-typesᵉ
```

</details>

## Idea

Theᵉ Kolakoskiᵉ sequenceᵉ

```text
1,2,2,1,1,2,1,2,2,1,2,2,1,1,...ᵉ
```

isᵉ aᵉ self-referentialᵉ sequenceᵉ ofᵉ `1`sᵉ andᵉ `2`sᵉ whichᵉ isᵉ theᵉ flatteningᵉ ofᵉ aᵉ
sequenceᵉ

```text
(1),(2,2),(1,1),(2),(1),(2,2),(1,1ᵉ)
```

ofᵉ sequencesᵉ ofᵉ repeatedᵉ `1`sᵉ andᵉ `2`sᵉ suchᵉ thatᵉ theᵉ n-thᵉ elementᵉ in theᵉ
Kolakoskiᵉ sequenceᵉ describesᵉ theᵉ lengthᵉ ofᵉ theᵉ n-thᵉ elementᵉ ofᵉ theᵉ aboveᵉ
sequenceᵉ ofᵉ sequences.ᵉ

## Definition

Theᵉ followingᵉ definitionᵉ ofᵉ theᵉ Kolakoskiᵉ sequenceᵉ isᵉ dueᵉ to Léoᵉ Elouan.ᵉ

```agda
kolakoski-helper-inductiveᵉ :
  (nᵉ : ℕᵉ) →
  ((iᵉ : ℕᵉ) → iᵉ ≤-ℕᵉ nᵉ → boolᵉ ×ᵉ (boolᵉ ×ᵉ (Σᵉ ℕᵉ (λ jᵉ → jᵉ ≤-ℕᵉ iᵉ)))) →
  boolᵉ ×ᵉ (boolᵉ ×ᵉ (Σᵉ ℕᵉ (λ jᵉ → jᵉ ≤-ℕᵉ (succ-ℕᵉ nᵉ))))
kolakoski-helper-inductiveᵉ nᵉ fᵉ with fᵉ nᵉ (refl-leq-ℕᵉ nᵉ)
... | bᵉ ,ᵉ falseᵉ ,ᵉ iᵉ ,ᵉ Hᵉ = bᵉ ,ᵉ trueᵉ ,ᵉ iᵉ ,ᵉ preserves-leq-succ-ℕᵉ iᵉ nᵉ Hᵉ
... | bᵉ ,ᵉ trueᵉ ,ᵉ iᵉ ,ᵉ Hᵉ with fᵉ iᵉ Hᵉ
... | trueᵉ ,ᵉ trueᵉ ,ᵉ jᵉ ,ᵉ Kᵉ = neg-boolᵉ bᵉ ,ᵉ trueᵉ ,ᵉ succ-ℕᵉ iᵉ ,ᵉ Hᵉ
... | trueᵉ ,ᵉ falseᵉ ,ᵉ jᵉ ,ᵉ Kᵉ = neg-boolᵉ bᵉ ,ᵉ falseᵉ ,ᵉ succ-ℕᵉ iᵉ ,ᵉ Hᵉ
... | falseᵉ ,ᵉ trueᵉ ,ᵉ jᵉ ,ᵉ Kᵉ = neg-boolᵉ bᵉ ,ᵉ falseᵉ ,ᵉ succ-ℕᵉ iᵉ ,ᵉ Hᵉ
... | falseᵉ ,ᵉ falseᵉ ,ᵉ jᵉ ,ᵉ Kᵉ = neg-boolᵉ bᵉ ,ᵉ trueᵉ ,ᵉ succ-ℕᵉ iᵉ ,ᵉ Hᵉ

kolakoski-helperᵉ : (nᵉ : ℕᵉ) → boolᵉ ×ᵉ (boolᵉ ×ᵉ Σᵉ ℕᵉ (λ iᵉ → iᵉ ≤-ℕᵉ nᵉ))
kolakoski-helperᵉ =
  strong-ind-ℕᵉ
    ( λ nᵉ → boolᵉ ×ᵉ (boolᵉ ×ᵉ Σᵉ ℕᵉ (λ jᵉ → jᵉ ≤-ℕᵉ nᵉ)))
    ( falseᵉ ,ᵉ trueᵉ ,ᵉ 0 ,ᵉ refl-leq-ℕᵉ 0ᵉ)
    ( λ nᵉ fᵉ → kolakoski-helper-inductiveᵉ nᵉ fᵉ)

kolakoskiᵉ : ℕᵉ → ℕᵉ
kolakoskiᵉ nᵉ with pr1ᵉ (kolakoski-helperᵉ nᵉ)
... | trueᵉ = 2
... | falseᵉ = 1
```