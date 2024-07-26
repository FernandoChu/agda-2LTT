# Factorials of natural numbers

```agda
module elementary-number-theory.factorialsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.divisibility-natural-numbersᵉ
open import elementary-number-theory.equality-natural-numbersᵉ
open import elementary-number-theory.inequality-natural-numbersᵉ
open import elementary-number-theory.multiplication-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ

open import foundation.coproduct-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.empty-typesᵉ
open import foundation.identity-typesᵉ
```

</details>

## Definition

```agda
factorial-ℕᵉ : ℕᵉ → ℕᵉ
factorial-ℕᵉ 0 = 1
factorial-ℕᵉ (succ-ℕᵉ mᵉ) = (factorial-ℕᵉ mᵉ) *ℕᵉ (succ-ℕᵉ mᵉ)
```

## Properties

```agda
div-factorial-ℕᵉ :
  (nᵉ xᵉ : ℕᵉ) → leq-ℕᵉ xᵉ nᵉ → is-nonzero-ℕᵉ xᵉ → div-ℕᵉ xᵉ (factorial-ℕᵉ nᵉ)
div-factorial-ℕᵉ zero-ℕᵉ zero-ℕᵉ lᵉ Hᵉ = ex-falsoᵉ (Hᵉ reflᵉ)
div-factorial-ℕᵉ (succ-ℕᵉ nᵉ) xᵉ lᵉ Hᵉ with
  decide-leq-succ-ℕᵉ xᵉ nᵉ lᵉ
... | inlᵉ l'ᵉ =
  transitive-div-ℕᵉ xᵉ
    ( factorial-ℕᵉ nᵉ)
    ( factorial-ℕᵉ (succ-ℕᵉ nᵉ))
    ( pairᵉ (succ-ℕᵉ nᵉ) (commutative-mul-ℕᵉ (succ-ℕᵉ nᵉ) (factorial-ℕᵉ nᵉ)))
    ( div-factorial-ℕᵉ nᵉ xᵉ l'ᵉ Hᵉ)
... | inrᵉ reflᵉ = pairᵉ (factorial-ℕᵉ nᵉ) reflᵉ
```

```agda
is-nonzero-factorial-ℕᵉ :
  (xᵉ : ℕᵉ) → is-nonzero-ℕᵉ (factorial-ℕᵉ xᵉ)
is-nonzero-factorial-ℕᵉ zero-ℕᵉ = Eq-eq-ℕᵉ
is-nonzero-factorial-ℕᵉ (succ-ℕᵉ xᵉ) =
  is-nonzero-mul-ℕᵉ
    ( factorial-ℕᵉ xᵉ)
    ( succ-ℕᵉ xᵉ)
    ( is-nonzero-factorial-ℕᵉ xᵉ)
    ( is-nonzero-succ-ℕᵉ xᵉ)

leq-factorial-ℕᵉ :
  (nᵉ : ℕᵉ) → leq-ℕᵉ nᵉ (factorial-ℕᵉ nᵉ)
leq-factorial-ℕᵉ zero-ℕᵉ = leq-zero-ℕᵉ 1
leq-factorial-ℕᵉ (succ-ℕᵉ nᵉ) =
  leq-mul-is-nonzero-ℕ'ᵉ
    ( factorial-ℕᵉ nᵉ)
    ( succ-ℕᵉ nᵉ)
    ( is-nonzero-factorial-ℕᵉ nᵉ)
```