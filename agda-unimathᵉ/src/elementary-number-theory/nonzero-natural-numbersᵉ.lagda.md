# Nonzero natural numbers

```agda
module elementary-number-theory.nonzero-natural-numbersᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.divisibility-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Aᵉ [naturalᵉ number](elementary-number-theory.natural-numbers.mdᵉ) `n`ᵉ isᵉ saidᵉ to
beᵉ **nonzero**ᵉ ifᵉ theᵉ [proposition](foundation.propositions.mdᵉ)

```text
  nᵉ ≠ᵉ 0
```

holds.ᵉ Thisᵉ conditionᵉ wasᵉ alreadyᵉ definedᵉ in theᵉ fileᵉ
[`elementary-number-theory.natural-numbers`](elementary-number-theory.natural-numbers.md).ᵉ
Theᵉ typeᵉ ofᵉ nonzeroᵉ naturalᵉ numbersᵉ consistsᵉ ofᵉ naturalᵉ numbersᵉ equippedᵉ with aᵉ
proofᵉ thatᵉ theyᵉ areᵉ nonzero.ᵉ

## Definitions

### The type of nonzero natural numbers

```agda
nonzero-ℕᵉ : UUᵉ lzero
nonzero-ℕᵉ = Σᵉ ℕᵉ is-nonzero-ℕᵉ

nat-nonzero-ℕᵉ : nonzero-ℕᵉ → ℕᵉ
nat-nonzero-ℕᵉ = pr1ᵉ

is-nonzero-nat-nonzero-ℕᵉ : (nᵉ : nonzero-ℕᵉ) → is-nonzero-ℕᵉ (nat-nonzero-ℕᵉ nᵉ)
is-nonzero-nat-nonzero-ℕᵉ = pr2ᵉ
```

### The nonzero natural number `1`

```agda
one-nonzero-ℕᵉ : nonzero-ℕᵉ
pr1ᵉ one-nonzero-ℕᵉ = 1
pr2ᵉ one-nonzero-ℕᵉ = is-nonzero-one-ℕᵉ
```

### The successor function on the nonzero natural numbers

```agda
succ-nonzero-ℕᵉ : nonzero-ℕᵉ → nonzero-ℕᵉ
pr1ᵉ (succ-nonzero-ℕᵉ (pairᵉ xᵉ _)) = succ-ℕᵉ xᵉ
pr2ᵉ (succ-nonzero-ℕᵉ (pairᵉ xᵉ _)) = is-nonzero-succ-ℕᵉ xᵉ
```

### The successor function from the natural numbers to the nonzero natural numbers

```agda
succ-nonzero-ℕ'ᵉ : ℕᵉ → nonzero-ℕᵉ
pr1ᵉ (succ-nonzero-ℕ'ᵉ nᵉ) = succ-ℕᵉ nᵉ
pr2ᵉ (succ-nonzero-ℕ'ᵉ nᵉ) = is-nonzero-succ-ℕᵉ nᵉ
```

### The quotient of a nonzero natural number by a divisor

```agda
quotient-div-nonzero-ℕᵉ :
  (dᵉ : ℕᵉ) (xᵉ : nonzero-ℕᵉ) (Hᵉ : div-ℕᵉ dᵉ (pr1ᵉ xᵉ)) → nonzero-ℕᵉ
pr1ᵉ (quotient-div-nonzero-ℕᵉ dᵉ (pairᵉ xᵉ Kᵉ) Hᵉ) = quotient-div-ℕᵉ dᵉ xᵉ Hᵉ
pr2ᵉ (quotient-div-nonzero-ℕᵉ dᵉ (pairᵉ xᵉ Kᵉ) Hᵉ) = is-nonzero-quotient-div-ℕᵉ Hᵉ Kᵉ
```