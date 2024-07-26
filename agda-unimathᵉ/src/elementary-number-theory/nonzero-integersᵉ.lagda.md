# Nonzero integers

```agda
module elementary-number-theory.nonzero-integersᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.integersᵉ
open import elementary-number-theory.natural-numbersᵉ

open import foundation.coproduct-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.negationᵉ
open import foundation.propositionsᵉ
open import foundation.subtypesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Anᵉ [integer](elementary-number-theory.integers.mdᵉ) `k`ᵉ isᵉ saidᵉ to beᵉ **nonzero**ᵉ
ifᵉ theᵉ [proposition](foundation.propositions.mdᵉ)

```text
  kᵉ ≠ᵉ 0
```

holds.ᵉ

## Definition

### The predicate of being a nonzero integer

```agda
is-nonzero-prop-ℤᵉ : ℤᵉ → Propᵉ lzero
is-nonzero-prop-ℤᵉ kᵉ = neg-type-Propᵉ (kᵉ ＝ᵉ zero-ℤᵉ)

is-nonzero-ℤᵉ : ℤᵉ → UUᵉ lzero
is-nonzero-ℤᵉ kᵉ = type-Propᵉ (is-nonzero-prop-ℤᵉ kᵉ)

is-prop-is-nonzero-ℤᵉ : (kᵉ : ℤᵉ) → is-propᵉ (is-nonzero-ℤᵉ kᵉ)
is-prop-is-nonzero-ℤᵉ kᵉ = is-prop-type-Propᵉ (is-nonzero-prop-ℤᵉ kᵉ)
```

### The nonzero integers

```agda
nonzero-ℤᵉ : UUᵉ lzero
nonzero-ℤᵉ = type-subtypeᵉ is-nonzero-prop-ℤᵉ

module _
  (kᵉ : nonzero-ℤᵉ)
  where

  int-nonzero-ℤᵉ : ℤᵉ
  int-nonzero-ℤᵉ = pr1ᵉ kᵉ

  is-nonzero-nonzero-ℤᵉ : is-nonzero-ℤᵉ int-nonzero-ℤᵉ
  is-nonzero-nonzero-ℤᵉ = pr2ᵉ kᵉ
```

### The nonzero integer `1`

```agda
is-nonzero-one-ℤᵉ : is-nonzero-ℤᵉ one-ℤᵉ
is-nonzero-one-ℤᵉ ()

one-nonzero-ℤᵉ : nonzero-ℤᵉ
pr1ᵉ one-nonzero-ℤᵉ = one-ℤᵉ
pr2ᵉ one-nonzero-ℤᵉ = is-nonzero-one-ℤᵉ
```

## Properties

### The integer image of a nonzero natural number is nonzero

```agda
is-nonzero-int-ℕᵉ : (nᵉ : ℕᵉ) → is-nonzero-ℕᵉ nᵉ → is-nonzero-ℤᵉ (int-ℕᵉ nᵉ)
is-nonzero-int-ℕᵉ zero-ℕᵉ Hᵉ pᵉ = Hᵉ reflᵉ
```

### The negative of a nonzero integer is nonzero

```agda
is-nonzero-neg-nonzero-ℤᵉ : (xᵉ : ℤᵉ) → is-nonzero-ℤᵉ xᵉ → is-nonzero-ℤᵉ (neg-ℤᵉ xᵉ)
is-nonzero-neg-nonzero-ℤᵉ xᵉ Hᵉ Kᵉ = Hᵉ (is-zero-is-zero-neg-ℤᵉ xᵉ Kᵉ)
```