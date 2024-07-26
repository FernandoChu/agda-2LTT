# The binomial coefficients

```agda
module elementary-number-theory.binomial-coefficientsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ
open import elementary-number-theory.strict-inequality-natural-numbersᵉ

open import foundation.identity-typesᵉ

open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Theᵉ binomialᵉ coefficientᵉ `(nᵉ chooseᵉ k)`ᵉ measuresᵉ howᵉ manyᵉ decidableᵉ subsetsᵉ ofᵉ
`Finᵉ n`ᵉ thereᵉ areᵉ ofᵉ sizeᵉ `k`.ᵉ

## Definition

### Binomial coefficients of natural numbers

```agda
binomial-coefficient-ℕᵉ : ℕᵉ → ℕᵉ → ℕᵉ
binomial-coefficient-ℕᵉ zero-ℕᵉ zero-ℕᵉ = 1
binomial-coefficient-ℕᵉ zero-ℕᵉ (succ-ℕᵉ kᵉ) = 0
binomial-coefficient-ℕᵉ (succ-ℕᵉ nᵉ) zero-ℕᵉ = 1
binomial-coefficient-ℕᵉ (succ-ℕᵉ nᵉ) (succ-ℕᵉ kᵉ) =
  (binomial-coefficient-ℕᵉ nᵉ kᵉ) +ℕᵉ (binomial-coefficient-ℕᵉ nᵉ (succ-ℕᵉ kᵉ))
```

### Binomial coefficients indexed by elements of standard finite types

```agda
binomial-coefficient-Finᵉ : (nᵉ : ℕᵉ) → Finᵉ (succ-ℕᵉ nᵉ) → ℕᵉ
binomial-coefficient-Finᵉ nᵉ xᵉ = binomial-coefficient-ℕᵉ nᵉ (nat-Finᵉ (succ-ℕᵉ nᵉ) xᵉ)
```

## Properties

### If `k > n` then `binomial-coefficient-ℕ n k ＝ 0`

```agda
is-zero-binomial-coefficient-ℕᵉ :
  (nᵉ kᵉ : ℕᵉ) → le-ℕᵉ nᵉ kᵉ → is-zero-ℕᵉ (binomial-coefficient-ℕᵉ nᵉ kᵉ)
is-zero-binomial-coefficient-ℕᵉ zero-ℕᵉ (succ-ℕᵉ kᵉ) _ = reflᵉ
is-zero-binomial-coefficient-ℕᵉ (succ-ℕᵉ nᵉ) (succ-ℕᵉ kᵉ) Hᵉ =
  ap-add-ℕᵉ
    ( is-zero-binomial-coefficient-ℕᵉ nᵉ kᵉ Hᵉ)
    ( is-zero-binomial-coefficient-ℕᵉ nᵉ (succ-ℕᵉ kᵉ) (preserves-le-succ-ℕᵉ nᵉ kᵉ Hᵉ))
```

### `binomial-coefficient-ℕ n n ＝ 1`

```agda
is-one-on-diagonal-binomial-coefficient-ℕᵉ :
  (nᵉ : ℕᵉ) → is-one-ℕᵉ (binomial-coefficient-ℕᵉ nᵉ nᵉ)
is-one-on-diagonal-binomial-coefficient-ℕᵉ zero-ℕᵉ = reflᵉ
is-one-on-diagonal-binomial-coefficient-ℕᵉ (succ-ℕᵉ nᵉ) =
  ap-add-ℕᵉ
    ( is-one-on-diagonal-binomial-coefficient-ℕᵉ nᵉ)
    ( is-zero-binomial-coefficient-ℕᵉ nᵉ (succ-ℕᵉ nᵉ) (succ-le-ℕᵉ nᵉ))
```