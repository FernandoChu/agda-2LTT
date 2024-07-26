# Upper bounds for type families over the natural numbers

```agda
module elementary-number-theory.upper-bounds-natural-numbersᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ
open import elementary-number-theory.strict-inequality-natural-numbersᵉ

open import foundation.universe-levelsᵉ
```

</details>

## Idea

Aᵉ typeᵉ familyᵉ overᵉ theᵉ naturalᵉ numbersᵉ hasᵉ anᵉ upperᵉ boundᵉ `n`,ᵉ ifᵉ thereᵉ isᵉ aᵉ
functionᵉ fromᵉ `Pᵉ x`ᵉ to theᵉ typeᵉ `xᵉ ≤ᵉ n`ᵉ forᵉ allᵉ `xᵉ : ℕ`.ᵉ Similarᵉ forᵉ strictᵉ
upperᵉ bounds.ᵉ

## Definition

### Upper bounds

```agda
is-upper-bound-ℕᵉ :
  {lᵉ : Level} (Pᵉ : ℕᵉ → UUᵉ lᵉ) (nᵉ : ℕᵉ) → UUᵉ lᵉ
is-upper-bound-ℕᵉ Pᵉ nᵉ =
  (mᵉ : ℕᵉ) → Pᵉ mᵉ → leq-ℕᵉ mᵉ nᵉ
```

### Strict upper bounds

```agda
is-strict-upper-bound-ℕᵉ :
  {lᵉ : Level} (Pᵉ : ℕᵉ → UUᵉ lᵉ) (nᵉ : ℕᵉ) → UUᵉ lᵉ
is-strict-upper-bound-ℕᵉ Pᵉ nᵉ =
  (mᵉ : ℕᵉ) → Pᵉ mᵉ → le-ℕᵉ mᵉ nᵉ
```

## Properties

### A strict upper bound is an upper bound

```agda
is-upper-bound-is-strict-upper-bound-ℕᵉ :
  {lᵉ : Level} (Pᵉ : ℕᵉ → UUᵉ lᵉ) (nᵉ : ℕᵉ) →
  is-strict-upper-bound-ℕᵉ Pᵉ nᵉ → is-upper-bound-ℕᵉ Pᵉ nᵉ
is-upper-bound-is-strict-upper-bound-ℕᵉ Pᵉ nᵉ Hᵉ xᵉ pᵉ =
  leq-le-ℕᵉ xᵉ nᵉ (Hᵉ xᵉ pᵉ)
```