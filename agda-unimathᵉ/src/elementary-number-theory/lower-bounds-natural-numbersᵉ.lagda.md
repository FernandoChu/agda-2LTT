# Lower bounds of type families over the natural numbers

```agda
module elementary-number-theory.lower-bounds-natural-numbersᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.propositionsᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Aᵉ lowerᵉ boundᵉ forᵉ aᵉ typeᵉ familyᵉ `P`ᵉ overᵉ theᵉ naturalᵉ numbersᵉ isᵉ aᵉ naturalᵉ numberᵉ
`n`ᵉ suchᵉ thatᵉ `Pᵉ xᵉ → nᵉ ≤ᵉ x`ᵉ forᵉ allᵉ `xᵉ : ℕ`.ᵉ

## Definition

```agda
is-lower-bound-ℕᵉ :
  {lᵉ : Level} (Pᵉ : ℕᵉ → UUᵉ lᵉ) (nᵉ : ℕᵉ) → UUᵉ lᵉ
is-lower-bound-ℕᵉ Pᵉ nᵉ =
  (mᵉ : ℕᵉ) → Pᵉ mᵉ → leq-ℕᵉ nᵉ mᵉ
```

## Properties

### Being a lower bound is a property

```agda
module _
  {l1ᵉ : Level} {Pᵉ : ℕᵉ → UUᵉ l1ᵉ}
  where

  abstract
    is-prop-is-lower-bound-ℕᵉ : (xᵉ : ℕᵉ) → is-propᵉ (is-lower-bound-ℕᵉ Pᵉ xᵉ)
    is-prop-is-lower-bound-ℕᵉ xᵉ =
      is-prop-Πᵉ (λ yᵉ → is-prop-function-typeᵉ (is-prop-leq-ℕᵉ xᵉ yᵉ))

  is-lower-bound-ℕ-Propᵉ : (xᵉ : ℕᵉ) → Propᵉ l1ᵉ
  pr1ᵉ (is-lower-bound-ℕ-Propᵉ xᵉ) = is-lower-bound-ℕᵉ Pᵉ xᵉ
  pr2ᵉ (is-lower-bound-ℕ-Propᵉ xᵉ) = is-prop-is-lower-bound-ℕᵉ xᵉ
```