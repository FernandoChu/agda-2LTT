# Tuples of types

```agda
module foundation.tuples-of-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.universe-levelsᵉ

open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Anᵉ `n`-tupleᵉ ofᵉ typesᵉ isᵉ aᵉ typeᵉ familyᵉ `Finᵉ nᵉ → UU`.ᵉ

## Definition

```agda
tuple-typesᵉ : (lᵉ : Level) (nᵉ : ℕᵉ) → UUᵉ (lsuc lᵉ)
tuple-typesᵉ lᵉ nᵉ = Finᵉ nᵉ → UUᵉ lᵉ
```

## Properties

### The tuple of types `A j` for `i ≠ j`, given `i`

```agda
{-ᵉ
tuple-types-complement-pointᵉ :
  {lᵉ : Level} {nᵉ : ℕᵉ} (Aᵉ : tuple-typesᵉ lᵉ (succ-ℕᵉ nᵉ)) (iᵉ : Finᵉ (succ-ℕᵉ nᵉ)) →
  tuple-typesᵉ lᵉ nᵉ
tuple-types-complement-pointᵉ Aᵉ iᵉ = {!!ᵉ}
-ᵉ}
```