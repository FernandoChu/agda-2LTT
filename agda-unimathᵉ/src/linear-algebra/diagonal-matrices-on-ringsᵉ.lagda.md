# Diagonal matrices on rings

```agda
module linear-algebra.diagonal-matrices-on-ringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.universe-levelsᵉ

open import linear-algebra.constant-vectorsᵉ
open import linear-algebra.functoriality-vectorsᵉ
open import linear-algebra.matrices-on-ringsᵉ
open import linear-algebra.vectorsᵉ
open import linear-algebra.vectors-on-ringsᵉ

open import ring-theory.ringsᵉ
```

</details>

## Definitions

### Diagonal matrices

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  diagonal-matrix-Ringᵉ : (nᵉ : ℕᵉ) → vec-Ringᵉ Rᵉ nᵉ → matrix-Ringᵉ Rᵉ nᵉ nᵉ
  diagonal-matrix-Ringᵉ zero-ℕᵉ vᵉ = empty-vecᵉ
  diagonal-matrix-Ringᵉ (succ-ℕᵉ nᵉ) (xᵉ ∷ᵉ vᵉ) =
    ( xᵉ ∷ᵉ zero-vec-Ringᵉ Rᵉ) ∷ᵉ
    ( map-vecᵉ (λ v'ᵉ → zero-Ringᵉ Rᵉ ∷ᵉ v'ᵉ) (diagonal-matrix-Ringᵉ nᵉ vᵉ))
```

### Scalar matrices

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  scalar-matrix-Ringᵉ : (nᵉ : ℕᵉ) → type-Ringᵉ Rᵉ → matrix-Ringᵉ Rᵉ nᵉ nᵉ
  scalar-matrix-Ringᵉ nᵉ xᵉ = diagonal-matrix-Ringᵉ Rᵉ nᵉ (constant-vecᵉ xᵉ)

  identity-matrix-Ringᵉ : (nᵉ : ℕᵉ) → matrix-Ringᵉ Rᵉ nᵉ nᵉ
  identity-matrix-Ringᵉ nᵉ = scalar-matrix-Ringᵉ nᵉ (one-Ringᵉ Rᵉ)
```