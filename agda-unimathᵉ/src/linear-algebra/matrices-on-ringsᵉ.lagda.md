# Matrices on rings

```agda
module linear-algebra.matrices-on-ringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.action-on-identifications-binary-functionsᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ

open import linear-algebra.constant-matricesᵉ
open import linear-algebra.functoriality-matricesᵉ
open import linear-algebra.matricesᵉ
open import linear-algebra.vectorsᵉ
open import linear-algebra.vectors-on-ringsᵉ

open import ring-theory.ringsᵉ
```

</details>

## Definitions

### Matrices

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  matrix-Ringᵉ : ℕᵉ → ℕᵉ → UUᵉ lᵉ
  matrix-Ringᵉ mᵉ nᵉ = matrixᵉ (type-Ringᵉ Rᵉ) mᵉ nᵉ
```

### The zero matrix

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  zero-matrix-Ringᵉ : {mᵉ nᵉ : ℕᵉ} → matrix-Ringᵉ Rᵉ mᵉ nᵉ
  zero-matrix-Ringᵉ = constant-matrixᵉ (zero-Ringᵉ Rᵉ)
```

### Addition of matrices on rings

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  add-matrix-Ringᵉ : {mᵉ nᵉ : ℕᵉ} (Aᵉ Bᵉ : matrix-Ringᵉ Rᵉ mᵉ nᵉ) → matrix-Ringᵉ Rᵉ mᵉ nᵉ
  add-matrix-Ringᵉ = binary-map-matrixᵉ (add-Ringᵉ Rᵉ)
```

## Properties

### Addition of matrices is associative

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  associative-add-matrix-Ringᵉ :
    {mᵉ nᵉ : ℕᵉ} (Aᵉ Bᵉ Cᵉ : matrix-Ringᵉ Rᵉ mᵉ nᵉ) →
    Idᵉ
      ( add-matrix-Ringᵉ Rᵉ (add-matrix-Ringᵉ Rᵉ Aᵉ Bᵉ) Cᵉ)
      ( add-matrix-Ringᵉ Rᵉ Aᵉ (add-matrix-Ringᵉ Rᵉ Bᵉ Cᵉ))
  associative-add-matrix-Ringᵉ empty-vecᵉ empty-vecᵉ empty-vecᵉ = reflᵉ
  associative-add-matrix-Ringᵉ (vᵉ ∷ᵉ Aᵉ) (wᵉ ∷ᵉ Bᵉ) (zᵉ ∷ᵉ Cᵉ) =
    ap-binaryᵉ _∷ᵉ_
      ( associative-add-vec-Ringᵉ Rᵉ vᵉ wᵉ zᵉ)
      ( associative-add-matrix-Ringᵉ Aᵉ Bᵉ Cᵉ)
```

### Addition of matrices is commutative

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  commutative-add-matrix-Ringᵉ :
    {mᵉ nᵉ : ℕᵉ} (Aᵉ Bᵉ : matrix-Ringᵉ Rᵉ mᵉ nᵉ) →
    Idᵉ (add-matrix-Ringᵉ Rᵉ Aᵉ Bᵉ) (add-matrix-Ringᵉ Rᵉ Bᵉ Aᵉ)
  commutative-add-matrix-Ringᵉ empty-vecᵉ empty-vecᵉ = reflᵉ
  commutative-add-matrix-Ringᵉ (vᵉ ∷ᵉ Aᵉ) (wᵉ ∷ᵉ Bᵉ) =
    ap-binaryᵉ _∷ᵉ_
      ( commutative-add-vec-Ringᵉ Rᵉ vᵉ wᵉ)
      ( commutative-add-matrix-Ringᵉ Aᵉ Bᵉ)
```

### Left unit law for addition of matrices

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  left-unit-law-add-matrix-Ringᵉ :
    {mᵉ nᵉ : ℕᵉ} (Aᵉ : matrix-Ringᵉ Rᵉ mᵉ nᵉ) →
    Idᵉ (add-matrix-Ringᵉ Rᵉ (zero-matrix-Ringᵉ Rᵉ) Aᵉ) Aᵉ
  left-unit-law-add-matrix-Ringᵉ empty-vecᵉ = reflᵉ
  left-unit-law-add-matrix-Ringᵉ (vᵉ ∷ᵉ Aᵉ) =
    ap-binaryᵉ _∷ᵉ_
      ( left-unit-law-add-vec-Ringᵉ Rᵉ vᵉ)
      ( left-unit-law-add-matrix-Ringᵉ Aᵉ)
```

### Right unit law for addition of matrices

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  right-unit-law-add-matrix-Ringᵉ :
    {mᵉ nᵉ : ℕᵉ} (Aᵉ : matrix-Ringᵉ Rᵉ mᵉ nᵉ) →
    Idᵉ (add-matrix-Ringᵉ Rᵉ Aᵉ (zero-matrix-Ringᵉ Rᵉ)) Aᵉ
  right-unit-law-add-matrix-Ringᵉ empty-vecᵉ = reflᵉ
  right-unit-law-add-matrix-Ringᵉ (vᵉ ∷ᵉ Aᵉ) =
    ap-binaryᵉ _∷ᵉ_
      ( right-unit-law-add-vec-Ringᵉ Rᵉ vᵉ)
      ( right-unit-law-add-matrix-Ringᵉ Aᵉ)
```