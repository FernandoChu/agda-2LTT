# Functoriality of the type of matrices

```agda
module linear-algebra.functoriality-matricesᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.universe-levelsᵉ

open import linear-algebra.functoriality-vectorsᵉ
open import linear-algebra.matricesᵉ
```

</details>

## Idea

Anyᵉ mapᵉ `fᵉ : Aᵉ → B`ᵉ inducesᵉ aᵉ mapᵉ `matrixᵉ Aᵉ mᵉ nᵉ → matrixᵉ Bᵉ mᵉ n`.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ)
  where

  map-matrixᵉ : {mᵉ nᵉ : ℕᵉ} → matrixᵉ Aᵉ mᵉ nᵉ → matrixᵉ Bᵉ mᵉ nᵉ
  map-matrixᵉ = map-vecᵉ (map-vecᵉ fᵉ)
```

### Binar maps

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} (fᵉ : Aᵉ → Bᵉ → Cᵉ)
  where

  binary-map-matrixᵉ :
    {mᵉ nᵉ : ℕᵉ} → matrixᵉ Aᵉ mᵉ nᵉ → matrixᵉ Bᵉ mᵉ nᵉ → matrixᵉ Cᵉ mᵉ nᵉ
  binary-map-matrixᵉ = binary-map-vecᵉ (binary-map-vecᵉ fᵉ)
```