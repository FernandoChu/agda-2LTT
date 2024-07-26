# Constant matrices

```agda
module linear-algebra.constant-matricesᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.universe-levelsᵉ

open import linear-algebra.constant-vectorsᵉ
open import linear-algebra.matricesᵉ
```

</details>

## Idea

Constantᵉ matricesᵉ areᵉ matricesᵉ in whichᵉ allᵉ elementsᵉ areᵉ theᵉ same.ᵉ

## Definition

```agda
constant-matrixᵉ : {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {mᵉ nᵉ : ℕᵉ} → Aᵉ → matrixᵉ Aᵉ mᵉ nᵉ
constant-matrixᵉ aᵉ = constant-vecᵉ (constant-vecᵉ aᵉ)
```