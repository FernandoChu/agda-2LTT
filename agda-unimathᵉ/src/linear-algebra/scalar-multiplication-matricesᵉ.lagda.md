# Scalar multiplication on matrices

```agda
module linear-algebra.scalar-multiplication-matricesᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.universe-levelsᵉ

open import linear-algebra.matricesᵉ
open import linear-algebra.scalar-multiplication-vectorsᵉ
```

</details>

```agda
scalar-mul-matrixᵉ :
  {l1ᵉ l2ᵉ : Level} {Bᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {mᵉ nᵉ : ℕᵉ} →
  (Bᵉ → Aᵉ → Aᵉ) → Bᵉ → matrixᵉ Aᵉ mᵉ nᵉ → matrixᵉ Aᵉ mᵉ nᵉ
scalar-mul-matrixᵉ μᵉ = scalar-mul-vecᵉ (scalar-mul-vecᵉ μᵉ)
```