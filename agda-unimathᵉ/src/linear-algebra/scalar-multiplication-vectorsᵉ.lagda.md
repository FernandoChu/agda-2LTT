# Scalar multiplication of vectors

```agda
module linear-algebra.scalar-multiplication-vectorsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.universe-levelsᵉ

open import linear-algebra.functoriality-vectorsᵉ
open import linear-algebra.vectorsᵉ
```

</details>

## Idea

Anyᵉ operationᵉ `Bᵉ → Aᵉ → A`ᵉ forᵉ someᵉ typeᵉ `B`ᵉ ofᵉ formalᵉ scalarsᵉ inducesᵉ anᵉ
operationᵉ `Bᵉ → vecᵉ nᵉ Aᵉ → vecᵉ nᵉ A`.ᵉ

## Definition

```agda
scalar-mul-vecᵉ :
  {l1ᵉ l2ᵉ : Level} {Bᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {nᵉ : ℕᵉ} →
  (Bᵉ → Aᵉ → Aᵉ) → Bᵉ → vecᵉ Aᵉ nᵉ → vecᵉ Aᵉ nᵉ
scalar-mul-vecᵉ μᵉ xᵉ = map-vecᵉ (μᵉ xᵉ)
```