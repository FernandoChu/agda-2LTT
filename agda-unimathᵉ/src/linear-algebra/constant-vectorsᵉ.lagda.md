# Diagonal vectors

```agda
module linear-algebra.constant-vectorsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.universe-levelsᵉ

open import linear-algebra.vectorsᵉ
```

</details>

## Idea

Diagonalᵉ vectorsᵉ areᵉ vectorsᵉ onᵉ theᵉ diagonal,ᵉ i.e.,ᵉ theyᵉ areᵉ vectorsᵉ ofᵉ whichᵉ
allᵉ coefficientsᵉ areᵉ equal.ᵉ

## Definition

```agda
constant-vecᵉ : {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {nᵉ : ℕᵉ} → Aᵉ → vecᵉ Aᵉ nᵉ
constant-vecᵉ {nᵉ = zero-ℕᵉ} _ = empty-vecᵉ
constant-vecᵉ {nᵉ = succ-ℕᵉ nᵉ} xᵉ = xᵉ ∷ᵉ (constant-vecᵉ xᵉ)
```