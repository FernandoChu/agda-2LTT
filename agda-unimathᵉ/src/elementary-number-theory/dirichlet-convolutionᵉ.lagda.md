# Dirichlet convolution

```agda
module elementary-number-theory.dirichlet-convolutionᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.arithmetic-functionsᵉ
open import elementary-number-theory.bounded-sums-arithmetic-functionsᵉ
open import elementary-number-theory.modular-arithmetic-standard-finite-typesᵉ
open import elementary-number-theory.natural-numbersᵉ
open import elementary-number-theory.nonzero-natural-numbersᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.empty-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ

open import ring-theory.ringsᵉ
```

</details>

## Definition

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  dirichlet-convolution-arithmetic-functions-Ringᵉ :
    (fᵉ gᵉ : type-arithmetic-functions-Ringᵉ Rᵉ) →
    type-arithmetic-functions-Ringᵉ Rᵉ
  dirichlet-convolution-arithmetic-functions-Ringᵉ fᵉ gᵉ (pairᵉ zero-ℕᵉ Hᵉ) =
    ex-falsoᵉ (Hᵉ reflᵉ)
  dirichlet-convolution-arithmetic-functions-Ringᵉ fᵉ gᵉ (pairᵉ (succ-ℕᵉ nᵉ) Hᵉ) =
    bounded-sum-arithmetic-function-Ringᵉ Rᵉ
      ( succ-ℕᵉ nᵉ)
      ( λ xᵉ → div-ℕ-Decidable-Propᵉ (pr1ᵉ xᵉ) (succ-ℕᵉ nᵉ) (pr2ᵉ xᵉ))
      ( λ (xᵉ ,ᵉ Kᵉ) Hᵉ →
        mul-Ringᵉ Rᵉ
          ( fᵉ ( pairᵉ xᵉ Kᵉ))
          ( gᵉ ( quotient-div-nonzero-ℕᵉ xᵉ (succ-nonzero-ℕ'ᵉ nᵉ) Hᵉ)))
```