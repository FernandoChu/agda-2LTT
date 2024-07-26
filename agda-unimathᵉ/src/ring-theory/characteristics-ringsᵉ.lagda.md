# Characteristics of rings

```agda
module ring-theory.characteristics-ringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.ring-of-integersᵉ

open import foundation.universe-levelsᵉ

open import ring-theory.ideals-ringsᵉ
open import ring-theory.kernels-of-ring-homomorphismsᵉ
open import ring-theory.ringsᵉ
```

</details>

## Idea

Theᵉ **characteristic**ᵉ ofᵉ aᵉ [ring](ring-theory.rings.mdᵉ) `R`ᵉ isᵉ definedᵉ to beᵉ
theᵉ kernelᵉ ofᵉ theᵉ
[initialᵉ ringᵉ homomorphism](elementary-number-theory.ring-of-integers.mdᵉ) fromᵉ
theᵉ [ringᵉ `ℤ`ᵉ ofᵉ integers](elementary-number-theory.ring-of-integers.mdᵉ) to `R`.ᵉ

## Definitions

### Characteristics of rings

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  characteristic-Ringᵉ : ideal-Ringᵉ lᵉ ℤ-Ringᵉ
  characteristic-Ringᵉ = kernel-hom-Ringᵉ ℤ-Ringᵉ Rᵉ (initial-hom-Ringᵉ Rᵉ)
```