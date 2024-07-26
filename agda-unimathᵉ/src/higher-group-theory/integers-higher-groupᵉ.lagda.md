# The higher group of integers

```agda
module higher-group-theory.integers-higher-groupᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import higher-group-theory.higher-groupsᵉ

open import structured-types.pointed-typesᵉ

open import synthetic-homotopy-theory.circleᵉ
```

</details>

## Idea

Theᵉ **higherᵉ groupᵉ ofᵉ integers**ᵉ isᵉ definedᵉ to beᵉ theᵉ
[circle](synthetic-homotopy-theory.circle.md).ᵉ Theᵉ
[loopᵉ space](synthetic-homotopy-theory.loop-spaces.mdᵉ) ofᵉ theᵉ circleᵉ isᵉ
[`ℤ`](elementary-number-theory.integers.md).ᵉ

## Definition

```agda
module _
  where

  classifying-type-ℤ-∞-Groupᵉ : UUᵉ lzero
  classifying-type-ℤ-∞-Groupᵉ = 𝕊¹ᵉ

  shape-ℤ-∞-Groupᵉ : 𝕊¹ᵉ
  shape-ℤ-∞-Groupᵉ = base-𝕊¹ᵉ

  classifying-pointed-type-ℤ-∞-Groupᵉ : Pointed-Typeᵉ lzero
  pr1ᵉ classifying-pointed-type-ℤ-∞-Groupᵉ = classifying-type-ℤ-∞-Groupᵉ
  pr2ᵉ classifying-pointed-type-ℤ-∞-Groupᵉ = shape-ℤ-∞-Groupᵉ

  ℤ-∞-Groupᵉ : ∞-Groupᵉ lzero
  pr1ᵉ ℤ-∞-Groupᵉ = classifying-pointed-type-ℤ-∞-Groupᵉ
  pr2ᵉ ℤ-∞-Groupᵉ = is-0-connected-𝕊¹ᵉ
```