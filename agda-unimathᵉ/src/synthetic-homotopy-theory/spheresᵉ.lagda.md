# Spheres

```agda
module synthetic-homotopy-theory.spheresᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.function-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ

open import structured-types.pointed-typesᵉ

open import synthetic-homotopy-theory.iterated-suspensions-of-pointed-typesᵉ
open import synthetic-homotopy-theory.suspensions-of-typesᵉ

open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Theᵉ **spheres**ᵉ areᵉ definedᵉ asᵉ
[iteratedᵉ suspensions](synthetic-homotopy-theory.iterated-suspensions-of-pointed-types.mdᵉ)
ofᵉ theᵉ
[standardᵉ two-elementᵉ typeᵉ `Finᵉ 2`](univalent-combinatorics.standard-finite-types.md).ᵉ

## Definition

```agda
sphere-Pointed-Typeᵉ : ℕᵉ → Pointed-Typeᵉ lzero
sphere-Pointed-Typeᵉ nᵉ = iterated-suspension-Pointed-Typeᵉ nᵉ (Finᵉ 2 ,ᵉ zero-Finᵉ 1ᵉ)

sphereᵉ : ℕᵉ → UUᵉ lzero
sphereᵉ = type-Pointed-Typeᵉ ∘ᵉ sphere-Pointed-Typeᵉ

north-sphereᵉ : (nᵉ : ℕᵉ) → sphereᵉ nᵉ
north-sphereᵉ zero-ℕᵉ = zero-Finᵉ 1
north-sphereᵉ (succ-ℕᵉ nᵉ) = north-suspensionᵉ

south-sphereᵉ : (nᵉ : ℕᵉ) → sphereᵉ nᵉ
south-sphereᵉ zero-ℕᵉ = one-Finᵉ 1
south-sphereᵉ (succ-ℕᵉ nᵉ) = south-suspensionᵉ

meridian-sphereᵉ :
  (nᵉ : ℕᵉ) → sphereᵉ nᵉ → north-sphereᵉ (succ-ℕᵉ nᵉ) ＝ᵉ south-sphereᵉ (succ-ℕᵉ nᵉ)
meridian-sphereᵉ nᵉ = meridian-suspensionᵉ
```