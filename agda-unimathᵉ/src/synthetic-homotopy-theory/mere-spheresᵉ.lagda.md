# Mere spheres

```agda
module synthetic-homotopy-theory.mere-spheresᵉ where
```

<details></summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.mere-equivalencesᵉ
open import foundation.propositionsᵉ
open import foundation.universe-levelsᵉ

open import synthetic-homotopy-theory.spheresᵉ
```

</details>

## Idea

Aᵉ **mereᵉ `n`-sphere**ᵉ isᵉ aᵉ typeᵉ `X`ᵉ thatᵉ isᵉ
[merelyᵉ equivalent](foundation.mere-equivalences.mdᵉ) to theᵉ
[`n`-sphere](synthetic-homotopy-theory.spheres.md).ᵉ

## Definitions

### The predicate of being a mere `n`-sphere

```agda
module _
  {lᵉ : Level} (nᵉ : ℕᵉ) (Xᵉ : UUᵉ lᵉ)
  where

  is-mere-sphere-Propᵉ : Propᵉ lᵉ
  is-mere-sphere-Propᵉ = mere-equiv-Propᵉ (sphereᵉ nᵉ) Xᵉ

  is-mere-sphereᵉ : UUᵉ lᵉ
  is-mere-sphereᵉ = type-Propᵉ is-mere-sphere-Propᵉ

  is-prop-is-mere-sphereᵉ : is-propᵉ is-mere-sphereᵉ
  is-prop-is-mere-sphereᵉ = is-prop-type-Propᵉ is-mere-sphere-Propᵉ
```

### Mere spheres

```agda
mere-sphereᵉ : (lᵉ : Level) (nᵉ : ℕᵉ) → UUᵉ (lsuc lᵉ)
mere-sphereᵉ lᵉ nᵉ = Σᵉ (UUᵉ lᵉ) (is-mere-sphereᵉ nᵉ)

module _
  {lᵉ : Level} (nᵉ : ℕᵉ) (Xᵉ : mere-sphereᵉ lᵉ nᵉ)
  where

  type-mere-sphereᵉ : UUᵉ lᵉ
  type-mere-sphereᵉ = pr1ᵉ Xᵉ

  mere-equiv-mere-sphereᵉ : mere-equivᵉ (sphereᵉ nᵉ) type-mere-sphereᵉ
  mere-equiv-mere-sphereᵉ = pr2ᵉ Xᵉ
```