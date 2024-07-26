# Premanifolds

```agda
module synthetic-homotopy-theory.premanifoldsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.commuting-squares-of-mapsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.mere-equivalencesᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import synthetic-homotopy-theory.cocones-under-spansᵉ
open import synthetic-homotopy-theory.mere-spheresᵉ
open import synthetic-homotopy-theory.pushoutsᵉ
open import synthetic-homotopy-theory.spheresᵉ
open import synthetic-homotopy-theory.tangent-spheresᵉ
```

</details>

## Idea

Anᵉ **`n`-dimensionalᵉ premanifold**ᵉ isᵉ aᵉ typeᵉ `M`ᵉ suchᵉ thatᵉ everyᵉ elementᵉ `xᵉ : M`ᵉ
comesᵉ equippedᵉ with aᵉ
[tangentᵉ `n`-sphere](synthetic-homotopy-theory.tangent-spheres.md).ᵉ

## Definitions

### Premanifolds

```agda
Premanifoldᵉ : (lᵉ : Level) (nᵉ : ℕᵉ) → UUᵉ (lsuc lᵉ)
Premanifoldᵉ lᵉ nᵉ = Σᵉ (UUᵉ lᵉ) (λ Mᵉ → (xᵉ : Mᵉ) → has-tangent-sphereᵉ nᵉ xᵉ)

module _
  {lᵉ : Level} (nᵉ : ℕᵉ) (Mᵉ : Premanifoldᵉ lᵉ nᵉ)
  where

  type-Premanifoldᵉ : UUᵉ lᵉ
  type-Premanifoldᵉ = pr1ᵉ Mᵉ

  tangent-sphere-Premanifoldᵉ : (xᵉ : type-Premanifoldᵉ) → mere-sphereᵉ lzero nᵉ
  tangent-sphere-Premanifoldᵉ xᵉ =
    tangent-sphere-has-tangent-sphereᵉ nᵉ (pr2ᵉ Mᵉ xᵉ)

  type-tangent-sphere-Premanifoldᵉ : (xᵉ : type-Premanifoldᵉ) → UUᵉ lzero
  type-tangent-sphere-Premanifoldᵉ xᵉ =
    type-tangent-sphere-has-tangent-sphereᵉ nᵉ (pr2ᵉ Mᵉ xᵉ)

  mere-equiv-tangent-sphere-Premanifoldᵉ :
    (xᵉ : type-Premanifoldᵉ) →
    mere-equivᵉ (sphereᵉ nᵉ) (type-tangent-sphere-Premanifoldᵉ xᵉ)
  mere-equiv-tangent-sphere-Premanifoldᵉ xᵉ =
    mere-equiv-tangent-sphere-has-tangent-sphereᵉ nᵉ (pr2ᵉ Mᵉ xᵉ)

  complement-Premanifoldᵉ : (xᵉ : type-Premanifoldᵉ) → UUᵉ lᵉ
  complement-Premanifoldᵉ xᵉ =
    complement-has-tangent-sphereᵉ nᵉ (pr2ᵉ Mᵉ xᵉ)

  inclusion-tangent-sphere-Premanifoldᵉ :
    (xᵉ : type-Premanifoldᵉ) →
    type-tangent-sphere-Premanifoldᵉ xᵉ → complement-Premanifoldᵉ xᵉ
  inclusion-tangent-sphere-Premanifoldᵉ xᵉ =
    inclusion-tangent-sphere-has-tangent-sphereᵉ nᵉ (pr2ᵉ Mᵉ xᵉ)

  inclusion-complement-Premanifoldᵉ :
    (xᵉ : type-Premanifoldᵉ) → complement-Premanifoldᵉ xᵉ → type-Premanifoldᵉ
  inclusion-complement-Premanifoldᵉ xᵉ =
    inclusion-complement-has-tangent-sphereᵉ nᵉ (pr2ᵉ Mᵉ xᵉ)

  coherence-square-Premanifoldᵉ :
    (xᵉ : type-Premanifoldᵉ) →
    coherence-square-mapsᵉ
      ( inclusion-tangent-sphere-Premanifoldᵉ xᵉ)
      ( terminal-mapᵉ (type-tangent-sphere-Premanifoldᵉ xᵉ))
      ( inclusion-complement-Premanifoldᵉ xᵉ)
      ( pointᵉ xᵉ)
  coherence-square-Premanifoldᵉ xᵉ =
    coherence-square-has-tangent-sphereᵉ nᵉ (pr2ᵉ Mᵉ xᵉ)

  cocone-Premanifoldᵉ :
    (xᵉ : type-Premanifoldᵉ) →
    coconeᵉ
      ( terminal-mapᵉ (type-tangent-sphere-Premanifoldᵉ xᵉ))
      ( inclusion-tangent-sphere-Premanifoldᵉ xᵉ)
      ( type-Premanifoldᵉ)
  cocone-Premanifoldᵉ xᵉ =
    cocone-has-tangent-sphereᵉ nᵉ (pr2ᵉ Mᵉ xᵉ)

  is-pushout-Premanifoldᵉ :
    (xᵉ : type-Premanifoldᵉ) →
    is-pushoutᵉ
      ( terminal-mapᵉ (type-tangent-sphere-Premanifoldᵉ xᵉ))
      ( inclusion-tangent-sphere-Premanifoldᵉ xᵉ)
      ( cocone-Premanifoldᵉ xᵉ)
  is-pushout-Premanifoldᵉ xᵉ =
    is-pushout-has-tangent-sphereᵉ nᵉ (pr2ᵉ Mᵉ xᵉ)
```