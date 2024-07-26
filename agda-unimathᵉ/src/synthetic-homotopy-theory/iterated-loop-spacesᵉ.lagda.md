# Iterated loop spaces

```agda
module synthetic-homotopy-theory.iterated-loop-spacesᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.iterating-functionsᵉ
open import foundation.universe-levelsᵉ

open import structured-types.h-spacesᵉ
open import structured-types.pointed-typesᵉ

open import synthetic-homotopy-theory.loop-spacesᵉ
```

</details>

## Idea

Anᵉ **iteratedᵉ loopᵉ space**ᵉ `Ωⁿᵉ A`ᵉ isᵉ theᵉ
[pointedᵉ type](structured-types.pointed-types.mdᵉ) obtainedᵉ byᵉ `n`ᵉ timesᵉ
[iterating](foundation.iterating-functions.mdᵉ) theᵉ
[loopᵉ space](synthetic-homotopy-theory.loop-spaces.mdᵉ) functorᵉ
`Ωᵉ : Pointed-Typeᵉ → Pointed-Type`.ᵉ

## Definitions

### Iterated loop spaces

```agda
module _
  {lᵉ : Level}
  where

  iterated-loop-spaceᵉ : ℕᵉ → Pointed-Typeᵉ lᵉ → Pointed-Typeᵉ lᵉ
  iterated-loop-spaceᵉ nᵉ = iterateᵉ nᵉ Ωᵉ
```

### Iterated loop spaces of H-spaces

```agda
module _
  {lᵉ : Level}
  where

  iterated-loop-space-H-Spaceᵉ : ℕᵉ → H-Spaceᵉ lᵉ → H-Spaceᵉ lᵉ
  iterated-loop-space-H-Spaceᵉ zero-ℕᵉ Xᵉ = Xᵉ
  iterated-loop-space-H-Spaceᵉ (succ-ℕᵉ nᵉ) Xᵉ =
    Ω-H-Spaceᵉ (iterated-loop-spaceᵉ nᵉ (pointed-type-H-Spaceᵉ Xᵉ))
```

## See also

-ᵉ [Doubleᵉ loopᵉ spaces](synthetic-homotopy-theory.double-loop-spaces.mdᵉ)
-ᵉ [Tripleᵉ loopᵉ spaces](synthetic-homotopy-theory.triple-loop-spaces.mdᵉ)