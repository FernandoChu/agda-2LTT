# Cubes of natural numbers

```agda
module elementary-number-theory.cubes-natural-numbersᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.multiplication-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ
open import elementary-number-theory.squares-natural-numbersᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.fibers-of-mapsᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Theᵉ {{#conceptᵉ "cube"ᵉ Disambiguation="naturalᵉ number"ᵉ Agda=cube-ℕᵉ}} `n³`ᵉ ofᵉ aᵉ
[naturalᵉ number](elementary-number-theory.natural-numbers.mdᵉ) `n`ᵉ isᵉ theᵉ tripleᵉ
[product](elementary-number-theory.multiplication-natural-numbers.mdᵉ)

```text
  n³ᵉ :=ᵉ nᵉ *ᵉ nᵉ *ᵉ nᵉ
```

ofᵉ `n`ᵉ with itself.ᵉ

## Definitions

### Cubes of natural numbers

```agda
cube-ℕᵉ : ℕᵉ → ℕᵉ
cube-ℕᵉ nᵉ = square-ℕᵉ nᵉ *ℕᵉ nᵉ
```

### The predicate of being a cube of natural numbers

```agda
is-cube-ℕᵉ : ℕᵉ → UUᵉ lzero
is-cube-ℕᵉ = fiberᵉ cube-ℕᵉ
```

### The cubic root of cubic natural numbers

```agda
cubic-root-ℕᵉ : (nᵉ : ℕᵉ) → is-cube-ℕᵉ nᵉ → ℕᵉ
cubic-root-ℕᵉ nᵉ = pr1ᵉ
```

## See also

-ᵉ [Squaresᵉ ofᵉ naturalᵉ numbers](elementary-number-theory.squares-natural-numbers.mdᵉ)