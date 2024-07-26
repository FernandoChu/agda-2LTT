# Iterated suspensions of pointed types

```agda
module synthetic-homotopy-theory.iterated-suspensions-of-pointed-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.iterating-functionsᵉ
open import foundation.universe-levelsᵉ

open import structured-types.pointed-typesᵉ

open import synthetic-homotopy-theory.suspensions-of-pointed-typesᵉ
```

</details>

## Idea

Givenᵉ aᵉ [pointedᵉ type](structured-types.pointed-types.mdᵉ) `X`ᵉ andᵉ aᵉ
[naturalᵉ number](elementary-number-theory.natural-numbers.mdᵉ) `n`,ᵉ weᵉ canᵉ formᵉ
theᵉ **`n`-iteratedᵉ suspension**ᵉ ofᵉ `X`.ᵉ

## Definitions

### The iterated suspension of a pointed type

```agda
iterated-suspension-Pointed-Typeᵉ :
  {lᵉ : Level} (nᵉ : ℕᵉ) → Pointed-Typeᵉ lᵉ → Pointed-Typeᵉ lᵉ
iterated-suspension-Pointed-Typeᵉ nᵉ = iterateᵉ nᵉ suspension-Pointed-Typeᵉ
```