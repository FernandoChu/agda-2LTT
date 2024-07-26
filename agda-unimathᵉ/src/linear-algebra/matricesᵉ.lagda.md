# Matrices

```agda
module linear-algebra.matricesᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.action-on-identifications-binary-functionsᵉ
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ

open import linear-algebra.functoriality-vectorsᵉ
open import linear-algebra.vectorsᵉ
```

</details>

## Idea

Anᵉ `(mᵉ ×ᵉ n)`-matrixᵉ ofᵉ elementsᵉ in `A`ᵉ isᵉ anᵉ arrangementᵉ ofᵉ elementsᵉ ofᵉ Aᵉ with
`m`ᵉ rowsᵉ andᵉ `n`ᵉ columns.ᵉ Inᵉ otherᵉ words,ᵉ aᵉ matrixᵉ isᵉ vectorᵉ ofᵉ lengthᵉ `m`ᵉ ofᵉ
vectorsᵉ ofᵉ lengthᵉ `n`ᵉ ofᵉ elementsᵉ ofᵉ `A`.ᵉ

## Definitions

### Matrices

```agda
matrixᵉ : {lᵉ : Level} (Aᵉ : UUᵉ lᵉ) → ℕᵉ → ℕᵉ → UUᵉ lᵉ
matrixᵉ Aᵉ mᵉ nᵉ = vecᵉ (vecᵉ Aᵉ nᵉ) mᵉ
```

### The top row of a matrix

```agda
top-row-matrixᵉ :
  {lᵉ : Level} {mᵉ nᵉ : ℕᵉ} {Aᵉ : UUᵉ lᵉ} → matrixᵉ Aᵉ (succ-ℕᵉ mᵉ) nᵉ → vecᵉ Aᵉ nᵉ
top-row-matrixᵉ (vᵉ ∷ᵉ Mᵉ) = vᵉ
```

### The left column of a matrix

```agda
left-column-matrixᵉ :
  {lᵉ : Level} {mᵉ nᵉ : ℕᵉ} {Aᵉ : UUᵉ lᵉ} → matrixᵉ Aᵉ mᵉ (succ-ℕᵉ nᵉ) → vecᵉ Aᵉ mᵉ
left-column-matrixᵉ = map-vecᵉ head-vecᵉ
```

### The vertical tail of a matrix

```agda
vertical-tail-matrixᵉ :
  {lᵉ : Level} {mᵉ nᵉ : ℕᵉ} {Aᵉ : UUᵉ lᵉ} → matrixᵉ Aᵉ (succ-ℕᵉ mᵉ) nᵉ → matrixᵉ Aᵉ mᵉ nᵉ
vertical-tail-matrixᵉ Mᵉ = tail-vecᵉ Mᵉ
```

### The horizontal tail of a matrix

```agda
horizontal-tail-matrixᵉ :
  {lᵉ : Level} {mᵉ nᵉ : ℕᵉ} {Aᵉ : UUᵉ lᵉ} → matrixᵉ Aᵉ mᵉ (succ-ℕᵉ nᵉ) → matrixᵉ Aᵉ mᵉ nᵉ
horizontal-tail-matrixᵉ = map-vecᵉ tail-vecᵉ
```

### The vertically empty matrix

```agda
vertically-empty-matrixᵉ :
  {lᵉ : Level} {nᵉ : ℕᵉ} {Aᵉ : UUᵉ lᵉ} → matrixᵉ Aᵉ 0 nᵉ
vertically-empty-matrixᵉ = empty-vecᵉ

eq-vertically-empty-matrixᵉ :
  {lᵉ : Level} {nᵉ : ℕᵉ} {Aᵉ : UUᵉ lᵉ}
  (xᵉ : matrixᵉ Aᵉ 0 nᵉ) → Idᵉ vertically-empty-matrixᵉ xᵉ
eq-vertically-empty-matrixᵉ empty-vecᵉ = reflᵉ

is-contr-matrix-zero-ℕᵉ :
  {lᵉ : Level} {nᵉ : ℕᵉ} {Aᵉ : UUᵉ lᵉ} → is-contrᵉ (matrixᵉ Aᵉ 0 nᵉ)
pr1ᵉ is-contr-matrix-zero-ℕᵉ = vertically-empty-matrixᵉ
pr2ᵉ is-contr-matrix-zero-ℕᵉ = eq-vertically-empty-matrixᵉ
```

### The horizontally empty matrix

```agda
horizontally-empty-matrixᵉ :
  {lᵉ : Level} {mᵉ : ℕᵉ} {Aᵉ : UUᵉ lᵉ} → matrixᵉ Aᵉ mᵉ 0
horizontally-empty-matrixᵉ {mᵉ = zero-ℕᵉ} = empty-vecᵉ
horizontally-empty-matrixᵉ {mᵉ = succ-ℕᵉ mᵉ} = empty-vecᵉ ∷ᵉ horizontally-empty-matrixᵉ

eq-horizontally-empty-matrixᵉ :
  {lᵉ : Level} {mᵉ : ℕᵉ} {Aᵉ : UUᵉ lᵉ}
  (xᵉ : matrixᵉ Aᵉ mᵉ 0ᵉ) → Idᵉ horizontally-empty-matrixᵉ xᵉ
eq-horizontally-empty-matrixᵉ {mᵉ = zero-ℕᵉ} empty-vecᵉ = reflᵉ
eq-horizontally-empty-matrixᵉ {mᵉ = succ-ℕᵉ mᵉ} (empty-vecᵉ ∷ᵉ Mᵉ) =
  ap-binaryᵉ _∷ᵉ_ reflᵉ (eq-horizontally-empty-matrixᵉ Mᵉ)

is-contr-matrix-zero-ℕ'ᵉ :
  {lᵉ : Level} {mᵉ : ℕᵉ} {Aᵉ : UUᵉ lᵉ} → is-contrᵉ (matrixᵉ Aᵉ mᵉ 0ᵉ)
pr1ᵉ is-contr-matrix-zero-ℕ'ᵉ = horizontally-empty-matrixᵉ
pr2ᵉ is-contr-matrix-zero-ℕ'ᵉ = eq-horizontally-empty-matrixᵉ
```