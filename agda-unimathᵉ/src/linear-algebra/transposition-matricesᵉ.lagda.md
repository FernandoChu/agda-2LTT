# Transposition of matrices

```agda
module linear-algebra.transposition-matricesᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.action-on-identifications-binary-functionsᵉ
open import foundation.action-on-identifications-functionsᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ

open import linear-algebra.functoriality-vectorsᵉ
open import linear-algebra.matricesᵉ
open import linear-algebra.vectorsᵉ
```

</details>

## Idea

Theᵉ transpositionᵉ ofᵉ aᵉ matrixᵉ isᵉ theᵉ operationᵉ thatᵉ turnsᵉ rowsᵉ intoᵉ columnsᵉ andᵉ
columnsᵉ intoᵉ rows.ᵉ

## Definition

```agda
transpose-matrixᵉ :
  {lᵉ : Level} → {Aᵉ : UUᵉ lᵉ} → {mᵉ nᵉ : ℕᵉ} → matrixᵉ Aᵉ mᵉ nᵉ → matrixᵉ Aᵉ nᵉ mᵉ
transpose-matrixᵉ {nᵉ = zero-ℕᵉ} xᵉ = empty-vecᵉ
transpose-matrixᵉ {nᵉ = succ-ℕᵉ nᵉ} xᵉ =
  map-vecᵉ head-vecᵉ xᵉ ∷ᵉ transpose-matrixᵉ (map-vecᵉ tail-vecᵉ xᵉ)
```

## Properties

```agda
is-involution-transpose-matrixᵉ :
  {lᵉ : Level} → {Aᵉ : UUᵉ lᵉ} → {mᵉ nᵉ : ℕᵉ} →
  (xᵉ : matrixᵉ Aᵉ mᵉ nᵉ) → Idᵉ xᵉ (transpose-matrixᵉ (transpose-matrixᵉ xᵉ))
is-involution-transpose-matrixᵉ {mᵉ = zero-ℕᵉ} empty-vecᵉ = reflᵉ
is-involution-transpose-matrixᵉ {mᵉ = succ-ℕᵉ mᵉ} (rᵉ ∷ᵉ rsᵉ) =
  ( apᵉ (_∷ᵉ_ rᵉ) (is-involution-transpose-matrixᵉ rsᵉ)) ∙ᵉ
  ( ap-binaryᵉ _∷ᵉ_
    ( lemma-first-rowᵉ rᵉ rsᵉ) (apᵉ transpose-matrixᵉ (lemma-restᵉ rᵉ rsᵉ)))
  where
  lemma-first-rowᵉ :
    {lᵉ : Level} → {Aᵉ : UUᵉ lᵉ} → {mᵉ nᵉ : ℕᵉ} → (xᵉ : vecᵉ Aᵉ nᵉ) → (xsᵉ : matrixᵉ Aᵉ mᵉ nᵉ) →
    Idᵉ xᵉ (map-vecᵉ head-vecᵉ (transpose-matrixᵉ (xᵉ ∷ᵉ xsᵉ)))
  lemma-first-rowᵉ {nᵉ = zero-ℕᵉ} empty-vecᵉ _ = reflᵉ
  lemma-first-rowᵉ {nᵉ = succ-ℕᵉ mᵉ} (kᵉ ∷ᵉ ksᵉ) xsᵉ =
    apᵉ (_∷ᵉ_ kᵉ) (lemma-first-rowᵉ ksᵉ (map-vecᵉ tail-vecᵉ xsᵉ))

  lemma-restᵉ :
    {lᵉ : Level} → {Aᵉ : UUᵉ lᵉ} → {mᵉ nᵉ : ℕᵉ} → (xᵉ : vecᵉ Aᵉ nᵉ) → (xsᵉ : matrixᵉ Aᵉ mᵉ nᵉ) →
    Idᵉ (transpose-matrixᵉ xsᵉ) (map-vecᵉ tail-vecᵉ (transpose-matrixᵉ (xᵉ ∷ᵉ xsᵉ)))
  lemma-restᵉ {nᵉ = zero-ℕᵉ} empty-vecᵉ xsᵉ = reflᵉ
  lemma-restᵉ {nᵉ = succ-ℕᵉ nᵉ} (kᵉ ∷ᵉ ksᵉ) xsᵉ =
    apᵉ
      ( _∷ᵉ_ (map-vecᵉ head-vecᵉ xsᵉ))
      ( lemma-restᵉ (tail-vecᵉ (kᵉ ∷ᵉ ksᵉ)) (map-vecᵉ tail-vecᵉ xsᵉ))
```