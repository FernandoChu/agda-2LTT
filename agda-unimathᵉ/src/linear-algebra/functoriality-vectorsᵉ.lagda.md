# Functoriality of the type of vectors

```agda
module linear-algebra.functoriality-vectorsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.action-on-identifications-binary-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.function-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.postcomposition-functionsᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ

open import linear-algebra.vectorsᵉ

open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Anyᵉ mapᵉ `fᵉ : Aᵉ → B`ᵉ determinesᵉ aᵉ mapᵉ `vecᵉ Aᵉ nᵉ → vecᵉ Bᵉ n`ᵉ forᵉ everyᵉ `n`.ᵉ

## Definition

### Functoriality of the type of listed vectors

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  map-vecᵉ : {nᵉ : ℕᵉ} → (Aᵉ → Bᵉ) → vecᵉ Aᵉ nᵉ → vecᵉ Bᵉ nᵉ
  map-vecᵉ _ empty-vecᵉ = empty-vecᵉ
  map-vecᵉ fᵉ (xᵉ ∷ᵉ xsᵉ) = fᵉ xᵉ ∷ᵉ map-vecᵉ fᵉ xsᵉ

  htpy-vecᵉ :
    {nᵉ : ℕᵉ} {fᵉ gᵉ : Aᵉ → Bᵉ} → (fᵉ ~ᵉ gᵉ) → map-vecᵉ {nᵉ = nᵉ} fᵉ ~ᵉ map-vecᵉ {nᵉ = nᵉ} gᵉ
  htpy-vecᵉ Hᵉ empty-vecᵉ = reflᵉ
  htpy-vecᵉ Hᵉ (xᵉ ∷ᵉ vᵉ) = ap-binaryᵉ _∷ᵉ_ (Hᵉ xᵉ) (htpy-vecᵉ Hᵉ vᵉ)
```

### Binary functoriality of the type of listed vectors

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ}
  where

  binary-map-vecᵉ :
    {nᵉ : ℕᵉ} → (Aᵉ → Bᵉ → Cᵉ) → vecᵉ Aᵉ nᵉ → vecᵉ Bᵉ nᵉ → vecᵉ Cᵉ nᵉ
  binary-map-vecᵉ fᵉ empty-vecᵉ empty-vecᵉ = empty-vecᵉ
  binary-map-vecᵉ fᵉ (xᵉ ∷ᵉ vᵉ) (yᵉ ∷ᵉ wᵉ) = fᵉ xᵉ yᵉ ∷ᵉ binary-map-vecᵉ fᵉ vᵉ wᵉ
```

### Functoriality of the type of functional vectors

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  map-functional-vecᵉ :
    (nᵉ : ℕᵉ) → (Aᵉ → Bᵉ) → functional-vecᵉ Aᵉ nᵉ → functional-vecᵉ Bᵉ nᵉ
  map-functional-vecᵉ nᵉ fᵉ vᵉ = fᵉ ∘ᵉ vᵉ

  htpy-functional-vecᵉ :
    (nᵉ : ℕᵉ) {fᵉ gᵉ : Aᵉ → Bᵉ} → (fᵉ ~ᵉ gᵉ) →
    map-functional-vecᵉ nᵉ fᵉ ~ᵉ map-functional-vecᵉ nᵉ gᵉ
  htpy-functional-vecᵉ nᵉ = htpy-postcompᵉ (Finᵉ nᵉ)
```

### Binary functoriality of the type of functional vectors

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ}
  where

  binary-map-functional-vecᵉ :
    (nᵉ : ℕᵉ) → (Aᵉ → Bᵉ → Cᵉ) →
    functional-vecᵉ Aᵉ nᵉ → functional-vecᵉ Bᵉ nᵉ → functional-vecᵉ Cᵉ nᵉ
  binary-map-functional-vecᵉ nᵉ fᵉ vᵉ wᵉ iᵉ = fᵉ (vᵉ iᵉ) (wᵉ iᵉ)
```

### Link between functoriality of the type of vectors and of the type of functional vectors

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  (fᵉ : Aᵉ → Bᵉ)
  where

  map-vec-map-functional-vecᵉ :
    (nᵉ : ℕᵉ) (vᵉ : vecᵉ Aᵉ nᵉ) →
    listed-vec-functional-vecᵉ
      ( nᵉ)
      ( map-functional-vecᵉ nᵉ fᵉ (functional-vec-vecᵉ nᵉ vᵉ)) ＝ᵉ
    map-vecᵉ fᵉ vᵉ
  map-vec-map-functional-vecᵉ zero-ℕᵉ empty-vecᵉ = reflᵉ
  map-vec-map-functional-vecᵉ (succ-ℕᵉ nᵉ) (xᵉ ∷ᵉ vᵉ) =
    eq-Eq-vecᵉ
      ( succ-ℕᵉ nᵉ)
      ( listed-vec-functional-vecᵉ
        ( succ-ℕᵉ nᵉ)
        ( map-functional-vecᵉ
          ( succ-ℕᵉ nᵉ)
          ( fᵉ)
          ( functional-vec-vecᵉ (succ-ℕᵉ nᵉ) (xᵉ ∷ᵉ vᵉ))))
      ( map-vecᵉ fᵉ (xᵉ ∷ᵉ vᵉ))
      ( reflᵉ ,ᵉ
        Eq-eq-vecᵉ
          ( nᵉ)
          ( listed-vec-functional-vecᵉ
            ( nᵉ)
            ( map-functional-vecᵉ nᵉ fᵉ (functional-vec-vecᵉ nᵉ vᵉ)))
          ( map-vecᵉ fᵉ vᵉ)
          ( map-vec-map-functional-vecᵉ nᵉ vᵉ))
```