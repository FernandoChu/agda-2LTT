# Sums of natural numbers

```agda
module elementary-number-theory.sums-of-natural-numbersᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbersᵉ
open import elementary-number-theory.multiplication-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ
open import elementary-number-theory.strict-inequality-natural-numbersᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.constant-mapsᵉ
open import foundation.coproduct-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ

open import lists.listsᵉ

open import univalent-combinatorics.countingᵉ
open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Theᵉ valuesᵉ ofᵉ aᵉ mapᵉ `fᵉ : Xᵉ → ℕ`ᵉ outᵉ ofᵉ aᵉ finiteᵉ typeᵉ `X`ᵉ canᵉ beᵉ summedᵉ up.ᵉ

## Definition

### Sums of lists of natural numbers

```agda
sum-list-ℕᵉ : listᵉ ℕᵉ → ℕᵉ
sum-list-ℕᵉ = fold-listᵉ 0 add-ℕᵉ
```

### Sums of natural numbers indexed by a standard finite type

```agda
sum-Fin-ℕᵉ : (kᵉ : ℕᵉ) → (Finᵉ kᵉ → ℕᵉ) → ℕᵉ
sum-Fin-ℕᵉ zero-ℕᵉ fᵉ = zero-ℕᵉ
sum-Fin-ℕᵉ (succ-ℕᵉ kᵉ) fᵉ = (sum-Fin-ℕᵉ kᵉ (λ xᵉ → fᵉ (inlᵉ xᵉ))) +ℕᵉ (fᵉ (inrᵉ starᵉ))
```

### Sums of natural numbers indexed by a type equipped with a counting

```agda
sum-count-ℕᵉ : {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} (eᵉ : countᵉ Aᵉ) → (fᵉ : Aᵉ → ℕᵉ) → ℕᵉ
sum-count-ℕᵉ (pairᵉ kᵉ eᵉ) fᵉ = sum-Fin-ℕᵉ kᵉ (fᵉ ∘ᵉ (map-equivᵉ eᵉ))
```

### Bounded sums of natural numbers

```agda
bounded-sum-ℕᵉ : (uᵉ : ℕᵉ) → ((xᵉ : ℕᵉ) → le-ℕᵉ xᵉ uᵉ → ℕᵉ) → ℕᵉ
bounded-sum-ℕᵉ zero-ℕᵉ fᵉ = zero-ℕᵉ
bounded-sum-ℕᵉ (succ-ℕᵉ uᵉ) fᵉ =
  add-ℕᵉ
    ( bounded-sum-ℕᵉ uᵉ (λ xᵉ Hᵉ → fᵉ xᵉ (preserves-le-succ-ℕᵉ xᵉ uᵉ Hᵉ)))
    ( fᵉ uᵉ (succ-le-ℕᵉ uᵉ))
```

## Properties

### Sums are invariant under homotopy

```agda
abstract
  htpy-sum-Fin-ℕᵉ :
    (kᵉ : ℕᵉ) {fᵉ gᵉ : Finᵉ kᵉ → ℕᵉ} (Hᵉ : fᵉ ~ᵉ gᵉ) → sum-Fin-ℕᵉ kᵉ fᵉ ＝ᵉ sum-Fin-ℕᵉ kᵉ gᵉ
  htpy-sum-Fin-ℕᵉ zero-ℕᵉ Hᵉ = reflᵉ
  htpy-sum-Fin-ℕᵉ (succ-ℕᵉ kᵉ) Hᵉ =
    ap-add-ℕᵉ
      ( htpy-sum-Fin-ℕᵉ kᵉ (λ xᵉ → Hᵉ (inlᵉ xᵉ)))
      ( Hᵉ (inrᵉ starᵉ))

abstract
  htpy-sum-count-ℕᵉ :
    {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} (eᵉ : countᵉ Aᵉ) {fᵉ gᵉ : Aᵉ → ℕᵉ} (Hᵉ : fᵉ ~ᵉ gᵉ) →
    sum-count-ℕᵉ eᵉ fᵉ ＝ᵉ sum-count-ℕᵉ eᵉ gᵉ
  htpy-sum-count-ℕᵉ (pairᵉ kᵉ eᵉ) Hᵉ = htpy-sum-Fin-ℕᵉ kᵉ (Hᵉ ·rᵉ (map-equivᵉ eᵉ))
```

### Summing up the same value `m` times is multiplication by `m`

```agda
abstract
  constant-sum-Fin-ℕᵉ :
    (mᵉ nᵉ : ℕᵉ) → sum-Fin-ℕᵉ mᵉ (constᵉ (Finᵉ mᵉ) nᵉ) ＝ᵉ mᵉ *ℕᵉ nᵉ
  constant-sum-Fin-ℕᵉ zero-ℕᵉ nᵉ = reflᵉ
  constant-sum-Fin-ℕᵉ (succ-ℕᵉ mᵉ) nᵉ = apᵉ (_+ℕᵉ nᵉ) (constant-sum-Fin-ℕᵉ mᵉ nᵉ)

abstract
  constant-sum-count-ℕᵉ :
    {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} (eᵉ : countᵉ Aᵉ) (nᵉ : ℕᵉ) →
    sum-count-ℕᵉ eᵉ (constᵉ Aᵉ nᵉ) ＝ᵉ (number-of-elements-countᵉ eᵉ) *ℕᵉ nᵉ
  constant-sum-count-ℕᵉ (pairᵉ mᵉ eᵉ) nᵉ = constant-sum-Fin-ℕᵉ mᵉ nᵉ
```

### Each of the summands is less than or equal to the total sum

```text
leq-sum-Fin-ℕᵉ :
  {kᵉ : ℕᵉ} (fᵉ : Finᵉ kᵉ → ℕᵉ) (xᵉ : Finᵉ kᵉ) → leq-ℕᵉ (fᵉ xᵉ) (sum-Fin-ℕᵉ fᵉ)
leq-sum-Fin-ℕᵉ {succ-ℕᵉ kᵉ} fᵉ xᵉ = {!leq-add-ℕ!ᵉ}
```