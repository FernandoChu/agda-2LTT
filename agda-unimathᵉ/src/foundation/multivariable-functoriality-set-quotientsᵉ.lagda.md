# Multivariable functoriality of set quotients

```agda
module foundation.multivariable-functoriality-set-quotientsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.functoriality-set-quotientsᵉ
open import foundation.set-quotientsᵉ
open import foundation.universe-levelsᵉ
open import foundation.vectors-set-quotientsᵉ

open import foundation-core.equivalence-relationsᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.homotopiesᵉ

open import linear-algebra.vectorsᵉ

open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Sayᵉ weᵉ haveᵉ aᵉ familyᵉ ofᵉ typesᵉ `A1`,ᵉ ...,ᵉ `An`ᵉ eachᵉ equippedᵉ with anᵉ equivalenceᵉ
relationᵉ `Ri`,ᵉ asᵉ wellᵉ asᵉ aᵉ typeᵉ `X`ᵉ equippedᵉ with anᵉ equivalenceᵉ relationᵉ `S`,ᵉ
Then,ᵉ anyᵉ multivariableᵉ operationᵉ fromᵉ theᵉ `Ai`sᵉ to theᵉ `X`ᵉ thatᵉ respectsᵉ theᵉ
equivalenceᵉ relationsᵉ extendsᵉ uniquelyᵉ to aᵉ multivariableᵉ operationᵉ fromᵉ theᵉ
`Ai/Ri`sᵉ to `X/S`.ᵉ

## Definition

### `n`-ary hom of equivalence relation

```agda
module _
  { l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  ( nᵉ : ℕᵉ)
  ( Aᵉ : functional-vecᵉ (UUᵉ l1ᵉ) nᵉ)
  ( Rᵉ : (iᵉ : Finᵉ nᵉ) → equivalence-relationᵉ l2ᵉ (Aᵉ iᵉ))
  { Xᵉ : UUᵉ l3ᵉ} (Sᵉ : equivalence-relationᵉ l4ᵉ Xᵉ)
  where

  multivariable-map-set-quotientᵉ :
    ( hᵉ : hom-equivalence-relationᵉ (all-sim-equivalence-relationᵉ nᵉ Aᵉ Rᵉ) Sᵉ) →
    set-quotient-vectorᵉ nᵉ Aᵉ Rᵉ → set-quotientᵉ Sᵉ
  multivariable-map-set-quotientᵉ =
    map-is-set-quotientᵉ
      ( all-sim-equivalence-relationᵉ nᵉ Aᵉ Rᵉ)
      ( set-quotient-vector-Setᵉ nᵉ Aᵉ Rᵉ)
      ( reflecting-map-quotient-vector-mapᵉ nᵉ Aᵉ Rᵉ)
      ( Sᵉ)
      ( quotient-Setᵉ Sᵉ)
      ( reflecting-map-quotient-mapᵉ Sᵉ)
      ( is-set-quotient-vector-set-quotientᵉ nᵉ Aᵉ Rᵉ)
      ( is-set-quotient-set-quotientᵉ Sᵉ)

  compute-multivariable-map-set-quotientᵉ :
    ( hᵉ : hom-equivalence-relationᵉ (all-sim-equivalence-relationᵉ nᵉ Aᵉ Rᵉ) Sᵉ) →
    ( multivariable-map-set-quotientᵉ hᵉ ∘ᵉ
      quotient-vector-mapᵉ nᵉ Aᵉ Rᵉ) ~ᵉ
    ( quotient-mapᵉ Sᵉ ∘ᵉ
      map-hom-equivalence-relationᵉ (all-sim-equivalence-relationᵉ nᵉ Aᵉ Rᵉ) Sᵉ hᵉ)
  compute-multivariable-map-set-quotientᵉ =
    coherence-square-map-is-set-quotientᵉ
      ( all-sim-equivalence-relationᵉ nᵉ Aᵉ Rᵉ)
      ( set-quotient-vector-Setᵉ nᵉ Aᵉ Rᵉ)
      ( reflecting-map-quotient-vector-mapᵉ nᵉ Aᵉ Rᵉ)
      ( Sᵉ)
      ( quotient-Setᵉ Sᵉ)
      ( reflecting-map-quotient-mapᵉ Sᵉ)
      ( is-set-quotient-vector-set-quotientᵉ nᵉ Aᵉ Rᵉ)
      ( is-set-quotient-set-quotientᵉ Sᵉ)
```