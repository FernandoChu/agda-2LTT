# The monoid of the natural numbers with maximum

```agda
module elementary-number-theory.monoid-of-natural-numbers-with-maximumᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.equality-natural-numbersᵉ
open import elementary-number-theory.initial-segments-natural-numbersᵉ
open import elementary-number-theory.maximum-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import group-theory.commutative-monoidsᵉ
open import group-theory.monoidsᵉ
open import group-theory.normal-submonoids-commutative-monoidsᵉ
open import group-theory.semigroupsᵉ
open import group-theory.submonoids-commutative-monoidsᵉ
```

</details>

## Idea

Theᵉ typeᵉ `ℕ`ᵉ ofᵉ naturalᵉ numbersᵉ equippedᵉ with `0`ᵉ andᵉ `max-ℕ`ᵉ formsᵉ aᵉ monoid.ᵉ
Normalᵉ submonoidsᵉ ofᵉ thisᵉ monoidᵉ areᵉ initialᵉ segmentsᵉ ofᵉ theᵉ naturalᵉ numbers.ᵉ
Furthermore,ᵉ theᵉ identityᵉ relationᵉ isᵉ aᵉ nonsaturatedᵉ congruenceᵉ relationᵉ onᵉ
`ℕ-Max`.ᵉ

## Definition

```agda
semigroup-ℕ-Maxᵉ : Semigroupᵉ lzero
pr1ᵉ semigroup-ℕ-Maxᵉ = ℕ-Setᵉ
pr1ᵉ (pr2ᵉ semigroup-ℕ-Maxᵉ) = max-ℕᵉ
pr2ᵉ (pr2ᵉ semigroup-ℕ-Maxᵉ) = associative-max-ℕᵉ

monoid-ℕ-Maxᵉ : Monoidᵉ lzero
pr1ᵉ monoid-ℕ-Maxᵉ = semigroup-ℕ-Maxᵉ
pr1ᵉ (pr2ᵉ monoid-ℕ-Maxᵉ) = 0
pr1ᵉ (pr2ᵉ (pr2ᵉ monoid-ℕ-Maxᵉ)) = left-unit-law-max-ℕᵉ
pr2ᵉ (pr2ᵉ (pr2ᵉ monoid-ℕ-Maxᵉ)) = right-unit-law-max-ℕᵉ

ℕ-Maxᵉ : Commutative-Monoidᵉ lzero
pr1ᵉ ℕ-Maxᵉ = monoid-ℕ-Maxᵉ
pr2ᵉ ℕ-Maxᵉ = commutative-max-ℕᵉ
```

## Properties

### Normal Submonoids of `ℕ-Max` are initial segments of the natural numbers

```agda
module _
  {lᵉ : Level} (Nᵉ : Normal-Commutative-Submonoidᵉ lᵉ ℕ-Maxᵉ)
  where

  is-initial-segment-Normal-Commutative-Submonoid-ℕ-Maxᵉ :
    is-initial-segment-subset-ℕᵉ
      ( subset-Normal-Commutative-Submonoidᵉ ℕ-Maxᵉ Nᵉ)
  is-initial-segment-Normal-Commutative-Submonoid-ℕ-Maxᵉ xᵉ Hᵉ =
      ( is-normal-Normal-Commutative-Submonoidᵉ ℕ-Maxᵉ Nᵉ xᵉ
        ( succ-ℕᵉ xᵉ)
        ( Hᵉ))
      ( is-closed-under-eq-Normal-Commutative-Submonoid'ᵉ
        ( ℕ-Maxᵉ)
        ( Nᵉ)
        ( Hᵉ)
        ( right-successor-diagonal-law-max-ℕᵉ xᵉ))

  initial-segment-Normal-Submonoid-ℕ-Maxᵉ : initial-segment-ℕᵉ lᵉ
  pr1ᵉ initial-segment-Normal-Submonoid-ℕ-Maxᵉ =
    subset-Normal-Commutative-Submonoidᵉ ℕ-Maxᵉ Nᵉ
  pr2ᵉ initial-segment-Normal-Submonoid-ℕ-Maxᵉ =
    is-initial-segment-Normal-Commutative-Submonoid-ℕ-Maxᵉ
```

### Initial segments of the natural numbers are normal submonoids of `ℕ-Max`

```agda
submonoid-initial-segment-ℕ-Maxᵉ :
  {lᵉ : Level} (Iᵉ : initial-segment-ℕᵉ lᵉ) (i0ᵉ : is-in-initial-segment-ℕᵉ Iᵉ 0ᵉ) →
  Commutative-Submonoidᵉ lᵉ ℕ-Maxᵉ
pr1ᵉ (submonoid-initial-segment-ℕ-Maxᵉ Iᵉ i0ᵉ) = subset-initial-segment-ℕᵉ Iᵉ
pr1ᵉ (pr2ᵉ (submonoid-initial-segment-ℕ-Maxᵉ Iᵉ i0ᵉ)) = i0ᵉ
pr2ᵉ (pr2ᵉ (submonoid-initial-segment-ℕ-Maxᵉ Iᵉ i0ᵉ)) = max-initial-segment-ℕᵉ Iᵉ

is-normal-submonoid-initial-segment-ℕ-Maxᵉ :
  {lᵉ : Level} (Iᵉ : initial-segment-ℕᵉ lᵉ) (i0ᵉ : is-in-initial-segment-ℕᵉ Iᵉ 0ᵉ) →
  is-normal-Commutative-Submonoidᵉ
    ℕ-Maxᵉ
    (submonoid-initial-segment-ℕ-Maxᵉ Iᵉ i0ᵉ)
is-normal-submonoid-initial-segment-ℕ-Maxᵉ Iᵉ i0ᵉ uᵉ zero-ℕᵉ Hᵉ Kᵉ =
  is-closed-under-eq-Commutative-Submonoidᵉ
    ( ℕ-Maxᵉ)
    ( submonoid-initial-segment-ℕ-Maxᵉ Iᵉ i0ᵉ)
    ( Kᵉ)
    ( right-unit-law-max-ℕᵉ uᵉ)
is-normal-submonoid-initial-segment-ℕ-Maxᵉ Iᵉ i0ᵉ zero-ℕᵉ (succ-ℕᵉ xᵉ) Hᵉ Kᵉ = i0ᵉ
is-normal-submonoid-initial-segment-ℕ-Maxᵉ Iᵉ i0ᵉ (succ-ℕᵉ uᵉ) (succ-ℕᵉ xᵉ) Hᵉ Kᵉ =
  is-normal-submonoid-initial-segment-ℕ-Maxᵉ
    ( shift-initial-segment-ℕᵉ Iᵉ)
    ( contains-one-initial-segment-ℕᵉ Iᵉ (max-ℕᵉ uᵉ xᵉ) Kᵉ)
    ( uᵉ)
    ( xᵉ)
    ( Hᵉ)
    ( Kᵉ)
```