# Initial segments of the natural numbers

```agda
module elementary-number-theory.initial-segments-natural-numbersᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.maximum-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.function-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.subtypesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Anᵉ **initialᵉ segment**ᵉ ofᵉ theᵉ naturalᵉ numbersᵉ isᵉ aᵉ subtypeᵉ `Pᵉ : ℕᵉ → Prop`ᵉ suchᵉ
thatᵉ theᵉ implicationᵉ

```text
  Pᵉ (nᵉ +ᵉ 1ᵉ) → Pᵉ nᵉ
```

holdsᵉ forᵉ everyᵉ `nᵉ : ℕ`.ᵉ

## Definitions

### Initial segments

```agda
is-initial-segment-subset-ℕ-Propᵉ : {lᵉ : Level} (Pᵉ : subtypeᵉ lᵉ ℕᵉ) → Propᵉ lᵉ
is-initial-segment-subset-ℕ-Propᵉ Pᵉ =
  Π-Propᵉ ℕᵉ (λ nᵉ → hom-Propᵉ (Pᵉ (succ-ℕᵉ nᵉ)) (Pᵉ nᵉ))

is-initial-segment-subset-ℕᵉ : {lᵉ : Level} (Pᵉ : subtypeᵉ lᵉ ℕᵉ) → UUᵉ lᵉ
is-initial-segment-subset-ℕᵉ Pᵉ = type-Propᵉ (is-initial-segment-subset-ℕ-Propᵉ Pᵉ)

initial-segment-ℕᵉ : (lᵉ : Level) → UUᵉ (lsuc lᵉ)
initial-segment-ℕᵉ lᵉ = type-subtypeᵉ is-initial-segment-subset-ℕ-Propᵉ

module _
  {lᵉ : Level} (Iᵉ : initial-segment-ℕᵉ lᵉ)
  where

  subset-initial-segment-ℕᵉ : subtypeᵉ lᵉ ℕᵉ
  subset-initial-segment-ℕᵉ = pr1ᵉ Iᵉ

  is-initial-segment-initial-segment-ℕᵉ :
    is-initial-segment-subset-ℕᵉ subset-initial-segment-ℕᵉ
  is-initial-segment-initial-segment-ℕᵉ = pr2ᵉ Iᵉ

  is-in-initial-segment-ℕᵉ : ℕᵉ → UUᵉ lᵉ
  is-in-initial-segment-ℕᵉ = is-in-subtypeᵉ subset-initial-segment-ℕᵉ

  is-closed-under-eq-initial-segment-ℕᵉ :
    {xᵉ yᵉ : ℕᵉ} → is-in-initial-segment-ℕᵉ xᵉ → xᵉ ＝ᵉ yᵉ → is-in-initial-segment-ℕᵉ yᵉ
  is-closed-under-eq-initial-segment-ℕᵉ =
    is-closed-under-eq-subtypeᵉ subset-initial-segment-ℕᵉ

  is-closed-under-eq-initial-segment-ℕ'ᵉ :
    {xᵉ yᵉ : ℕᵉ} → is-in-initial-segment-ℕᵉ yᵉ → xᵉ ＝ᵉ yᵉ → is-in-initial-segment-ℕᵉ xᵉ
  is-closed-under-eq-initial-segment-ℕ'ᵉ =
    is-closed-under-eq-subtype'ᵉ subset-initial-segment-ℕᵉ
```

### Shifting initial segments

```agda
shift-initial-segment-ℕᵉ :
  {lᵉ : Level} → initial-segment-ℕᵉ lᵉ → initial-segment-ℕᵉ lᵉ
pr1ᵉ (shift-initial-segment-ℕᵉ Iᵉ) = subset-initial-segment-ℕᵉ Iᵉ ∘ᵉ succ-ℕᵉ
pr2ᵉ (shift-initial-segment-ℕᵉ Iᵉ) =
  is-initial-segment-initial-segment-ℕᵉ Iᵉ ∘ᵉ succ-ℕᵉ
```

## Properties

### Inhabited initial segments contain `0`

```agda
contains-zero-initial-segment-ℕᵉ :
  {lᵉ : Level} (Iᵉ : initial-segment-ℕᵉ lᵉ) →
  (xᵉ : ℕᵉ) → is-in-initial-segment-ℕᵉ Iᵉ xᵉ → is-in-initial-segment-ℕᵉ Iᵉ 0
contains-zero-initial-segment-ℕᵉ Iᵉ zero-ℕᵉ Hᵉ = Hᵉ
contains-zero-initial-segment-ℕᵉ Iᵉ (succ-ℕᵉ xᵉ) Hᵉ =
  is-initial-segment-initial-segment-ℕᵉ Iᵉ 0
    ( contains-zero-initial-segment-ℕᵉ (shift-initial-segment-ℕᵉ Iᵉ) xᵉ Hᵉ)
```

### Initial segments that contain a successor contain `1`

```agda
contains-one-initial-segment-ℕᵉ :
  {lᵉ : Level} (Iᵉ : initial-segment-ℕᵉ lᵉ) →
  (xᵉ : ℕᵉ) → is-in-initial-segment-ℕᵉ Iᵉ (succ-ℕᵉ xᵉ) → is-in-initial-segment-ℕᵉ Iᵉ 1
contains-one-initial-segment-ℕᵉ Iᵉ =
  contains-zero-initial-segment-ℕᵉ (shift-initial-segment-ℕᵉ Iᵉ)
```

### Initial segments are closed under `max-ℕ`

```agda
max-initial-segment-ℕᵉ :
  {lᵉ : Level} (Iᵉ : initial-segment-ℕᵉ lᵉ) →
  (xᵉ yᵉ : ℕᵉ) → is-in-initial-segment-ℕᵉ Iᵉ xᵉ → is-in-initial-segment-ℕᵉ Iᵉ yᵉ →
  is-in-initial-segment-ℕᵉ Iᵉ (max-ℕᵉ xᵉ yᵉ)
max-initial-segment-ℕᵉ Iᵉ zero-ℕᵉ yᵉ Hᵉ Kᵉ = Kᵉ
max-initial-segment-ℕᵉ Iᵉ (succ-ℕᵉ xᵉ) zero-ℕᵉ Hᵉ Kᵉ = Hᵉ
max-initial-segment-ℕᵉ Iᵉ (succ-ℕᵉ xᵉ) (succ-ℕᵉ yᵉ) Hᵉ Kᵉ =
  max-initial-segment-ℕᵉ (shift-initial-segment-ℕᵉ Iᵉ) xᵉ yᵉ Hᵉ Kᵉ
```