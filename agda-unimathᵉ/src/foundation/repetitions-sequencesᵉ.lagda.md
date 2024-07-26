# Repetitions in sequences

```agda
module foundation.repetitions-sequencesᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ
open import elementary-number-theory.strictly-ordered-pairs-of-natural-numbersᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.negated-equalityᵉ
open import foundation.pairs-of-distinct-elementsᵉ
open import foundation.repetitions-of-valuesᵉ
open import foundation.sequencesᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.embeddingsᵉ
open import foundation-core.empty-typesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.functoriality-dependent-pair-typesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.injective-mapsᵉ
```

</details>

## Idea

Aᵉ repetitionᵉ in aᵉ sequenceᵉ `aᵉ : ℕᵉ → A`ᵉ consistsᵉ ofᵉ aᵉ pairᵉ ofᵉ distinctᵉ naturalᵉ
numbersᵉ `m`ᵉ andᵉ `n`ᵉ suchᵉ thatᵉ `aᵉ mᵉ = aᵉ n`.ᵉ

## Definition

### Repetitions of values in a sequence

```agda
is-repetition-of-values-sequenceᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} (aᵉ : sequenceᵉ Aᵉ) (pᵉ : pair-of-distinct-elementsᵉ ℕᵉ) →
  UUᵉ lᵉ
is-repetition-of-values-sequenceᵉ aᵉ pᵉ =
  is-repetition-of-valuesᵉ aᵉ pᵉ

repetition-of-values-sequenceᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} → sequenceᵉ Aᵉ → UUᵉ lᵉ
repetition-of-values-sequenceᵉ aᵉ =
  Σᵉ (pair-of-distinct-elementsᵉ ℕᵉ) (is-repetition-of-valuesᵉ aᵉ)

module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} (aᵉ : sequenceᵉ Aᵉ) (rᵉ : repetition-of-values-sequenceᵉ aᵉ)
  where

  pair-of-distinct-elements-repetition-of-values-sequenceᵉ :
    pair-of-distinct-elementsᵉ ℕᵉ
  pair-of-distinct-elements-repetition-of-values-sequenceᵉ = pr1ᵉ rᵉ

  first-repetition-of-values-sequenceᵉ : ℕᵉ
  first-repetition-of-values-sequenceᵉ =
    first-pair-of-distinct-elementsᵉ
      pair-of-distinct-elements-repetition-of-values-sequenceᵉ

  second-repetition-of-values-sequenceᵉ : ℕᵉ
  second-repetition-of-values-sequenceᵉ =
    second-pair-of-distinct-elementsᵉ
      pair-of-distinct-elements-repetition-of-values-sequenceᵉ

  distinction-repetition-of-values-sequenceᵉ :
    first-repetition-of-values-sequenceᵉ ≠ᵉ second-repetition-of-values-sequenceᵉ
  distinction-repetition-of-values-sequenceᵉ =
    distinction-pair-of-distinct-elementsᵉ
      pair-of-distinct-elements-repetition-of-values-sequenceᵉ

  is-repetition-of-values-repetition-of-values-sequenceᵉ :
    is-repetition-of-valuesᵉ aᵉ
      pair-of-distinct-elements-repetition-of-values-sequenceᵉ
  is-repetition-of-values-repetition-of-values-sequenceᵉ = pr2ᵉ rᵉ
```

### Ordered repetitions of values in a sequence

```agda
is-ordered-repetition-of-values-ℕᵉ :
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (fᵉ : ℕᵉ → Aᵉ) (xᵉ : strictly-ordered-pair-ℕᵉ) → UUᵉ l1ᵉ
is-ordered-repetition-of-values-ℕᵉ fᵉ xᵉ =
  fᵉ (first-strictly-ordered-pair-ℕᵉ xᵉ) ＝ᵉ fᵉ (second-strictly-ordered-pair-ℕᵉ xᵉ)

ordered-repetition-of-values-ℕᵉ :
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (fᵉ : ℕᵉ → Aᵉ) → UUᵉ l1ᵉ
ordered-repetition-of-values-ℕᵉ fᵉ =
  Σᵉ strictly-ordered-pair-ℕᵉ (is-ordered-repetition-of-values-ℕᵉ fᵉ)

ordered-repetition-of-values-comp-ℕᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (gᵉ : Aᵉ → Bᵉ) {fᵉ : ℕᵉ → Aᵉ} →
  ordered-repetition-of-values-ℕᵉ fᵉ →
  ordered-repetition-of-values-ℕᵉ (gᵉ ∘ᵉ fᵉ)
ordered-repetition-of-values-comp-ℕᵉ gᵉ ((aᵉ ,ᵉ bᵉ ,ᵉ Hᵉ) ,ᵉ pᵉ) =
  ((aᵉ ,ᵉ bᵉ ,ᵉ Hᵉ) ,ᵉ apᵉ gᵉ pᵉ)

ordered-repetition-of-values-right-factor-ℕᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {gᵉ : Aᵉ → Bᵉ} {fᵉ : ℕᵉ → Aᵉ} →
  is-embᵉ gᵉ → ordered-repetition-of-values-ℕᵉ (gᵉ ∘ᵉ fᵉ) →
  ordered-repetition-of-values-ℕᵉ fᵉ
ordered-repetition-of-values-right-factor-ℕᵉ Eᵉ ((aᵉ ,ᵉ bᵉ ,ᵉ Hᵉ) ,ᵉ pᵉ) =
  ((aᵉ ,ᵉ bᵉ ,ᵉ Hᵉ) ,ᵉ is-injective-is-embᵉ Eᵉ pᵉ)
```

### Any repetition of values in a sequence can be ordered

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  ordered-repetition-of-values-repetition-of-values-ℕ'ᵉ :
    (fᵉ : ℕᵉ → Aᵉ) (aᵉ bᵉ : ℕᵉ) → aᵉ ≠ᵉ bᵉ → fᵉ aᵉ ＝ᵉ fᵉ bᵉ →
    ordered-repetition-of-values-ℕᵉ fᵉ
  ordered-repetition-of-values-repetition-of-values-ℕ'ᵉ fᵉ zero-ℕᵉ zero-ℕᵉ Hᵉ pᵉ =
    ex-falsoᵉ (Hᵉ reflᵉ)
  ordered-repetition-of-values-repetition-of-values-ℕ'ᵉ fᵉ zero-ℕᵉ (succ-ℕᵉ bᵉ) Hᵉ pᵉ =
    ((0ᵉ ,ᵉ succ-ℕᵉ bᵉ ,ᵉ starᵉ) ,ᵉ pᵉ)
  ordered-repetition-of-values-repetition-of-values-ℕ'ᵉ fᵉ (succ-ℕᵉ aᵉ) zero-ℕᵉ Hᵉ pᵉ =
    ((0ᵉ ,ᵉ succ-ℕᵉ aᵉ ,ᵉ starᵉ) ,ᵉ invᵉ pᵉ)
  ordered-repetition-of-values-repetition-of-values-ℕ'ᵉ fᵉ
    (succ-ℕᵉ aᵉ) (succ-ℕᵉ bᵉ) Hᵉ pᵉ =
    map-Σᵉ
      ( λ uᵉ → fᵉ (pr1ᵉ uᵉ) ＝ᵉ fᵉ (pr1ᵉ (pr2ᵉ uᵉ)))
      ( map-Σᵉ _ succ-ℕᵉ (λ _ → map-Σᵉ _ succ-ℕᵉ (λ _ → idᵉ)))
      ( λ uᵉ → idᵉ)
      ( ordered-repetition-of-values-repetition-of-values-ℕ'ᵉ
        ( fᵉ ∘ᵉ succ-ℕᵉ)
        ( aᵉ)
        ( bᵉ)
        ( λ qᵉ → Hᵉ (apᵉ succ-ℕᵉ qᵉ))
        ( pᵉ))

  ordered-repetition-of-values-repetition-of-values-ℕᵉ :
    (fᵉ : ℕᵉ → Aᵉ) → repetition-of-valuesᵉ fᵉ → ordered-repetition-of-values-ℕᵉ fᵉ
  ordered-repetition-of-values-repetition-of-values-ℕᵉ fᵉ ((aᵉ ,ᵉ bᵉ ,ᵉ Hᵉ) ,ᵉ pᵉ) =
    ordered-repetition-of-values-repetition-of-values-ℕ'ᵉ fᵉ aᵉ bᵉ Hᵉ pᵉ
```