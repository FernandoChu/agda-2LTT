# Sequences of elements in finite types

```agda
module univalent-combinatorics.sequences-finite-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.decidable-typesᵉ
open import elementary-number-theory.natural-numbersᵉ
open import elementary-number-theory.strict-inequality-natural-numbersᵉ
open import elementary-number-theory.well-ordering-principle-natural-numbersᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.cartesian-product-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.injective-mapsᵉ
open import foundation.negated-equalityᵉ
open import foundation.pairs-of-distinct-elementsᵉ
open import foundation.repetitions-of-valuesᵉ
open import foundation.repetitions-sequencesᵉ
open import foundation.sequencesᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ

open import univalent-combinatorics.countingᵉ
open import univalent-combinatorics.equality-standard-finite-typesᵉ
open import univalent-combinatorics.pigeonhole-principleᵉ
open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Sequencesᵉ ofᵉ elementsᵉ in finiteᵉ typesᵉ mustᵉ haveᵉ repetitions.ᵉ Furthermore,ᵉ sinceᵉ
equalityᵉ in finiteᵉ typesᵉ isᵉ decidable,ᵉ thereᵉ mustᵉ beᵉ aᵉ firstᵉ repetitionᵉ in anyᵉ
sequenceᵉ ofᵉ elementsᵉ in aᵉ finiteᵉ type.ᵉ

## Properties

```agda
repetition-of-values-sequence-Finᵉ :
  (kᵉ : ℕᵉ) (fᵉ : ℕᵉ → Finᵉ kᵉ) → repetition-of-valuesᵉ fᵉ
repetition-of-values-sequence-Finᵉ kᵉ fᵉ =
  repetition-of-values-left-factorᵉ
    ( is-emb-nat-Finᵉ (succ-ℕᵉ kᵉ))
    ( repetition-of-values-Fin-succ-to-Finᵉ kᵉ (fᵉ ∘ᵉ nat-Finᵉ (succ-ℕᵉ kᵉ)))

pair-of-distinct-elements-repetition-of-values-sequence-Finᵉ :
  (kᵉ : ℕᵉ) (fᵉ : sequenceᵉ (Finᵉ kᵉ)) → pair-of-distinct-elementsᵉ ℕᵉ
pair-of-distinct-elements-repetition-of-values-sequence-Finᵉ kᵉ fᵉ =
  pair-of-distinct-elements-repetition-of-valuesᵉ fᵉ
    ( repetition-of-values-sequence-Finᵉ kᵉ fᵉ)

first-repetition-of-values-sequence-Finᵉ :
  (kᵉ : ℕᵉ) (fᵉ : sequenceᵉ (Finᵉ kᵉ)) → ℕᵉ
first-repetition-of-values-sequence-Finᵉ kᵉ fᵉ =
  first-repetition-of-valuesᵉ fᵉ (repetition-of-values-sequence-Finᵉ kᵉ fᵉ)

second-repetition-of-values-sequence-Finᵉ :
  (kᵉ : ℕᵉ) (fᵉ : sequenceᵉ (Finᵉ kᵉ)) → ℕᵉ
second-repetition-of-values-sequence-Finᵉ kᵉ fᵉ =
  second-repetition-of-valuesᵉ fᵉ (repetition-of-values-sequence-Finᵉ kᵉ fᵉ)

distinction-repetition-of-values-sequence-Finᵉ :
  (kᵉ : ℕᵉ) (fᵉ : sequenceᵉ (Finᵉ kᵉ)) →
  first-repetition-of-values-sequence-Finᵉ kᵉ fᵉ ≠ᵉ
  second-repetition-of-values-sequence-Finᵉ kᵉ fᵉ
distinction-repetition-of-values-sequence-Finᵉ kᵉ fᵉ =
  distinction-repetition-of-valuesᵉ fᵉ (repetition-of-values-sequence-Finᵉ kᵉ fᵉ)

is-repetition-pair-of-distinct-elements-repetition-of-values-sequence-Finᵉ :
  (kᵉ : ℕᵉ) (fᵉ : sequenceᵉ (Finᵉ kᵉ)) →
  is-repetition-of-valuesᵉ fᵉ
    ( pair-of-distinct-elements-repetition-of-values-sequence-Finᵉ kᵉ fᵉ)
is-repetition-pair-of-distinct-elements-repetition-of-values-sequence-Finᵉ kᵉ fᵉ =
  is-repetition-of-values-repetition-of-valuesᵉ fᵉ
    ( repetition-of-values-sequence-Finᵉ kᵉ fᵉ)

le-first-repetition-of-values-sequence-Finᵉ :
  (kᵉ : ℕᵉ) (fᵉ : sequenceᵉ (Finᵉ kᵉ)) →
  le-ℕᵉ (first-repetition-of-values-sequence-Finᵉ kᵉ fᵉ) (succ-ℕᵉ kᵉ)
le-first-repetition-of-values-sequence-Finᵉ kᵉ fᵉ =
  strict-upper-bound-nat-Finᵉ
    ( succ-ℕᵉ kᵉ)
    ( first-repetition-of-valuesᵉ
      ( fᵉ ∘ᵉ nat-Finᵉ (succ-ℕᵉ kᵉ))
      ( repetition-of-values-le-Finᵉ
        ( succ-ℕᵉ kᵉ)
        ( kᵉ)
        ( fᵉ ∘ᵉ nat-Finᵉ (succ-ℕᵉ kᵉ))
        ( succ-le-ℕᵉ kᵉ)))
```

### Ordered repetitions of values of maps out of the natural numbers

```agda
repetition-of-values-nat-to-countᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} (eᵉ : countᵉ Aᵉ) (fᵉ : ℕᵉ → Aᵉ) → repetition-of-valuesᵉ fᵉ
repetition-of-values-nat-to-countᵉ eᵉ fᵉ =
  repetition-of-values-right-factorᵉ
    ( is-emb-is-equivᵉ (is-equiv-map-inv-equivᵉ (equiv-countᵉ eᵉ)))
    ( repetition-of-values-sequence-Finᵉ
      ( number-of-elements-countᵉ eᵉ)
      ( map-inv-equiv-countᵉ eᵉ ∘ᵉ fᵉ))

ordered-repetition-of-values-sequence-Finᵉ :
  (kᵉ : ℕᵉ) (fᵉ : ℕᵉ → Finᵉ kᵉ) → ordered-repetition-of-values-ℕᵉ fᵉ
ordered-repetition-of-values-sequence-Finᵉ kᵉ fᵉ =
  ordered-repetition-of-values-repetition-of-values-ℕᵉ fᵉ
    (repetition-of-values-sequence-Finᵉ kᵉ fᵉ)

ordered-repetition-of-values-nat-to-countᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} (eᵉ : countᵉ Aᵉ) (fᵉ : ℕᵉ → Aᵉ) →
  ordered-repetition-of-values-ℕᵉ fᵉ
ordered-repetition-of-values-nat-to-countᵉ eᵉ fᵉ =
  ordered-repetition-of-values-right-factor-ℕᵉ
    ( is-emb-is-equivᵉ (is-equiv-map-inv-equivᵉ (equiv-countᵉ eᵉ)))
    ( ordered-repetition-of-values-sequence-Finᵉ
      ( number-of-elements-countᵉ eᵉ)
      ( map-inv-equiv-countᵉ eᵉ ∘ᵉ fᵉ))

minimal-element-repetition-of-values-sequence-Finᵉ :
  (kᵉ : ℕᵉ) (fᵉ : ℕᵉ → Finᵉ kᵉ) →
  minimal-element-ℕᵉ (λ xᵉ → Σᵉ ℕᵉ (λ yᵉ → (le-ℕᵉ yᵉ xᵉ) ×ᵉ (fᵉ yᵉ ＝ᵉ fᵉ xᵉ)))
minimal-element-repetition-of-values-sequence-Finᵉ kᵉ fᵉ =
  well-ordering-principle-ℕᵉ
    ( λ xᵉ → Σᵉ ℕᵉ (λ yᵉ → (le-ℕᵉ yᵉ xᵉ) ×ᵉ (Idᵉ (fᵉ yᵉ) (fᵉ xᵉ))))
    ( λ xᵉ →
      is-decidable-strictly-bounded-Σ-ℕ'ᵉ xᵉ
        ( λ yᵉ → fᵉ yᵉ ＝ᵉ fᵉ xᵉ)
        ( λ yᵉ → has-decidable-equality-Finᵉ kᵉ (fᵉ yᵉ) (fᵉ xᵉ)))
    ( vᵉ ,ᵉ uᵉ ,ᵉ Hᵉ ,ᵉ pᵉ)
  where
  rᵉ = ordered-repetition-of-values-sequence-Finᵉ kᵉ fᵉ
  uᵉ = pr1ᵉ (pr1ᵉ rᵉ)
  vᵉ = pr1ᵉ (pr2ᵉ (pr1ᵉ rᵉ))
  Hᵉ = pr2ᵉ (pr2ᵉ (pr1ᵉ rᵉ))
  pᵉ = pr2ᵉ rᵉ

minimal-element-repetition-of-values-sequence-countᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} (eᵉ : countᵉ Aᵉ) (fᵉ : ℕᵉ → Aᵉ) →
  minimal-element-ℕᵉ (λ xᵉ → Σᵉ ℕᵉ (λ yᵉ → (le-ℕᵉ yᵉ xᵉ) ×ᵉ (fᵉ yᵉ ＝ᵉ fᵉ xᵉ)))
minimal-element-repetition-of-values-sequence-countᵉ (kᵉ ,ᵉ eᵉ) fᵉ =
  ( ( nᵉ) ,ᵉ
    ( ( uᵉ) ,ᵉ
      ( Hᵉ) ,ᵉ
      ( is-injective-is-embᵉ (is-emb-is-equivᵉ (is-equiv-map-inv-equivᵉ eᵉ)) pᵉ)) ,ᵉ
    ( λ tᵉ (vᵉ ,ᵉ Kᵉ ,ᵉ qᵉ) → lᵉ tᵉ (vᵉ ,ᵉ Kᵉ ,ᵉ apᵉ (map-inv-equivᵉ eᵉ) qᵉ)))
  where
  mᵉ = minimal-element-repetition-of-values-sequence-Finᵉ kᵉ (map-inv-equivᵉ eᵉ ∘ᵉ fᵉ)
  nᵉ = pr1ᵉ mᵉ
  uᵉ = pr1ᵉ (pr1ᵉ (pr2ᵉ mᵉ))
  Hᵉ = pr1ᵉ (pr2ᵉ (pr1ᵉ (pr2ᵉ mᵉ)))
  pᵉ = pr2ᵉ (pr2ᵉ (pr1ᵉ (pr2ᵉ mᵉ)))
  lᵉ = pr2ᵉ (pr2ᵉ mᵉ)
```