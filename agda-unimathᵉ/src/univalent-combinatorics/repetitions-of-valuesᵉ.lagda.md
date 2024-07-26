# Repetitions of values

```agda
module univalent-combinatorics.repetitions-of-valuesᵉ where

open import foundation.repetitions-of-valuesᵉ public
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ
open import elementary-number-theory.well-ordering-principle-standard-finite-typesᵉ

open import foundation.cartesian-product-typesᵉ
open import foundation.decidable-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.injective-mapsᵉ
open import foundation.negated-equalityᵉ
open import foundation.negationᵉ
open import foundation.setsᵉ

open import univalent-combinatorics.decidable-dependent-function-typesᵉ
open import univalent-combinatorics.decidable-propositionsᵉ
open import univalent-combinatorics.dependent-pair-typesᵉ
open import univalent-combinatorics.equality-standard-finite-typesᵉ
open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Aᵉ **repetitionᵉ ofᵉ values**ᵉ ofᵉ aᵉ functionᵉ `fᵉ : Aᵉ → B`ᵉ consistsᵉ ofᵉ aᵉ pairᵉ
`aᵉ a'ᵉ : A`ᵉ suchᵉ thatᵉ `aᵉ ≠ᵉ a'`ᵉ andᵉ `fᵉ aᵉ ＝ᵉ fᵉ a'`.ᵉ

## Properties

### If `f : Fin k → Fin l` is not injective, then it has a repetition of values

bᵉ

```agda
repetition-of-values-is-not-injective-Finᵉ :
  (kᵉ lᵉ : ℕᵉ) (fᵉ : Finᵉ kᵉ → Finᵉ lᵉ) →
  is-not-injectiveᵉ fᵉ → repetition-of-valuesᵉ fᵉ
repetition-of-values-is-not-injective-Finᵉ kᵉ lᵉ fᵉ Nᵉ =
  pairᵉ (pairᵉ xᵉ (pairᵉ yᵉ (pr2ᵉ wᵉ))) (pr1ᵉ wᵉ)
  where
  uᵉ : Σᵉ (Finᵉ kᵉ) (λ xᵉ → ¬ᵉ ((yᵉ : Finᵉ kᵉ) → fᵉ xᵉ ＝ᵉ fᵉ yᵉ → xᵉ ＝ᵉ yᵉ))
  uᵉ =
    exists-not-not-for-all-Finᵉ kᵉ
      ( λ xᵉ →
        is-decidable-Π-Finᵉ kᵉ
          ( λ yᵉ →
            is-decidable-function-typeᵉ
              ( has-decidable-equality-Finᵉ lᵉ (fᵉ xᵉ) (fᵉ yᵉ))
              ( has-decidable-equality-Finᵉ kᵉ xᵉ yᵉ)))
      ( λ fᵉ → Nᵉ (λ {xᵉ} {yᵉ} → fᵉ xᵉ yᵉ))
  xᵉ : Finᵉ kᵉ
  xᵉ = pr1ᵉ uᵉ
  Hᵉ : ¬ᵉ ((yᵉ : Finᵉ kᵉ) → fᵉ xᵉ ＝ᵉ fᵉ yᵉ → xᵉ ＝ᵉ yᵉ)
  Hᵉ = pr2ᵉ uᵉ
  vᵉ : Σᵉ (Finᵉ kᵉ) (λ yᵉ → ¬ᵉ (fᵉ xᵉ ＝ᵉ fᵉ yᵉ → xᵉ ＝ᵉ yᵉ))
  vᵉ = exists-not-not-for-all-Finᵉ kᵉ
      ( λ yᵉ →
        is-decidable-function-typeᵉ
          ( has-decidable-equality-Finᵉ lᵉ (fᵉ xᵉ) (fᵉ yᵉ))
          ( has-decidable-equality-Finᵉ kᵉ xᵉ yᵉ))
      ( Hᵉ)
  yᵉ : Finᵉ kᵉ
  yᵉ = pr1ᵉ vᵉ
  Kᵉ : ¬ᵉ (fᵉ xᵉ ＝ᵉ fᵉ yᵉ → xᵉ ＝ᵉ yᵉ)
  Kᵉ = pr2ᵉ vᵉ
  wᵉ : (fᵉ xᵉ ＝ᵉ fᵉ yᵉ) ×ᵉ (xᵉ ≠ᵉ yᵉ)
  wᵉ = exists-not-not-for-all-countᵉ
      ( λ _ → Idᵉ xᵉ yᵉ)
      ( λ _ →
        has-decidable-equality-Finᵉ kᵉ xᵉ yᵉ)
      ( count-is-decidable-is-propᵉ
        ( is-set-Finᵉ lᵉ (fᵉ xᵉ) (fᵉ yᵉ))
        ( has-decidable-equality-Finᵉ lᵉ (fᵉ xᵉ) (fᵉ yᵉ)))
      ( Kᵉ)
```

### On the standard finite sets, `is-repetition-of-values f x` is decidable

```text
is-decidable-is-repetition-of-values-Finᵉ :
  {kᵉ lᵉ : ℕᵉ} (fᵉ : Finᵉ kᵉ → Finᵉ lᵉ) (xᵉ : Finᵉ kᵉ) →
  is-decidableᵉ (is-repetition-of-valuesᵉ fᵉ xᵉ)
is-decidable-is-repetition-of-values-Finᵉ fᵉ xᵉ =
  is-decidable-Σ-Finᵉ
    ( λ yᵉ →
      is-decidable-productᵉ
        ( is-decidable-negᵉ (has-decidable-equality-Finᵉ xᵉ yᵉ))
        ( has-decidable-equality-Finᵉ (fᵉ xᵉ) (fᵉ yᵉ)))
```

### On the standard finite sets, `is-repeated-value f x` is decidable

```text
is-decidable-is-repeated-value-Finᵉ :
  (kᵉ lᵉ : ℕᵉ) (fᵉ : Finᵉ kᵉ → Finᵉ lᵉ) (xᵉ : Finᵉ kᵉ) →
  is-decidableᵉ (is-repeated-valueᵉ fᵉ xᵉ)
is-decidable-is-repeated-value-Finᵉ kᵉ lᵉ fᵉ xᵉ =
  is-decidable-Σ-Finᵉ kᵉ
    ( λ yᵉ →
      is-decidable-productᵉ
        ( is-decidable-negᵉ (has-decidable-equality-Finᵉ kᵉ xᵉ yᵉ))
        ( has-decidable-equality-Finᵉ lᵉ (fᵉ xᵉ) (fᵉ yᵉ)))
```

### The predicate that `f` maps two different elements to the same value

Thisᵉ remainsᵉ to beᵉ defined.ᵉ
[#748](https://github.com/UniMath/agda-unimath/issues/748ᵉ)

### On the standard finite sets, `has-repetition-of-values f` is decidable

```text
is-decidable-has-repetition-of-values-Finᵉ :
  (kᵉ lᵉ : ℕᵉ) (fᵉ : Finᵉ kᵉ → Finᵉ lᵉ) → is-decidableᵉ (has-repetition-of-valuesᵉ fᵉ)
is-decidable-has-repetition-of-values-Finᵉ kᵉ lᵉ fᵉ =
  is-decidable-Σ-Finᵉ kᵉ (is-decidable-is-repetition-of-values-Finᵉ kᵉ lᵉ fᵉ)
```

### If `f` is not injective, then it has a `repetition-of-values`

```text
is-injective-map-Fin-zero-Finᵉ :
  {kᵉ : ℕᵉ} (fᵉ : Finᵉ zero-ℕᵉ → Finᵉ kᵉ) → is-injectiveᵉ fᵉ
is-injective-map-Fin-zero-Finᵉ fᵉ {()}

is-injective-map-Fin-one-Finᵉ : {kᵉ : ℕᵉ} (fᵉ : Finᵉ 1 → Finᵉ kᵉ) → is-injectiveᵉ fᵉ
is-injective-map-Fin-one-Finᵉ fᵉ {inrᵉ starᵉ} {inrᵉ starᵉ} pᵉ = reflᵉ

has-repetition-of-values-is-not-injective-Finᵉ :
  (kᵉ lᵉ : ℕᵉ) (fᵉ : Finᵉ lᵉ → Finᵉ kᵉ) →
  is-not-injectiveᵉ fᵉ → has-repetition-of-valuesᵉ fᵉ
has-repetition-of-values-is-not-injective-Finᵉ kᵉ zero-ℕᵉ fᵉ Hᵉ =
  ex-falsoᵉ (Hᵉ (is-injective-map-Fin-zero-Finᵉ {kᵉ} fᵉ))
has-repetition-of-values-is-not-injective-Finᵉ kᵉ (succ-ℕᵉ lᵉ) fᵉ Hᵉ with
  is-decidable-is-repetition-of-values-Finᵉ (succ-ℕᵉ lᵉ) kᵉ fᵉ (inrᵉ starᵉ)
... | inlᵉ rᵉ = pairᵉ (inrᵉ starᵉ) rᵉ
... | inrᵉ gᵉ =
  αᵉ (has-repetition-of-values-is-not-injective-Finᵉ kᵉ lᵉ (fᵉ ∘ᵉ inlᵉ) Kᵉ)
  where
  Kᵉ : is-not-injectiveᵉ (fᵉ ∘ᵉ inlᵉ)
  Kᵉ Iᵉ = Hᵉ (λ {xᵉ} {yᵉ} → Jᵉ xᵉ yᵉ)
    where
    Jᵉ : (xᵉ yᵉ : Finᵉ (succ-ℕᵉ lᵉ)) → Idᵉ (fᵉ xᵉ) (fᵉ yᵉ) → Idᵉ xᵉ yᵉ
    Jᵉ (inlᵉ xᵉ) (inlᵉ yᵉ) pᵉ = apᵉ inlᵉ (Iᵉ pᵉ)
    Jᵉ (inlᵉ xᵉ) (inrᵉ starᵉ) pᵉ =
      ex-falsoᵉ (gᵉ (tripleᵉ (inlᵉ xᵉ) (Eq-Fin-eqᵉ (succ-ℕᵉ lᵉ)) (invᵉ pᵉ)))
    Jᵉ (inrᵉ starᵉ) (inlᵉ yᵉ) pᵉ =
      ex-falsoᵉ (gᵉ (tripleᵉ (inlᵉ yᵉ) (Eq-Fin-eqᵉ (succ-ℕᵉ lᵉ)) pᵉ))
    Jᵉ (inrᵉ starᵉ) (inrᵉ starᵉ) pᵉ = reflᵉ
    αᵉ : has-repetition-of-valuesᵉ (fᵉ ∘ᵉ inlᵉ) → has-repetition-of-valuesᵉ fᵉ
    αᵉ (pairᵉ xᵉ (pairᵉ yᵉ (pairᵉ hᵉ qᵉ))) =
      pairᵉ (inlᵉ xᵉ) (pairᵉ (inlᵉ yᵉ) (pairᵉ (λ rᵉ → hᵉ (is-injective-inlᵉ rᵉ)) qᵉ))
```