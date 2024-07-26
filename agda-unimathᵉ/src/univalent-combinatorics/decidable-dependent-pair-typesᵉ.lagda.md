# Decidability of dependent pair types

```agda
module univalent-combinatorics.decidable-dependent-pair-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.coproduct-typesᵉ
open import foundation.decidable-dependent-pair-typesᵉ
open import foundation.decidable-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.empty-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import univalent-combinatorics.countingᵉ
open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Weᵉ describeᵉ conditionsᵉ underᵉ whichᵉ dependentᵉ sumsᵉ areᵉ decidable.ᵉ

## Note

Itᵉ isᵉ _notᵉ_ theᵉ caseᵉ forᵉ aᵉ familyᵉ `B`ᵉ ofᵉ decidableᵉ typesᵉ overᵉ aᵉ finiteᵉ typeᵉ `A`,ᵉ
thatᵉ theᵉ dependentᵉ pairᵉ typeᵉ `Σᵉ Aᵉ B`ᵉ isᵉ decidable.ᵉ

## Properties

### The Σ-type of any family of decidable types over `Fin k` is decidable

```agda
is-decidable-Σ-Finᵉ :
  {lᵉ : Level} (kᵉ : ℕᵉ) {Pᵉ : Finᵉ kᵉ → UUᵉ lᵉ} →
  ((xᵉ : Finᵉ kᵉ) → is-decidableᵉ (Pᵉ xᵉ)) → is-decidableᵉ (Σᵉ (Finᵉ kᵉ) Pᵉ)
is-decidable-Σ-Finᵉ zero-ℕᵉ {Pᵉ} dᵉ = inrᵉ pr1ᵉ
is-decidable-Σ-Finᵉ (succ-ℕᵉ kᵉ) {Pᵉ} dᵉ with dᵉ (inrᵉ starᵉ)
... | inlᵉ pᵉ = inlᵉ (pairᵉ (inrᵉ starᵉ) pᵉ)
... | inrᵉ fᵉ =
  is-decidable-iffᵉ
    ( λ tᵉ → pairᵉ (inlᵉ (pr1ᵉ tᵉ)) (pr2ᵉ tᵉ))
    ( gᵉ)
    ( is-decidable-Σ-Finᵉ kᵉ {Pᵉ ∘ᵉ inlᵉ} (λ xᵉ → dᵉ (inlᵉ xᵉ)))
  where
  gᵉ : Σᵉ (Finᵉ (succ-ℕᵉ kᵉ)) Pᵉ → Σᵉ (Finᵉ kᵉ) (Pᵉ ∘ᵉ inlᵉ)
  gᵉ (pairᵉ (inlᵉ xᵉ) pᵉ) = pairᵉ xᵉ pᵉ
  gᵉ (pairᵉ (inrᵉ starᵉ) pᵉ) = ex-falsoᵉ (fᵉ pᵉ)
```

### The Σ-type of any family of decidable types over a type equipped with count is decidable

```agda
is-decidable-Σ-countᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} → countᵉ Aᵉ →
  ((xᵉ : Aᵉ) → is-decidableᵉ (Bᵉ xᵉ)) → is-decidableᵉ (Σᵉ Aᵉ Bᵉ)
is-decidable-Σ-countᵉ eᵉ dᵉ =
  is-decidable-Σ-equivᵉ
    ( equiv-countᵉ eᵉ)
    ( λ xᵉ → id-equivᵉ)
    ( is-decidable-Σ-Finᵉ
      ( number-of-elements-countᵉ eᵉ)
      ( λ xᵉ → dᵉ (map-equiv-countᵉ eᵉ xᵉ)))
```