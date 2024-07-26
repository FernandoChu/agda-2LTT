# The strong induction principle for the natural numbers

```agda
module elementary-number-theory.strong-induction-natural-numbersᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.equality-natural-numbersᵉ
open import elementary-number-theory.inequality-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.cartesian-product-typesᵉ
open import foundation.coproduct-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.empty-typesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.function-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Theᵉ strongᵉ inductionᵉ principleᵉ allowsᵉ oneᵉ to assumeᵉ in theᵉ inductive stepᵉ thatᵉ
theᵉ inductive hypothesisᵉ isᵉ satisfiedᵉ atᵉ allᵉ smallerᵉ values.ᵉ

## Definition

### The `□`-modality on families indexed by `ℕ`

```agda
□-≤-ℕᵉ : {lᵉ : Level} → (ℕᵉ → UUᵉ lᵉ) → ℕᵉ → UUᵉ lᵉ
□-≤-ℕᵉ Pᵉ nᵉ = (mᵉ : ℕᵉ) → (mᵉ ≤-ℕᵉ nᵉ) → Pᵉ mᵉ

η-□-≤-ℕᵉ : {lᵉ : Level} {Pᵉ : ℕᵉ → UUᵉ lᵉ} → ((nᵉ : ℕᵉ) → Pᵉ nᵉ) → (nᵉ : ℕᵉ) → □-≤-ℕᵉ Pᵉ nᵉ
η-□-≤-ℕᵉ fᵉ nᵉ mᵉ pᵉ = fᵉ mᵉ

ε-□-≤-ℕᵉ :
  {lᵉ : Level} {Pᵉ : ℕᵉ → UUᵉ lᵉ} → ((nᵉ : ℕᵉ) → □-≤-ℕᵉ Pᵉ nᵉ) → ((nᵉ : ℕᵉ) → Pᵉ nᵉ)
ε-□-≤-ℕᵉ fᵉ nᵉ = fᵉ nᵉ nᵉ (refl-leq-ℕᵉ nᵉ)
```

## Theorem

### The base case of the strong induction principle

```agda
zero-strong-ind-ℕᵉ :
  {lᵉ : Level} (Pᵉ : ℕᵉ → UUᵉ lᵉ) → Pᵉ zero-ℕᵉ → □-≤-ℕᵉ Pᵉ zero-ℕᵉ
zero-strong-ind-ℕᵉ Pᵉ p0ᵉ zero-ℕᵉ tᵉ = p0ᵉ

eq-zero-strong-ind-ℕᵉ :
  {lᵉ : Level} (Pᵉ : ℕᵉ → UUᵉ lᵉ) (p0ᵉ : Pᵉ zero-ℕᵉ) (tᵉ : leq-ℕᵉ zero-ℕᵉ zero-ℕᵉ) →
  zero-strong-ind-ℕᵉ Pᵉ p0ᵉ zero-ℕᵉ tᵉ ＝ᵉ p0ᵉ
eq-zero-strong-ind-ℕᵉ Pᵉ p0ᵉ tᵉ = reflᵉ
```

### The successor case of the strong induction principle

```agda
cases-succ-strong-ind-ℕᵉ :
  {lᵉ : Level} (Pᵉ : ℕᵉ → UUᵉ lᵉ) (pSᵉ : (nᵉ : ℕᵉ) → (□-≤-ℕᵉ Pᵉ nᵉ) → Pᵉ (succ-ℕᵉ nᵉ)) (nᵉ : ℕᵉ)
  (Hᵉ : □-≤-ℕᵉ Pᵉ nᵉ) (mᵉ : ℕᵉ) (cᵉ : (leq-ℕᵉ mᵉ nᵉ) +ᵉ (mᵉ ＝ᵉ succ-ℕᵉ nᵉ)) → Pᵉ mᵉ
cases-succ-strong-ind-ℕᵉ Pᵉ pSᵉ nᵉ Hᵉ mᵉ (inlᵉ qᵉ) = Hᵉ mᵉ qᵉ
cases-succ-strong-ind-ℕᵉ Pᵉ pSᵉ nᵉ Hᵉ .(succ-ℕᵉ nᵉ) (inrᵉ reflᵉ) = pSᵉ nᵉ Hᵉ

succ-strong-ind-ℕᵉ :
  {lᵉ : Level} (Pᵉ : ℕᵉ → UUᵉ lᵉ) → ((kᵉ : ℕᵉ) → (□-≤-ℕᵉ Pᵉ kᵉ) → Pᵉ (succ-ℕᵉ kᵉ)) →
  (kᵉ : ℕᵉ) → (□-≤-ℕᵉ Pᵉ kᵉ) → (□-≤-ℕᵉ Pᵉ (succ-ℕᵉ kᵉ))
succ-strong-ind-ℕᵉ Pᵉ pSᵉ kᵉ Hᵉ mᵉ pᵉ =
  cases-succ-strong-ind-ℕᵉ Pᵉ pSᵉ kᵉ Hᵉ mᵉ (cases-leq-succ-ℕᵉ pᵉ)

cases-htpy-succ-strong-ind-ℕᵉ :
  {lᵉ : Level} (Pᵉ : ℕᵉ → UUᵉ lᵉ) (pSᵉ : (kᵉ : ℕᵉ) → (□-≤-ℕᵉ Pᵉ kᵉ) → Pᵉ (succ-ℕᵉ kᵉ)) →
  (kᵉ : ℕᵉ) (Hᵉ : □-≤-ℕᵉ Pᵉ kᵉ) (mᵉ : ℕᵉ) (cᵉ : (leq-ℕᵉ mᵉ kᵉ) +ᵉ (mᵉ ＝ᵉ succ-ℕᵉ kᵉ)) →
  (qᵉ : leq-ℕᵉ mᵉ kᵉ) →
  ( cases-succ-strong-ind-ℕᵉ Pᵉ pSᵉ kᵉ Hᵉ mᵉ cᵉ) ＝ᵉ
  ( Hᵉ mᵉ qᵉ)
cases-htpy-succ-strong-ind-ℕᵉ Pᵉ pSᵉ kᵉ Hᵉ mᵉ (inlᵉ pᵉ) qᵉ =
  apᵉ (Hᵉ mᵉ) (eq-is-propᵉ (is-prop-leq-ℕᵉ mᵉ kᵉ))
cases-htpy-succ-strong-ind-ℕᵉ Pᵉ pSᵉ kᵉ Hᵉ mᵉ (inrᵉ αᵉ) qᵉ =
  ex-falsoᵉ (neg-succ-leq-ℕᵉ kᵉ (concatenate-eq-leq-ℕᵉ kᵉ (invᵉ αᵉ) qᵉ))

htpy-succ-strong-ind-ℕᵉ :
  {lᵉ : Level} (Pᵉ : ℕᵉ → UUᵉ lᵉ) → (pSᵉ : (kᵉ : ℕᵉ) → (□-≤-ℕᵉ Pᵉ kᵉ) → Pᵉ (succ-ℕᵉ kᵉ)) →
  (kᵉ : ℕᵉ) (Hᵉ : □-≤-ℕᵉ Pᵉ kᵉ) (mᵉ : ℕᵉ) (pᵉ : leq-ℕᵉ mᵉ (succ-ℕᵉ kᵉ)) (qᵉ : leq-ℕᵉ mᵉ kᵉ) →
  ( succ-strong-ind-ℕᵉ Pᵉ pSᵉ kᵉ Hᵉ mᵉ pᵉ) ＝ᵉ
  ( Hᵉ mᵉ qᵉ)
htpy-succ-strong-ind-ℕᵉ Pᵉ pSᵉ kᵉ Hᵉ mᵉ pᵉ qᵉ =
  cases-htpy-succ-strong-ind-ℕᵉ Pᵉ pSᵉ kᵉ Hᵉ mᵉ (cases-leq-succ-ℕᵉ pᵉ) qᵉ

cases-eq-succ-strong-ind-ℕᵉ :
  {lᵉ : Level} (Pᵉ : ℕᵉ → UUᵉ lᵉ) (pSᵉ : (kᵉ : ℕᵉ) → (□-≤-ℕᵉ Pᵉ kᵉ) → Pᵉ (succ-ℕᵉ kᵉ)) →
  (kᵉ : ℕᵉ) (Hᵉ : □-≤-ℕᵉ Pᵉ kᵉ)
  (cᵉ : (leq-ℕᵉ (succ-ℕᵉ kᵉ) kᵉ) +ᵉ (succ-ℕᵉ kᵉ ＝ᵉ succ-ℕᵉ kᵉ)) →
  ( (cases-succ-strong-ind-ℕᵉ Pᵉ pSᵉ kᵉ Hᵉ (succ-ℕᵉ kᵉ) cᵉ)) ＝ᵉ
  ( pSᵉ kᵉ Hᵉ)
cases-eq-succ-strong-ind-ℕᵉ Pᵉ pSᵉ kᵉ Hᵉ (inlᵉ pᵉ) = ex-falsoᵉ (neg-succ-leq-ℕᵉ kᵉ pᵉ)
cases-eq-succ-strong-ind-ℕᵉ Pᵉ pSᵉ kᵉ Hᵉ (inrᵉ αᵉ) =
  apᵉ
    ( (cases-succ-strong-ind-ℕᵉ Pᵉ pSᵉ kᵉ Hᵉ (succ-ℕᵉ kᵉ)) ∘ᵉ inrᵉ)
    ( eq-is-prop'ᵉ (is-set-ℕᵉ (succ-ℕᵉ kᵉ) (succ-ℕᵉ kᵉ)) αᵉ reflᵉ)

eq-succ-strong-ind-ℕᵉ :
  {lᵉ : Level} (Pᵉ : ℕᵉ → UUᵉ lᵉ) (pSᵉ : (kᵉ : ℕᵉ) → (□-≤-ℕᵉ Pᵉ kᵉ) → Pᵉ (succ-ℕᵉ kᵉ)) →
  (kᵉ : ℕᵉ) (Hᵉ : □-≤-ℕᵉ Pᵉ kᵉ) (pᵉ : leq-ℕᵉ (succ-ℕᵉ kᵉ) (succ-ℕᵉ kᵉ)) →
  ( (succ-strong-ind-ℕᵉ Pᵉ pSᵉ kᵉ Hᵉ (succ-ℕᵉ kᵉ) pᵉ)) ＝ᵉ
  ( pSᵉ kᵉ Hᵉ)
eq-succ-strong-ind-ℕᵉ Pᵉ pSᵉ kᵉ Hᵉ pᵉ =
  cases-eq-succ-strong-ind-ℕᵉ Pᵉ pSᵉ kᵉ Hᵉ (cases-leq-succ-ℕᵉ pᵉ)
```

### The inductive step

```agda
induction-strong-ind-ℕᵉ :
  {lᵉ : Level} (Pᵉ : ℕᵉ → UUᵉ lᵉ) → (□-≤-ℕᵉ Pᵉ zero-ℕᵉ) →
  ((kᵉ : ℕᵉ) → (□-≤-ℕᵉ Pᵉ kᵉ) → (□-≤-ℕᵉ Pᵉ (succ-ℕᵉ kᵉ))) → (nᵉ : ℕᵉ) → □-≤-ℕᵉ Pᵉ nᵉ
induction-strong-ind-ℕᵉ Pᵉ p0ᵉ pSᵉ zero-ℕᵉ = p0ᵉ
induction-strong-ind-ℕᵉ Pᵉ p0ᵉ pSᵉ (succ-ℕᵉ nᵉ) =
  pSᵉ nᵉ (induction-strong-ind-ℕᵉ Pᵉ p0ᵉ pSᵉ nᵉ)

computation-succ-strong-ind-ℕᵉ :
  {lᵉ : Level} (Pᵉ : ℕᵉ → UUᵉ lᵉ) (p0ᵉ : □-≤-ℕᵉ Pᵉ zero-ℕᵉ) →
  (pSᵉ : (kᵉ : ℕᵉ) → (□-≤-ℕᵉ Pᵉ kᵉ) → (□-≤-ℕᵉ Pᵉ (succ-ℕᵉ kᵉ))) →
  (nᵉ : ℕᵉ) →
  ( induction-strong-ind-ℕᵉ Pᵉ p0ᵉ pSᵉ (succ-ℕᵉ nᵉ)) ＝ᵉ
  ( pSᵉ nᵉ (induction-strong-ind-ℕᵉ Pᵉ p0ᵉ pSᵉ nᵉ))
computation-succ-strong-ind-ℕᵉ Pᵉ p0ᵉ pSᵉ nᵉ = reflᵉ
```

### The strong induction principle

```agda
strong-ind-ℕᵉ :
  {lᵉ : Level} → (Pᵉ : ℕᵉ → UUᵉ lᵉ) (p0ᵉ : Pᵉ zero-ℕᵉ) →
  (pSᵉ : (kᵉ : ℕᵉ) → (□-≤-ℕᵉ Pᵉ kᵉ) → Pᵉ (succ-ℕᵉ kᵉ)) (nᵉ : ℕᵉ) → Pᵉ nᵉ
strong-ind-ℕᵉ Pᵉ p0ᵉ pSᵉ =
  ε-□-≤-ℕᵉ
    ( induction-strong-ind-ℕᵉ Pᵉ
      ( zero-strong-ind-ℕᵉ Pᵉ p0ᵉ)
      ( succ-strong-ind-ℕᵉ Pᵉ pSᵉ))

compute-zero-strong-ind-ℕᵉ :
  {lᵉ : Level} (Pᵉ : ℕᵉ → UUᵉ lᵉ) (p0ᵉ : Pᵉ zero-ℕᵉ) →
  (pSᵉ : (kᵉ : ℕᵉ) → (□-≤-ℕᵉ Pᵉ kᵉ) → Pᵉ (succ-ℕᵉ kᵉ)) →
  strong-ind-ℕᵉ Pᵉ p0ᵉ pSᵉ zero-ℕᵉ ＝ᵉ p0ᵉ
compute-zero-strong-ind-ℕᵉ Pᵉ p0ᵉ pSᵉ = reflᵉ

cases-eq-compute-succ-strong-ind-ℕᵉ :
  { lᵉ : Level} (Pᵉ : ℕᵉ → UUᵉ lᵉ) (p0ᵉ : Pᵉ zero-ℕᵉ) →
  ( pSᵉ : (kᵉ : ℕᵉ) → (□-≤-ℕᵉ Pᵉ kᵉ) → Pᵉ (succ-ℕᵉ kᵉ)) →
  ( nᵉ : ℕᵉ) →
  ( αᵉ :
    ( mᵉ : ℕᵉ) (pᵉ : leq-ℕᵉ mᵉ nᵉ) →
    ( induction-strong-ind-ℕᵉ Pᵉ (zero-strong-ind-ℕᵉ Pᵉ p0ᵉ)
      ( λ kᵉ zᵉ m₁ᵉ z₁ᵉ →
        cases-succ-strong-ind-ℕᵉ Pᵉ pSᵉ kᵉ zᵉ m₁ᵉ (cases-leq-succ-ℕᵉ z₁ᵉ))
      nᵉ mᵉ pᵉ) ＝ᵉ
    ( strong-ind-ℕᵉ Pᵉ p0ᵉ pSᵉ mᵉ)) →
  ( mᵉ : ℕᵉ) (pᵉ : leq-ℕᵉ mᵉ (succ-ℕᵉ nᵉ)) →
  ( qᵉ : (leq-ℕᵉ mᵉ nᵉ) +ᵉ (mᵉ ＝ᵉ succ-ℕᵉ nᵉ)) →
  ( succ-strong-ind-ℕᵉ Pᵉ pSᵉ nᵉ
    ( induction-strong-ind-ℕᵉ Pᵉ
      ( zero-strong-ind-ℕᵉ Pᵉ p0ᵉ)
      ( succ-strong-ind-ℕᵉ Pᵉ pSᵉ) nᵉ) mᵉ pᵉ) ＝ᵉ
  ( strong-ind-ℕᵉ Pᵉ p0ᵉ pSᵉ mᵉ)
cases-eq-compute-succ-strong-ind-ℕᵉ Pᵉ p0ᵉ pSᵉ nᵉ αᵉ mᵉ pᵉ (inlᵉ xᵉ) =
  ( htpy-succ-strong-ind-ℕᵉ Pᵉ pSᵉ nᵉ
    ( induction-strong-ind-ℕᵉ Pᵉ
      ( zero-strong-ind-ℕᵉ Pᵉ p0ᵉ)
      ( succ-strong-ind-ℕᵉ Pᵉ pSᵉ) nᵉ)
    mᵉ pᵉ xᵉ) ∙ᵉ
  ( αᵉ mᵉ xᵉ)
cases-eq-compute-succ-strong-ind-ℕᵉ Pᵉ p0ᵉ pSᵉ nᵉ αᵉ .(succ-ℕᵉ nᵉ) pᵉ (inrᵉ reflᵉ) =
  ( eq-succ-strong-ind-ℕᵉ Pᵉ pSᵉ nᵉ
    ( induction-strong-ind-ℕᵉ Pᵉ
      ( zero-strong-ind-ℕᵉ Pᵉ p0ᵉ)
      ( succ-strong-ind-ℕᵉ Pᵉ pSᵉ) nᵉ)
    ( pᵉ)) ∙ᵉ
  ( invᵉ
    ( apᵉ
      ( cases-succ-strong-ind-ℕᵉ Pᵉ pSᵉ nᵉ
        ( induction-strong-ind-ℕᵉ Pᵉ
          ( zero-strong-ind-ℕᵉ Pᵉ p0ᵉ)
          ( λ kᵉ Hᵉ mᵉ p₁ᵉ →
            cases-succ-strong-ind-ℕᵉ Pᵉ pSᵉ kᵉ Hᵉ mᵉ (cases-leq-succ-ℕᵉ p₁ᵉ))
          nᵉ)
        ( succ-ℕᵉ nᵉ))
      ( cases-leq-succ-reflexive-leq-ℕᵉ)))

eq-compute-succ-strong-ind-ℕᵉ :
  { lᵉ : Level} (Pᵉ : ℕᵉ → UUᵉ lᵉ) (p0ᵉ : Pᵉ zero-ℕᵉ) →
  ( pSᵉ : (kᵉ : ℕᵉ) → (□-≤-ℕᵉ Pᵉ kᵉ) → Pᵉ (succ-ℕᵉ kᵉ)) →
  ( nᵉ : ℕᵉ) →
  ( mᵉ : ℕᵉ) (pᵉ : leq-ℕᵉ mᵉ nᵉ) →
  ( induction-strong-ind-ℕᵉ Pᵉ (zero-strong-ind-ℕᵉ Pᵉ p0ᵉ)
    ( λ kᵉ zᵉ m₁ᵉ z₁ᵉ →
      cases-succ-strong-ind-ℕᵉ Pᵉ pSᵉ kᵉ zᵉ m₁ᵉ (cases-leq-succ-ℕᵉ z₁ᵉ))
    nᵉ mᵉ pᵉ) ＝ᵉ
  ( strong-ind-ℕᵉ Pᵉ p0ᵉ pSᵉ mᵉ)
eq-compute-succ-strong-ind-ℕᵉ Pᵉ p0ᵉ pSᵉ zero-ℕᵉ zero-ℕᵉ _ = reflᵉ
eq-compute-succ-strong-ind-ℕᵉ Pᵉ p0ᵉ pSᵉ (succ-ℕᵉ nᵉ) mᵉ pᵉ =
  cases-eq-compute-succ-strong-ind-ℕᵉ Pᵉ p0ᵉ pSᵉ nᵉ
    ( eq-compute-succ-strong-ind-ℕᵉ Pᵉ p0ᵉ pSᵉ nᵉ) mᵉ pᵉ
    ( cases-leq-succ-ℕᵉ pᵉ)

compute-succ-strong-ind-ℕᵉ :
  { lᵉ : Level} (Pᵉ : ℕᵉ → UUᵉ lᵉ) (p0ᵉ : Pᵉ zero-ℕᵉ) →
  ( pSᵉ : (kᵉ : ℕᵉ) → (□-≤-ℕᵉ Pᵉ kᵉ) → Pᵉ (succ-ℕᵉ kᵉ)) →
  ( nᵉ : ℕᵉ) →
  strong-ind-ℕᵉ Pᵉ p0ᵉ pSᵉ (succ-ℕᵉ nᵉ) ＝ᵉ pSᵉ nᵉ (λ mᵉ pᵉ → strong-ind-ℕᵉ Pᵉ p0ᵉ pSᵉ mᵉ)
compute-succ-strong-ind-ℕᵉ Pᵉ p0ᵉ pSᵉ nᵉ =
  ( eq-succ-strong-ind-ℕᵉ Pᵉ pSᵉ nᵉ
    ( induction-strong-ind-ℕᵉ Pᵉ
      ( zero-strong-ind-ℕᵉ Pᵉ p0ᵉ)
      ( succ-strong-ind-ℕᵉ Pᵉ pSᵉ)
      ( nᵉ))
    ( refl-leq-ℕᵉ nᵉ)) ∙ᵉ
  ( apᵉ
    ( pSᵉ nᵉ)
    ( eq-htpyᵉ (eq-htpyᵉ ∘ᵉ eq-compute-succ-strong-ind-ℕᵉ Pᵉ p0ᵉ pSᵉ nᵉ)))

total-strong-ind-ℕᵉ :
  { lᵉ : Level} (Pᵉ : ℕᵉ → UUᵉ lᵉ) (p0ᵉ : Pᵉ zero-ℕᵉ) →
  ( pSᵉ : (kᵉ : ℕᵉ) → (□-≤-ℕᵉ Pᵉ kᵉ) → Pᵉ (succ-ℕᵉ kᵉ)) →
  Σᵉ ( (nᵉ : ℕᵉ) → Pᵉ nᵉ)
    ( λ hᵉ →
      ( hᵉ zero-ℕᵉ ＝ᵉ p0ᵉ) ×ᵉ
      ( (nᵉ : ℕᵉ) → hᵉ (succ-ℕᵉ nᵉ) ＝ᵉ pSᵉ nᵉ (λ mᵉ pᵉ → hᵉ mᵉ)))
pr1ᵉ (total-strong-ind-ℕᵉ Pᵉ p0ᵉ pSᵉ) = strong-ind-ℕᵉ Pᵉ p0ᵉ pSᵉ
pr1ᵉ (pr2ᵉ (total-strong-ind-ℕᵉ Pᵉ p0ᵉ pSᵉ)) = compute-zero-strong-ind-ℕᵉ Pᵉ p0ᵉ pSᵉ
pr2ᵉ (pr2ᵉ (total-strong-ind-ℕᵉ Pᵉ p0ᵉ pSᵉ)) = compute-succ-strong-ind-ℕᵉ Pᵉ p0ᵉ pSᵉ
```

## See also

-ᵉ Theᵉ basedᵉ strongᵉ inductionᵉ principleᵉ isᵉ definedᵉ in
  [`based-strong-induction-natural-numbers`](elementary-number-theory.based-strong-induction-natural-numbers.md).ᵉ