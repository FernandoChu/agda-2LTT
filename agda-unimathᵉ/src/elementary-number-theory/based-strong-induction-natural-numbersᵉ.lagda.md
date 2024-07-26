# Based strong induction for the natural numbers

```agda
module elementary-number-theory.based-strong-induction-natural-numbersᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.based-induction-natural-numbersᵉ
open import elementary-number-theory.equality-natural-numbersᵉ
open import elementary-number-theory.inequality-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ

open import foundation.action-on-identifications-binary-functionsᵉ
open import foundation.action-on-identifications-functionsᵉ
open import foundation.coproduct-typesᵉ
open import foundation.empty-typesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.function-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.universal-property-contractible-typesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Theᵉ **basedᵉ strongᵉ inductionᵉ principle**ᵉ forᵉ theᵉ naturalᵉ numbersᵉ assertsᵉ thatᵉ
forᵉ anyᵉ naturalᵉ numberᵉ `kᵉ : ℕ`ᵉ andᵉ anyᵉ familyᵉ `P`ᵉ ofᵉ typesᵉ overᵉ theᵉ naturalᵉ
numbersᵉ equippedᵉ with

1.ᵉ anᵉ elementᵉ `p0ᵉ : Pᵉ k`,ᵉ andᵉ
2.ᵉ aᵉ functionᵉ
   `pSᵉ : (xᵉ : ℕᵉ) → kᵉ ≤-ℕᵉ xᵉ → ((yᵉ : ℕᵉ) → kᵉ ≤-ℕᵉ yᵉ ≤-ℕᵉ xᵉ → Pᵉ yᵉ) → Pᵉ (xᵉ +ᵉ 1)`ᵉ thereᵉ
   isᵉ aᵉ functionᵉ

```text
  fᵉ :=ᵉ based-strong-ind-ℕᵉ kᵉ Pᵉ p0ᵉ pSᵉ : (xᵉ : ℕᵉ) → kᵉ ≤-ℕᵉ xᵉ → Pᵉ kᵉ
```

satisfyingᵉ

1.ᵉ `fᵉ kᵉ Kᵉ ＝ᵉ p0`ᵉ forᵉ anyᵉ `Kᵉ : kᵉ ≤-ℕᵉ k`,ᵉ andᵉ
2.ᵉ `fᵉ (nᵉ +ᵉ 1ᵉ) N'ᵉ ＝ᵉ pSᵉ nᵉ Nᵉ (λ mᵉ Mᵉ Hᵉ → fᵉ mᵉ M)`ᵉ forᵉ anyᵉ `Nᵉ : kᵉ ≤-ℕᵉ n`ᵉ andᵉ anyᵉ
   `N'ᵉ : kᵉ ≤-ℕᵉ nᵉ +ᵉ 1`.ᵉ

## Definitions

### The based `□`-modality on families indexed by `ℕ`

```agda
based-□-≤-ℕᵉ : {lᵉ : Level} (kᵉ : ℕᵉ) → (ℕᵉ → UUᵉ lᵉ) → ℕᵉ → UUᵉ lᵉ
based-□-≤-ℕᵉ kᵉ Pᵉ nᵉ = (mᵉ : ℕᵉ) → (kᵉ ≤-ℕᵉ mᵉ) → (mᵉ ≤-ℕᵉ nᵉ) → Pᵉ mᵉ

η-based-□-≤-ℕᵉ :
  {lᵉ : Level} (kᵉ : ℕᵉ) {Pᵉ : ℕᵉ → UUᵉ lᵉ} → ((nᵉ : ℕᵉ) → kᵉ ≤-ℕᵉ nᵉ → Pᵉ nᵉ) →
  (nᵉ : ℕᵉ) → kᵉ ≤-ℕᵉ nᵉ → based-□-≤-ℕᵉ kᵉ Pᵉ nᵉ
η-based-□-≤-ℕᵉ kᵉ fᵉ nᵉ Nᵉ mᵉ Mᵉ pᵉ = fᵉ mᵉ Mᵉ

ε-based-□-≤-ℕᵉ :
  {lᵉ : Level} (kᵉ : ℕᵉ) {Pᵉ : ℕᵉ → UUᵉ lᵉ} → ((nᵉ : ℕᵉ) → kᵉ ≤-ℕᵉ nᵉ → based-□-≤-ℕᵉ kᵉ Pᵉ nᵉ) →
  ((nᵉ : ℕᵉ) → kᵉ ≤-ℕᵉ nᵉ → Pᵉ nᵉ)
ε-based-□-≤-ℕᵉ kᵉ fᵉ nᵉ Nᵉ = fᵉ nᵉ Nᵉ nᵉ Nᵉ (refl-leq-ℕᵉ nᵉ)
```

## Theorem

### The base case of the based strong induction principle

```agda
base-based-strong-ind-ℕᵉ :
  {lᵉ : Level} (kᵉ : ℕᵉ) (Pᵉ : ℕᵉ → UUᵉ lᵉ) → Pᵉ kᵉ → based-□-≤-ℕᵉ kᵉ Pᵉ kᵉ
base-based-strong-ind-ℕᵉ zero-ℕᵉ Pᵉ pᵉ zero-ℕᵉ Mᵉ Hᵉ = pᵉ
base-based-strong-ind-ℕᵉ (succ-ℕᵉ kᵉ) Pᵉ p0ᵉ (succ-ℕᵉ mᵉ) =
  base-based-strong-ind-ℕᵉ kᵉ (Pᵉ ∘ᵉ succ-ℕᵉ) p0ᵉ mᵉ

eq-base-based-strong-ind-ℕᵉ :
  {lᵉ : Level} (kᵉ : ℕᵉ) (Pᵉ : ℕᵉ → UUᵉ lᵉ) (pᵉ : Pᵉ kᵉ)
  (sᵉ tᵉ : leq-ℕᵉ kᵉ kᵉ) → base-based-strong-ind-ℕᵉ kᵉ Pᵉ pᵉ kᵉ sᵉ tᵉ ＝ᵉ pᵉ
eq-base-based-strong-ind-ℕᵉ zero-ℕᵉ Pᵉ p0ᵉ Mᵉ Hᵉ = reflᵉ
eq-base-based-strong-ind-ℕᵉ (succ-ℕᵉ kᵉ) Pᵉ =
  eq-base-based-strong-ind-ℕᵉ kᵉ (Pᵉ ∘ᵉ succ-ℕᵉ)
```

### The successor case of the based strong induction principle

```agda
cases-succ-based-strong-ind-ℕᵉ :
  {lᵉ : Level} (kᵉ : ℕᵉ) (Pᵉ : ℕᵉ → UUᵉ lᵉ)
  (pSᵉ : (nᵉ : ℕᵉ) → kᵉ ≤-ℕᵉ nᵉ → based-□-≤-ℕᵉ kᵉ Pᵉ nᵉ → Pᵉ (succ-ℕᵉ nᵉ))
  (nᵉ : ℕᵉ) (Nᵉ : kᵉ ≤-ℕᵉ nᵉ) (fᵉ : based-□-≤-ℕᵉ kᵉ Pᵉ nᵉ)
  (mᵉ : ℕᵉ) (Mᵉ : kᵉ ≤-ℕᵉ mᵉ) (cᵉ : (leq-ℕᵉ mᵉ nᵉ) +ᵉ (mᵉ ＝ᵉ succ-ℕᵉ nᵉ)) → Pᵉ mᵉ
cases-succ-based-strong-ind-ℕᵉ kᵉ Pᵉ pSᵉ nᵉ Nᵉ fᵉ mᵉ Mᵉ (inlᵉ H'ᵉ) = fᵉ mᵉ Mᵉ H'ᵉ
cases-succ-based-strong-ind-ℕᵉ kᵉ Pᵉ pSᵉ nᵉ Nᵉ fᵉ .(succ-ℕᵉ nᵉ) Mᵉ (inrᵉ reflᵉ) = pSᵉ nᵉ Nᵉ fᵉ

succ-based-strong-ind-ℕᵉ :
  {lᵉ : Level} (kᵉ : ℕᵉ) (Pᵉ : ℕᵉ → UUᵉ lᵉ) →
  ((xᵉ : ℕᵉ) → leq-ℕᵉ kᵉ xᵉ → based-□-≤-ℕᵉ kᵉ Pᵉ xᵉ → Pᵉ (succ-ℕᵉ xᵉ)) →
  (nᵉ : ℕᵉ) → leq-ℕᵉ kᵉ nᵉ → based-□-≤-ℕᵉ kᵉ Pᵉ nᵉ → based-□-≤-ℕᵉ kᵉ Pᵉ (succ-ℕᵉ nᵉ)
succ-based-strong-ind-ℕᵉ kᵉ Pᵉ pSᵉ nᵉ Nᵉ fᵉ mᵉ Mᵉ Hᵉ =
  cases-succ-based-strong-ind-ℕᵉ kᵉ Pᵉ pSᵉ nᵉ Nᵉ fᵉ mᵉ Mᵉ (cases-leq-succ-ℕᵉ Hᵉ)

cases-htpy-succ-based-strong-ind-ℕᵉ :
  {lᵉ : Level} (kᵉ : ℕᵉ) (Pᵉ : ℕᵉ → UUᵉ lᵉ)
  (pSᵉ : (xᵉ : ℕᵉ) → kᵉ ≤-ℕᵉ xᵉ → based-□-≤-ℕᵉ kᵉ Pᵉ xᵉ → Pᵉ (succ-ℕᵉ xᵉ)) →
  (nᵉ : ℕᵉ) (Nᵉ : kᵉ ≤-ℕᵉ nᵉ) (fᵉ : based-□-≤-ℕᵉ kᵉ Pᵉ nᵉ)
  (mᵉ : ℕᵉ) (Mᵉ : kᵉ ≤-ℕᵉ mᵉ) (cᵉ : (leq-ℕᵉ mᵉ nᵉ) +ᵉ (mᵉ ＝ᵉ succ-ℕᵉ nᵉ)) →
  (Hᵉ : leq-ℕᵉ mᵉ nᵉ) →
  cases-succ-based-strong-ind-ℕᵉ kᵉ Pᵉ pSᵉ nᵉ Nᵉ fᵉ mᵉ Mᵉ cᵉ ＝ᵉ fᵉ mᵉ Mᵉ Hᵉ
cases-htpy-succ-based-strong-ind-ℕᵉ kᵉ Pᵉ pSᵉ nᵉ Nᵉ fᵉ mᵉ Mᵉ (inlᵉ pᵉ) Hᵉ =
  apᵉ (fᵉ mᵉ Mᵉ) (eq-is-propᵉ (is-prop-leq-ℕᵉ mᵉ nᵉ))
cases-htpy-succ-based-strong-ind-ℕᵉ kᵉ Pᵉ pSᵉ nᵉ Nᵉ fᵉ mᵉ Mᵉ (inrᵉ αᵉ) Hᵉ =
  ex-falsoᵉ (neg-succ-leq-ℕᵉ nᵉ (concatenate-eq-leq-ℕᵉ nᵉ (invᵉ αᵉ) Hᵉ))

htpy-succ-based-strong-ind-ℕᵉ :
  {lᵉ : Level} (kᵉ : ℕᵉ) (Pᵉ : ℕᵉ → UUᵉ lᵉ) →
  (pSᵉ : (xᵉ : ℕᵉ) → kᵉ ≤-ℕᵉ xᵉ → based-□-≤-ℕᵉ kᵉ Pᵉ xᵉ → Pᵉ (succ-ℕᵉ xᵉ)) →
  (nᵉ : ℕᵉ) (Nᵉ : kᵉ ≤-ℕᵉ nᵉ) (fᵉ : based-□-≤-ℕᵉ kᵉ Pᵉ nᵉ)
  (mᵉ : ℕᵉ) (Mᵉ : kᵉ ≤-ℕᵉ mᵉ) (Hᵉ : leq-ℕᵉ mᵉ (succ-ℕᵉ nᵉ)) (Kᵉ : leq-ℕᵉ mᵉ nᵉ) →
  succ-based-strong-ind-ℕᵉ kᵉ Pᵉ pSᵉ nᵉ Nᵉ fᵉ mᵉ Mᵉ Hᵉ ＝ᵉ fᵉ mᵉ Mᵉ Kᵉ
htpy-succ-based-strong-ind-ℕᵉ kᵉ Pᵉ pSᵉ nᵉ Nᵉ fᵉ mᵉ Mᵉ Hᵉ =
  cases-htpy-succ-based-strong-ind-ℕᵉ kᵉ Pᵉ pSᵉ nᵉ Nᵉ fᵉ mᵉ Mᵉ (cases-leq-succ-ℕᵉ Hᵉ)

cases-eq-succ-based-strong-ind-ℕᵉ :
  {lᵉ : Level} (kᵉ : ℕᵉ) (Pᵉ : ℕᵉ → UUᵉ lᵉ)
  (pSᵉ : (xᵉ : ℕᵉ) → kᵉ ≤-ℕᵉ xᵉ → based-□-≤-ℕᵉ kᵉ Pᵉ xᵉ → Pᵉ (succ-ℕᵉ xᵉ)) →
  (nᵉ : ℕᵉ) (Nᵉ : kᵉ ≤-ℕᵉ nᵉ) (fᵉ : based-□-≤-ℕᵉ kᵉ Pᵉ nᵉ) (Mᵉ : kᵉ ≤-ℕᵉ succ-ℕᵉ nᵉ)
  (cᵉ : (leq-ℕᵉ (succ-ℕᵉ nᵉ) nᵉ) +ᵉ (succ-ℕᵉ nᵉ ＝ᵉ succ-ℕᵉ nᵉ)) →
  cases-succ-based-strong-ind-ℕᵉ kᵉ Pᵉ pSᵉ nᵉ Nᵉ fᵉ (succ-ℕᵉ nᵉ) Mᵉ cᵉ ＝ᵉ pSᵉ nᵉ Nᵉ fᵉ
cases-eq-succ-based-strong-ind-ℕᵉ kᵉ Pᵉ pSᵉ nᵉ Nᵉ fᵉ Mᵉ (inlᵉ Hᵉ) =
  ex-falsoᵉ (neg-succ-leq-ℕᵉ nᵉ Hᵉ)
cases-eq-succ-based-strong-ind-ℕᵉ kᵉ Pᵉ pSᵉ nᵉ Nᵉ fᵉ Mᵉ (inrᵉ αᵉ) =
  apᵉ
    ( (cases-succ-based-strong-ind-ℕᵉ kᵉ Pᵉ pSᵉ nᵉ Nᵉ fᵉ (succ-ℕᵉ nᵉ) Mᵉ) ∘ᵉ inrᵉ)
    ( eq-is-prop'ᵉ (is-set-ℕᵉ (succ-ℕᵉ nᵉ) (succ-ℕᵉ nᵉ)) αᵉ reflᵉ)

eq-succ-based-strong-ind-ℕᵉ :
  {lᵉ : Level} (kᵉ : ℕᵉ) (Pᵉ : ℕᵉ → UUᵉ lᵉ)
  (pSᵉ : (xᵉ : ℕᵉ) → kᵉ ≤-ℕᵉ xᵉ → (based-□-≤-ℕᵉ kᵉ Pᵉ xᵉ) → Pᵉ (succ-ℕᵉ xᵉ)) →
  (nᵉ : ℕᵉ) (Nᵉ : kᵉ ≤-ℕᵉ nᵉ) (fᵉ : based-□-≤-ℕᵉ kᵉ Pᵉ nᵉ) (Mᵉ : kᵉ ≤-ℕᵉ succ-ℕᵉ nᵉ)
  (Hᵉ : leq-ℕᵉ (succ-ℕᵉ nᵉ) (succ-ℕᵉ nᵉ)) →
  succ-based-strong-ind-ℕᵉ kᵉ Pᵉ pSᵉ nᵉ Nᵉ fᵉ (succ-ℕᵉ nᵉ) Mᵉ Hᵉ ＝ᵉ pSᵉ nᵉ Nᵉ fᵉ
eq-succ-based-strong-ind-ℕᵉ kᵉ Pᵉ pSᵉ nᵉ Nᵉ fᵉ Mᵉ Hᵉ =
  cases-eq-succ-based-strong-ind-ℕᵉ kᵉ Pᵉ pSᵉ nᵉ Nᵉ fᵉ Mᵉ (cases-leq-succ-ℕᵉ Hᵉ)
```

### The inductive step in the proof of based strong induction

```agda
module _
  {lᵉ : Level} (kᵉ : ℕᵉ) (Pᵉ : ℕᵉ → UUᵉ lᵉ) (zᵉ : based-□-≤-ℕᵉ kᵉ Pᵉ kᵉ)
  (sᵉ : (mᵉ : ℕᵉ) → kᵉ ≤-ℕᵉ mᵉ → based-□-≤-ℕᵉ kᵉ Pᵉ mᵉ → based-□-≤-ℕᵉ kᵉ Pᵉ (succ-ℕᵉ mᵉ))
  where

  inductive-step-based-strong-ind-ℕᵉ : (nᵉ : ℕᵉ) → kᵉ ≤-ℕᵉ nᵉ → based-□-≤-ℕᵉ kᵉ Pᵉ nᵉ
  inductive-step-based-strong-ind-ℕᵉ =
    based-ind-ℕᵉ kᵉ (based-□-≤-ℕᵉ kᵉ Pᵉ) zᵉ sᵉ

  compute-base-inductive-step-based-strong-ind-ℕᵉ :
    (Kᵉ : kᵉ ≤-ℕᵉ kᵉ) (mᵉ : ℕᵉ) (Mᵉ : kᵉ ≤-ℕᵉ mᵉ) (Hᵉ : mᵉ ≤-ℕᵉ kᵉ) →
    inductive-step-based-strong-ind-ℕᵉ kᵉ Kᵉ mᵉ Mᵉ Hᵉ ＝ᵉ zᵉ mᵉ Mᵉ Hᵉ
  compute-base-inductive-step-based-strong-ind-ℕᵉ Kᵉ mᵉ Mᵉ =
    htpy-eqᵉ
      ( htpy-eqᵉ
        ( htpy-eqᵉ
          ( compute-base-based-ind-ℕᵉ kᵉ (based-□-≤-ℕᵉ kᵉ Pᵉ) zᵉ sᵉ Kᵉ)
          ( mᵉ))
        ( Mᵉ))

  compute-succ-inductive-step-based-strong-ind-ℕᵉ :
    (nᵉ : ℕᵉ) (Nᵉ : kᵉ ≤-ℕᵉ nᵉ) (N'ᵉ : kᵉ ≤-ℕᵉ succ-ℕᵉ nᵉ) →
    (mᵉ : ℕᵉ) (Mᵉ : kᵉ ≤-ℕᵉ mᵉ) (Hᵉ : mᵉ ≤-ℕᵉ succ-ℕᵉ nᵉ) →
    inductive-step-based-strong-ind-ℕᵉ (succ-ℕᵉ nᵉ) N'ᵉ mᵉ Mᵉ Hᵉ ＝ᵉ
    sᵉ nᵉ Nᵉ (inductive-step-based-strong-ind-ℕᵉ nᵉ Nᵉ) mᵉ Mᵉ Hᵉ
  compute-succ-inductive-step-based-strong-ind-ℕᵉ nᵉ Nᵉ N'ᵉ mᵉ Mᵉ =
    htpy-eqᵉ
      ( htpy-eqᵉ
        ( htpy-eqᵉ
          ( compute-succ-based-ind-ℕᵉ kᵉ (based-□-≤-ℕᵉ kᵉ Pᵉ) zᵉ sᵉ nᵉ Nᵉ N'ᵉ)
          ( mᵉ))
        ( Mᵉ))

  ap-inductive-step-based-strong-ind-ℕᵉ :
    {nᵉ n'ᵉ : ℕᵉ} (pᵉ : nᵉ ＝ᵉ n'ᵉ) (Nᵉ : kᵉ ≤-ℕᵉ nᵉ) (N'ᵉ : kᵉ ≤-ℕᵉ n'ᵉ)
    (mᵉ : ℕᵉ) (Mᵉ : kᵉ ≤-ℕᵉ mᵉ) (Hᵉ : mᵉ ≤-ℕᵉ nᵉ) (H'ᵉ : mᵉ ≤-ℕᵉ n'ᵉ) →
    inductive-step-based-strong-ind-ℕᵉ nᵉ Nᵉ mᵉ Mᵉ Hᵉ ＝ᵉ
    inductive-step-based-strong-ind-ℕᵉ n'ᵉ N'ᵉ mᵉ Mᵉ H'ᵉ
  ap-inductive-step-based-strong-ind-ℕᵉ reflᵉ Nᵉ N'ᵉ mᵉ Mᵉ Hᵉ H'ᵉ =
    ap-binaryᵉ
      ( λ uᵉ vᵉ → inductive-step-based-strong-ind-ℕᵉ _ uᵉ mᵉ Mᵉ vᵉ)
      ( eq-is-propᵉ (is-prop-leq-ℕᵉ kᵉ _))
      ( eq-is-propᵉ (is-prop-leq-ℕᵉ mᵉ _))
```

### The based strong induction principle

```agda
based-strong-ind-ℕᵉ :
  {lᵉ : Level} (kᵉ : ℕᵉ) (Pᵉ : ℕᵉ → UUᵉ lᵉ) (p0ᵉ : Pᵉ kᵉ) →
  (pSᵉ : (xᵉ : ℕᵉ) → kᵉ ≤-ℕᵉ xᵉ → based-□-≤-ℕᵉ kᵉ Pᵉ xᵉ → Pᵉ (succ-ℕᵉ xᵉ))
  (nᵉ : ℕᵉ) → kᵉ ≤-ℕᵉ nᵉ → Pᵉ nᵉ
based-strong-ind-ℕᵉ kᵉ Pᵉ p0ᵉ pSᵉ =
  ε-based-□-≤-ℕᵉ kᵉ
    ( inductive-step-based-strong-ind-ℕᵉ kᵉ Pᵉ
      ( base-based-strong-ind-ℕᵉ kᵉ Pᵉ p0ᵉ)
      ( succ-based-strong-ind-ℕᵉ kᵉ Pᵉ pSᵉ))

compute-base-based-strong-ind-ℕᵉ :
  {lᵉ : Level} (kᵉ : ℕᵉ) (Pᵉ : ℕᵉ → UUᵉ lᵉ) (p0ᵉ : Pᵉ kᵉ) →
  (pSᵉ : (xᵉ : ℕᵉ) → kᵉ ≤-ℕᵉ xᵉ → (based-□-≤-ℕᵉ kᵉ Pᵉ xᵉ) → Pᵉ (succ-ℕᵉ xᵉ)) →
  based-strong-ind-ℕᵉ kᵉ Pᵉ p0ᵉ pSᵉ kᵉ (refl-leq-ℕᵉ kᵉ) ＝ᵉ p0ᵉ
compute-base-based-strong-ind-ℕᵉ kᵉ Pᵉ p0ᵉ pSᵉ =
  ( compute-base-inductive-step-based-strong-ind-ℕᵉ kᵉ Pᵉ
    ( base-based-strong-ind-ℕᵉ kᵉ Pᵉ p0ᵉ)
    ( succ-based-strong-ind-ℕᵉ kᵉ Pᵉ pSᵉ)
    ( refl-leq-ℕᵉ kᵉ)
    ( kᵉ)
    ( refl-leq-ℕᵉ kᵉ)
    ( refl-leq-ℕᵉ kᵉ)) ∙ᵉ
  ( eq-base-based-strong-ind-ℕᵉ kᵉ Pᵉ p0ᵉ (refl-leq-ℕᵉ kᵉ) (refl-leq-ℕᵉ kᵉ))

cases-eq-inductive-step-compute-succ-based-strong-ind-ℕᵉ :
  { lᵉ : Level} (kᵉ : ℕᵉ) (Pᵉ : ℕᵉ → UUᵉ lᵉ) (p0ᵉ : Pᵉ kᵉ) →
  ( pSᵉ : (xᵉ : ℕᵉ) → kᵉ ≤-ℕᵉ xᵉ → based-□-≤-ℕᵉ kᵉ Pᵉ xᵉ → Pᵉ (succ-ℕᵉ xᵉ))
  ( nᵉ : ℕᵉ) (Nᵉ : kᵉ ≤-ℕᵉ nᵉ) (N'ᵉ : kᵉ ≤-ℕᵉ succ-ℕᵉ nᵉ)
  ( mᵉ : ℕᵉ) (Mᵉ : kᵉ ≤-ℕᵉ mᵉ) (Hᵉ : mᵉ ≤-ℕᵉ succ-ℕᵉ nᵉ) →
  ( cᵉ : (mᵉ ≤-ℕᵉ nᵉ) +ᵉ (mᵉ ＝ᵉ succ-ℕᵉ nᵉ)) →
  ( αᵉ :
    (Iᵉ : kᵉ ≤-ℕᵉ nᵉ) (Jᵉ : mᵉ ≤-ℕᵉ nᵉ) →
    inductive-step-based-strong-ind-ℕᵉ kᵉ Pᵉ
      ( base-based-strong-ind-ℕᵉ kᵉ Pᵉ p0ᵉ)
      ( succ-based-strong-ind-ℕᵉ kᵉ Pᵉ pSᵉ)
      ( nᵉ)
      ( Iᵉ)
      ( mᵉ)
      ( Mᵉ)
      ( Jᵉ) ＝ᵉ
    inductive-step-based-strong-ind-ℕᵉ kᵉ Pᵉ
      ( base-based-strong-ind-ℕᵉ kᵉ Pᵉ p0ᵉ)
      ( succ-based-strong-ind-ℕᵉ kᵉ Pᵉ pSᵉ)
      ( mᵉ)
      ( Mᵉ)
      ( mᵉ)
      ( Mᵉ)
      ( refl-leq-ℕᵉ mᵉ)) →
  inductive-step-based-strong-ind-ℕᵉ kᵉ Pᵉ
    ( base-based-strong-ind-ℕᵉ kᵉ Pᵉ p0ᵉ)
    ( succ-based-strong-ind-ℕᵉ kᵉ Pᵉ pSᵉ)
    ( succ-ℕᵉ nᵉ)
    ( N'ᵉ)
    ( mᵉ)
    ( Mᵉ)
    ( Hᵉ) ＝ᵉ
  inductive-step-based-strong-ind-ℕᵉ kᵉ Pᵉ
    ( base-based-strong-ind-ℕᵉ kᵉ Pᵉ p0ᵉ)
    ( succ-based-strong-ind-ℕᵉ kᵉ Pᵉ pSᵉ)
    ( mᵉ)
    ( Mᵉ)
    ( mᵉ)
    ( Mᵉ)
    ( refl-leq-ℕᵉ mᵉ)
cases-eq-inductive-step-compute-succ-based-strong-ind-ℕᵉ
  kᵉ Pᵉ p0ᵉ pSᵉ nᵉ Nᵉ N'ᵉ mᵉ Mᵉ Hᵉ (inlᵉ H'ᵉ) αᵉ =
  ( compute-succ-inductive-step-based-strong-ind-ℕᵉ kᵉ Pᵉ
    ( base-based-strong-ind-ℕᵉ kᵉ Pᵉ p0ᵉ)
    ( succ-based-strong-ind-ℕᵉ kᵉ Pᵉ pSᵉ)
    ( nᵉ)
    ( Nᵉ)
    ( N'ᵉ)
    ( mᵉ)
    ( Mᵉ)
    ( Hᵉ)) ∙ᵉ
  ( ( htpy-succ-based-strong-ind-ℕᵉ kᵉ Pᵉ pSᵉ nᵉ Nᵉ
      ( inductive-step-based-strong-ind-ℕᵉ kᵉ Pᵉ
        ( base-based-strong-ind-ℕᵉ kᵉ Pᵉ p0ᵉ)
        ( succ-based-strong-ind-ℕᵉ kᵉ Pᵉ pSᵉ)
        ( nᵉ)
        ( Nᵉ))
      ( mᵉ)
      ( Mᵉ)
      ( Hᵉ)
      ( H'ᵉ)) ∙ᵉ
    ( αᵉ Nᵉ H'ᵉ))
cases-eq-inductive-step-compute-succ-based-strong-ind-ℕᵉ
  kᵉ Pᵉ p0ᵉ pSᵉ nᵉ Nᵉ N'ᵉ mᵉ Mᵉ Hᵉ (inrᵉ pᵉ) αᵉ =
  ap-inductive-step-based-strong-ind-ℕᵉ kᵉ Pᵉ
    ( base-based-strong-ind-ℕᵉ kᵉ Pᵉ p0ᵉ)
    ( succ-based-strong-ind-ℕᵉ kᵉ Pᵉ pSᵉ)
    ( invᵉ pᵉ)
    ( N'ᵉ)
    ( Mᵉ)
    ( mᵉ)
    ( Mᵉ)
    ( Hᵉ)
    ( refl-leq-ℕᵉ mᵉ)

eq-inductive-step-compute-succ-based-strong-ind-ℕᵉ :
  {lᵉ : Level} (kᵉ : ℕᵉ) (Pᵉ : ℕᵉ → UUᵉ lᵉ) (p0ᵉ : Pᵉ kᵉ) →
  (pSᵉ : (xᵉ : ℕᵉ) → kᵉ ≤-ℕᵉ xᵉ → based-□-≤-ℕᵉ kᵉ Pᵉ xᵉ → Pᵉ (succ-ℕᵉ xᵉ))
  (nᵉ : ℕᵉ) (Nᵉ : kᵉ ≤-ℕᵉ nᵉ)
  (mᵉ : ℕᵉ) (Mᵉ : kᵉ ≤-ℕᵉ mᵉ) (Hᵉ : mᵉ ≤-ℕᵉ nᵉ) →
  inductive-step-based-strong-ind-ℕᵉ kᵉ Pᵉ
    ( base-based-strong-ind-ℕᵉ kᵉ Pᵉ p0ᵉ)
    ( succ-based-strong-ind-ℕᵉ kᵉ Pᵉ pSᵉ)
    ( nᵉ)
    ( Nᵉ)
    ( mᵉ)
    ( Mᵉ)
    ( Hᵉ) ＝ᵉ
  inductive-step-based-strong-ind-ℕᵉ kᵉ Pᵉ
    ( base-based-strong-ind-ℕᵉ kᵉ Pᵉ p0ᵉ)
    ( succ-based-strong-ind-ℕᵉ kᵉ Pᵉ pSᵉ)
    ( mᵉ)
    ( Mᵉ)
    ( mᵉ)
    ( Mᵉ)
    ( refl-leq-ℕᵉ mᵉ)
eq-inductive-step-compute-succ-based-strong-ind-ℕᵉ kᵉ Pᵉ p0ᵉ pSᵉ nᵉ Nᵉ mᵉ Mᵉ =
  based-ind-ℕᵉ kᵉ
    ( λ iᵉ →
      (Iᵉ : kᵉ ≤-ℕᵉ iᵉ) (Jᵉ : mᵉ ≤-ℕᵉ iᵉ) →
      inductive-step-based-strong-ind-ℕᵉ kᵉ Pᵉ
        ( base-based-strong-ind-ℕᵉ kᵉ Pᵉ p0ᵉ)
        ( succ-based-strong-ind-ℕᵉ kᵉ Pᵉ pSᵉ)
        ( iᵉ)
        ( Iᵉ)
        ( mᵉ)
        ( Mᵉ)
        ( Jᵉ) ＝ᵉ
      inductive-step-based-strong-ind-ℕᵉ kᵉ Pᵉ
        ( base-based-strong-ind-ℕᵉ kᵉ Pᵉ p0ᵉ)
        ( succ-based-strong-ind-ℕᵉ kᵉ Pᵉ pSᵉ)
        ( mᵉ)
        ( Mᵉ)
        ( mᵉ)
        ( Mᵉ)
        ( refl-leq-ℕᵉ mᵉ))
    ( λ Iᵉ Jᵉ →
      ap-inductive-step-based-strong-ind-ℕᵉ kᵉ Pᵉ
        ( base-based-strong-ind-ℕᵉ kᵉ Pᵉ p0ᵉ)
        ( succ-based-strong-ind-ℕᵉ kᵉ Pᵉ pSᵉ)
        ( antisymmetric-leq-ℕᵉ kᵉ mᵉ Mᵉ Jᵉ)
        ( Iᵉ)
        ( Mᵉ)
        ( mᵉ)
        ( Mᵉ)
        ( Jᵉ)
        ( refl-leq-ℕᵉ mᵉ))
    ( λ iᵉ I'ᵉ αᵉ Iᵉ Jᵉ →
      cases-eq-inductive-step-compute-succ-based-strong-ind-ℕᵉ
        kᵉ Pᵉ p0ᵉ pSᵉ iᵉ I'ᵉ Iᵉ mᵉ Mᵉ
        ( Jᵉ)
        ( cases-leq-succ-ℕᵉ Jᵉ)
        ( αᵉ))
    ( nᵉ)
    ( Nᵉ)
    ( Nᵉ)

compute-succ-based-strong-ind-ℕᵉ :
  { lᵉ : Level} (kᵉ : ℕᵉ) (Pᵉ : ℕᵉ → UUᵉ lᵉ) (p0ᵉ : Pᵉ kᵉ) →
  ( pSᵉ : (xᵉ : ℕᵉ) → kᵉ ≤-ℕᵉ xᵉ → (based-□-≤-ℕᵉ kᵉ Pᵉ xᵉ) → Pᵉ (succ-ℕᵉ xᵉ)) →
  ( nᵉ : ℕᵉ) (Nᵉ : kᵉ ≤-ℕᵉ nᵉ) (N'ᵉ : kᵉ ≤-ℕᵉ succ-ℕᵉ nᵉ) →
  based-strong-ind-ℕᵉ kᵉ Pᵉ p0ᵉ pSᵉ (succ-ℕᵉ nᵉ) N'ᵉ ＝ᵉ
  pSᵉ nᵉ Nᵉ (λ mᵉ Mᵉ Hᵉ → based-strong-ind-ℕᵉ kᵉ Pᵉ p0ᵉ pSᵉ mᵉ Mᵉ)
compute-succ-based-strong-ind-ℕᵉ kᵉ Pᵉ p0ᵉ pSᵉ nᵉ Nᵉ N'ᵉ =
  ( compute-succ-inductive-step-based-strong-ind-ℕᵉ kᵉ Pᵉ
    ( base-based-strong-ind-ℕᵉ kᵉ Pᵉ p0ᵉ)
    ( succ-based-strong-ind-ℕᵉ kᵉ Pᵉ pSᵉ)
    ( nᵉ)
    ( Nᵉ)
    ( N'ᵉ)
    ( succ-ℕᵉ nᵉ)
    ( N'ᵉ)
    ( refl-leq-ℕᵉ (succ-ℕᵉ nᵉ))) ∙ᵉ
  ( ( eq-succ-based-strong-ind-ℕᵉ kᵉ Pᵉ pSᵉ nᵉ Nᵉ
      ( inductive-step-based-strong-ind-ℕᵉ kᵉ Pᵉ
        ( base-based-strong-ind-ℕᵉ kᵉ Pᵉ p0ᵉ)
        ( succ-based-strong-ind-ℕᵉ kᵉ Pᵉ pSᵉ)
        ( nᵉ)
        ( Nᵉ))
      ( N'ᵉ)
      ( refl-leq-ℕᵉ nᵉ)) ∙ᵉ
    ( apᵉ
      ( pSᵉ nᵉ Nᵉ)
      ( eq-htpyᵉ
        ( λ mᵉ →
          eq-htpyᵉ
          ( eq-htpyᵉ ∘ᵉ
            eq-inductive-step-compute-succ-based-strong-ind-ℕᵉ
              kᵉ Pᵉ p0ᵉ pSᵉ nᵉ Nᵉ mᵉ)))))
```

## Corollaries

### Based strong induction for a type family defined for `n ≥ k`

```agda
based-□-≤-ℕ'ᵉ : {lᵉ : Level} (kᵉ : ℕᵉ) → ((nᵉ : ℕᵉ) → (kᵉ ≤-ℕᵉ nᵉ) → UUᵉ lᵉ) → ℕᵉ → UUᵉ lᵉ
based-□-≤-ℕ'ᵉ kᵉ Pᵉ xᵉ = (mᵉ : ℕᵉ) → (Hᵉ : kᵉ ≤-ℕᵉ mᵉ) → (mᵉ ≤-ℕᵉ xᵉ) → Pᵉ mᵉ Hᵉ

compute-base-□-≤-ℕ'ᵉ :
  {lᵉ : Level} (kᵉ : ℕᵉ) (Pᵉ : (nᵉ : ℕᵉ) → (kᵉ ≤-ℕᵉ nᵉ) → UUᵉ lᵉ) (xᵉ : ℕᵉ) →
  based-□-≤-ℕᵉ kᵉ (λ nᵉ → (Hᵉ : kᵉ ≤-ℕᵉ nᵉ) → Pᵉ nᵉ Hᵉ) xᵉ →
  based-□-≤-ℕ'ᵉ kᵉ Pᵉ xᵉ
compute-base-□-≤-ℕ'ᵉ kᵉ Pᵉ xᵉ pᵉ mᵉ Hᵉ Iᵉ = pᵉ mᵉ Hᵉ Iᵉ Hᵉ

based-strong-ind-ℕ'ᵉ :
  {lᵉ : Level} (kᵉ : ℕᵉ) (Pᵉ : (nᵉ : ℕᵉ) → (kᵉ ≤-ℕᵉ nᵉ → UUᵉ lᵉ))
  (p0ᵉ : Pᵉ kᵉ (refl-leq-ℕᵉ kᵉ)) →
  (pSᵉ : (xᵉ : ℕᵉ) → (Hᵉ : kᵉ ≤-ℕᵉ xᵉ) →
    based-□-≤-ℕ'ᵉ kᵉ Pᵉ xᵉ →
    Pᵉ (succ-ℕᵉ xᵉ) (preserves-leq-succ-ℕᵉ kᵉ xᵉ Hᵉ))
  (nᵉ : ℕᵉ) → (Hᵉ : kᵉ ≤-ℕᵉ nᵉ) → Pᵉ nᵉ Hᵉ
based-strong-ind-ℕ'ᵉ {lᵉ} kᵉ Pᵉ p0ᵉ pSᵉ nᵉ Hᵉ =
  based-strong-ind-ℕᵉ
    ( kᵉ)
    ( λ nᵉ → (Hᵉ : kᵉ ≤-ℕᵉ nᵉ) → Pᵉ nᵉ Hᵉ)
    ( apply-dependent-universal-property-contrᵉ
      ( refl-leq-ℕᵉ kᵉ)
      ( is-proof-irrelevant-is-propᵉ (is-prop-leq-ℕᵉ kᵉ kᵉ) (refl-leq-ℕᵉ kᵉ))
      ( Pᵉ kᵉ)
      ( p0ᵉ))
    ( λ xᵉ Hᵉ pᵉ →
      apply-dependent-universal-property-contrᵉ
        ( preserves-leq-succ-ℕᵉ kᵉ xᵉ Hᵉ)
        ( is-proof-irrelevant-is-propᵉ
          ( is-prop-leq-ℕᵉ kᵉ (succ-ℕᵉ xᵉ))
          ( preserves-leq-succ-ℕᵉ kᵉ xᵉ Hᵉ))
        ( Pᵉ (succ-ℕᵉ xᵉ))
        ( pSᵉ xᵉ Hᵉ ( compute-base-□-≤-ℕ'ᵉ kᵉ Pᵉ xᵉ pᵉ)))
    ( nᵉ)
    ( Hᵉ)
    ( Hᵉ)
```