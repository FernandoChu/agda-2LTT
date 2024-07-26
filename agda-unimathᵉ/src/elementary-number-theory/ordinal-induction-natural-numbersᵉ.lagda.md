# The ordinal induction principle for the natural numbers

```agda
module elementary-number-theory.ordinal-induction-natural-numbersᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ
open import elementary-number-theory.strict-inequality-natural-numbersᵉ

open import foundation.empty-typesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Theᵉ **ordinalᵉ inductionᵉ principleᵉ ofᵉ theᵉ naturalᵉ numbers**ᵉ isᵉ theᵉ well-foundedᵉ
inductionᵉ principleᵉ ofᵉ ℕ.ᵉ

## To Do

Theᵉ computationᵉ ruleᵉ shouldᵉ stillᵉ beᵉ proven.ᵉ

```agda
□-<-ℕᵉ :
  {lᵉ : Level} → (ℕᵉ → UUᵉ lᵉ) → ℕᵉ → UUᵉ lᵉ
□-<-ℕᵉ Pᵉ nᵉ = (mᵉ : ℕᵉ) → (le-ℕᵉ mᵉ nᵉ) → Pᵉ mᵉ

reflect-□-<-ℕᵉ :
  {lᵉ : Level} (Pᵉ : ℕᵉ → UUᵉ lᵉ) →
  (( nᵉ : ℕᵉ) → □-<-ℕᵉ Pᵉ nᵉ) → (nᵉ : ℕᵉ) → Pᵉ nᵉ
reflect-□-<-ℕᵉ Pᵉ fᵉ nᵉ = fᵉ (succ-ℕᵉ nᵉ) nᵉ (succ-le-ℕᵉ nᵉ)

zero-ordinal-ind-ℕᵉ :
  { lᵉ : Level} (Pᵉ : ℕᵉ → UUᵉ lᵉ) → □-<-ℕᵉ Pᵉ zero-ℕᵉ
zero-ordinal-ind-ℕᵉ Pᵉ mᵉ tᵉ = ex-falsoᵉ (contradiction-le-zero-ℕᵉ mᵉ tᵉ)

succ-ordinal-ind-ℕᵉ :
  {lᵉ : Level} (Pᵉ : ℕᵉ → UUᵉ lᵉ) → ((nᵉ : ℕᵉ) → (□-<-ℕᵉ Pᵉ nᵉ) → Pᵉ nᵉ) →
  (kᵉ : ℕᵉ) → □-<-ℕᵉ Pᵉ kᵉ → □-<-ℕᵉ Pᵉ (succ-ℕᵉ kᵉ)
succ-ordinal-ind-ℕᵉ Pᵉ fᵉ kᵉ gᵉ mᵉ tᵉ =
  fᵉ mᵉ (λ m'ᵉ t'ᵉ → gᵉ m'ᵉ (transitive-le-ℕ'ᵉ m'ᵉ mᵉ kᵉ t'ᵉ tᵉ))

induction-ordinal-ind-ℕᵉ :
  { lᵉ : Level} (Pᵉ : ℕᵉ → UUᵉ lᵉ) →
  ( qSᵉ : (kᵉ : ℕᵉ) → □-<-ℕᵉ Pᵉ kᵉ → □-<-ℕᵉ Pᵉ (succ-ℕᵉ kᵉ))
  ( nᵉ : ℕᵉ) → □-<-ℕᵉ Pᵉ nᵉ
induction-ordinal-ind-ℕᵉ Pᵉ qSᵉ zero-ℕᵉ = zero-ordinal-ind-ℕᵉ Pᵉ
induction-ordinal-ind-ℕᵉ Pᵉ qSᵉ (succ-ℕᵉ nᵉ) =
  qSᵉ nᵉ (induction-ordinal-ind-ℕᵉ Pᵉ qSᵉ nᵉ)

ordinal-ind-ℕᵉ :
  { lᵉ : Level} (Pᵉ : ℕᵉ → UUᵉ lᵉ) →
  ( (nᵉ : ℕᵉ) → (□-<-ℕᵉ Pᵉ nᵉ) → Pᵉ nᵉ) →
  ( nᵉ : ℕᵉ) → Pᵉ nᵉ
ordinal-ind-ℕᵉ Pᵉ fᵉ =
  reflect-□-<-ℕᵉ Pᵉ
    ( induction-ordinal-ind-ℕᵉ Pᵉ (succ-ordinal-ind-ℕᵉ Pᵉ fᵉ))
```