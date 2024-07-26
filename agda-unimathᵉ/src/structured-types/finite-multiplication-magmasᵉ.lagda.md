# Finite multiplication in magmas

```agda
module structured-types.finite-multiplication-magmasᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.coproduct-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import structured-types.magmasᵉ

open import univalent-combinatorics.countingᵉ
open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Definition

```agda
fold-Fin-mul-Magmaᵉ :
  {lᵉ : Level} (Mᵉ : Magmaᵉ lᵉ) → type-Magmaᵉ Mᵉ →
  (kᵉ : ℕᵉ) → (Finᵉ kᵉ → type-Magmaᵉ Mᵉ) → type-Magmaᵉ Mᵉ
fold-Fin-mul-Magmaᵉ Mᵉ mᵉ zero-ℕᵉ fᵉ = mᵉ
fold-Fin-mul-Magmaᵉ Mᵉ mᵉ (succ-ℕᵉ kᵉ) fᵉ =
  mul-Magmaᵉ Mᵉ (fold-Fin-mul-Magmaᵉ Mᵉ mᵉ kᵉ (fᵉ ∘ᵉ inlᵉ)) (fᵉ (inrᵉ starᵉ))

fold-count-mul-Magma'ᵉ :
  {l1ᵉ l2ᵉ : Level} (Mᵉ : Magmaᵉ l1ᵉ) → type-Magmaᵉ Mᵉ →
  {Aᵉ : UUᵉ l2ᵉ} (kᵉ : ℕᵉ) → (Finᵉ kᵉ ≃ᵉ Aᵉ) → (Aᵉ → type-Magmaᵉ Mᵉ) → type-Magmaᵉ Mᵉ
fold-count-mul-Magma'ᵉ Mᵉ mᵉ kᵉ eᵉ fᵉ = fold-Fin-mul-Magmaᵉ Mᵉ mᵉ kᵉ (fᵉ ∘ᵉ map-equivᵉ eᵉ)

fold-count-mul-Magmaᵉ :
  {l1ᵉ l2ᵉ : Level} (Mᵉ : Magmaᵉ l1ᵉ) → type-Magmaᵉ Mᵉ →
  {Aᵉ : UUᵉ l2ᵉ} → countᵉ Aᵉ → (Aᵉ → type-Magmaᵉ Mᵉ) → type-Magmaᵉ Mᵉ
fold-count-mul-Magmaᵉ Mᵉ mᵉ eᵉ fᵉ =
  fold-Fin-mul-Magmaᵉ Mᵉ mᵉ (number-of-elements-countᵉ eᵉ) (fᵉ ∘ᵉ map-equiv-countᵉ eᵉ)
```