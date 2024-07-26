# Bounded sums of arithmetic functions

```agda
module elementary-number-theory.bounded-sums-arithmetic-functionsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.arithmetic-functionsᵉ
open import elementary-number-theory.natural-numbersᵉ
open import elementary-number-theory.nonzero-natural-numbersᵉ

open import foundation.coproduct-typesᵉ
open import foundation.decidable-propositionsᵉ
open import foundation.decidable-typesᵉ
open import foundation.function-typesᵉ
open import foundation.universe-levelsᵉ

open import ring-theory.ringsᵉ
```

</details>

## Idea

Givenᵉ aᵉ decidableᵉ predicateᵉ `P`ᵉ onᵉ theᵉ nonzeroᵉ naturalᵉ numbers,ᵉ andᵉ aᵉ mapᵉ `f`ᵉ
fromᵉ theᵉ nonzeroᵉ naturalᵉ numbersᵉ in `P`ᵉ intoᵉ aᵉ ringᵉ `R`,ᵉ theᵉ boundedᵉ sumᵉ isᵉ aᵉ
summationᵉ ofᵉ theᵉ valuesᵉ ofᵉ `f`ᵉ upᵉ to anᵉ upperᵉ boundᵉ `b`.ᵉ

## Definition

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  restricted-arithmetic-function-Ringᵉ :
    {l'ᵉ : Level} (Pᵉ : nonzero-ℕᵉ → Decidable-Propᵉ l'ᵉ) → UUᵉ (lᵉ ⊔ l'ᵉ)
  restricted-arithmetic-function-Ringᵉ Pᵉ =
    (xᵉ : nonzero-ℕᵉ) → type-Decidable-Propᵉ (Pᵉ xᵉ) → type-Ringᵉ Rᵉ

  shift-arithmetic-function-Ringᵉ :
    type-arithmetic-functions-Ringᵉ Rᵉ → type-arithmetic-functions-Ringᵉ Rᵉ
  shift-arithmetic-function-Ringᵉ fᵉ = fᵉ ∘ᵉ succ-nonzero-ℕᵉ

  shift-restricted-arithmetic-function-Ringᵉ :
    {l'ᵉ : Level} (Pᵉ : nonzero-ℕᵉ → Decidable-Propᵉ l'ᵉ) →
    restricted-arithmetic-function-Ringᵉ Pᵉ →
    restricted-arithmetic-function-Ringᵉ (Pᵉ ∘ᵉ succ-nonzero-ℕᵉ)
  shift-restricted-arithmetic-function-Ringᵉ Pᵉ fᵉ = fᵉ ∘ᵉ succ-nonzero-ℕᵉ

  case-one-bounded-sum-arithmetic-function-Ringᵉ :
    {l'ᵉ : Level} → (Pᵉ : Decidable-Propᵉ l'ᵉ) →
    is-decidableᵉ (type-Decidable-Propᵉ Pᵉ) →
    (type-Decidable-Propᵉ Pᵉ → type-Ringᵉ Rᵉ) → type-Ringᵉ Rᵉ
  case-one-bounded-sum-arithmetic-function-Ringᵉ Pᵉ (inlᵉ xᵉ) fᵉ = fᵉ xᵉ
  case-one-bounded-sum-arithmetic-function-Ringᵉ Pᵉ (inrᵉ xᵉ) fᵉ =
    zero-Ringᵉ Rᵉ

  bounded-sum-arithmetic-function-Ringᵉ :
    (bᵉ : ℕᵉ) {l'ᵉ : Level} (Pᵉ : nonzero-ℕᵉ → Decidable-Propᵉ l'ᵉ)
    (fᵉ : restricted-arithmetic-function-Ringᵉ Pᵉ) → type-Ringᵉ Rᵉ
  bounded-sum-arithmetic-function-Ringᵉ zero-ℕᵉ Pᵉ fᵉ = zero-Ringᵉ Rᵉ
  bounded-sum-arithmetic-function-Ringᵉ (succ-ℕᵉ zero-ℕᵉ) Pᵉ fᵉ =
    case-one-bounded-sum-arithmetic-function-Ringᵉ
      ( Pᵉ one-nonzero-ℕᵉ)
      ( is-decidable-Decidable-Propᵉ (Pᵉ one-nonzero-ℕᵉ))
      ( fᵉ one-nonzero-ℕᵉ)
  bounded-sum-arithmetic-function-Ringᵉ (succ-ℕᵉ (succ-ℕᵉ bᵉ)) Pᵉ fᵉ =
    add-Ringᵉ Rᵉ
      ( case-one-bounded-sum-arithmetic-function-Ringᵉ
        ( Pᵉ one-nonzero-ℕᵉ)
        ( is-decidable-Decidable-Propᵉ (Pᵉ one-nonzero-ℕᵉ))
        ( fᵉ one-nonzero-ℕᵉ))
      ( bounded-sum-arithmetic-function-Ringᵉ
        ( succ-ℕᵉ bᵉ)
        ( Pᵉ ∘ᵉ succ-nonzero-ℕᵉ)
        ( fᵉ ∘ᵉ succ-nonzero-ℕᵉ))
```