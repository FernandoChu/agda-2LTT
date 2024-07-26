# The based induction principle of the natural numbers

```agda
module elementary-number-theory.based-induction-natural-numbersᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ

open import foundation.function-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Theᵉ **basedᵉ inductionᵉ principle**ᵉ forᵉ theᵉ naturalᵉ numbersᵉ assertsᵉ thatᵉ forᵉ anyᵉ
familyᵉ `P`ᵉ ofᵉ typesᵉ overᵉ `ℕ`ᵉ andᵉ anyᵉ naturalᵉ numberᵉ `kᵉ : ℕ`,ᵉ equippedᵉ with

1.ᵉ Anᵉ elementᵉ `p0ᵉ : Pᵉ k`ᵉ
2.ᵉ Aᵉ functionᵉ `pSᵉ : (xᵉ : ℕᵉ) → kᵉ ≤-ℕᵉ xᵉ → Pᵉ xᵉ → Pᵉ (xᵉ +ᵉ 1)`ᵉ thereᵉ isᵉ aᵉ functionᵉ

```text
  based-ind-ℕᵉ kᵉ Pᵉ p0ᵉ pSᵉ : (xᵉ : ℕᵉ) → kᵉ ≤-ℕᵉ xᵉ → Pᵉ xᵉ
```

suchᵉ thatᵉ

1.ᵉ `based-ind-ℕᵉ kᵉ Pᵉ p0ᵉ pSᵉ kᵉ Kᵉ ＝ᵉ p0`ᵉ forᵉ anyᵉ `Kᵉ : kᵉ ≤-ℕᵉ k,ᵉ andᵉ
2.ᵉ `based-ind-ℕᵉ kᵉ Pᵉ p0ᵉ pSᵉ (nᵉ +ᵉ 1ᵉ) N'ᵉ ＝ᵉ pSᵉ nᵉ Nᵉ (based-ind-ℕᵉ kᵉ Pᵉ p0ᵉ pSᵉ nᵉ N`ᵉ forᵉ
   anyᵉ `Nᵉ : kᵉ ≤-ℕᵉ n`ᵉ andᵉ anyᵉ `N'ᵉ : kᵉ ≤-ℕᵉ nᵉ +ᵉ 1`.ᵉ

## Theorem

### The based induction principle for the natural numbers

```agda
based-ind-ℕᵉ :
  {lᵉ : Level} (kᵉ : ℕᵉ) (Pᵉ : ℕᵉ → UUᵉ lᵉ) →
  Pᵉ kᵉ → ((nᵉ : ℕᵉ) → kᵉ ≤-ℕᵉ nᵉ → Pᵉ nᵉ → Pᵉ (succ-ℕᵉ nᵉ)) → (nᵉ : ℕᵉ) → kᵉ ≤-ℕᵉ nᵉ → Pᵉ nᵉ
based-ind-ℕᵉ zero-ℕᵉ Pᵉ p0ᵉ pSᵉ zero-ℕᵉ Hᵉ = p0ᵉ
based-ind-ℕᵉ zero-ℕᵉ Pᵉ p0ᵉ pSᵉ (succ-ℕᵉ nᵉ) Hᵉ =
  pSᵉ nᵉ Hᵉ (based-ind-ℕᵉ 0 Pᵉ p0ᵉ pSᵉ nᵉ (leq-zero-ℕᵉ nᵉ))
based-ind-ℕᵉ (succ-ℕᵉ kᵉ) Pᵉ p0ᵉ pSᵉ (succ-ℕᵉ nᵉ) =
  based-ind-ℕᵉ kᵉ (Pᵉ ∘ᵉ succ-ℕᵉ) p0ᵉ (pSᵉ ∘ᵉ succ-ℕᵉ) nᵉ

compute-base-based-ind-ℕᵉ :
  {lᵉ : Level} (kᵉ : ℕᵉ) (Pᵉ : ℕᵉ → UUᵉ lᵉ) (p0ᵉ : Pᵉ kᵉ) →
  (pSᵉ : (nᵉ : ℕᵉ) → kᵉ ≤-ℕᵉ nᵉ → Pᵉ nᵉ → Pᵉ (succ-ℕᵉ nᵉ)) → (Hᵉ : kᵉ ≤-ℕᵉ kᵉ) →
  based-ind-ℕᵉ kᵉ Pᵉ p0ᵉ pSᵉ kᵉ Hᵉ ＝ᵉ p0ᵉ
compute-base-based-ind-ℕᵉ zero-ℕᵉ Pᵉ p0ᵉ pSᵉ _ = reflᵉ
compute-base-based-ind-ℕᵉ (succ-ℕᵉ kᵉ) Pᵉ p0ᵉ pSᵉ =
  compute-base-based-ind-ℕᵉ kᵉ (Pᵉ ∘ᵉ succ-ℕᵉ) p0ᵉ (pSᵉ ∘ᵉ succ-ℕᵉ)

compute-succ-based-ind-ℕᵉ :
  {lᵉ : Level} (kᵉ : ℕᵉ) (Pᵉ : ℕᵉ → UUᵉ lᵉ) (p0ᵉ : Pᵉ kᵉ) →
  (pSᵉ : (nᵉ : ℕᵉ) → kᵉ ≤-ℕᵉ nᵉ → Pᵉ nᵉ → Pᵉ (succ-ℕᵉ nᵉ)) →
  (nᵉ : ℕᵉ) (Nᵉ : kᵉ ≤-ℕᵉ nᵉ) (N'ᵉ : kᵉ ≤-ℕᵉ succ-ℕᵉ nᵉ) →
  based-ind-ℕᵉ kᵉ Pᵉ p0ᵉ pSᵉ (succ-ℕᵉ nᵉ) N'ᵉ ＝ᵉ
  pSᵉ nᵉ Nᵉ (based-ind-ℕᵉ kᵉ Pᵉ p0ᵉ pSᵉ nᵉ Nᵉ)
compute-succ-based-ind-ℕᵉ zero-ℕᵉ Pᵉ p0ᵉ pSᵉ zero-ℕᵉ _ _ = reflᵉ
compute-succ-based-ind-ℕᵉ zero-ℕᵉ Pᵉ p0ᵉ pSᵉ (succ-ℕᵉ nᵉ) _ _ = reflᵉ
compute-succ-based-ind-ℕᵉ (succ-ℕᵉ kᵉ) Pᵉ p0ᵉ pSᵉ (succ-ℕᵉ nᵉ) =
  compute-succ-based-ind-ℕᵉ kᵉ (Pᵉ ∘ᵉ succ-ℕᵉ) p0ᵉ (pSᵉ ∘ᵉ succ-ℕᵉ) nᵉ
```

## See also

-ᵉ Theᵉ basedᵉ strongᵉ inductionᵉ principleᵉ isᵉ definedᵉ in
  [`based-strong-induction-natural-numbers`](elementary-number-theory.based-strong-induction-natural-numbers.md).ᵉ