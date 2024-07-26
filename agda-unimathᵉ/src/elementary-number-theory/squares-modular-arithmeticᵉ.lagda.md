# Squares in ℤₚ

```agda
module elementary-number-theory.squares-modular-arithmeticᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.modular-arithmeticᵉ
open import elementary-number-theory.natural-numbersᵉ
open import elementary-number-theory.squares-integersᵉ

open import foundation.decidable-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ

open import univalent-combinatorics.fibers-of-mapsᵉ
```

</details>

## Definition

```agda
square-ℤ-Modᵉ : (pᵉ : ℕᵉ) → ℤ-Modᵉ pᵉ → ℤ-Modᵉ pᵉ
square-ℤ-Modᵉ pᵉ aᵉ = mul-ℤ-Modᵉ pᵉ aᵉ aᵉ

cube-ℤ-Modᵉ : (pᵉ : ℕᵉ) → ℤ-Modᵉ pᵉ → ℤ-Modᵉ pᵉ
cube-ℤ-Modᵉ pᵉ kᵉ = mul-ℤ-Modᵉ pᵉ (square-ℤ-Modᵉ pᵉ kᵉ) kᵉ

is-square-ℤ-Modᵉ : (pᵉ : ℕᵉ) → ℤ-Modᵉ pᵉ → UUᵉ lzero
is-square-ℤ-Modᵉ 0 kᵉ = is-square-ℤᵉ kᵉ
is-square-ℤ-Modᵉ (succ-ℕᵉ pᵉ) kᵉ =
  Σᵉ (ℤ-Modᵉ (succ-ℕᵉ pᵉ)) (λ xᵉ → square-ℤ-Modᵉ (succ-ℕᵉ pᵉ) xᵉ ＝ᵉ kᵉ)

square-root-ℤ-Modᵉ : {pᵉ : ℕᵉ} → (kᵉ : ℤ-Modᵉ pᵉ) → is-square-ℤ-Modᵉ pᵉ kᵉ → ℤ-Modᵉ pᵉ
square-root-ℤ-Modᵉ {0ᵉ} _ (rootᵉ ,ᵉ _) = rootᵉ
square-root-ℤ-Modᵉ {succ-ℕᵉ pᵉ} _ (rootᵉ ,ᵉ _) = rootᵉ
```

## Properties

### Squareness in ℤₚ is decidable

```agda
is-decidable-is-square-ℤ-Modᵉ :
  (pᵉ : ℕᵉ) (kᵉ : ℤ-Modᵉ pᵉ) →
  is-decidableᵉ (is-square-ℤ-Modᵉ pᵉ kᵉ)
is-decidable-is-square-ℤ-Modᵉ 0 kᵉ = is-decidable-is-square-ℤᵉ kᵉ
is-decidable-is-square-ℤ-Modᵉ (succ-ℕᵉ pᵉ) kᵉ =
  is-decidable-fiber-Finᵉ {succ-ℕᵉ pᵉ} {succ-ℕᵉ pᵉ} (square-ℤ-Modᵉ (succ-ℕᵉ pᵉ)) kᵉ
```