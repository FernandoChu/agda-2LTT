# Divisibility in modular arithmetic

```agda
module elementary-number-theory.divisibility-modular-arithmeticᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.divisibility-integersᵉ
open import elementary-number-theory.divisibility-standard-finite-typesᵉ
open import elementary-number-theory.modular-arithmeticᵉ
open import elementary-number-theory.natural-numbersᵉ

open import foundation.binary-relationsᵉ
open import foundation.decidable-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ

open import univalent-combinatorics.fibers-of-mapsᵉ
```

</details>

## Idea

Forᵉ twoᵉ numbersᵉ `x`ᵉ andᵉ `y`ᵉ in `ℤ-Modᵉ k`,ᵉ weᵉ sayᵉ thatᵉ `x`ᵉ dividesᵉ `y`ᵉ ifᵉ thereᵉ
isᵉ aᵉ numberᵉ `u`ᵉ in `ℤ-Modᵉ k`ᵉ suchᵉ thatᵉ `mul-ℤ-Modᵉ kᵉ uᵉ xᵉ = y`.ᵉ

## Definition

```agda
div-ℤ-Modᵉ : (kᵉ : ℕᵉ) → ℤ-Modᵉ kᵉ → ℤ-Modᵉ kᵉ → UUᵉ lzero
div-ℤ-Modᵉ kᵉ xᵉ yᵉ = Σᵉ (ℤ-Modᵉ kᵉ) (λ uᵉ → mul-ℤ-Modᵉ kᵉ uᵉ xᵉ ＝ᵉ yᵉ)
```

## Properties

### The divisibility relation is reflexive

```agda
refl-div-ℤ-Modᵉ : {kᵉ : ℕᵉ} (xᵉ : ℤ-Modᵉ kᵉ) → div-ℤ-Modᵉ kᵉ xᵉ xᵉ
refl-div-ℤ-Modᵉ {ℕ.zero-ℕᵉ} = refl-div-ℤᵉ
refl-div-ℤ-Modᵉ {ℕ.succ-ℕᵉ kᵉ} = refl-div-Finᵉ
```

### The divisibility relation is transitive

```agda
transitive-div-ℤ-Modᵉ : {kᵉ : ℕᵉ} → is-transitiveᵉ (div-ℤ-Modᵉ kᵉ)
transitive-div-ℤ-Modᵉ {zero-ℕᵉ} = transitive-div-ℤᵉ
transitive-div-ℤ-Modᵉ {succ-ℕᵉ kᵉ} = transitive-div-Finᵉ (succ-ℕᵉ kᵉ)
```

### The divisibility relation is decidable

```agda
is-decidable-div-ℤ-Modᵉ :
  (kᵉ : ℕᵉ) (xᵉ yᵉ : ℤ-Modᵉ kᵉ) → is-decidableᵉ (div-ℤ-Modᵉ kᵉ xᵉ yᵉ)
is-decidable-div-ℤ-Modᵉ zero-ℕᵉ xᵉ yᵉ = is-decidable-div-ℤᵉ xᵉ yᵉ
is-decidable-div-ℤ-Modᵉ (succ-ℕᵉ kᵉ) xᵉ yᵉ = is-decidable-fiber-Finᵉ
  {succ-ℕᵉ kᵉ} {succ-ℕᵉ kᵉ} (mul-ℤ-Mod'ᵉ (succ-ℕᵉ kᵉ) xᵉ) yᵉ
```