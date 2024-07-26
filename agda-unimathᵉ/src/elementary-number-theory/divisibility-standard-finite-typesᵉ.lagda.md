# The divisibility relation on the standard finite types

```agda
module elementary-number-theory.divisibility-standard-finite-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.modular-arithmetic-standard-finite-typesᵉ
open import elementary-number-theory.natural-numbersᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.binary-relationsᵉ
open import foundation.decidable-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ

open import univalent-combinatorics.decidable-dependent-pair-typesᵉ
open import univalent-combinatorics.equality-standard-finite-typesᵉ
open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Givenᵉ twoᵉ elementsᵉ `xᵉ yᵉ : Finᵉ k`,ᵉ weᵉ sayᵉ thatᵉ `x`ᵉ dividesᵉ `y`ᵉ ifᵉ thereᵉ isᵉ anᵉ
elementᵉ `uᵉ : Finᵉ k`ᵉ suchᵉ thatᵉ `mul-Finᵉ uᵉ xᵉ = y`.ᵉ

## Definition

```agda
div-Finᵉ : (kᵉ : ℕᵉ) → Finᵉ kᵉ → Finᵉ kᵉ → UUᵉ lzero
div-Finᵉ kᵉ xᵉ yᵉ = Σᵉ (Finᵉ kᵉ) (λ uᵉ → mul-Finᵉ kᵉ uᵉ xᵉ ＝ᵉ yᵉ)
```

## Properties

### The divisibility relation is reflexive

```agda
refl-div-Finᵉ : {kᵉ : ℕᵉ} (xᵉ : Finᵉ kᵉ) → div-Finᵉ kᵉ xᵉ xᵉ
pr1ᵉ (refl-div-Finᵉ {succ-ℕᵉ kᵉ} xᵉ) = one-Finᵉ kᵉ
pr2ᵉ (refl-div-Finᵉ {succ-ℕᵉ kᵉ} xᵉ) = left-unit-law-mul-Finᵉ kᵉ xᵉ
```

### The divisibility relation is transitive

```agda
transitive-div-Finᵉ :
  (kᵉ : ℕᵉ) → is-transitiveᵉ (div-Finᵉ kᵉ)
pr1ᵉ (transitive-div-Finᵉ kᵉ xᵉ yᵉ zᵉ (pairᵉ vᵉ qᵉ) (pairᵉ uᵉ pᵉ)) = mul-Finᵉ kᵉ vᵉ uᵉ
pr2ᵉ (transitive-div-Finᵉ kᵉ xᵉ yᵉ zᵉ (pairᵉ vᵉ qᵉ) (pairᵉ uᵉ pᵉ)) =
  associative-mul-Finᵉ kᵉ vᵉ uᵉ xᵉ ∙ᵉ (apᵉ (mul-Finᵉ kᵉ vᵉ) pᵉ ∙ᵉ qᵉ)
```

### Every element divides zero

```agda
div-zero-Finᵉ : (kᵉ : ℕᵉ) (xᵉ : Finᵉ (succ-ℕᵉ kᵉ)) → div-Finᵉ (succ-ℕᵉ kᵉ) xᵉ (zero-Finᵉ kᵉ)
pr1ᵉ (div-zero-Finᵉ kᵉ xᵉ) = zero-Finᵉ kᵉ
pr2ᵉ (div-zero-Finᵉ kᵉ xᵉ) = left-zero-law-mul-Finᵉ kᵉ xᵉ
```

### Every element is divisible by one

```agda
div-one-Finᵉ : (kᵉ : ℕᵉ) (xᵉ : Finᵉ (succ-ℕᵉ kᵉ)) → div-Finᵉ (succ-ℕᵉ kᵉ) (one-Finᵉ kᵉ) xᵉ
pr1ᵉ (div-one-Finᵉ kᵉ xᵉ) = xᵉ
pr2ᵉ (div-one-Finᵉ kᵉ xᵉ) = right-unit-law-mul-Finᵉ kᵉ xᵉ
```

### The only element that is divisible by zero is zero itself

```agda
is-zero-div-zero-Finᵉ :
  {kᵉ : ℕᵉ} (xᵉ : Finᵉ (succ-ℕᵉ kᵉ)) →
  div-Finᵉ (succ-ℕᵉ kᵉ) (zero-Finᵉ kᵉ) xᵉ → is-zero-Finᵉ (succ-ℕᵉ kᵉ) xᵉ
is-zero-div-zero-Finᵉ {kᵉ} xᵉ (pairᵉ uᵉ pᵉ) = invᵉ pᵉ ∙ᵉ right-zero-law-mul-Finᵉ kᵉ uᵉ
```

### The divisibility relation is decidable

```agda
is-decidable-div-Finᵉ : (kᵉ : ℕᵉ) (xᵉ yᵉ : Finᵉ kᵉ) → is-decidableᵉ (div-Finᵉ kᵉ xᵉ yᵉ)
is-decidable-div-Finᵉ kᵉ xᵉ yᵉ =
  is-decidable-Σ-Finᵉ kᵉ (λ uᵉ → has-decidable-equality-Finᵉ kᵉ (mul-Finᵉ kᵉ uᵉ xᵉ) yᵉ)
```