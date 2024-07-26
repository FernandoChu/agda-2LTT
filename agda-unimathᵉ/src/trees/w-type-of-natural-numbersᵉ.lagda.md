# The W-type of natural numbers

```agda
module trees.w-type-of-natural-numbersᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.booleansᵉ
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.function-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.unit-typeᵉ
open import foundation.universal-property-empty-typeᵉ
open import foundation.universe-levelsᵉ

open import trees.w-typesᵉ
```

</details>

## Idea

Sinceᵉ theᵉ typeᵉ ofᵉ naturalᵉ numbersᵉ isᵉ anᵉ initialᵉ algebraᵉ forᵉ theᵉ polynomialᵉ
endofunctorᵉ

```text
  Xᵉ ↦ᵉ Xᵉ +ᵉ 𝟙,ᵉ
```

thereᵉ isᵉ anᵉ equivalentᵉ definitionᵉ ofᵉ theᵉ naturalᵉ numbersᵉ asᵉ aᵉ W-type.ᵉ

## Definition

### The type of natural numbers defined as a W-type

```agda
Nat-𝕎ᵉ : UUᵉ lzero
Nat-𝕎ᵉ = 𝕎ᵉ boolᵉ (Eq-boolᵉ trueᵉ)

zero-Nat-𝕎ᵉ : Nat-𝕎ᵉ
zero-Nat-𝕎ᵉ = constant-𝕎ᵉ falseᵉ idᵉ

succ-Nat-𝕎ᵉ : Nat-𝕎ᵉ → Nat-𝕎ᵉ
succ-Nat-𝕎ᵉ xᵉ = tree-𝕎ᵉ trueᵉ (λ yᵉ → xᵉ)
```

## Properties

### The type of natural numbers is equivalent to the W-type Nat-𝕎

```agda
Nat-𝕎-ℕᵉ : ℕᵉ → Nat-𝕎ᵉ
Nat-𝕎-ℕᵉ zero-ℕᵉ = zero-Nat-𝕎ᵉ
Nat-𝕎-ℕᵉ (succ-ℕᵉ xᵉ) = succ-Nat-𝕎ᵉ (Nat-𝕎-ℕᵉ xᵉ)

ℕ-Nat-𝕎ᵉ : Nat-𝕎ᵉ → ℕᵉ
ℕ-Nat-𝕎ᵉ (tree-𝕎ᵉ trueᵉ αᵉ) = succ-ℕᵉ (ℕ-Nat-𝕎ᵉ (αᵉ starᵉ))
ℕ-Nat-𝕎ᵉ (tree-𝕎ᵉ falseᵉ αᵉ) = zero-ℕᵉ

is-section-ℕ-Nat-𝕎ᵉ : (Nat-𝕎-ℕᵉ ∘ᵉ ℕ-Nat-𝕎ᵉ) ~ᵉ idᵉ
is-section-ℕ-Nat-𝕎ᵉ (tree-𝕎ᵉ trueᵉ αᵉ) =
  apᵉ
    ( tree-𝕎ᵉ trueᵉ)
    ( eq-htpyᵉ Hᵉ)
  where
  Hᵉ : (zᵉ : unitᵉ) → Nat-𝕎-ℕᵉ (ℕ-Nat-𝕎ᵉ (αᵉ starᵉ)) ＝ᵉ αᵉ zᵉ
  Hᵉ starᵉ = is-section-ℕ-Nat-𝕎ᵉ (αᵉ starᵉ)
is-section-ℕ-Nat-𝕎ᵉ (tree-𝕎ᵉ falseᵉ αᵉ) =
  apᵉ (tree-𝕎ᵉ falseᵉ) (eq-is-contrᵉ (universal-property-empty'ᵉ Nat-𝕎ᵉ))

is-retraction-ℕ-Nat-𝕎ᵉ : (ℕ-Nat-𝕎ᵉ ∘ᵉ Nat-𝕎-ℕᵉ) ~ᵉ idᵉ
is-retraction-ℕ-Nat-𝕎ᵉ zero-ℕᵉ = reflᵉ
is-retraction-ℕ-Nat-𝕎ᵉ (succ-ℕᵉ xᵉ) = apᵉ succ-ℕᵉ (is-retraction-ℕ-Nat-𝕎ᵉ xᵉ)

is-equiv-Nat-𝕎-ℕᵉ : is-equivᵉ Nat-𝕎-ℕᵉ
is-equiv-Nat-𝕎-ℕᵉ =
  is-equiv-is-invertibleᵉ
    ℕ-Nat-𝕎ᵉ
    is-section-ℕ-Nat-𝕎ᵉ
    is-retraction-ℕ-Nat-𝕎ᵉ

equiv-Nat-𝕎-ℕᵉ : ℕᵉ ≃ᵉ Nat-𝕎ᵉ
equiv-Nat-𝕎-ℕᵉ = pairᵉ Nat-𝕎-ℕᵉ is-equiv-Nat-𝕎-ℕᵉ

is-equiv-ℕ-Nat-𝕎ᵉ : is-equivᵉ ℕ-Nat-𝕎ᵉ
is-equiv-ℕ-Nat-𝕎ᵉ =
  is-equiv-is-invertibleᵉ
    Nat-𝕎-ℕᵉ
    is-retraction-ℕ-Nat-𝕎ᵉ
    is-section-ℕ-Nat-𝕎ᵉ

equiv-ℕ-Nat-𝕎ᵉ : Nat-𝕎ᵉ ≃ᵉ ℕᵉ
equiv-ℕ-Nat-𝕎ᵉ = pairᵉ ℕ-Nat-𝕎ᵉ is-equiv-ℕ-Nat-𝕎ᵉ
```