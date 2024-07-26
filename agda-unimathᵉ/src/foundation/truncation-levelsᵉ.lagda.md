# Truncation levels

```agda
module foundation.truncation-levelsᵉ where

open import foundation-core.truncation-levelsᵉ public
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.action-on-identifications-functionsᵉ

open import foundation-core.function-typesᵉ
open import foundation-core.identity-typesᵉ
```

</details>

## Definitions

### Inclusions of the natural numbers into the truncation levels

```agda
truncation-level-minus-two-ℕᵉ : ℕᵉ → 𝕋ᵉ
truncation-level-minus-two-ℕᵉ zero-ℕᵉ = neg-two-𝕋ᵉ
truncation-level-minus-two-ℕᵉ (succ-ℕᵉ nᵉ) =
  succ-𝕋ᵉ (truncation-level-minus-two-ℕᵉ nᵉ)

truncation-level-minus-one-ℕᵉ : ℕᵉ → 𝕋ᵉ
truncation-level-minus-one-ℕᵉ = succ-𝕋ᵉ ∘ᵉ truncation-level-minus-two-ℕᵉ

truncation-level-ℕᵉ : ℕᵉ → 𝕋ᵉ
truncation-level-ℕᵉ = succ-𝕋ᵉ ∘ᵉ truncation-level-minus-one-ℕᵉ
```

### Inclusion of the truncation levels into the natural numbers

```agda
nat-succ-succ-𝕋ᵉ : 𝕋ᵉ → ℕᵉ
nat-succ-succ-𝕋ᵉ neg-two-𝕋ᵉ = zero-ℕᵉ
nat-succ-succ-𝕋ᵉ (succ-𝕋ᵉ kᵉ) = succ-ℕᵉ (nat-succ-succ-𝕋ᵉ kᵉ)
```

### Addition of truncation levels

```agda
add-𝕋ᵉ : 𝕋ᵉ → 𝕋ᵉ → 𝕋ᵉ
add-𝕋ᵉ neg-two-𝕋ᵉ neg-two-𝕋ᵉ = neg-two-𝕋ᵉ
add-𝕋ᵉ neg-two-𝕋ᵉ (succ-𝕋ᵉ neg-two-𝕋ᵉ) = neg-two-𝕋ᵉ
add-𝕋ᵉ neg-two-𝕋ᵉ (succ-𝕋ᵉ (succ-𝕋ᵉ lᵉ)) = lᵉ
add-𝕋ᵉ (succ-𝕋ᵉ neg-two-𝕋ᵉ) neg-two-𝕋ᵉ = neg-two-𝕋ᵉ
add-𝕋ᵉ (succ-𝕋ᵉ neg-two-𝕋ᵉ) (succ-𝕋ᵉ lᵉ) = lᵉ
add-𝕋ᵉ (succ-𝕋ᵉ (succ-𝕋ᵉ kᵉ)) neg-two-𝕋ᵉ = kᵉ
add-𝕋ᵉ (succ-𝕋ᵉ (succ-𝕋ᵉ kᵉ)) (succ-𝕋ᵉ lᵉ) = succ-𝕋ᵉ (add-𝕋ᵉ (succ-𝕋ᵉ kᵉ) (succ-𝕋ᵉ lᵉ))

infixl 35 _+𝕋ᵉ_
_+𝕋ᵉ_ = add-𝕋ᵉ
```

### Iterated successor functions on truncation levels

Althoughᵉ weᵉ canᵉ defineᵉ anᵉ additionᵉ operationᵉ onᵉ truncationᵉ levels,ᵉ whenᵉ itᵉ comesᵉ
to doingᵉ inductionᵉ onᵉ them,ᵉ itᵉ isᵉ moreᵉ naturalᵉ to speakᵉ in termsᵉ ofᵉ anᵉ iteratedᵉ
successorᵉ:

```agda
iterated-succ-𝕋ᵉ : ℕᵉ → 𝕋ᵉ → 𝕋ᵉ
iterated-succ-𝕋ᵉ zero-ℕᵉ xᵉ = xᵉ
iterated-succ-𝕋ᵉ (succ-ℕᵉ nᵉ) xᵉ = iterated-succ-𝕋ᵉ nᵉ (succ-𝕋ᵉ xᵉ)

iterated-succ-𝕋'ᵉ : 𝕋ᵉ → ℕᵉ → 𝕋ᵉ
iterated-succ-𝕋'ᵉ xᵉ nᵉ = iterated-succ-𝕋ᵉ nᵉ xᵉ
```

## Properties

### Unit laws for addition of truncation levels

```agda
left-unit-law-add-𝕋ᵉ : (kᵉ : 𝕋ᵉ) → zero-𝕋ᵉ +𝕋ᵉ kᵉ ＝ᵉ kᵉ
left-unit-law-add-𝕋ᵉ neg-two-𝕋ᵉ = reflᵉ
left-unit-law-add-𝕋ᵉ (succ-𝕋ᵉ neg-two-𝕋ᵉ) = reflᵉ
left-unit-law-add-𝕋ᵉ (succ-𝕋ᵉ (succ-𝕋ᵉ neg-two-𝕋ᵉ)) = reflᵉ
left-unit-law-add-𝕋ᵉ (succ-𝕋ᵉ (succ-𝕋ᵉ (succ-𝕋ᵉ kᵉ))) = reflᵉ

right-unit-law-add-𝕋ᵉ : (kᵉ : 𝕋ᵉ) → kᵉ +𝕋ᵉ zero-𝕋ᵉ ＝ᵉ kᵉ
right-unit-law-add-𝕋ᵉ neg-two-𝕋ᵉ = reflᵉ
right-unit-law-add-𝕋ᵉ (succ-𝕋ᵉ neg-two-𝕋ᵉ) = reflᵉ
right-unit-law-add-𝕋ᵉ (succ-𝕋ᵉ (succ-𝕋ᵉ kᵉ)) =
  apᵉ succ-𝕋ᵉ (right-unit-law-add-𝕋ᵉ (succ-𝕋ᵉ kᵉ))
```

### Successor laws for addition of truncation levels

```agda
left-successor-law-add-𝕋ᵉ :
  (nᵉ kᵉ : 𝕋ᵉ) →
  (succ-𝕋ᵉ (succ-𝕋ᵉ (succ-𝕋ᵉ nᵉ))) +𝕋ᵉ kᵉ ＝ᵉ
  succ-𝕋ᵉ (add-𝕋ᵉ (succ-𝕋ᵉ (succ-𝕋ᵉ nᵉ)) kᵉ)
left-successor-law-add-𝕋ᵉ nᵉ neg-two-𝕋ᵉ = reflᵉ
left-successor-law-add-𝕋ᵉ nᵉ (succ-𝕋ᵉ kᵉ) = reflᵉ

right-successor-law-add-𝕋ᵉ :
  (kᵉ nᵉ : 𝕋ᵉ) →
  kᵉ +𝕋ᵉ (succ-𝕋ᵉ (succ-𝕋ᵉ (succ-𝕋ᵉ nᵉ))) ＝ᵉ
  succ-𝕋ᵉ (kᵉ +𝕋ᵉ (succ-𝕋ᵉ (succ-𝕋ᵉ nᵉ)))
right-successor-law-add-𝕋ᵉ neg-two-𝕋ᵉ nᵉ = reflᵉ
right-successor-law-add-𝕋ᵉ (succ-𝕋ᵉ neg-two-𝕋ᵉ) nᵉ = reflᵉ
right-successor-law-add-𝕋ᵉ (succ-𝕋ᵉ (succ-𝕋ᵉ kᵉ)) nᵉ =
  apᵉ succ-𝕋ᵉ (right-successor-law-add-𝕋ᵉ (succ-𝕋ᵉ kᵉ) nᵉ)
```