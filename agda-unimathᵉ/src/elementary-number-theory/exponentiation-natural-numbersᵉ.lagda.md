# Exponentiation of natural numbers

```agda
module elementary-number-theory.exponentiation-natural-numbersᵉ where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.powers-of-elements-commutative-semiringsᵉ

open import elementary-number-theory.addition-natural-numbersᵉ
open import elementary-number-theory.commutative-semiring-of-natural-numbersᵉ
open import elementary-number-theory.multiplication-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.identity-typesᵉ
```

</details>

## Idea

Theᵉ exponentᵉ `m^n`ᵉ isᵉ theᵉ numberᵉ obtainedᵉ byᵉ multiplyingᵉ `m`ᵉ with itselfᵉ `n`ᵉ
times.ᵉ

## Definition

```agda
exp-ℕᵉ : ℕᵉ → ℕᵉ → ℕᵉ
exp-ℕᵉ mᵉ 0 = 1
exp-ℕᵉ mᵉ (succ-ℕᵉ nᵉ) = (exp-ℕᵉ mᵉ nᵉ) *ℕᵉ mᵉ

infixr 45 _^ℕᵉ_
_^ℕᵉ_ = exp-ℕᵉ
```

```agda
power-ℕᵉ : ℕᵉ → ℕᵉ → ℕᵉ
power-ℕᵉ = power-Commutative-Semiringᵉ ℕ-Commutative-Semiringᵉ
```

## Properties

### Tarski's high school arithmetic laws for exponentiation

```agda
annihilation-law-exp-ℕᵉ : (nᵉ : ℕᵉ) → 1 ^ℕᵉ nᵉ ＝ᵉ 1
annihilation-law-exp-ℕᵉ zero-ℕᵉ = reflᵉ
annihilation-law-exp-ℕᵉ (succ-ℕᵉ nᵉ) =
  right-unit-law-mul-ℕᵉ (1ᵉ ^ℕᵉ nᵉ) ∙ᵉ annihilation-law-exp-ℕᵉ nᵉ

left-distributive-exp-add-ℕᵉ :
  (xᵉ yᵉ zᵉ : ℕᵉ) → xᵉ ^ℕᵉ (yᵉ +ℕᵉ zᵉ) ＝ᵉ (xᵉ ^ℕᵉ yᵉ) *ℕᵉ (xᵉ ^ℕᵉ zᵉ)
left-distributive-exp-add-ℕᵉ xᵉ yᵉ zero-ℕᵉ = invᵉ (right-unit-law-mul-ℕᵉ (xᵉ ^ℕᵉ yᵉ))
left-distributive-exp-add-ℕᵉ xᵉ yᵉ (succ-ℕᵉ zᵉ) =
  ( apᵉ (_*ℕᵉ xᵉ) (left-distributive-exp-add-ℕᵉ xᵉ yᵉ zᵉ)) ∙ᵉ
  ( associative-mul-ℕᵉ (xᵉ ^ℕᵉ yᵉ) (xᵉ ^ℕᵉ zᵉ) xᵉ)

right-distributive-exp-mul-ℕᵉ :
  (xᵉ yᵉ zᵉ : ℕᵉ) → (xᵉ *ℕᵉ yᵉ) ^ℕᵉ zᵉ ＝ᵉ (xᵉ ^ℕᵉ zᵉ) *ℕᵉ (yᵉ ^ℕᵉ zᵉ)
right-distributive-exp-mul-ℕᵉ xᵉ yᵉ zero-ℕᵉ = reflᵉ
right-distributive-exp-mul-ℕᵉ xᵉ yᵉ (succ-ℕᵉ zᵉ) =
  ( apᵉ (_*ℕᵉ (xᵉ *ℕᵉ yᵉ)) (right-distributive-exp-mul-ℕᵉ xᵉ yᵉ zᵉ)) ∙ᵉ
  ( interchange-law-mul-mul-ℕᵉ (xᵉ ^ℕᵉ zᵉ) (yᵉ ^ℕᵉ zᵉ) xᵉ yᵉ)

exp-mul-ℕᵉ : (xᵉ yᵉ zᵉ : ℕᵉ) → xᵉ ^ℕᵉ (yᵉ *ℕᵉ zᵉ) ＝ᵉ (xᵉ ^ℕᵉ yᵉ) ^ℕᵉ zᵉ
exp-mul-ℕᵉ xᵉ zero-ℕᵉ zᵉ = invᵉ (annihilation-law-exp-ℕᵉ zᵉ)
exp-mul-ℕᵉ xᵉ (succ-ℕᵉ yᵉ) zᵉ =
  ( left-distributive-exp-add-ℕᵉ xᵉ (yᵉ *ℕᵉ zᵉ) zᵉ) ∙ᵉ
  ( ( apᵉ (_*ℕᵉ (xᵉ ^ℕᵉ zᵉ)) (exp-mul-ℕᵉ xᵉ yᵉ zᵉ)) ∙ᵉ
    ( invᵉ (right-distributive-exp-mul-ℕᵉ (xᵉ ^ℕᵉ yᵉ) xᵉ zᵉ)))
```

### The exponent `m^n` is always nonzero

```agda
is-nonzero-exp-ℕᵉ :
  (mᵉ nᵉ : ℕᵉ) → is-nonzero-ℕᵉ mᵉ → is-nonzero-ℕᵉ (mᵉ ^ℕᵉ nᵉ)
is-nonzero-exp-ℕᵉ mᵉ zero-ℕᵉ pᵉ = is-nonzero-one-ℕᵉ
is-nonzero-exp-ℕᵉ mᵉ (succ-ℕᵉ nᵉ) pᵉ =
  is-nonzero-mul-ℕᵉ (mᵉ ^ℕᵉ nᵉ) mᵉ (is-nonzero-exp-ℕᵉ mᵉ nᵉ pᵉ) pᵉ
```