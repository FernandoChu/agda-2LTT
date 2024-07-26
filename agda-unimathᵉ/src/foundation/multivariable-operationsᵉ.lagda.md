# Multivariable operations

```agda
module foundation.multivariable-operationsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equality-cartesian-product-typesᵉ
open import foundation.raising-universe-levelsᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.cartesian-product-typesᵉ
open import foundation-core.coproduct-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ

open import linear-algebra.vectorsᵉ
```

</details>

## Idea

Givenᵉ `n`ᵉ types,ᵉ anᵉ n-aryᵉ multivariableᵉ operationᵉ onᵉ themᵉ isᵉ aᵉ functionᵉ thatᵉ
takesᵉ asᵉ inputsᵉ oneᵉ elementᵉ ofᵉ eachᵉ type,ᵉ andᵉ returnsᵉ anᵉ elementᵉ in someᵉ typeᵉ
`X`.ᵉ

## Definitions

```agda
multivariable-inputᵉ :
  {lᵉ : Level}
  (nᵉ : ℕᵉ)
  (Aᵉ : functional-vecᵉ (UUᵉ lᵉ) nᵉ) →
  UUᵉ lᵉ
multivariable-inputᵉ zero-ℕᵉ Aᵉ = raise-unitᵉ _
multivariable-inputᵉ (succ-ℕᵉ nᵉ) Aᵉ =
  Aᵉ (inrᵉ starᵉ) ×ᵉ multivariable-inputᵉ nᵉ (tail-functional-vecᵉ nᵉ Aᵉ)

empty-multivariable-inputᵉ :
  {lᵉ : Level}
  (Aᵉ : functional-vecᵉ (UUᵉ lᵉ) 0ᵉ) →
  multivariable-inputᵉ 0 Aᵉ
empty-multivariable-inputᵉ Aᵉ = raise-starᵉ

head-multivariable-inputᵉ :
  {lᵉ : Level}
  (nᵉ : ℕᵉ)
  (Aᵉ : functional-vecᵉ (UUᵉ lᵉ) (succ-ℕᵉ nᵉ)) →
  multivariable-inputᵉ (succ-ℕᵉ nᵉ) Aᵉ →
  head-functional-vecᵉ nᵉ Aᵉ
head-multivariable-inputᵉ nᵉ Aᵉ (a0ᵉ ,ᵉ aᵉ) = a0ᵉ

tail-multivariable-inputᵉ :
  {lᵉ : Level}
  (nᵉ : ℕᵉ)
  (Aᵉ : functional-vecᵉ (UUᵉ lᵉ) (succ-ℕᵉ nᵉ)) →
  multivariable-inputᵉ (succ-ℕᵉ nᵉ) Aᵉ →
  multivariable-inputᵉ nᵉ (tail-functional-vecᵉ nᵉ Aᵉ)
tail-multivariable-inputᵉ nᵉ Aᵉ (a0ᵉ ,ᵉ aᵉ) = aᵉ

cons-multivariable-inputᵉ :
  {lᵉ : Level}
  (nᵉ : ℕᵉ)
  (Aᵉ : functional-vecᵉ (UUᵉ lᵉ) nᵉ) →
  {A0ᵉ : UUᵉ lᵉ} →
  A0ᵉ →
  multivariable-inputᵉ nᵉ Aᵉ →
  multivariable-inputᵉ (succ-ℕᵉ nᵉ) (cons-functional-vecᵉ nᵉ A0ᵉ Aᵉ)
pr1ᵉ (cons-multivariable-inputᵉ nᵉ Aᵉ a0ᵉ aᵉ) = a0ᵉ
pr2ᵉ (cons-multivariable-inputᵉ nᵉ Aᵉ a0ᵉ aᵉ) = aᵉ

multivariable-operationᵉ :
  { lᵉ : Level}
  ( nᵉ : ℕᵉ)
  ( Aᵉ : functional-vecᵉ (UUᵉ lᵉ) nᵉ)
  ( Xᵉ : UUᵉ lᵉ) →
  UUᵉ lᵉ
multivariable-operationᵉ nᵉ Aᵉ Xᵉ =
  multivariable-inputᵉ nᵉ Aᵉ → Xᵉ
```

## Properties

### For the case of constant families, multivariable inputs and vectors coincide

```agda
vector-multivariable-inputᵉ :
  {lᵉ : Level}
  (nᵉ : ℕᵉ)
  (Aᵉ : UUᵉ lᵉ) →
  multivariable-inputᵉ nᵉ (λ _ → Aᵉ) →
  vecᵉ Aᵉ nᵉ
vector-multivariable-inputᵉ zero-ℕᵉ Aᵉ _ = empty-vecᵉ
vector-multivariable-inputᵉ (succ-ℕᵉ nᵉ) Aᵉ (a0ᵉ ,ᵉ aᵉ) =
  a0ᵉ ∷ᵉ (vector-multivariable-inputᵉ nᵉ Aᵉ aᵉ)

multivariable-input-vectorᵉ :
  {lᵉ : Level}
  (nᵉ : ℕᵉ)
  (Aᵉ : UUᵉ lᵉ) →
  vecᵉ Aᵉ nᵉ →
  multivariable-inputᵉ nᵉ (λ _ → Aᵉ)
multivariable-input-vectorᵉ zero-ℕᵉ Aᵉ _ = raise-starᵉ
multivariable-input-vectorᵉ (succ-ℕᵉ nᵉ) Aᵉ (a0ᵉ ∷ᵉ aᵉ) =
  cons-multivariable-inputᵉ nᵉ (λ _ → Aᵉ) a0ᵉ
    ( multivariable-input-vectorᵉ nᵉ Aᵉ aᵉ)

is-section-multivariable-input-vectorᵉ :
  {lᵉ : Level}
  (nᵉ : ℕᵉ)
  (Aᵉ : UUᵉ lᵉ) →
  ( vector-multivariable-inputᵉ nᵉ Aᵉ ∘ᵉ
    multivariable-input-vectorᵉ nᵉ Aᵉ) ~ᵉ idᵉ
is-section-multivariable-input-vectorᵉ zero-ℕᵉ Aᵉ empty-vecᵉ = reflᵉ
is-section-multivariable-input-vectorᵉ (succ-ℕᵉ nᵉ) Aᵉ (a0ᵉ ∷ᵉ aᵉ) =
  apᵉ (_∷ᵉ_ a0ᵉ) ( is-section-multivariable-input-vectorᵉ nᵉ Aᵉ aᵉ)

is-retraction-multivariable-input-vectorᵉ :
  {lᵉ : Level}
  (nᵉ : ℕᵉ)
  (Aᵉ : UUᵉ lᵉ) →
  ( multivariable-input-vectorᵉ nᵉ Aᵉ ∘ᵉ
    vector-multivariable-inputᵉ nᵉ Aᵉ) ~ᵉ idᵉ
is-retraction-multivariable-input-vectorᵉ zero-ℕᵉ Aᵉ (map-raiseᵉ starᵉ) = reflᵉ
is-retraction-multivariable-input-vectorᵉ (succ-ℕᵉ nᵉ) Aᵉ (a0ᵉ ,ᵉ aᵉ) =
  eq-pairᵉ reflᵉ ( is-retraction-multivariable-input-vectorᵉ nᵉ Aᵉ aᵉ)

is-equiv-vector-multivariable-inputᵉ :
  {lᵉ : Level}
  (nᵉ : ℕᵉ)
  (Aᵉ : UUᵉ lᵉ) →
  is-equivᵉ (vector-multivariable-inputᵉ nᵉ Aᵉ)
is-equiv-vector-multivariable-inputᵉ nᵉ Aᵉ =
  is-equiv-is-invertibleᵉ
    ( multivariable-input-vectorᵉ nᵉ Aᵉ)
    ( is-section-multivariable-input-vectorᵉ nᵉ Aᵉ)
    ( is-retraction-multivariable-input-vectorᵉ nᵉ Aᵉ)

compute-vector-multivariable-inputᵉ :
  {lᵉ : Level}
  (nᵉ : ℕᵉ)
  (Aᵉ : UUᵉ lᵉ) →
  multivariable-inputᵉ nᵉ (λ _ → Aᵉ) ≃ᵉ vecᵉ Aᵉ nᵉ
pr1ᵉ (compute-vector-multivariable-inputᵉ nᵉ Aᵉ) =
  vector-multivariable-inputᵉ nᵉ Aᵉ
pr2ᵉ (compute-vector-multivariable-inputᵉ nᵉ Aᵉ) =
  is-equiv-vector-multivariable-inputᵉ nᵉ Aᵉ
```