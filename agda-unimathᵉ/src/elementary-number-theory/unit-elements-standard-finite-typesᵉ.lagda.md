# Unit elements in the standard finite types

```agda
module elementary-number-theory.unit-elements-standard-finite-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.congruence-natural-numbersᵉ
open import elementary-number-theory.distance-natural-numbersᵉ
open import elementary-number-theory.divisibility-standard-finite-typesᵉ
open import elementary-number-theory.modular-arithmetic-standard-finite-typesᵉ
open import elementary-number-theory.multiplication-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ
open import elementary-number-theory.squares-natural-numbersᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ

open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Aᵉ unitᵉ elementᵉ in aᵉ standardᵉ finiteᵉ typeᵉ isᵉ aᵉ divisorᵉ ofᵉ oneᵉ

## Definition

### Units in the standard finite types

```agda
is-unit-Finᵉ : (kᵉ : ℕᵉ) → Finᵉ kᵉ → UUᵉ lzero
is-unit-Finᵉ (succ-ℕᵉ kᵉ) xᵉ = div-Finᵉ (succ-ℕᵉ kᵉ) xᵉ (one-Finᵉ kᵉ)

unit-Finᵉ : ℕᵉ → UUᵉ lzero
unit-Finᵉ kᵉ = Σᵉ (Finᵉ kᵉ) (is-unit-Finᵉ kᵉ)
```

## Properties

### One is a unit

```agda
is-unit-one-Finᵉ : {kᵉ : ℕᵉ} → is-unit-Finᵉ (succ-ℕᵉ kᵉ) (one-Finᵉ kᵉ)
is-unit-one-Finᵉ {kᵉ} = refl-div-Finᵉ (one-Finᵉ kᵉ)

one-unit-Finᵉ : {kᵉ : ℕᵉ} → unit-Finᵉ (succ-ℕᵉ kᵉ)
pr1ᵉ (one-unit-Finᵉ {kᵉ}) = one-Finᵉ kᵉ
pr2ᵉ (one-unit-Finᵉ {kᵉ}) = is-unit-one-Finᵉ
```

### Negative one is a unit

```agda
is-unit-neg-one-Finᵉ : {kᵉ : ℕᵉ} → is-unit-Finᵉ (succ-ℕᵉ kᵉ) (neg-one-Finᵉ kᵉ)
is-unit-neg-one-Finᵉ {zero-ℕᵉ} = refl-div-Finᵉ (neg-one-Finᵉ 0ᵉ)
pr1ᵉ (is-unit-neg-one-Finᵉ {succ-ℕᵉ kᵉ}) = neg-one-Finᵉ (succ-ℕᵉ kᵉ)
pr2ᵉ (is-unit-neg-one-Finᵉ {succ-ℕᵉ kᵉ}) =
  eq-mod-succ-cong-ℕᵉ
    ( succ-ℕᵉ kᵉ)
    ( (succ-ℕᵉ kᵉ) *ℕᵉ (succ-ℕᵉ kᵉ))
    ( 1ᵉ)
    ( concatenate-eq-cong-ℕᵉ
      ( succ-ℕᵉ (succ-ℕᵉ kᵉ))
      { x3ᵉ = 1ᵉ}
      ( square-succ-ℕᵉ kᵉ)
      ( pairᵉ kᵉ
        ( ( commutative-mul-ℕᵉ kᵉ (succ-ℕᵉ (succ-ℕᵉ kᵉ))) ∙ᵉ
          ( invᵉ (right-unit-law-dist-ℕᵉ ((succ-ℕᵉ (succ-ℕᵉ kᵉ)) *ℕᵉ kᵉ))))))

neg-one-unit-Finᵉ : (kᵉ : ℕᵉ) → unit-Finᵉ (succ-ℕᵉ kᵉ)
pr1ᵉ (neg-one-unit-Finᵉ kᵉ) = neg-one-Finᵉ kᵉ
pr2ᵉ (neg-one-unit-Finᵉ kᵉ) = is-unit-neg-one-Finᵉ
```

### Units are closed under multiplication

```agda
is-unit-mul-Finᵉ :
  {kᵉ : ℕᵉ} {xᵉ yᵉ : Finᵉ kᵉ} →
  is-unit-Finᵉ kᵉ xᵉ → is-unit-Finᵉ kᵉ yᵉ → is-unit-Finᵉ kᵉ (mul-Finᵉ kᵉ xᵉ yᵉ)
pr1ᵉ (is-unit-mul-Finᵉ {succ-ℕᵉ kᵉ} {xᵉ} {yᵉ} (pairᵉ dᵉ pᵉ) (pairᵉ eᵉ qᵉ)) =
  mul-Finᵉ (succ-ℕᵉ kᵉ) eᵉ dᵉ
pr2ᵉ (is-unit-mul-Finᵉ {succ-ℕᵉ kᵉ} {xᵉ} {yᵉ} (pairᵉ dᵉ pᵉ) (pairᵉ eᵉ qᵉ)) =
  ( associative-mul-Finᵉ (succ-ℕᵉ kᵉ) eᵉ dᵉ (mul-Finᵉ (succ-ℕᵉ kᵉ) xᵉ yᵉ)) ∙ᵉ
    ( ( apᵉ
        ( mul-Finᵉ (succ-ℕᵉ kᵉ) eᵉ)
        ( ( invᵉ (associative-mul-Finᵉ (succ-ℕᵉ kᵉ) dᵉ xᵉ yᵉ)) ∙ᵉ
          ( apᵉ (mul-Fin'ᵉ (succ-ℕᵉ kᵉ) yᵉ) pᵉ ∙ᵉ left-unit-law-mul-Finᵉ kᵉ yᵉ))) ∙ᵉ
      ( qᵉ))

mul-unit-Finᵉ : (kᵉ : ℕᵉ) → unit-Finᵉ kᵉ → unit-Finᵉ kᵉ → unit-Finᵉ kᵉ
pr1ᵉ (mul-unit-Finᵉ kᵉ uᵉ vᵉ) = mul-Finᵉ kᵉ (pr1ᵉ uᵉ) (pr1ᵉ vᵉ)
pr2ᵉ (mul-unit-Finᵉ kᵉ uᵉ vᵉ) = is-unit-mul-Finᵉ (pr2ᵉ uᵉ) (pr2ᵉ vᵉ)
```

### The multiplicative inverse of a unit

```agda
inv-unit-Finᵉ : {kᵉ : ℕᵉ} → unit-Finᵉ kᵉ → unit-Finᵉ kᵉ
pr1ᵉ (inv-unit-Finᵉ {succ-ℕᵉ kᵉ} (pairᵉ uᵉ (pairᵉ vᵉ pᵉ))) = vᵉ
pr1ᵉ (pr2ᵉ (inv-unit-Finᵉ {succ-ℕᵉ kᵉ} (pairᵉ uᵉ (pairᵉ vᵉ pᵉ)))) = uᵉ
pr2ᵉ (pr2ᵉ (inv-unit-Finᵉ {succ-ℕᵉ kᵉ} (pairᵉ uᵉ (pairᵉ vᵉ pᵉ)))) =
  commutative-mul-Finᵉ (succ-ℕᵉ kᵉ) uᵉ vᵉ ∙ᵉ pᵉ
```