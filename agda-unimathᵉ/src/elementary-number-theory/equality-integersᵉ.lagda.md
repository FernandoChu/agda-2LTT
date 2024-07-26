# Equality of integers

```agda
module elementary-number-theory.equality-integersᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.equality-natural-numbersᵉ
open import elementary-number-theory.integersᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.coproduct-typesᵉ
open import foundation.decidable-equalityᵉ
open import foundation.decidable-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.discrete-typesᵉ
open import foundation.empty-typesᵉ
open import foundation.equality-dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.set-truncationsᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Anᵉ equalityᵉ predicateᵉ isᵉ definedᵉ byᵉ pattern matchingᵉ onᵉ theᵉ integers.ᵉ Thenᵉ weᵉ
showᵉ thatᵉ thisᵉ predicateᵉ characterizesᵉ theᵉ identitᵉ typeᵉ ofᵉ theᵉ integersᵉ

## Definition

```agda
Eq-ℤᵉ : ℤᵉ → ℤᵉ → UUᵉ lzero
Eq-ℤᵉ (inlᵉ xᵉ) (inlᵉ yᵉ) = Eq-ℕᵉ xᵉ yᵉ
Eq-ℤᵉ (inlᵉ xᵉ) (inrᵉ yᵉ) = emptyᵉ
Eq-ℤᵉ (inrᵉ xᵉ) (inlᵉ yᵉ) = emptyᵉ
Eq-ℤᵉ (inrᵉ (inlᵉ xᵉ)) (inrᵉ (inlᵉ yᵉ)) = unitᵉ
Eq-ℤᵉ (inrᵉ (inlᵉ xᵉ)) (inrᵉ (inrᵉ yᵉ)) = emptyᵉ
Eq-ℤᵉ (inrᵉ (inrᵉ xᵉ)) (inrᵉ (inlᵉ yᵉ)) = emptyᵉ
Eq-ℤᵉ (inrᵉ (inrᵉ xᵉ)) (inrᵉ (inrᵉ yᵉ)) = Eq-ℕᵉ xᵉ yᵉ

refl-Eq-ℤᵉ : (xᵉ : ℤᵉ) → Eq-ℤᵉ xᵉ xᵉ
refl-Eq-ℤᵉ (inlᵉ xᵉ) = refl-Eq-ℕᵉ xᵉ
refl-Eq-ℤᵉ (inrᵉ (inlᵉ xᵉ)) = starᵉ
refl-Eq-ℤᵉ (inrᵉ (inrᵉ xᵉ)) = refl-Eq-ℕᵉ xᵉ

Eq-eq-ℤᵉ : {xᵉ yᵉ : ℤᵉ} → xᵉ ＝ᵉ yᵉ → Eq-ℤᵉ xᵉ yᵉ
Eq-eq-ℤᵉ {xᵉ} {.xᵉ} reflᵉ = refl-Eq-ℤᵉ xᵉ

eq-Eq-ℤᵉ : (xᵉ yᵉ : ℤᵉ) → Eq-ℤᵉ xᵉ yᵉ → xᵉ ＝ᵉ yᵉ
eq-Eq-ℤᵉ (inlᵉ xᵉ) (inlᵉ yᵉ) eᵉ = apᵉ inlᵉ (eq-Eq-ℕᵉ xᵉ yᵉ eᵉ)
eq-Eq-ℤᵉ (inrᵉ (inlᵉ starᵉ)) (inrᵉ (inlᵉ starᵉ)) eᵉ = reflᵉ
eq-Eq-ℤᵉ (inrᵉ (inrᵉ xᵉ)) (inrᵉ (inrᵉ yᵉ)) eᵉ = apᵉ (inrᵉ ∘ᵉ inrᵉ) (eq-Eq-ℕᵉ xᵉ yᵉ eᵉ)
```

## Properties

### Equality on the integers is decidable

```agda
has-decidable-equality-ℤᵉ : has-decidable-equalityᵉ ℤᵉ
has-decidable-equality-ℤᵉ =
  has-decidable-equality-coproductᵉ
    has-decidable-equality-ℕᵉ
    ( has-decidable-equality-coproductᵉ
      has-decidable-equality-unitᵉ
      has-decidable-equality-ℕᵉ)

is-decidable-is-zero-ℤᵉ :
  (xᵉ : ℤᵉ) → is-decidableᵉ (is-zero-ℤᵉ xᵉ)
is-decidable-is-zero-ℤᵉ xᵉ = has-decidable-equality-ℤᵉ xᵉ zero-ℤᵉ

is-decidable-is-one-ℤᵉ :
  (xᵉ : ℤᵉ) → is-decidableᵉ (is-one-ℤᵉ xᵉ)
is-decidable-is-one-ℤᵉ xᵉ = has-decidable-equality-ℤᵉ xᵉ one-ℤᵉ

is-decidable-is-neg-one-ℤᵉ :
  (xᵉ : ℤᵉ) → is-decidableᵉ (is-neg-one-ℤᵉ xᵉ)
is-decidable-is-neg-one-ℤᵉ xᵉ = has-decidable-equality-ℤᵉ xᵉ neg-one-ℤᵉ

ℤ-Discrete-Typeᵉ : Discrete-Typeᵉ lzero
pr1ᵉ ℤ-Discrete-Typeᵉ = ℤᵉ
pr2ᵉ ℤ-Discrete-Typeᵉ = has-decidable-equality-ℤᵉ
```

### The type of integers is its own set truncation

```agda
equiv-unit-trunc-ℤ-Setᵉ : ℤᵉ ≃ᵉ type-trunc-Setᵉ ℤᵉ
equiv-unit-trunc-ℤ-Setᵉ = equiv-unit-trunc-Setᵉ ℤ-Setᵉ
```

### Equality on the integers is a proposition

```agda
is-prop-Eq-ℤᵉ :
  (xᵉ yᵉ : ℤᵉ) → is-propᵉ (Eq-ℤᵉ xᵉ yᵉ)
is-prop-Eq-ℤᵉ (inlᵉ xᵉ) (inlᵉ yᵉ) = is-prop-Eq-ℕᵉ xᵉ yᵉ
is-prop-Eq-ℤᵉ (inlᵉ xᵉ) (inrᵉ yᵉ) = is-prop-emptyᵉ
is-prop-Eq-ℤᵉ (inrᵉ xᵉ) (inlᵉ x₁ᵉ) = is-prop-emptyᵉ
is-prop-Eq-ℤᵉ (inrᵉ (inlᵉ xᵉ)) (inrᵉ (inlᵉ yᵉ)) = is-prop-unitᵉ
is-prop-Eq-ℤᵉ (inrᵉ (inlᵉ xᵉ)) (inrᵉ (inrᵉ yᵉ)) = is-prop-emptyᵉ
is-prop-Eq-ℤᵉ (inrᵉ (inrᵉ xᵉ)) (inrᵉ (inlᵉ yᵉ)) = is-prop-emptyᵉ
is-prop-Eq-ℤᵉ (inrᵉ (inrᵉ xᵉ)) (inrᵉ (inrᵉ yᵉ)) = is-prop-Eq-ℕᵉ xᵉ yᵉ

Eq-ℤ-eqᵉ :
  {xᵉ yᵉ : ℤᵉ} → xᵉ ＝ᵉ yᵉ → Eq-ℤᵉ xᵉ yᵉ
Eq-ℤ-eqᵉ {xᵉ} {.xᵉ} reflᵉ = refl-Eq-ℤᵉ xᵉ

contraction-total-Eq-ℤᵉ :
  (xᵉ : ℤᵉ) (yᵉ : Σᵉ ℤᵉ (Eq-ℤᵉ xᵉ)) → pairᵉ xᵉ (refl-Eq-ℤᵉ xᵉ) ＝ᵉ yᵉ
contraction-total-Eq-ℤᵉ (inlᵉ xᵉ) (pairᵉ (inlᵉ yᵉ) eᵉ) =
  eq-pair-Σᵉ
    ( apᵉ inlᵉ (eq-Eq-ℕᵉ xᵉ yᵉ eᵉ))
    ( eq-is-propᵉ (is-prop-Eq-ℕᵉ xᵉ yᵉ))
contraction-total-Eq-ℤᵉ (inrᵉ (inlᵉ starᵉ)) (pairᵉ (inrᵉ (inlᵉ starᵉ)) eᵉ) =
  eq-pair-eq-fiberᵉ (eq-is-propᵉ is-prop-unitᵉ)
contraction-total-Eq-ℤᵉ (inrᵉ (inrᵉ xᵉ)) (pairᵉ (inrᵉ (inrᵉ yᵉ)) eᵉ) =
  eq-pair-Σᵉ
    ( apᵉ (inrᵉ ∘ᵉ inrᵉ) (eq-Eq-ℕᵉ xᵉ yᵉ eᵉ))
    ( eq-is-propᵉ (is-prop-Eq-ℕᵉ xᵉ yᵉ))

is-torsorial-Eq-ℤᵉ :
  (xᵉ : ℤᵉ) → is-torsorialᵉ (Eq-ℤᵉ xᵉ)
is-torsorial-Eq-ℤᵉ xᵉ =
  pairᵉ (pairᵉ xᵉ (refl-Eq-ℤᵉ xᵉ)) (contraction-total-Eq-ℤᵉ xᵉ)

is-equiv-Eq-ℤ-eqᵉ :
  (xᵉ yᵉ : ℤᵉ) → is-equivᵉ (Eq-ℤ-eqᵉ {xᵉ} {yᵉ})
is-equiv-Eq-ℤ-eqᵉ xᵉ =
  fundamental-theorem-idᵉ
    ( is-torsorial-Eq-ℤᵉ xᵉ)
    ( λ yᵉ → Eq-ℤ-eqᵉ {xᵉ} {yᵉ})
```