# Equality in the standard finite types

```agda
module univalent-combinatorics.equality-standard-finite-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.apartness-relationsᵉ
open import foundation.contractible-typesᵉ
open import foundation.coproduct-typesᵉ
open import foundation.decidable-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.discrete-typesᵉ
open import foundation.empty-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.functoriality-coproduct-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.negated-equalityᵉ
open import foundation.negationᵉ
open import foundation.propositionsᵉ
open import foundation.set-truncationsᵉ
open import foundation.tight-apartness-relationsᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.decidable-propositionsᵉ

open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Sinceᵉ theᵉ standardᵉ finiteᵉ typesᵉ areᵉ definedᵉ recursivelyᵉ byᵉ addingᵉ aᵉ pointᵉ oneᵉ atᵉ
aᵉ time,ᵉ itᵉ followsᵉ thatᵉ equalityᵉ in theᵉ standardᵉ finiteᵉ typesᵉ isᵉ decidable,ᵉ andᵉ
thatᵉ theyᵉ areᵉ sets.ᵉ

## Properties

### Characterization of the identity types of the standard finite types

```agda
Eq-Finᵉ : (kᵉ : ℕᵉ) → Finᵉ kᵉ → Finᵉ kᵉ → UUᵉ lzero
Eq-Finᵉ (succ-ℕᵉ kᵉ) (inlᵉ xᵉ) (inlᵉ yᵉ) = Eq-Finᵉ kᵉ xᵉ yᵉ
Eq-Finᵉ (succ-ℕᵉ kᵉ) (inlᵉ xᵉ) (inrᵉ yᵉ) = emptyᵉ
Eq-Finᵉ (succ-ℕᵉ kᵉ) (inrᵉ xᵉ) (inlᵉ yᵉ) = emptyᵉ
Eq-Finᵉ (succ-ℕᵉ kᵉ) (inrᵉ xᵉ) (inrᵉ yᵉ) = unitᵉ

is-prop-Eq-Finᵉ : (kᵉ : ℕᵉ) → (xᵉ : Finᵉ kᵉ) → (yᵉ : Finᵉ kᵉ) → is-propᵉ (Eq-Finᵉ kᵉ xᵉ yᵉ)
is-prop-Eq-Finᵉ (succ-ℕᵉ kᵉ) (inlᵉ xᵉ) (inlᵉ yᵉ) = is-prop-Eq-Finᵉ kᵉ xᵉ yᵉ
is-prop-Eq-Finᵉ (succ-ℕᵉ kᵉ) (inrᵉ xᵉ) (inlᵉ yᵉ) = is-prop-emptyᵉ
is-prop-Eq-Finᵉ (succ-ℕᵉ kᵉ) (inlᵉ xᵉ) (inrᵉ yᵉ) = is-prop-emptyᵉ
is-prop-Eq-Finᵉ (succ-ℕᵉ kᵉ) (inrᵉ xᵉ) (inrᵉ yᵉ) = is-prop-unitᵉ

refl-Eq-Finᵉ : (kᵉ : ℕᵉ) (xᵉ : Finᵉ kᵉ) → Eq-Finᵉ kᵉ xᵉ xᵉ
refl-Eq-Finᵉ (succ-ℕᵉ kᵉ) (inlᵉ xᵉ) = refl-Eq-Finᵉ kᵉ xᵉ
refl-Eq-Finᵉ (succ-ℕᵉ kᵉ) (inrᵉ xᵉ) = starᵉ

Eq-Fin-eqᵉ : (kᵉ : ℕᵉ) {xᵉ yᵉ : Finᵉ kᵉ} → Idᵉ xᵉ yᵉ → Eq-Finᵉ kᵉ xᵉ yᵉ
Eq-Fin-eqᵉ kᵉ reflᵉ = refl-Eq-Finᵉ kᵉ _

eq-Eq-Finᵉ :
  (kᵉ : ℕᵉ) {xᵉ yᵉ : Finᵉ kᵉ} → Eq-Finᵉ kᵉ xᵉ yᵉ → Idᵉ xᵉ yᵉ
eq-Eq-Finᵉ (succ-ℕᵉ kᵉ) {inlᵉ xᵉ} {inlᵉ yᵉ} eᵉ = apᵉ inlᵉ (eq-Eq-Finᵉ kᵉ eᵉ)
eq-Eq-Finᵉ (succ-ℕᵉ kᵉ) {inrᵉ starᵉ} {inrᵉ starᵉ} starᵉ = reflᵉ

extensionality-Finᵉ :
  (kᵉ : ℕᵉ)
  (xᵉ yᵉ : Finᵉ kᵉ) →
  (xᵉ ＝ᵉ yᵉ) ≃ᵉ (Eq-Finᵉ kᵉ xᵉ yᵉ)
pr1ᵉ (extensionality-Finᵉ kᵉ xᵉ yᵉ) = Eq-Fin-eqᵉ kᵉ
pr2ᵉ (extensionality-Finᵉ kᵉ xᵉ yᵉ) =
  is-equiv-has-converse-is-propᵉ
    ( is-set-Finᵉ kᵉ xᵉ yᵉ)
    ( is-prop-Eq-Finᵉ kᵉ xᵉ yᵉ)
    ( eq-Eq-Finᵉ kᵉ)

is-decidable-Eq-Finᵉ : (kᵉ : ℕᵉ) (xᵉ yᵉ : Finᵉ kᵉ) → is-decidableᵉ (Eq-Finᵉ kᵉ xᵉ yᵉ)
is-decidable-Eq-Finᵉ (succ-ℕᵉ kᵉ) (inlᵉ xᵉ) (inlᵉ yᵉ) = is-decidable-Eq-Finᵉ kᵉ xᵉ yᵉ
is-decidable-Eq-Finᵉ (succ-ℕᵉ kᵉ) (inlᵉ xᵉ) (inrᵉ yᵉ) = is-decidable-emptyᵉ
is-decidable-Eq-Finᵉ (succ-ℕᵉ kᵉ) (inrᵉ xᵉ) (inlᵉ yᵉ) = is-decidable-emptyᵉ
is-decidable-Eq-Finᵉ (succ-ℕᵉ kᵉ) (inrᵉ xᵉ) (inrᵉ yᵉ) = is-decidable-unitᵉ

has-decidable-equality-Finᵉ :
  (kᵉ : ℕᵉ) (xᵉ yᵉ : Finᵉ kᵉ) → is-decidableᵉ (Idᵉ xᵉ yᵉ)
has-decidable-equality-Finᵉ kᵉ xᵉ yᵉ =
  map-coproductᵉ
    ( eq-Eq-Finᵉ kᵉ)
    ( map-negᵉ (Eq-Fin-eqᵉ kᵉ))
    ( is-decidable-Eq-Finᵉ kᵉ xᵉ yᵉ)

Fin-Discrete-Typeᵉ : ℕᵉ → Discrete-Typeᵉ lzero
pr1ᵉ (Fin-Discrete-Typeᵉ kᵉ) = Finᵉ kᵉ
pr2ᵉ (Fin-Discrete-Typeᵉ kᵉ) = has-decidable-equality-Finᵉ kᵉ

is-decidable-is-zero-Finᵉ :
  {kᵉ : ℕᵉ} (xᵉ : Finᵉ kᵉ) → is-decidableᵉ (is-zero-Finᵉ kᵉ xᵉ)
is-decidable-is-zero-Finᵉ {succ-ℕᵉ kᵉ} xᵉ =
  has-decidable-equality-Finᵉ (succ-ℕᵉ kᵉ) xᵉ (zero-Finᵉ kᵉ)

is-decidable-is-neg-one-Finᵉ :
  {kᵉ : ℕᵉ} (xᵉ : Finᵉ kᵉ) → is-decidableᵉ (is-neg-one-Finᵉ kᵉ xᵉ)
is-decidable-is-neg-one-Finᵉ {succ-ℕᵉ kᵉ} xᵉ =
  has-decidable-equality-Finᵉ (succ-ℕᵉ kᵉ) xᵉ (neg-one-Finᵉ kᵉ)

is-decidable-is-one-Finᵉ :
  {kᵉ : ℕᵉ} (xᵉ : Finᵉ kᵉ) → is-decidableᵉ (is-one-Finᵉ kᵉ xᵉ)
is-decidable-is-one-Finᵉ {succ-ℕᵉ kᵉ} xᵉ =
  has-decidable-equality-Finᵉ (succ-ℕᵉ kᵉ) xᵉ (one-Finᵉ kᵉ)
```

### Being zero or being one is a proposition

```agda
is-prop-is-zero-Finᵉ :
  (kᵉ : ℕᵉ) (xᵉ : Finᵉ (succ-ℕᵉ kᵉ)) → is-propᵉ (is-zero-Finᵉ (succ-ℕᵉ kᵉ) xᵉ)
is-prop-is-zero-Finᵉ kᵉ xᵉ = is-set-Finᵉ (succ-ℕᵉ kᵉ) xᵉ (zero-Finᵉ kᵉ)

is-prop-is-one-Finᵉ :
  (kᵉ : ℕᵉ) (xᵉ : Finᵉ (succ-ℕᵉ kᵉ)) → is-propᵉ (is-one-Finᵉ (succ-ℕᵉ kᵉ) xᵉ)
is-prop-is-one-Finᵉ kᵉ xᵉ = is-set-Finᵉ (succ-ℕᵉ kᵉ) xᵉ (one-Finᵉ kᵉ)

is-prop-is-zero-or-one-Fin-two-ℕᵉ :
  (xᵉ : Finᵉ 2ᵉ) → is-propᵉ ((is-zero-Finᵉ 2 xᵉ) +ᵉ (is-one-Finᵉ 2 xᵉ))
is-prop-is-zero-or-one-Fin-two-ℕᵉ xᵉ =
  is-prop-coproductᵉ
    ( λ pᵉ qᵉ → Eq-Fin-eqᵉ 2 (invᵉ pᵉ ∙ᵉ qᵉ))
    ( is-prop-is-zero-Finᵉ 1 xᵉ)
    ( is-prop-is-one-Finᵉ 1 xᵉ)
```

### Every element in the standard two-element type is either `0` or `1`

```agda
is-contr-is-zero-or-one-Fin-two-ℕᵉ :
  (xᵉ : Finᵉ 2ᵉ) → is-contrᵉ ((is-zero-Finᵉ 2 xᵉ) +ᵉ (is-one-Finᵉ 2 xᵉ))
is-contr-is-zero-or-one-Fin-two-ℕᵉ xᵉ =
  is-proof-irrelevant-is-propᵉ
    ( is-prop-is-zero-or-one-Fin-two-ℕᵉ xᵉ)
    ( is-zero-or-one-Fin-two-ℕᵉ xᵉ)
```

```agda
decidable-Eq-Finᵉ :
  (nᵉ : ℕᵉ) (iᵉ jᵉ : Finᵉ nᵉ) → Decidable-Propᵉ lzero
pr1ᵉ (decidable-Eq-Finᵉ nᵉ iᵉ jᵉ) = Idᵉ iᵉ jᵉ
pr1ᵉ (pr2ᵉ (decidable-Eq-Finᵉ nᵉ iᵉ jᵉ)) = is-set-Finᵉ nᵉ iᵉ jᵉ
pr2ᵉ (pr2ᵉ (decidable-Eq-Finᵉ nᵉ iᵉ jᵉ)) = has-decidable-equality-Finᵉ nᵉ iᵉ jᵉ
```

### The standard finite types are their own set truncations

```agda
equiv-unit-trunc-Fin-Setᵉ : (kᵉ : ℕᵉ) → Finᵉ kᵉ ≃ᵉ type-trunc-Setᵉ (Finᵉ kᵉ)
equiv-unit-trunc-Fin-Setᵉ kᵉ = equiv-unit-trunc-Setᵉ (Fin-Setᵉ kᵉ)
```

### If `leq-ℕ 2 n`, then there exists two distinct elements in `Fin n`

```agda
two-distinct-elements-leq-2-Finᵉ :
  (nᵉ : ℕᵉ) → leq-ℕᵉ 2 nᵉ → Σᵉ (Finᵉ nᵉ) (λ xᵉ → Σᵉ (Finᵉ nᵉ) (λ yᵉ → xᵉ ≠ᵉ yᵉ))
pr1ᵉ (two-distinct-elements-leq-2-Finᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)) ineqᵉ) =
  inrᵉ starᵉ
pr1ᵉ (pr2ᵉ (two-distinct-elements-leq-2-Finᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)) ineqᵉ)) =
  inlᵉ (inrᵉ starᵉ)
pr2ᵉ (pr2ᵉ (two-distinct-elements-leq-2-Finᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)) ineqᵉ)) =
  neq-inr-inlᵉ
```

### The standard finite type with a (tight) apartness relation

```agda
Fin-Type-With-Apartnessᵉ : (kᵉ : ℕᵉ) → Type-With-Apartnessᵉ lzero lzero
Fin-Type-With-Apartnessᵉ kᵉ =
  type-with-apartness-Discrete-Typeᵉ (Fin-Discrete-Typeᵉ kᵉ)

Fin-Type-With-Tight-Apartnessᵉ : (kᵉ : ℕᵉ) → Type-With-Tight-Apartnessᵉ lzero lzero
Fin-Type-With-Tight-Apartnessᵉ kᵉ =
  type-with-tight-apartness-Discrete-Typeᵉ (Fin-Discrete-Typeᵉ kᵉ)
```