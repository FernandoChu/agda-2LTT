# Equality of natural numbers

```agda
module elementary-number-theory.equality-natural-numbersᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.coproduct-typesᵉ
open import foundation.decidable-equalityᵉ
open import foundation.decidable-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.empty-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.set-truncationsᵉ
open import foundation.setsᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.decidable-propositionsᵉ
open import foundation-core.torsorial-type-familiesᵉ
```

</details>

## Definitions

### Observational equality on the natural numbers

```agda
Eq-ℕᵉ : ℕᵉ → ℕᵉ → UUᵉ lzero
Eq-ℕᵉ zero-ℕᵉ zero-ℕᵉ = unitᵉ
Eq-ℕᵉ zero-ℕᵉ (succ-ℕᵉ nᵉ) = emptyᵉ
Eq-ℕᵉ (succ-ℕᵉ mᵉ) zero-ℕᵉ = emptyᵉ
Eq-ℕᵉ (succ-ℕᵉ mᵉ) (succ-ℕᵉ nᵉ) = Eq-ℕᵉ mᵉ nᵉ
```

## Properties

### The type of natural numbers is a set

```agda
abstract
  is-prop-Eq-ℕᵉ :
    (nᵉ mᵉ : ℕᵉ) → is-propᵉ (Eq-ℕᵉ nᵉ mᵉ)
  is-prop-Eq-ℕᵉ zero-ℕᵉ zero-ℕᵉ = is-prop-unitᵉ
  is-prop-Eq-ℕᵉ zero-ℕᵉ (succ-ℕᵉ mᵉ) = is-prop-emptyᵉ
  is-prop-Eq-ℕᵉ (succ-ℕᵉ nᵉ) zero-ℕᵉ = is-prop-emptyᵉ
  is-prop-Eq-ℕᵉ (succ-ℕᵉ nᵉ) (succ-ℕᵉ mᵉ) = is-prop-Eq-ℕᵉ nᵉ mᵉ

refl-Eq-ℕᵉ : (nᵉ : ℕᵉ) → Eq-ℕᵉ nᵉ nᵉ
refl-Eq-ℕᵉ zero-ℕᵉ = starᵉ
refl-Eq-ℕᵉ (succ-ℕᵉ nᵉ) = refl-Eq-ℕᵉ nᵉ

Eq-eq-ℕᵉ : {xᵉ yᵉ : ℕᵉ} → xᵉ ＝ᵉ yᵉ → Eq-ℕᵉ xᵉ yᵉ
Eq-eq-ℕᵉ {xᵉ} {.xᵉ} reflᵉ = refl-Eq-ℕᵉ xᵉ

eq-Eq-ℕᵉ : (xᵉ yᵉ : ℕᵉ) → Eq-ℕᵉ xᵉ yᵉ → xᵉ ＝ᵉ yᵉ
eq-Eq-ℕᵉ zero-ℕᵉ zero-ℕᵉ eᵉ = reflᵉ
eq-Eq-ℕᵉ (succ-ℕᵉ xᵉ) (succ-ℕᵉ yᵉ) eᵉ = apᵉ succ-ℕᵉ (eq-Eq-ℕᵉ xᵉ yᵉ eᵉ)

abstract
  is-set-ℕᵉ : is-setᵉ ℕᵉ
  is-set-ℕᵉ =
    is-set-prop-in-idᵉ
      Eq-ℕᵉ
      is-prop-Eq-ℕᵉ
      refl-Eq-ℕᵉ
      eq-Eq-ℕᵉ

ℕ-Setᵉ : Setᵉ lzero
pr1ᵉ ℕ-Setᵉ = ℕᵉ
pr2ᵉ ℕ-Setᵉ = is-set-ℕᵉ
```

### The property of being zero

```agda
is-prop-is-zero-ℕᵉ : (nᵉ : ℕᵉ) → is-propᵉ (is-zero-ℕᵉ nᵉ)
is-prop-is-zero-ℕᵉ nᵉ = is-set-ℕᵉ nᵉ zero-ℕᵉ

is-zero-ℕ-Propᵉ : ℕᵉ → Propᵉ lzero
pr1ᵉ (is-zero-ℕ-Propᵉ nᵉ) = is-zero-ℕᵉ nᵉ
pr2ᵉ (is-zero-ℕ-Propᵉ nᵉ) = is-prop-is-zero-ℕᵉ nᵉ
```

### The property of being one

```agda
is-prop-is-one-ℕᵉ : (nᵉ : ℕᵉ) → is-propᵉ (is-one-ℕᵉ nᵉ)
is-prop-is-one-ℕᵉ nᵉ = is-set-ℕᵉ nᵉ 1

is-one-ℕ-Propᵉ : ℕᵉ → Propᵉ lzero
pr1ᵉ (is-one-ℕ-Propᵉ nᵉ) = is-one-ℕᵉ nᵉ
pr2ᵉ (is-one-ℕ-Propᵉ nᵉ) = is-prop-is-one-ℕᵉ nᵉ
```

### The type of natural numbers has decidable equality

```agda
is-decidable-Eq-ℕᵉ :
  (mᵉ nᵉ : ℕᵉ) → is-decidableᵉ (Eq-ℕᵉ mᵉ nᵉ)
is-decidable-Eq-ℕᵉ zero-ℕᵉ zero-ℕᵉ = inlᵉ starᵉ
is-decidable-Eq-ℕᵉ zero-ℕᵉ (succ-ℕᵉ nᵉ) = inrᵉ idᵉ
is-decidable-Eq-ℕᵉ (succ-ℕᵉ mᵉ) zero-ℕᵉ = inrᵉ idᵉ
is-decidable-Eq-ℕᵉ (succ-ℕᵉ mᵉ) (succ-ℕᵉ nᵉ) = is-decidable-Eq-ℕᵉ mᵉ nᵉ

has-decidable-equality-ℕᵉ : has-decidable-equalityᵉ ℕᵉ
has-decidable-equality-ℕᵉ xᵉ yᵉ =
  is-decidable-iffᵉ (eq-Eq-ℕᵉ xᵉ yᵉ) Eq-eq-ℕᵉ (is-decidable-Eq-ℕᵉ xᵉ yᵉ)

decidable-eq-ℕᵉ : ℕᵉ → ℕᵉ → Decidable-Propᵉ lzero
pr1ᵉ (decidable-eq-ℕᵉ mᵉ nᵉ) = (mᵉ ＝ᵉ nᵉ)
pr1ᵉ (pr2ᵉ (decidable-eq-ℕᵉ mᵉ nᵉ)) = is-set-ℕᵉ mᵉ nᵉ
pr2ᵉ (pr2ᵉ (decidable-eq-ℕᵉ mᵉ nᵉ)) = has-decidable-equality-ℕᵉ mᵉ nᵉ

is-decidable-is-zero-ℕᵉ : (nᵉ : ℕᵉ) → is-decidableᵉ (is-zero-ℕᵉ nᵉ)
is-decidable-is-zero-ℕᵉ nᵉ = has-decidable-equality-ℕᵉ nᵉ zero-ℕᵉ

is-decidable-is-zero-ℕ'ᵉ : (nᵉ : ℕᵉ) → is-decidableᵉ (is-zero-ℕ'ᵉ nᵉ)
is-decidable-is-zero-ℕ'ᵉ nᵉ = has-decidable-equality-ℕᵉ zero-ℕᵉ nᵉ

is-decidable-is-nonzero-ℕᵉ : (nᵉ : ℕᵉ) → is-decidableᵉ (is-nonzero-ℕᵉ nᵉ)
is-decidable-is-nonzero-ℕᵉ nᵉ =
  is-decidable-negᵉ (is-decidable-is-zero-ℕᵉ nᵉ)

is-decidable-is-one-ℕᵉ : (nᵉ : ℕᵉ) → is-decidableᵉ (is-one-ℕᵉ nᵉ)
is-decidable-is-one-ℕᵉ nᵉ = has-decidable-equality-ℕᵉ nᵉ 1

is-decidable-is-one-ℕ'ᵉ : (nᵉ : ℕᵉ) → is-decidableᵉ (is-one-ℕ'ᵉ nᵉ)
is-decidable-is-one-ℕ'ᵉ nᵉ = has-decidable-equality-ℕᵉ 1 nᵉ

is-decidable-is-not-one-ℕᵉ :
  (xᵉ : ℕᵉ) → is-decidableᵉ (is-not-one-ℕᵉ xᵉ)
is-decidable-is-not-one-ℕᵉ xᵉ =
  is-decidable-negᵉ (is-decidable-is-one-ℕᵉ xᵉ)
```

## The full characterization of the identity type of `ℕ`

```agda
map-total-Eq-ℕᵉ :
  (mᵉ : ℕᵉ) → Σᵉ ℕᵉ (Eq-ℕᵉ mᵉ) → Σᵉ ℕᵉ (Eq-ℕᵉ (succ-ℕᵉ mᵉ))
pr1ᵉ (map-total-Eq-ℕᵉ mᵉ (nᵉ ,ᵉ eᵉ)) = succ-ℕᵉ nᵉ
pr2ᵉ (map-total-Eq-ℕᵉ mᵉ (nᵉ ,ᵉ eᵉ)) = eᵉ

is-torsorial-Eq-ℕᵉ :
  (mᵉ : ℕᵉ) → is-torsorialᵉ (Eq-ℕᵉ mᵉ)
pr1ᵉ (pr1ᵉ (is-torsorial-Eq-ℕᵉ mᵉ)) = mᵉ
pr2ᵉ (pr1ᵉ (is-torsorial-Eq-ℕᵉ mᵉ)) = refl-Eq-ℕᵉ mᵉ
pr2ᵉ (is-torsorial-Eq-ℕᵉ zero-ℕᵉ) (pairᵉ zero-ℕᵉ starᵉ) = reflᵉ
pr2ᵉ (is-torsorial-Eq-ℕᵉ (succ-ℕᵉ mᵉ)) (pairᵉ (succ-ℕᵉ nᵉ) eᵉ) =
  apᵉ (map-total-Eq-ℕᵉ mᵉ) (pr2ᵉ (is-torsorial-Eq-ℕᵉ mᵉ) (pairᵉ nᵉ eᵉ))

is-equiv-Eq-eq-ℕᵉ :
  {mᵉ nᵉ : ℕᵉ} → is-equivᵉ (Eq-eq-ℕᵉ {mᵉ} {nᵉ})
is-equiv-Eq-eq-ℕᵉ {mᵉ} {nᵉ} =
  fundamental-theorem-idᵉ
    ( is-torsorial-Eq-ℕᵉ mᵉ)
    ( λ yᵉ → Eq-eq-ℕᵉ {mᵉ} {yᵉ})
    ( nᵉ)
```

### The type of natural numbers is its own set truncation

```agda
equiv-unit-trunc-ℕ-Setᵉ : ℕᵉ ≃ᵉ type-trunc-Setᵉ ℕᵉ
equiv-unit-trunc-ℕ-Setᵉ = equiv-unit-trunc-Setᵉ ℕ-Setᵉ
```