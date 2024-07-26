# Modular arithmetic

```agda
module elementary-number-theory.modular-arithmeticᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.absolute-value-integersᵉ
open import elementary-number-theory.addition-integersᵉ
open import elementary-number-theory.congruence-integersᵉ
open import elementary-number-theory.congruence-natural-numbersᵉ
open import elementary-number-theory.divisibility-integersᵉ
open import elementary-number-theory.equality-integersᵉ
open import elementary-number-theory.inequality-integersᵉ
open import elementary-number-theory.integersᵉ
open import elementary-number-theory.modular-arithmetic-standard-finite-typesᵉ
open import elementary-number-theory.multiplication-integersᵉ
open import elementary-number-theory.multiplication-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ
open import elementary-number-theory.nonnegative-integersᵉ

open import foundation.action-on-identifications-binary-functionsᵉ
open import foundation.action-on-identifications-functionsᵉ
open import foundation.coproduct-typesᵉ
open import foundation.decidable-equalityᵉ
open import foundation.decidable-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.discrete-typesᵉ
open import foundation.empty-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.injective-mapsᵉ
open import foundation.negated-equalityᵉ
open import foundation.negationᵉ
open import foundation.setsᵉ
open import foundation.surjective-mapsᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import structured-types.types-equipped-with-endomorphismsᵉ

open import univalent-combinatorics.equality-standard-finite-typesᵉ
open import univalent-combinatorics.finite-typesᵉ
open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

**Modularᵉ arithmetic**ᵉ isᵉ arithmeticᵉ ofᵉ theᵉ integersᵉ moduloᵉ `n`.ᵉ Theᵉ integersᵉ
moduloᵉ `n`ᵉ haveᵉ addition,ᵉ negatives,ᵉ andᵉ multiplicationᵉ thatᵉ satisfyᵉ manyᵉ ofᵉ theᵉ
familiarᵉ propertiesᵉ ofᵉ usualᵉ arithmeticᵉ ofᵉ theᵉ
[integers](elementary-number-theory.integers.md).ᵉ

Someᵉ modularᵉ arithmeticᵉ wasᵉ alreadyᵉ definedᵉ in
`modular-arithmetic-standard-finite-types`.ᵉ Hereᵉ weᵉ collectᵉ thoseᵉ resultsᵉ in aᵉ
moreᵉ convenientᵉ formatᵉ thatᵉ alsoᵉ includesᵉ theᵉ integersᵉ moduloᵉ `0`,ᵉ i.e.,ᵉ theᵉ
integers.ᵉ

Theᵉ factᵉ thatᵉ `ℤ-Modᵉ n`ᵉ isᵉ aᵉ [ring](ring-theory.rings.mdᵉ) forᵉ everyᵉ `nᵉ : ℕ`ᵉ isᵉ
recordedᵉ in
[`elementary-number-theory.standard-cyclic-rings`](elementary-number-theory.standard-cyclic-rings.md).ᵉ

```agda
ℤ-Modᵉ : ℕᵉ → UUᵉ lzero
ℤ-Modᵉ zero-ℕᵉ = ℤᵉ
ℤ-Modᵉ (succ-ℕᵉ kᵉ) = Finᵉ (succ-ℕᵉ kᵉ)
```

## Important integers modulo k

```agda
zero-ℤ-Modᵉ : (kᵉ : ℕᵉ) → ℤ-Modᵉ kᵉ
zero-ℤ-Modᵉ zero-ℕᵉ = zero-ℤᵉ
zero-ℤ-Modᵉ (succ-ℕᵉ kᵉ) = zero-Finᵉ kᵉ

is-zero-ℤ-Modᵉ : (kᵉ : ℕᵉ) → ℤ-Modᵉ kᵉ → UUᵉ lzero
is-zero-ℤ-Modᵉ kᵉ xᵉ = (xᵉ ＝ᵉ zero-ℤ-Modᵉ kᵉ)

is-nonzero-ℤ-Modᵉ : (kᵉ : ℕᵉ) → ℤ-Modᵉ kᵉ → UUᵉ lzero
is-nonzero-ℤ-Modᵉ kᵉ xᵉ = ¬ᵉ (is-zero-ℤ-Modᵉ kᵉ xᵉ)

neg-one-ℤ-Modᵉ : (kᵉ : ℕᵉ) → ℤ-Modᵉ kᵉ
neg-one-ℤ-Modᵉ zero-ℕᵉ = neg-one-ℤᵉ
neg-one-ℤ-Modᵉ (succ-ℕᵉ kᵉ) = neg-one-Finᵉ kᵉ

one-ℤ-Modᵉ : (kᵉ : ℕᵉ) → ℤ-Modᵉ kᵉ
one-ℤ-Modᵉ zero-ℕᵉ = one-ℤᵉ
one-ℤ-Modᵉ (succ-ℕᵉ kᵉ) = one-Finᵉ kᵉ
```

### The integers modulo k have decidable equality

```agda
has-decidable-equality-ℤ-Modᵉ : (kᵉ : ℕᵉ) → has-decidable-equalityᵉ (ℤ-Modᵉ kᵉ)
has-decidable-equality-ℤ-Modᵉ zero-ℕᵉ = has-decidable-equality-ℤᵉ
has-decidable-equality-ℤ-Modᵉ (succ-ℕᵉ kᵉ) = has-decidable-equality-Finᵉ (succ-ℕᵉ kᵉ)
```

### The integers modulo `k` are a discrete type

```agda
ℤ-Mod-Discrete-Typeᵉ : (kᵉ : ℕᵉ) → Discrete-Typeᵉ lzero
ℤ-Mod-Discrete-Typeᵉ zero-ℕᵉ = ℤ-Discrete-Typeᵉ
ℤ-Mod-Discrete-Typeᵉ (succ-ℕᵉ kᵉ) = Fin-Discrete-Typeᵉ (succ-ℕᵉ kᵉ)
```

### The integers modulo `k` form a set

```agda
abstract
  is-set-ℤ-Modᵉ : (kᵉ : ℕᵉ) → is-setᵉ (ℤ-Modᵉ kᵉ)
  is-set-ℤ-Modᵉ zero-ℕᵉ = is-set-ℤᵉ
  is-set-ℤ-Modᵉ (succ-ℕᵉ kᵉ) = is-set-Finᵉ (succ-ℕᵉ kᵉ)

ℤ-Mod-Setᵉ : (kᵉ : ℕᵉ) → Setᵉ lzero
pr1ᵉ (ℤ-Mod-Setᵉ kᵉ) = ℤ-Modᵉ kᵉ
pr2ᵉ (ℤ-Mod-Setᵉ kᵉ) = is-set-ℤ-Modᵉ kᵉ
```

### The types `ℤ-Mod k` are finite for nonzero natural numbers `k`

```agda
abstract
  is-finite-ℤ-Modᵉ : {kᵉ : ℕᵉ} → is-nonzero-ℕᵉ kᵉ → is-finiteᵉ (ℤ-Modᵉ kᵉ)
  is-finite-ℤ-Modᵉ {zero-ℕᵉ} Hᵉ = ex-falsoᵉ (Hᵉ reflᵉ)
  is-finite-ℤ-Modᵉ {succ-ℕᵉ kᵉ} Hᵉ = is-finite-Finᵉ (succ-ℕᵉ kᵉ)

ℤ-Mod-𝔽ᵉ : (kᵉ : ℕᵉ) → is-nonzero-ℕᵉ kᵉ → 𝔽ᵉ lzero
pr1ᵉ (ℤ-Mod-𝔽ᵉ kᵉ Hᵉ) = ℤ-Modᵉ kᵉ
pr2ᵉ (ℤ-Mod-𝔽ᵉ kᵉ Hᵉ) = is-finite-ℤ-Modᵉ Hᵉ
```

## The inclusion of the integers modulo `k` into ℤ

```agda
int-ℤ-Modᵉ : (kᵉ : ℕᵉ) → ℤ-Modᵉ kᵉ → ℤᵉ
int-ℤ-Modᵉ zero-ℕᵉ xᵉ = xᵉ
int-ℤ-Modᵉ (succ-ℕᵉ kᵉ) xᵉ = int-ℕᵉ (nat-Finᵉ (succ-ℕᵉ kᵉ) xᵉ)

is-injective-int-ℤ-Modᵉ : (kᵉ : ℕᵉ) → is-injectiveᵉ (int-ℤ-Modᵉ kᵉ)
is-injective-int-ℤ-Modᵉ zero-ℕᵉ = is-injective-idᵉ
is-injective-int-ℤ-Modᵉ (succ-ℕᵉ kᵉ) =
  is-injective-compᵉ (is-injective-nat-Finᵉ (succ-ℕᵉ kᵉ)) is-injective-int-ℕᵉ

is-zero-int-zero-ℤ-Modᵉ : (kᵉ : ℕᵉ) → is-zero-ℤᵉ (int-ℤ-Modᵉ kᵉ (zero-ℤ-Modᵉ kᵉ))
is-zero-int-zero-ℤ-Modᵉ (zero-ℕᵉ) = reflᵉ
is-zero-int-zero-ℤ-Modᵉ (succ-ℕᵉ kᵉ) = apᵉ int-ℕᵉ (is-zero-nat-zero-Finᵉ {kᵉ})

int-ℤ-Mod-boundedᵉ :
  (kᵉ : ℕᵉ) → (xᵉ : ℤ-Modᵉ (succ-ℕᵉ kᵉ)) →
  leq-ℤᵉ (int-ℤ-Modᵉ (succ-ℕᵉ kᵉ) xᵉ) (int-ℕᵉ (succ-ℕᵉ kᵉ))
int-ℤ-Mod-boundedᵉ zero-ℕᵉ (inrᵉ xᵉ) = starᵉ
int-ℤ-Mod-boundedᵉ (succ-ℕᵉ kᵉ) (inlᵉ xᵉ) =
  is-nonnegative-succ-is-nonnegative-ℤᵉ
    ( int-ℤ-Mod-boundedᵉ kᵉ xᵉ)
int-ℤ-Mod-boundedᵉ (succ-ℕᵉ kᵉ) (inrᵉ xᵉ) =
  is-nonnegative-succ-is-nonnegative-ℤᵉ
    ( is-nonnegative-eq-ℤᵉ (invᵉ (left-inverse-law-add-ℤᵉ (inlᵉ kᵉ))) starᵉ)
```

## The successor and predecessor functions on the integers modulo `k`

```agda
succ-ℤ-Modᵉ : (kᵉ : ℕᵉ) → ℤ-Modᵉ kᵉ → ℤ-Modᵉ kᵉ
succ-ℤ-Modᵉ zero-ℕᵉ = succ-ℤᵉ
succ-ℤ-Modᵉ (succ-ℕᵉ kᵉ) = succ-Finᵉ (succ-ℕᵉ kᵉ)

ℤ-Mod-Type-With-Endomorphismᵉ : (kᵉ : ℕᵉ) → Type-With-Endomorphismᵉ lzero
pr1ᵉ (ℤ-Mod-Type-With-Endomorphismᵉ kᵉ) = ℤ-Modᵉ kᵉ
pr2ᵉ (ℤ-Mod-Type-With-Endomorphismᵉ kᵉ) = succ-ℤ-Modᵉ kᵉ

abstract
  is-equiv-succ-ℤ-Modᵉ : (kᵉ : ℕᵉ) → is-equivᵉ (succ-ℤ-Modᵉ kᵉ)
  is-equiv-succ-ℤ-Modᵉ zero-ℕᵉ = is-equiv-succ-ℤᵉ
  is-equiv-succ-ℤ-Modᵉ (succ-ℕᵉ kᵉ) = is-equiv-succ-Finᵉ (succ-ℕᵉ kᵉ)

equiv-succ-ℤ-Modᵉ : (kᵉ : ℕᵉ) → ℤ-Modᵉ kᵉ ≃ᵉ ℤ-Modᵉ kᵉ
pr1ᵉ (equiv-succ-ℤ-Modᵉ kᵉ) = succ-ℤ-Modᵉ kᵉ
pr2ᵉ (equiv-succ-ℤ-Modᵉ kᵉ) = is-equiv-succ-ℤ-Modᵉ kᵉ

pred-ℤ-Modᵉ : (kᵉ : ℕᵉ) → ℤ-Modᵉ kᵉ → ℤ-Modᵉ kᵉ
pred-ℤ-Modᵉ zero-ℕᵉ = pred-ℤᵉ
pred-ℤ-Modᵉ (succ-ℕᵉ kᵉ) = pred-Finᵉ (succ-ℕᵉ kᵉ)

is-section-pred-ℤ-Modᵉ :
  (kᵉ : ℕᵉ) (xᵉ : ℤ-Modᵉ kᵉ) → succ-ℤ-Modᵉ kᵉ (pred-ℤ-Modᵉ kᵉ xᵉ) ＝ᵉ xᵉ
is-section-pred-ℤ-Modᵉ zero-ℕᵉ = is-section-pred-ℤᵉ
is-section-pred-ℤ-Modᵉ (succ-ℕᵉ kᵉ) = is-section-pred-Finᵉ (succ-ℕᵉ kᵉ)

is-retraction-pred-ℤ-Modᵉ :
  (kᵉ : ℕᵉ) (xᵉ : ℤ-Modᵉ kᵉ) → pred-ℤ-Modᵉ kᵉ (succ-ℤ-Modᵉ kᵉ xᵉ) ＝ᵉ xᵉ
is-retraction-pred-ℤ-Modᵉ zero-ℕᵉ = is-retraction-pred-ℤᵉ
is-retraction-pred-ℤ-Modᵉ (succ-ℕᵉ kᵉ) = is-retraction-pred-Finᵉ (succ-ℕᵉ kᵉ)

abstract
  is-equiv-pred-ℤ-Modᵉ : (kᵉ : ℕᵉ) → is-equivᵉ (pred-ℤ-Modᵉ kᵉ)
  is-equiv-pred-ℤ-Modᵉ zero-ℕᵉ = is-equiv-pred-ℤᵉ
  is-equiv-pred-ℤ-Modᵉ (succ-ℕᵉ kᵉ) = is-equiv-pred-Finᵉ (succ-ℕᵉ kᵉ)

equiv-pred-ℤ-Modᵉ : (kᵉ : ℕᵉ) → ℤ-Modᵉ kᵉ ≃ᵉ ℤ-Modᵉ kᵉ
pr1ᵉ (equiv-pred-ℤ-Modᵉ kᵉ) = pred-ℤ-Modᵉ kᵉ
pr2ᵉ (equiv-pred-ℤ-Modᵉ kᵉ) = is-equiv-pred-ℤ-Modᵉ kᵉ
```

## Addition on the integers modulo k

```agda
add-ℤ-Modᵉ : (kᵉ : ℕᵉ) → ℤ-Modᵉ kᵉ → ℤ-Modᵉ kᵉ → ℤ-Modᵉ kᵉ
add-ℤ-Modᵉ zero-ℕᵉ = add-ℤᵉ
add-ℤ-Modᵉ (succ-ℕᵉ kᵉ) = add-Finᵉ (succ-ℕᵉ kᵉ)

add-ℤ-Mod'ᵉ : (kᵉ : ℕᵉ) → ℤ-Modᵉ kᵉ → ℤ-Modᵉ kᵉ → ℤ-Modᵉ kᵉ
add-ℤ-Mod'ᵉ kᵉ xᵉ yᵉ = add-ℤ-Modᵉ kᵉ yᵉ xᵉ

ap-add-ℤ-Modᵉ :
  (kᵉ : ℕᵉ) {xᵉ x'ᵉ yᵉ y'ᵉ : ℤ-Modᵉ kᵉ} →
  xᵉ ＝ᵉ x'ᵉ → yᵉ ＝ᵉ y'ᵉ → add-ℤ-Modᵉ kᵉ xᵉ yᵉ ＝ᵉ add-ℤ-Modᵉ kᵉ x'ᵉ y'ᵉ
ap-add-ℤ-Modᵉ kᵉ pᵉ qᵉ = ap-binaryᵉ (add-ℤ-Modᵉ kᵉ) pᵉ qᵉ

abstract
  is-equiv-left-add-ℤ-Modᵉ : (kᵉ : ℕᵉ) (xᵉ : ℤ-Modᵉ kᵉ) → is-equivᵉ (add-ℤ-Modᵉ kᵉ xᵉ)
  is-equiv-left-add-ℤ-Modᵉ zero-ℕᵉ = is-equiv-left-add-ℤᵉ
  is-equiv-left-add-ℤ-Modᵉ (succ-ℕᵉ kᵉ) = is-equiv-add-Finᵉ (succ-ℕᵉ kᵉ)

equiv-left-add-ℤ-Modᵉ : (kᵉ : ℕᵉ) (xᵉ : ℤ-Modᵉ kᵉ) → ℤ-Modᵉ kᵉ ≃ᵉ ℤ-Modᵉ kᵉ
pr1ᵉ (equiv-left-add-ℤ-Modᵉ kᵉ xᵉ) = add-ℤ-Modᵉ kᵉ xᵉ
pr2ᵉ (equiv-left-add-ℤ-Modᵉ kᵉ xᵉ) = is-equiv-left-add-ℤ-Modᵉ kᵉ xᵉ

abstract
  is-equiv-add-ℤ-Mod'ᵉ : (kᵉ : ℕᵉ) (xᵉ : ℤ-Modᵉ kᵉ) → is-equivᵉ (add-ℤ-Mod'ᵉ kᵉ xᵉ)
  is-equiv-add-ℤ-Mod'ᵉ zero-ℕᵉ = is-equiv-right-add-ℤᵉ
  is-equiv-add-ℤ-Mod'ᵉ (succ-ℕᵉ kᵉ) = is-equiv-add-Fin'ᵉ (succ-ℕᵉ kᵉ)

equiv-add-ℤ-Mod'ᵉ : (kᵉ : ℕᵉ) (xᵉ : ℤ-Modᵉ kᵉ) → ℤ-Modᵉ kᵉ ≃ᵉ ℤ-Modᵉ kᵉ
pr1ᵉ (equiv-add-ℤ-Mod'ᵉ kᵉ xᵉ) = add-ℤ-Mod'ᵉ kᵉ xᵉ
pr2ᵉ (equiv-add-ℤ-Mod'ᵉ kᵉ xᵉ) = is-equiv-add-ℤ-Mod'ᵉ kᵉ xᵉ

is-injective-add-ℤ-Modᵉ : (kᵉ : ℕᵉ) (xᵉ : ℤ-Modᵉ kᵉ) → is-injectiveᵉ (add-ℤ-Modᵉ kᵉ xᵉ)
is-injective-add-ℤ-Modᵉ zero-ℕᵉ = is-injective-left-add-ℤᵉ
is-injective-add-ℤ-Modᵉ (succ-ℕᵉ kᵉ) = is-injective-add-Finᵉ (succ-ℕᵉ kᵉ)

is-injective-add-ℤ-Mod'ᵉ : (kᵉ : ℕᵉ) (xᵉ : ℤ-Modᵉ kᵉ) → is-injectiveᵉ (add-ℤ-Mod'ᵉ kᵉ xᵉ)
is-injective-add-ℤ-Mod'ᵉ zero-ℕᵉ = is-injective-right-add-ℤᵉ
is-injective-add-ℤ-Mod'ᵉ (succ-ℕᵉ kᵉ) = is-injective-add-Fin'ᵉ (succ-ℕᵉ kᵉ)
```

## The negative of an integer modulo k

```agda
neg-ℤ-Modᵉ : (kᵉ : ℕᵉ) → ℤ-Modᵉ kᵉ → ℤ-Modᵉ kᵉ
neg-ℤ-Modᵉ zero-ℕᵉ = neg-ℤᵉ
neg-ℤ-Modᵉ (succ-ℕᵉ kᵉ) = neg-Finᵉ (succ-ℕᵉ kᵉ)

abstract
  is-equiv-neg-ℤ-Modᵉ : (kᵉ : ℕᵉ) → is-equivᵉ (neg-ℤ-Modᵉ kᵉ)
  is-equiv-neg-ℤ-Modᵉ zero-ℕᵉ = is-equiv-neg-ℤᵉ
  is-equiv-neg-ℤ-Modᵉ (succ-ℕᵉ kᵉ) = is-equiv-neg-Finᵉ (succ-ℕᵉ kᵉ)

equiv-neg-ℤ-Modᵉ : (kᵉ : ℕᵉ) → ℤ-Modᵉ kᵉ ≃ᵉ ℤ-Modᵉ kᵉ
pr1ᵉ (equiv-neg-ℤ-Modᵉ kᵉ) = neg-ℤ-Modᵉ kᵉ
pr2ᵉ (equiv-neg-ℤ-Modᵉ kᵉ) = is-equiv-neg-ℤ-Modᵉ kᵉ
```

## Laws of addition modulo `k`

```agda
associative-add-ℤ-Modᵉ :
  (kᵉ : ℕᵉ) (xᵉ yᵉ zᵉ : ℤ-Modᵉ kᵉ) →
  add-ℤ-Modᵉ kᵉ (add-ℤ-Modᵉ kᵉ xᵉ yᵉ) zᵉ ＝ᵉ add-ℤ-Modᵉ kᵉ xᵉ (add-ℤ-Modᵉ kᵉ yᵉ zᵉ)
associative-add-ℤ-Modᵉ zero-ℕᵉ = associative-add-ℤᵉ
associative-add-ℤ-Modᵉ (succ-ℕᵉ kᵉ) = associative-add-Finᵉ (succ-ℕᵉ kᵉ)

commutative-add-ℤ-Modᵉ :
  (kᵉ : ℕᵉ) (xᵉ yᵉ : ℤ-Modᵉ kᵉ) → add-ℤ-Modᵉ kᵉ xᵉ yᵉ ＝ᵉ add-ℤ-Modᵉ kᵉ yᵉ xᵉ
commutative-add-ℤ-Modᵉ zero-ℕᵉ = commutative-add-ℤᵉ
commutative-add-ℤ-Modᵉ (succ-ℕᵉ kᵉ) = commutative-add-Finᵉ (succ-ℕᵉ kᵉ)

left-unit-law-add-ℤ-Modᵉ :
  (kᵉ : ℕᵉ) (xᵉ : ℤ-Modᵉ kᵉ) → add-ℤ-Modᵉ kᵉ (zero-ℤ-Modᵉ kᵉ) xᵉ ＝ᵉ xᵉ
left-unit-law-add-ℤ-Modᵉ zero-ℕᵉ = left-unit-law-add-ℤᵉ
left-unit-law-add-ℤ-Modᵉ (succ-ℕᵉ kᵉ) = left-unit-law-add-Finᵉ kᵉ

right-unit-law-add-ℤ-Modᵉ :
  (kᵉ : ℕᵉ) (xᵉ : ℤ-Modᵉ kᵉ) → add-ℤ-Modᵉ kᵉ xᵉ (zero-ℤ-Modᵉ kᵉ) ＝ᵉ xᵉ
right-unit-law-add-ℤ-Modᵉ zero-ℕᵉ = right-unit-law-add-ℤᵉ
right-unit-law-add-ℤ-Modᵉ (succ-ℕᵉ kᵉ) = right-unit-law-add-Finᵉ kᵉ

left-inverse-law-add-ℤ-Modᵉ :
  (kᵉ : ℕᵉ) (xᵉ : ℤ-Modᵉ kᵉ) → add-ℤ-Modᵉ kᵉ (neg-ℤ-Modᵉ kᵉ xᵉ) xᵉ ＝ᵉ zero-ℤ-Modᵉ kᵉ
left-inverse-law-add-ℤ-Modᵉ zero-ℕᵉ = left-inverse-law-add-ℤᵉ
left-inverse-law-add-ℤ-Modᵉ (succ-ℕᵉ kᵉ) = left-inverse-law-add-Finᵉ kᵉ

right-inverse-law-add-ℤ-Modᵉ :
  (kᵉ : ℕᵉ) (xᵉ : ℤ-Modᵉ kᵉ) → add-ℤ-Modᵉ kᵉ xᵉ (neg-ℤ-Modᵉ kᵉ xᵉ) ＝ᵉ zero-ℤ-Modᵉ kᵉ
right-inverse-law-add-ℤ-Modᵉ zero-ℕᵉ = right-inverse-law-add-ℤᵉ
right-inverse-law-add-ℤ-Modᵉ (succ-ℕᵉ kᵉ) = right-inverse-law-add-Finᵉ kᵉ

left-successor-law-add-ℤ-Modᵉ :
  (kᵉ : ℕᵉ) (xᵉ yᵉ : ℤ-Modᵉ kᵉ) →
  add-ℤ-Modᵉ kᵉ (succ-ℤ-Modᵉ kᵉ xᵉ) yᵉ ＝ᵉ succ-ℤ-Modᵉ kᵉ (add-ℤ-Modᵉ kᵉ xᵉ yᵉ)
left-successor-law-add-ℤ-Modᵉ zero-ℕᵉ = left-successor-law-add-ℤᵉ
left-successor-law-add-ℤ-Modᵉ (succ-ℕᵉ kᵉ) = left-successor-law-add-Finᵉ (succ-ℕᵉ kᵉ)

right-successor-law-add-ℤ-Modᵉ :
  (kᵉ : ℕᵉ) (xᵉ yᵉ : ℤ-Modᵉ kᵉ) →
  add-ℤ-Modᵉ kᵉ xᵉ (succ-ℤ-Modᵉ kᵉ yᵉ) ＝ᵉ succ-ℤ-Modᵉ kᵉ (add-ℤ-Modᵉ kᵉ xᵉ yᵉ)
right-successor-law-add-ℤ-Modᵉ zero-ℕᵉ = right-successor-law-add-ℤᵉ
right-successor-law-add-ℤ-Modᵉ (succ-ℕᵉ kᵉ) =
  right-successor-law-add-Finᵉ (succ-ℕᵉ kᵉ)

left-predecessor-law-add-ℤ-Modᵉ :
  (kᵉ : ℕᵉ) (xᵉ yᵉ : ℤ-Modᵉ kᵉ) →
  add-ℤ-Modᵉ kᵉ (pred-ℤ-Modᵉ kᵉ xᵉ) yᵉ ＝ᵉ pred-ℤ-Modᵉ kᵉ (add-ℤ-Modᵉ kᵉ xᵉ yᵉ)
left-predecessor-law-add-ℤ-Modᵉ zero-ℕᵉ = left-predecessor-law-add-ℤᵉ
left-predecessor-law-add-ℤ-Modᵉ (succ-ℕᵉ kᵉ) =
  left-predecessor-law-add-Finᵉ (succ-ℕᵉ kᵉ)

right-predecessor-law-add-ℤ-Modᵉ :
  (kᵉ : ℕᵉ) (xᵉ yᵉ : ℤ-Modᵉ kᵉ) →
  add-ℤ-Modᵉ kᵉ xᵉ (pred-ℤ-Modᵉ kᵉ yᵉ) ＝ᵉ pred-ℤ-Modᵉ kᵉ (add-ℤ-Modᵉ kᵉ xᵉ yᵉ)
right-predecessor-law-add-ℤ-Modᵉ zero-ℕᵉ = right-predecessor-law-add-ℤᵉ
right-predecessor-law-add-ℤ-Modᵉ (succ-ℕᵉ kᵉ) =
  right-predecessor-law-add-Finᵉ (succ-ℕᵉ kᵉ)

is-left-add-one-succ-ℤ-Modᵉ :
  (kᵉ : ℕᵉ) (xᵉ : ℤ-Modᵉ kᵉ) → succ-ℤ-Modᵉ kᵉ xᵉ ＝ᵉ add-ℤ-Modᵉ kᵉ (one-ℤ-Modᵉ kᵉ) xᵉ
is-left-add-one-succ-ℤ-Modᵉ zero-ℕᵉ = is-left-add-one-succ-ℤᵉ
is-left-add-one-succ-ℤ-Modᵉ (succ-ℕᵉ kᵉ) = is-add-one-succ-Finᵉ kᵉ

is-left-add-one-succ-ℤ-Mod'ᵉ :
  (kᵉ : ℕᵉ) (xᵉ : ℤ-Modᵉ kᵉ) → succ-ℤ-Modᵉ kᵉ xᵉ ＝ᵉ add-ℤ-Modᵉ kᵉ xᵉ (one-ℤ-Modᵉ kᵉ)
is-left-add-one-succ-ℤ-Mod'ᵉ zero-ℕᵉ = is-right-add-one-succ-ℤᵉ
is-left-add-one-succ-ℤ-Mod'ᵉ (succ-ℕᵉ kᵉ) = is-add-one-succ-Fin'ᵉ kᵉ

is-left-add-neg-one-pred-ℤ-Modᵉ :
  (kᵉ : ℕᵉ) (xᵉ : ℤ-Modᵉ kᵉ) → pred-ℤ-Modᵉ kᵉ xᵉ ＝ᵉ add-ℤ-Modᵉ kᵉ (neg-one-ℤ-Modᵉ kᵉ) xᵉ
is-left-add-neg-one-pred-ℤ-Modᵉ zero-ℕᵉ = is-left-add-neg-one-pred-ℤᵉ
is-left-add-neg-one-pred-ℤ-Modᵉ (succ-ℕᵉ kᵉ) = is-add-neg-one-pred-Finᵉ kᵉ

is-left-add-neg-one-pred-ℤ-Mod'ᵉ :
  (kᵉ : ℕᵉ) (xᵉ : ℤ-Modᵉ kᵉ) → pred-ℤ-Modᵉ kᵉ xᵉ ＝ᵉ add-ℤ-Modᵉ kᵉ xᵉ (neg-one-ℤ-Modᵉ kᵉ)
is-left-add-neg-one-pred-ℤ-Mod'ᵉ zero-ℕᵉ = is-right-add-neg-one-pred-ℤᵉ
is-left-add-neg-one-pred-ℤ-Mod'ᵉ (succ-ℕᵉ kᵉ) = is-add-neg-one-pred-Fin'ᵉ kᵉ
```

## Multiplication modulo `k`

```agda
mul-ℤ-Modᵉ : (kᵉ : ℕᵉ) → ℤ-Modᵉ kᵉ → ℤ-Modᵉ kᵉ → ℤ-Modᵉ kᵉ
mul-ℤ-Modᵉ zero-ℕᵉ = mul-ℤᵉ
mul-ℤ-Modᵉ (succ-ℕᵉ kᵉ) = mul-Finᵉ (succ-ℕᵉ kᵉ)

mul-ℤ-Mod'ᵉ : (kᵉ : ℕᵉ) → ℤ-Modᵉ kᵉ → ℤ-Modᵉ kᵉ → ℤ-Modᵉ kᵉ
mul-ℤ-Mod'ᵉ kᵉ xᵉ yᵉ = mul-ℤ-Modᵉ kᵉ yᵉ xᵉ

ap-mul-ℤ-Modᵉ :
  (kᵉ : ℕᵉ) {xᵉ x'ᵉ yᵉ y'ᵉ : ℤ-Modᵉ kᵉ} →
  xᵉ ＝ᵉ x'ᵉ → yᵉ ＝ᵉ y'ᵉ → mul-ℤ-Modᵉ kᵉ xᵉ yᵉ ＝ᵉ mul-ℤ-Modᵉ kᵉ x'ᵉ y'ᵉ
ap-mul-ℤ-Modᵉ kᵉ pᵉ qᵉ = ap-binaryᵉ (mul-ℤ-Modᵉ kᵉ) pᵉ qᵉ
```

## Laws of multiplication modulo `k`

```agda
associative-mul-ℤ-Modᵉ :
  (kᵉ : ℕᵉ) (xᵉ yᵉ zᵉ : ℤ-Modᵉ kᵉ) →
  mul-ℤ-Modᵉ kᵉ (mul-ℤ-Modᵉ kᵉ xᵉ yᵉ) zᵉ ＝ᵉ mul-ℤ-Modᵉ kᵉ xᵉ (mul-ℤ-Modᵉ kᵉ yᵉ zᵉ)
associative-mul-ℤ-Modᵉ zero-ℕᵉ = associative-mul-ℤᵉ
associative-mul-ℤ-Modᵉ (succ-ℕᵉ kᵉ) = associative-mul-Finᵉ (succ-ℕᵉ kᵉ)

commutative-mul-ℤ-Modᵉ :
  (kᵉ : ℕᵉ) (xᵉ yᵉ : ℤ-Modᵉ kᵉ) → mul-ℤ-Modᵉ kᵉ xᵉ yᵉ ＝ᵉ mul-ℤ-Modᵉ kᵉ yᵉ xᵉ
commutative-mul-ℤ-Modᵉ zero-ℕᵉ = commutative-mul-ℤᵉ
commutative-mul-ℤ-Modᵉ (succ-ℕᵉ kᵉ) = commutative-mul-Finᵉ (succ-ℕᵉ kᵉ)

left-unit-law-mul-ℤ-Modᵉ :
  (kᵉ : ℕᵉ) (xᵉ : ℤ-Modᵉ kᵉ) → mul-ℤ-Modᵉ kᵉ (one-ℤ-Modᵉ kᵉ) xᵉ ＝ᵉ xᵉ
left-unit-law-mul-ℤ-Modᵉ zero-ℕᵉ = left-unit-law-mul-ℤᵉ
left-unit-law-mul-ℤ-Modᵉ (succ-ℕᵉ kᵉ) = left-unit-law-mul-Finᵉ kᵉ

right-unit-law-mul-ℤ-Modᵉ :
  (kᵉ : ℕᵉ) (xᵉ : ℤ-Modᵉ kᵉ) → mul-ℤ-Modᵉ kᵉ xᵉ (one-ℤ-Modᵉ kᵉ) ＝ᵉ xᵉ
right-unit-law-mul-ℤ-Modᵉ zero-ℕᵉ = right-unit-law-mul-ℤᵉ
right-unit-law-mul-ℤ-Modᵉ (succ-ℕᵉ kᵉ) = right-unit-law-mul-Finᵉ kᵉ

left-distributive-mul-add-ℤ-Modᵉ :
  (kᵉ : ℕᵉ) (xᵉ yᵉ zᵉ : ℤ-Modᵉ kᵉ) →
  ( mul-ℤ-Modᵉ kᵉ xᵉ (add-ℤ-Modᵉ kᵉ yᵉ zᵉ)) ＝ᵉ
  ( add-ℤ-Modᵉ kᵉ (mul-ℤ-Modᵉ kᵉ xᵉ yᵉ) (mul-ℤ-Modᵉ kᵉ xᵉ zᵉ))
left-distributive-mul-add-ℤ-Modᵉ zero-ℕᵉ = left-distributive-mul-add-ℤᵉ
left-distributive-mul-add-ℤ-Modᵉ (succ-ℕᵉ kᵉ) =
  left-distributive-mul-add-Finᵉ (succ-ℕᵉ kᵉ)

right-distributive-mul-add-ℤ-Modᵉ :
  (kᵉ : ℕᵉ) (xᵉ yᵉ zᵉ : ℤ-Modᵉ kᵉ) →
  ( mul-ℤ-Modᵉ kᵉ (add-ℤ-Modᵉ kᵉ xᵉ yᵉ) zᵉ) ＝ᵉ
  ( add-ℤ-Modᵉ kᵉ (mul-ℤ-Modᵉ kᵉ xᵉ zᵉ) (mul-ℤ-Modᵉ kᵉ yᵉ zᵉ))
right-distributive-mul-add-ℤ-Modᵉ zero-ℕᵉ = right-distributive-mul-add-ℤᵉ
right-distributive-mul-add-ℤ-Modᵉ (succ-ℕᵉ kᵉ) =
  right-distributive-mul-add-Finᵉ (succ-ℕᵉ kᵉ)

is-left-mul-neg-one-neg-ℤ-Modᵉ :
  (kᵉ : ℕᵉ) (xᵉ : ℤ-Modᵉ kᵉ) → neg-ℤ-Modᵉ kᵉ xᵉ ＝ᵉ mul-ℤ-Modᵉ kᵉ (neg-one-ℤ-Modᵉ kᵉ) xᵉ
is-left-mul-neg-one-neg-ℤ-Modᵉ zero-ℕᵉ = invᵉ ∘ᵉ left-neg-unit-law-mul-ℤᵉ
is-left-mul-neg-one-neg-ℤ-Modᵉ (succ-ℕᵉ kᵉ) = is-mul-neg-one-neg-Finᵉ kᵉ

is-left-mul-neg-one-neg-ℤ-Mod'ᵉ :
  (kᵉ : ℕᵉ) (xᵉ : ℤ-Modᵉ kᵉ) → neg-ℤ-Modᵉ kᵉ xᵉ ＝ᵉ mul-ℤ-Modᵉ kᵉ xᵉ (neg-one-ℤ-Modᵉ kᵉ)
is-left-mul-neg-one-neg-ℤ-Mod'ᵉ zero-ℕᵉ = invᵉ ∘ᵉ right-neg-unit-law-mul-ℤᵉ
is-left-mul-neg-one-neg-ℤ-Mod'ᵉ (succ-ℕᵉ kᵉ) = is-mul-neg-one-neg-Fin'ᵉ kᵉ
```

## Congruence classes of integers modulo `k`

```agda
mod-ℕᵉ : (kᵉ : ℕᵉ) → ℕᵉ → ℤ-Modᵉ kᵉ
mod-ℕᵉ zero-ℕᵉ xᵉ = int-ℕᵉ xᵉ
mod-ℕᵉ (succ-ℕᵉ kᵉ) xᵉ = mod-succ-ℕᵉ kᵉ xᵉ

mod-ℤᵉ : (kᵉ : ℕᵉ) → ℤᵉ → ℤ-Modᵉ kᵉ
mod-ℤᵉ zero-ℕᵉ xᵉ = xᵉ
mod-ℤᵉ (succ-ℕᵉ kᵉ) (inlᵉ xᵉ) = neg-Finᵉ (succ-ℕᵉ kᵉ) (mod-succ-ℕᵉ kᵉ (succ-ℕᵉ xᵉ))
mod-ℤᵉ (succ-ℕᵉ kᵉ) (inrᵉ (inlᵉ xᵉ)) = zero-Finᵉ kᵉ
mod-ℤᵉ (succ-ℕᵉ kᵉ) (inrᵉ (inrᵉ xᵉ)) = mod-succ-ℕᵉ kᵉ (succ-ℕᵉ xᵉ)

mod-int-ℕᵉ : (kᵉ xᵉ : ℕᵉ) → mod-ℤᵉ kᵉ (int-ℕᵉ xᵉ) ＝ᵉ mod-ℕᵉ kᵉ xᵉ
mod-int-ℕᵉ zero-ℕᵉ xᵉ = reflᵉ
mod-int-ℕᵉ (succ-ℕᵉ kᵉ) zero-ℕᵉ = reflᵉ
mod-int-ℕᵉ (succ-ℕᵉ kᵉ) (succ-ℕᵉ xᵉ) = reflᵉ
```

## Preservation laws of congruence classes

```agda
mod-zero-ℕᵉ : (kᵉ : ℕᵉ) → mod-ℕᵉ kᵉ zero-ℕᵉ ＝ᵉ zero-ℤ-Modᵉ kᵉ
mod-zero-ℕᵉ zero-ℕᵉ = reflᵉ
mod-zero-ℕᵉ (succ-ℕᵉ kᵉ) = reflᵉ

preserves-successor-mod-ℕᵉ :
  (kᵉ xᵉ : ℕᵉ) → mod-ℕᵉ kᵉ (succ-ℕᵉ xᵉ) ＝ᵉ succ-ℤ-Modᵉ kᵉ (mod-ℕᵉ kᵉ xᵉ)
preserves-successor-mod-ℕᵉ zero-ℕᵉ zero-ℕᵉ = reflᵉ
preserves-successor-mod-ℕᵉ zero-ℕᵉ (succ-ℕᵉ xᵉ) = reflᵉ
preserves-successor-mod-ℕᵉ (succ-ℕᵉ kᵉ) xᵉ = reflᵉ

mod-refl-ℕᵉ : (kᵉ : ℕᵉ) → mod-ℕᵉ kᵉ kᵉ ＝ᵉ zero-ℤ-Modᵉ kᵉ
mod-refl-ℕᵉ zero-ℕᵉ = reflᵉ
mod-refl-ℕᵉ (succ-ℕᵉ kᵉ) =
  is-zero-mod-succ-ℕᵉ kᵉ (succ-ℕᵉ kᵉ) (pairᵉ 1 (left-unit-law-mul-ℕᵉ (succ-ℕᵉ kᵉ)))

mod-zero-ℤᵉ : (kᵉ : ℕᵉ) → mod-ℤᵉ kᵉ zero-ℤᵉ ＝ᵉ zero-ℤ-Modᵉ kᵉ
mod-zero-ℤᵉ zero-ℕᵉ = reflᵉ
mod-zero-ℤᵉ (succ-ℕᵉ kᵉ) = reflᵉ

mod-one-ℤᵉ : (kᵉ : ℕᵉ) → mod-ℤᵉ kᵉ one-ℤᵉ ＝ᵉ one-ℤ-Modᵉ kᵉ
mod-one-ℤᵉ zero-ℕᵉ = reflᵉ
mod-one-ℤᵉ (succ-ℕᵉ kᵉ) = reflᵉ

mod-neg-one-ℤᵉ : (kᵉ : ℕᵉ) → mod-ℤᵉ kᵉ neg-one-ℤᵉ ＝ᵉ neg-one-ℤ-Modᵉ kᵉ
mod-neg-one-ℤᵉ zero-ℕᵉ = reflᵉ
mod-neg-one-ℤᵉ (succ-ℕᵉ kᵉ) =
  ( neg-succ-Finᵉ (succ-ℕᵉ kᵉ) (zero-Finᵉ kᵉ)) ∙ᵉ
  ( ( apᵉ (pred-Finᵉ (succ-ℕᵉ kᵉ)) (neg-zero-Finᵉ kᵉ)) ∙ᵉ
    ( ( is-add-neg-one-pred-Fin'ᵉ kᵉ (zero-Finᵉ kᵉ)) ∙ᵉ
      ( left-unit-law-add-Finᵉ kᵉ (neg-one-Finᵉ kᵉ))))

preserves-successor-mod-ℤᵉ :
  (kᵉ : ℕᵉ) (xᵉ : ℤᵉ) → mod-ℤᵉ kᵉ (succ-ℤᵉ xᵉ) ＝ᵉ succ-ℤ-Modᵉ kᵉ (mod-ℤᵉ kᵉ xᵉ)
preserves-successor-mod-ℤᵉ zero-ℕᵉ xᵉ = reflᵉ
preserves-successor-mod-ℤᵉ (succ-ℕᵉ kᵉ) (inlᵉ zero-ℕᵉ) =
  invᵉ (apᵉ (succ-Finᵉ (succ-ℕᵉ kᵉ)) (is-neg-one-neg-one-Finᵉ kᵉ))
preserves-successor-mod-ℤᵉ (succ-ℕᵉ kᵉ) (inlᵉ (succ-ℕᵉ xᵉ)) =
  ( apᵉ
    ( neg-Finᵉ (succ-ℕᵉ kᵉ))
    ( invᵉ
      ( is-retraction-pred-Finᵉ
        ( succ-ℕᵉ kᵉ)
        ( succ-Finᵉ (succ-ℕᵉ kᵉ) (mod-succ-ℕᵉ kᵉ xᵉ))))) ∙ᵉ
  ( neg-pred-Finᵉ
    ( succ-ℕᵉ kᵉ)
    ( succ-Finᵉ (succ-ℕᵉ kᵉ) (succ-Finᵉ (succ-ℕᵉ kᵉ) (mod-succ-ℕᵉ kᵉ xᵉ))))
preserves-successor-mod-ℤᵉ (succ-ℕᵉ kᵉ) (inrᵉ (inlᵉ starᵉ)) = reflᵉ
preserves-successor-mod-ℤᵉ (succ-ℕᵉ kᵉ) (inrᵉ (inrᵉ xᵉ)) = reflᵉ

preserves-predecessor-mod-ℤᵉ :
  (kᵉ : ℕᵉ) (xᵉ : ℤᵉ) → mod-ℤᵉ kᵉ (pred-ℤᵉ xᵉ) ＝ᵉ pred-ℤ-Modᵉ kᵉ (mod-ℤᵉ kᵉ xᵉ)
preserves-predecessor-mod-ℤᵉ zero-ℕᵉ xᵉ = reflᵉ
preserves-predecessor-mod-ℤᵉ (succ-ℕᵉ kᵉ) (inlᵉ xᵉ) =
  neg-succ-Finᵉ (succ-ℕᵉ kᵉ) (succ-Finᵉ (succ-ℕᵉ kᵉ) (mod-succ-ℕᵉ kᵉ xᵉ))
preserves-predecessor-mod-ℤᵉ (succ-ℕᵉ kᵉ) (inrᵉ (inlᵉ starᵉ)) =
  ( is-neg-one-neg-one-Finᵉ kᵉ) ∙ᵉ
  ( ( invᵉ (left-unit-law-add-Finᵉ kᵉ (neg-one-Finᵉ kᵉ))) ∙ᵉ
    ( invᵉ (is-add-neg-one-pred-Fin'ᵉ kᵉ (zero-Finᵉ kᵉ))))
preserves-predecessor-mod-ℤᵉ (succ-ℕᵉ kᵉ) (inrᵉ (inrᵉ zero-ℕᵉ)) =
  invᵉ
    ( ( apᵉ
        ( pred-Finᵉ (succ-ℕᵉ kᵉ))
        ( preserves-successor-mod-ℤᵉ (succ-ℕᵉ kᵉ) zero-ℤᵉ)) ∙ᵉ
      ( is-retraction-pred-Finᵉ (succ-ℕᵉ kᵉ) (zero-Finᵉ kᵉ)))
preserves-predecessor-mod-ℤᵉ (succ-ℕᵉ kᵉ) (inrᵉ (inrᵉ (succ-ℕᵉ xᵉ))) =
  invᵉ (is-retraction-pred-Finᵉ (succ-ℕᵉ kᵉ) (succ-Finᵉ (succ-ℕᵉ kᵉ) (mod-succ-ℕᵉ kᵉ xᵉ)))

preserves-add-mod-ℤᵉ :
  (kᵉ : ℕᵉ) (xᵉ yᵉ : ℤᵉ) →
  mod-ℤᵉ kᵉ (xᵉ +ℤᵉ yᵉ) ＝ᵉ add-ℤ-Modᵉ kᵉ (mod-ℤᵉ kᵉ xᵉ) (mod-ℤᵉ kᵉ yᵉ)
preserves-add-mod-ℤᵉ zero-ℕᵉ xᵉ yᵉ = reflᵉ
preserves-add-mod-ℤᵉ (succ-ℕᵉ kᵉ) (inlᵉ zero-ℕᵉ) yᵉ =
  ( preserves-predecessor-mod-ℤᵉ (succ-ℕᵉ kᵉ) yᵉ) ∙ᵉ
  ( ( is-add-neg-one-pred-Finᵉ kᵉ (mod-ℤᵉ (succ-ℕᵉ kᵉ) yᵉ)) ∙ᵉ
    ( apᵉ
      ( add-Fin'ᵉ (succ-ℕᵉ kᵉ) (mod-ℤᵉ (succ-ℕᵉ kᵉ) yᵉ))
      ( invᵉ (mod-neg-one-ℤᵉ (succ-ℕᵉ kᵉ)))))
preserves-add-mod-ℤᵉ (succ-ℕᵉ kᵉ) (inlᵉ (succ-ℕᵉ xᵉ)) yᵉ =
  ( preserves-predecessor-mod-ℤᵉ (succ-ℕᵉ kᵉ) ((inlᵉ xᵉ) +ℤᵉ yᵉ)) ∙ᵉ
  ( ( apᵉ (pred-Finᵉ (succ-ℕᵉ kᵉ)) (preserves-add-mod-ℤᵉ (succ-ℕᵉ kᵉ) (inlᵉ xᵉ) yᵉ)) ∙ᵉ
    ( ( invᵉ
        ( left-predecessor-law-add-Finᵉ (succ-ℕᵉ kᵉ)
          ( mod-ℤᵉ (succ-ℕᵉ kᵉ) (inlᵉ xᵉ))
          ( mod-ℤᵉ (succ-ℕᵉ kᵉ) yᵉ))) ∙ᵉ
      ( apᵉ
        ( add-Fin'ᵉ (succ-ℕᵉ kᵉ) (mod-ℤᵉ (succ-ℕᵉ kᵉ) yᵉ))
        ( invᵉ (preserves-predecessor-mod-ℤᵉ (succ-ℕᵉ kᵉ) (inlᵉ xᵉ))))))
preserves-add-mod-ℤᵉ (succ-ℕᵉ kᵉ) (inrᵉ (inlᵉ starᵉ)) yᵉ =
  invᵉ (left-unit-law-add-Finᵉ kᵉ (mod-ℤᵉ (succ-ℕᵉ kᵉ) yᵉ))
preserves-add-mod-ℤᵉ (succ-ℕᵉ kᵉ) (inrᵉ (inrᵉ zero-ℕᵉ)) yᵉ =
  ( preserves-successor-mod-ℤᵉ (succ-ℕᵉ kᵉ) yᵉ) ∙ᵉ
  ( ( apᵉ
      ( succ-Finᵉ (succ-ℕᵉ kᵉ))
      ( invᵉ (left-unit-law-add-Finᵉ kᵉ (mod-ℤᵉ (succ-ℕᵉ kᵉ) yᵉ)))) ∙ᵉ
    ( invᵉ
      ( left-successor-law-add-Finᵉ
        ( succ-ℕᵉ kᵉ)
        ( zero-Finᵉ kᵉ)
        ( mod-ℤᵉ (succ-ℕᵉ kᵉ) yᵉ))))
preserves-add-mod-ℤᵉ (succ-ℕᵉ kᵉ) (inrᵉ (inrᵉ (succ-ℕᵉ xᵉ))) yᵉ =
  ( preserves-successor-mod-ℤᵉ (succ-ℕᵉ kᵉ) ((inrᵉ (inrᵉ xᵉ)) +ℤᵉ yᵉ)) ∙ᵉ
  ( ( apᵉ
      ( succ-Finᵉ (succ-ℕᵉ kᵉ))
      ( preserves-add-mod-ℤᵉ (succ-ℕᵉ kᵉ) (inrᵉ (inrᵉ xᵉ)) yᵉ)) ∙ᵉ
    ( invᵉ
      ( left-successor-law-add-Finᵉ (succ-ℕᵉ kᵉ)
        ( mod-ℤᵉ (succ-ℕᵉ kᵉ) (inrᵉ (inrᵉ xᵉ)))
        ( mod-ℤᵉ (succ-ℕᵉ kᵉ) yᵉ))))

preserves-neg-mod-ℤᵉ :
  (kᵉ : ℕᵉ) (xᵉ : ℤᵉ) → mod-ℤᵉ kᵉ (neg-ℤᵉ xᵉ) ＝ᵉ neg-ℤ-Modᵉ kᵉ (mod-ℤᵉ kᵉ xᵉ)
preserves-neg-mod-ℤᵉ zero-ℕᵉ xᵉ = reflᵉ
preserves-neg-mod-ℤᵉ (succ-ℕᵉ kᵉ) xᵉ =
  is-injective-add-Finᵉ (succ-ℕᵉ kᵉ)
    ( mod-ℤᵉ (succ-ℕᵉ kᵉ) xᵉ)
    ( ( invᵉ (preserves-add-mod-ℤᵉ (succ-ℕᵉ kᵉ) xᵉ (neg-ℤᵉ xᵉ))) ∙ᵉ
      ( ( apᵉ (mod-ℤᵉ (succ-ℕᵉ kᵉ)) (right-inverse-law-add-ℤᵉ xᵉ)) ∙ᵉ
        ( invᵉ (right-inverse-law-add-ℤ-Modᵉ (succ-ℕᵉ kᵉ) (mod-ℤᵉ (succ-ℕᵉ kᵉ) xᵉ)))))

preserves-mul-mod-ℤᵉ :
  (kᵉ : ℕᵉ) (xᵉ yᵉ : ℤᵉ) →
  mod-ℤᵉ kᵉ (xᵉ *ℤᵉ yᵉ) ＝ᵉ mul-ℤ-Modᵉ kᵉ (mod-ℤᵉ kᵉ xᵉ) (mod-ℤᵉ kᵉ yᵉ)
preserves-mul-mod-ℤᵉ zero-ℕᵉ xᵉ yᵉ = reflᵉ
preserves-mul-mod-ℤᵉ (succ-ℕᵉ kᵉ) (inlᵉ zero-ℕᵉ) yᵉ =
  ( preserves-neg-mod-ℤᵉ (succ-ℕᵉ kᵉ) yᵉ) ∙ᵉ
  ( ( is-mul-neg-one-neg-Finᵉ kᵉ (mod-ℤᵉ (succ-ℕᵉ kᵉ) yᵉ)) ∙ᵉ
    ( apᵉ
      ( mul-ℤ-Mod'ᵉ (succ-ℕᵉ kᵉ) (mod-ℤᵉ (succ-ℕᵉ kᵉ) yᵉ))
      ( invᵉ (mod-neg-one-ℤᵉ (succ-ℕᵉ kᵉ)))))
preserves-mul-mod-ℤᵉ (succ-ℕᵉ kᵉ) (inlᵉ (succ-ℕᵉ xᵉ)) yᵉ =
  ( preserves-add-mod-ℤᵉ (succ-ℕᵉ kᵉ) (neg-ℤᵉ yᵉ) ((inlᵉ xᵉ) *ℤᵉ yᵉ)) ∙ᵉ
  ( ( ap-add-ℤ-Modᵉ
      ( succ-ℕᵉ kᵉ)
      ( preserves-neg-mod-ℤᵉ (succ-ℕᵉ kᵉ) yᵉ)
      ( preserves-mul-mod-ℤᵉ (succ-ℕᵉ kᵉ) (inlᵉ xᵉ) yᵉ)) ∙ᵉ
    ( ( invᵉ
        ( left-predecessor-law-mul-Finᵉ (succ-ℕᵉ kᵉ)
          ( mod-ℤᵉ (succ-ℕᵉ kᵉ) (inlᵉ xᵉ))
          ( mod-ℤᵉ (succ-ℕᵉ kᵉ) yᵉ))) ∙ᵉ
      ( apᵉ
        ( mul-Fin'ᵉ (succ-ℕᵉ kᵉ) (mod-ℤᵉ (succ-ℕᵉ kᵉ) yᵉ))
        ( invᵉ (preserves-predecessor-mod-ℤᵉ (succ-ℕᵉ kᵉ) (inlᵉ xᵉ))))))
preserves-mul-mod-ℤᵉ (succ-ℕᵉ kᵉ) (inrᵉ (inlᵉ starᵉ)) yᵉ =
  invᵉ (left-zero-law-mul-Finᵉ kᵉ (mod-ℤᵉ (succ-ℕᵉ kᵉ) yᵉ))
preserves-mul-mod-ℤᵉ (succ-ℕᵉ kᵉ) (inrᵉ (inrᵉ zero-ℕᵉ)) yᵉ =
  invᵉ (left-unit-law-mul-Finᵉ kᵉ (mod-ℤᵉ (succ-ℕᵉ kᵉ) yᵉ))
preserves-mul-mod-ℤᵉ (succ-ℕᵉ kᵉ) (inrᵉ (inrᵉ (succ-ℕᵉ xᵉ))) yᵉ =
  ( preserves-add-mod-ℤᵉ (succ-ℕᵉ kᵉ) yᵉ ((inrᵉ (inrᵉ xᵉ)) *ℤᵉ yᵉ)) ∙ᵉ
  ( ( apᵉ
      ( add-ℤ-Modᵉ (succ-ℕᵉ kᵉ) (mod-ℤᵉ (succ-ℕᵉ kᵉ) yᵉ))
      ( preserves-mul-mod-ℤᵉ (succ-ℕᵉ kᵉ) (inrᵉ (inrᵉ xᵉ)) yᵉ)) ∙ᵉ
    ( invᵉ
      ( left-successor-law-mul-Finᵉ (succ-ℕᵉ kᵉ)
        ( mod-ℤᵉ (succ-ℕᵉ kᵉ) (inrᵉ (inrᵉ xᵉ)))
        ( mod-ℤᵉ (succ-ℕᵉ kᵉ) yᵉ))))
```

```agda
cong-int-mod-ℕᵉ :
  (kᵉ xᵉ : ℕᵉ) → cong-ℤᵉ (int-ℕᵉ kᵉ) (int-ℤ-Modᵉ kᵉ (mod-ℕᵉ kᵉ xᵉ)) (int-ℕᵉ xᵉ)
cong-int-mod-ℕᵉ zero-ℕᵉ xᵉ = refl-cong-ℤᵉ zero-ℤᵉ (int-ℕᵉ xᵉ)
cong-int-mod-ℕᵉ (succ-ℕᵉ kᵉ) xᵉ =
  cong-int-cong-ℕᵉ
    ( succ-ℕᵉ kᵉ)
    ( nat-Finᵉ (succ-ℕᵉ kᵉ) (mod-succ-ℕᵉ kᵉ xᵉ))
    ( xᵉ)
    ( cong-nat-mod-succ-ℕᵉ kᵉ xᵉ)

cong-int-mod-ℤᵉ :
  (kᵉ : ℕᵉ) (xᵉ : ℤᵉ) → cong-ℤᵉ (int-ℕᵉ kᵉ) (int-ℤ-Modᵉ kᵉ (mod-ℤᵉ kᵉ xᵉ)) xᵉ
cong-int-mod-ℤᵉ zero-ℕᵉ xᵉ = refl-cong-ℤᵉ zero-ℤᵉ xᵉ
cong-int-mod-ℤᵉ (succ-ℕᵉ kᵉ) (inlᵉ xᵉ) =
  concatenate-eq-cong-ℤᵉ
    ( int-ℕᵉ (succ-ℕᵉ kᵉ))
    ( int-ℤ-Modᵉ (succ-ℕᵉ kᵉ) (mod-ℤᵉ (succ-ℕᵉ kᵉ) (inlᵉ xᵉ)))
    ( int-ℕᵉ
      ( nat-Finᵉ
        ( succ-ℕᵉ kᵉ)
        ( mul-Finᵉ (succ-ℕᵉ kᵉ) (neg-one-Finᵉ kᵉ) (mod-succ-ℕᵉ kᵉ (succ-ℕᵉ xᵉ)))))
    ( inlᵉ xᵉ)
    ( apᵉ
      ( int-ℤ-Modᵉ (succ-ℕᵉ kᵉ))
      ( preserves-mul-mod-ℤᵉ (succ-ℕᵉ kᵉ) neg-one-ℤᵉ (inrᵉ (inrᵉ xᵉ)) ∙ᵉ
        apᵉ
        ( mul-Fin'ᵉ
          ( succ-ℕᵉ kᵉ)
          ( mod-succ-ℕᵉ kᵉ (succ-ℕᵉ xᵉ)))
          ( mod-neg-one-ℤᵉ (succ-ℕᵉ kᵉ))))
    ( transitive-cong-ℤᵉ
      ( int-ℕᵉ (succ-ℕᵉ kᵉ))
      ( int-ℕᵉ
        ( nat-Finᵉ
          ( succ-ℕᵉ kᵉ)
          ( mul-Finᵉ (succ-ℕᵉ kᵉ) (neg-one-Finᵉ kᵉ) (mod-succ-ℕᵉ kᵉ (succ-ℕᵉ xᵉ)))))
      ( int-ℕᵉ (kᵉ *ℕᵉ (nat-Finᵉ (succ-ℕᵉ kᵉ) (mod-succ-ℕᵉ kᵉ (succ-ℕᵉ xᵉ)))))
      ( inlᵉ xᵉ)
      ( transitive-cong-ℤᵉ
        ( int-ℕᵉ (succ-ℕᵉ kᵉ))
        ( int-ℕᵉ (kᵉ *ℕᵉ (nat-Finᵉ (succ-ℕᵉ kᵉ) (mod-succ-ℕᵉ kᵉ (succ-ℕᵉ xᵉ)))))
        ( int-ℕᵉ (kᵉ *ℕᵉ (succ-ℕᵉ xᵉ)))
        ( inlᵉ xᵉ)
        ( pairᵉ
          ( inrᵉ (inrᵉ xᵉ))
          ( ( commutative-mul-ℤᵉ (inrᵉ (inrᵉ xᵉ)) (inrᵉ (inrᵉ kᵉ))) ∙ᵉ
            ( ( apᵉ
                ( _*ℤᵉ (inrᵉ (inrᵉ xᵉ)))
                ( invᵉ (succ-int-ℕᵉ kᵉ) ∙ᵉ commutative-add-ℤᵉ one-ℤᵉ (int-ℕᵉ kᵉ))) ∙ᵉ
              ( ( right-distributive-mul-add-ℤᵉ (int-ℕᵉ kᵉ) one-ℤᵉ (inrᵉ (inrᵉ xᵉ))) ∙ᵉ
                ( ap-add-ℤᵉ
                  ( mul-int-ℕᵉ kᵉ (succ-ℕᵉ xᵉ))
                  ( left-unit-law-mul-ℤᵉ (inrᵉ (inrᵉ xᵉ))))))))
        ( cong-int-cong-ℕᵉ
          ( succ-ℕᵉ kᵉ)
          ( kᵉ *ℕᵉ (nat-Finᵉ (succ-ℕᵉ kᵉ) (mod-succ-ℕᵉ kᵉ (succ-ℕᵉ xᵉ))))
          ( kᵉ *ℕᵉ (succ-ℕᵉ xᵉ))
          ( congruence-mul-ℕᵉ
            ( succ-ℕᵉ kᵉ)
            { kᵉ}
            { nat-Finᵉ (succ-ℕᵉ kᵉ) (mod-succ-ℕᵉ kᵉ (succ-ℕᵉ xᵉ))}
            { kᵉ}
            { succ-ℕᵉ xᵉ}
            ( refl-cong-ℕᵉ (succ-ℕᵉ kᵉ) kᵉ)
            ( cong-nat-mod-succ-ℕᵉ kᵉ (succ-ℕᵉ xᵉ)))))
      ( cong-int-cong-ℕᵉ
        ( succ-ℕᵉ kᵉ)
        ( nat-Finᵉ
          ( succ-ℕᵉ kᵉ)
          ( mul-Finᵉ (succ-ℕᵉ kᵉ) (neg-one-Finᵉ kᵉ) (mod-succ-ℕᵉ kᵉ (succ-ℕᵉ xᵉ))))
        ( kᵉ *ℕᵉ (nat-Finᵉ (succ-ℕᵉ kᵉ) (mod-succ-ℕᵉ kᵉ (succ-ℕᵉ xᵉ))))
        ( cong-mul-Finᵉ (neg-one-Finᵉ kᵉ) (mod-succ-ℕᵉ kᵉ (succ-ℕᵉ xᵉ)))))
cong-int-mod-ℤᵉ (succ-ℕᵉ kᵉ) (inrᵉ (inlᵉ starᵉ)) =
  cong-int-cong-ℕᵉ
    ( succ-ℕᵉ kᵉ)
    ( nat-Finᵉ (succ-ℕᵉ kᵉ) (mod-succ-ℕᵉ kᵉ zero-ℕᵉ))
    ( zero-ℕᵉ)
    ( cong-nat-mod-succ-ℕᵉ kᵉ zero-ℕᵉ)
cong-int-mod-ℤᵉ (succ-ℕᵉ kᵉ) (inrᵉ (inrᵉ xᵉ)) =
  cong-int-cong-ℕᵉ
    ( succ-ℕᵉ kᵉ)
    ( nat-Finᵉ (succ-ℕᵉ kᵉ) (mod-succ-ℕᵉ kᵉ (succ-ℕᵉ xᵉ)))
    ( succ-ℕᵉ xᵉ)
    ( cong-nat-mod-succ-ℕᵉ kᵉ (succ-ℕᵉ xᵉ))

cong-eq-mod-ℤᵉ :
  (kᵉ : ℕᵉ) (xᵉ yᵉ : ℤᵉ) → mod-ℤᵉ kᵉ xᵉ ＝ᵉ mod-ℤᵉ kᵉ yᵉ → cong-ℤᵉ (int-ℕᵉ kᵉ) xᵉ yᵉ
cong-eq-mod-ℤᵉ kᵉ xᵉ yᵉ pᵉ =
  concatenate-cong-eq-cong-ℤᵉ
    ( int-ℕᵉ kᵉ)
    ( xᵉ)
    ( int-ℤ-Modᵉ kᵉ (mod-ℤᵉ kᵉ xᵉ))
    ( int-ℤ-Modᵉ kᵉ (mod-ℤᵉ kᵉ yᵉ))
    ( yᵉ)
    ( symmetric-cong-ℤᵉ
      (int-ℕᵉ kᵉ)
      (int-ℤ-Modᵉ kᵉ (mod-ℤᵉ kᵉ xᵉ))
      ( xᵉ)
      ( cong-int-mod-ℤᵉ kᵉ xᵉ))
    ( apᵉ (int-ℤ-Modᵉ kᵉ) pᵉ)
    ( cong-int-mod-ℤᵉ kᵉ yᵉ)

eq-cong-int-ℤ-Modᵉ :
  (kᵉ : ℕᵉ) (xᵉ yᵉ : ℤ-Modᵉ kᵉ) →
  cong-ℤᵉ (int-ℕᵉ kᵉ) (int-ℤ-Modᵉ kᵉ xᵉ) (int-ℤ-Modᵉ kᵉ yᵉ) → xᵉ ＝ᵉ yᵉ
eq-cong-int-ℤ-Modᵉ zero-ℕᵉ = is-discrete-cong-ℤᵉ zero-ℤᵉ reflᵉ
eq-cong-int-ℤ-Modᵉ (succ-ℕᵉ kᵉ) xᵉ yᵉ Hᵉ =
  eq-cong-nat-Finᵉ (succ-ℕᵉ kᵉ) xᵉ yᵉ
    ( cong-cong-int-ℕᵉ
      ( succ-ℕᵉ kᵉ)
      ( nat-Finᵉ (succ-ℕᵉ kᵉ) xᵉ)
      ( nat-Finᵉ (succ-ℕᵉ kᵉ) yᵉ)
      ( Hᵉ))

eq-mod-cong-ℤᵉ :
  (kᵉ : ℕᵉ) (xᵉ yᵉ : ℤᵉ) → cong-ℤᵉ (int-ℕᵉ kᵉ) xᵉ yᵉ → mod-ℤᵉ kᵉ xᵉ ＝ᵉ mod-ℤᵉ kᵉ yᵉ
eq-mod-cong-ℤᵉ kᵉ xᵉ yᵉ Hᵉ =
  eq-cong-int-ℤ-Modᵉ kᵉ
    ( mod-ℤᵉ kᵉ xᵉ)
    ( mod-ℤᵉ kᵉ yᵉ)
    ( concatenate-cong-cong-cong-ℤᵉ
      ( int-ℕᵉ kᵉ)
      ( int-ℤ-Modᵉ kᵉ (mod-ℤᵉ kᵉ xᵉ))
      ( xᵉ)
      ( yᵉ)
      ( int-ℤ-Modᵉ kᵉ (mod-ℤᵉ kᵉ yᵉ))
      ( cong-int-mod-ℤᵉ kᵉ xᵉ)
      ( Hᵉ)
      ( symmetric-cong-ℤᵉ
        ( int-ℕᵉ kᵉ)
        ( int-ℤ-Modᵉ kᵉ (mod-ℤᵉ kᵉ yᵉ))
        ( yᵉ)
        ( cong-int-mod-ℤᵉ kᵉ yᵉ)))

is-zero-mod-div-ℤᵉ :
  (kᵉ : ℕᵉ) (xᵉ : ℤᵉ) → div-ℤᵉ (int-ℕᵉ kᵉ) xᵉ → is-zero-ℤ-Modᵉ kᵉ (mod-ℤᵉ kᵉ xᵉ)
is-zero-mod-div-ℤᵉ zero-ℕᵉ xᵉ dᵉ = is-zero-div-zero-ℤᵉ xᵉ dᵉ
is-zero-mod-div-ℤᵉ (succ-ℕᵉ kᵉ) xᵉ Hᵉ =
  eq-mod-cong-ℤᵉ
    ( succ-ℕᵉ kᵉ)
    ( xᵉ)
    ( zero-ℤᵉ)
    ( is-cong-zero-div-ℤᵉ (int-ℕᵉ (succ-ℕᵉ kᵉ)) xᵉ Hᵉ)

div-is-zero-mod-ℤᵉ :
  (kᵉ : ℕᵉ) (xᵉ : ℤᵉ) → is-zero-ℤ-Modᵉ kᵉ (mod-ℤᵉ kᵉ xᵉ) → div-ℤᵉ (int-ℕᵉ kᵉ) xᵉ
div-is-zero-mod-ℤᵉ zero-ℕᵉ .zero-ℤᵉ reflᵉ = refl-div-ℤᵉ zero-ℤᵉ
div-is-zero-mod-ℤᵉ (succ-ℕᵉ kᵉ) xᵉ pᵉ =
  div-is-cong-zero-ℤᵉ
    ( int-ℕᵉ (succ-ℕᵉ kᵉ))
    ( xᵉ)
    ( cong-eq-mod-ℤᵉ (succ-ℕᵉ kᵉ) xᵉ zero-ℤᵉ pᵉ)

is-section-int-ℤ-Modᵉ : (kᵉ : ℕᵉ) (xᵉ : ℤ-Modᵉ kᵉ) → mod-ℤᵉ kᵉ (int-ℤ-Modᵉ kᵉ xᵉ) ＝ᵉ xᵉ
is-section-int-ℤ-Modᵉ kᵉ xᵉ =
  eq-cong-int-ℤ-Modᵉ kᵉ
    ( mod-ℤᵉ kᵉ (int-ℤ-Modᵉ kᵉ xᵉ))
    ( xᵉ)
    ( cong-int-mod-ℤᵉ kᵉ (int-ℤ-Modᵉ kᵉ xᵉ))

is-one-is-fixed-point-succ-ℤ-Modᵉ :
  (kᵉ : ℕᵉ) (xᵉ : ℤ-Modᵉ kᵉ) → succ-ℤ-Modᵉ kᵉ xᵉ ＝ᵉ xᵉ → is-one-ℕᵉ kᵉ
is-one-is-fixed-point-succ-ℤ-Modᵉ kᵉ xᵉ pᵉ =
  is-one-is-unit-int-ℕᵉ kᵉ
    ( is-unit-cong-succ-ℤᵉ
      ( int-ℕᵉ kᵉ)
      ( int-ℤ-Modᵉ kᵉ xᵉ)
      ( cong-eq-mod-ℤᵉ kᵉ
        ( int-ℤ-Modᵉ kᵉ xᵉ)
        ( succ-ℤᵉ (int-ℤ-Modᵉ kᵉ xᵉ))
        ( ( is-section-int-ℤ-Modᵉ kᵉ xᵉ) ∙ᵉ
          ( ( invᵉ pᵉ) ∙ᵉ
            ( invᵉ
              ( ( preserves-successor-mod-ℤᵉ kᵉ (int-ℤ-Modᵉ kᵉ xᵉ)) ∙ᵉ
                ( apᵉ (succ-ℤ-Modᵉ kᵉ) (is-section-int-ℤ-Modᵉ kᵉ xᵉ))))))))

has-no-fixed-points-succ-ℤ-Modᵉ :
  (kᵉ : ℕᵉ) (xᵉ : ℤ-Modᵉ kᵉ) → is-not-one-ℕᵉ kᵉ → succ-ℤ-Modᵉ kᵉ xᵉ ≠ᵉ xᵉ
has-no-fixed-points-succ-ℤ-Modᵉ kᵉ xᵉ =
  map-negᵉ (is-one-is-fixed-point-succ-ℤ-Modᵉ kᵉ xᵉ)

has-no-fixed-points-succ-Finᵉ :
  {kᵉ : ℕᵉ} (xᵉ : Finᵉ kᵉ) → is-not-one-ℕᵉ kᵉ → succ-Finᵉ kᵉ xᵉ ≠ᵉ xᵉ
has-no-fixed-points-succ-Finᵉ {succ-ℕᵉ kᵉ} xᵉ =
  has-no-fixed-points-succ-ℤ-Modᵉ (succ-ℕᵉ kᵉ) xᵉ
```

### Divisibility is decidable

```agda
is-decidable-div-ℤᵉ : (dᵉ xᵉ : ℤᵉ) → is-decidableᵉ (div-ℤᵉ dᵉ xᵉ)
is-decidable-div-ℤᵉ dᵉ xᵉ =
  is-decidable-iffᵉ
    ( div-div-int-abs-ℤᵉ ∘ᵉ div-is-zero-mod-ℤᵉ (abs-ℤᵉ dᵉ) xᵉ)
    ( is-zero-mod-div-ℤᵉ (abs-ℤᵉ dᵉ) xᵉ ∘ᵉ div-int-abs-div-ℤᵉ)
    ( has-decidable-equality-ℤ-Modᵉ
      ( abs-ℤᵉ dᵉ)
      ( mod-ℤᵉ (abs-ℤᵉ dᵉ) xᵉ)
      ( zero-ℤ-Modᵉ (abs-ℤᵉ dᵉ)))
```

### `mod-ℤ` is surjective

```agda
is-surjective-succ-Fin-comp-mod-succ-ℕᵉ :
  (nᵉ : ℕᵉ) → is-surjectiveᵉ (succ-Finᵉ (succ-ℕᵉ nᵉ) ∘ᵉ mod-succ-ℕᵉ nᵉ)
is-surjective-succ-Fin-comp-mod-succ-ℕᵉ nᵉ =
  is-surjective-compᵉ
    ( is-surjective-is-equivᵉ (is-equiv-succ-Finᵉ (succ-ℕᵉ nᵉ)))
    ( is-surjective-mod-succ-ℕᵉ nᵉ)

is-surjective-mod-ℤᵉ : (nᵉ : ℕᵉ) → is-surjectiveᵉ (mod-ℤᵉ nᵉ)
is-surjective-mod-ℤᵉ zero-ℕᵉ = is-surjective-idᵉ
is-surjective-mod-ℤᵉ (succ-ℕᵉ nᵉ) =
  is-surjective-left-factorᵉ
    ( inrᵉ ∘ᵉ inrᵉ)
    ( is-surjective-htpyᵉ
      ( λ xᵉ → reflᵉ)
      ( is-surjective-succ-Fin-comp-mod-succ-ℕᵉ nᵉ))
```