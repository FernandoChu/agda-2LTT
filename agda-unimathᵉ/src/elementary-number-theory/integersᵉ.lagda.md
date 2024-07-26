# The integers

```agda
module elementary-number-theory.integersᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.equality-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.coproduct-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.embeddingsᵉ
open import foundation.empty-typesᵉ
open import foundation.equality-coproduct-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.injective-mapsᵉ
open import foundation.negated-equalityᵉ
open import foundation.negationᵉ
open import foundation.propositionsᵉ
open import foundation.retractionsᵉ
open import foundation.sectionsᵉ
open import foundation.setsᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import structured-types.types-equipped-with-endomorphismsᵉ
```

</details>

## Idea

Theᵉ typeᵉ ofᵉ integersᵉ isᵉ anᵉ extensionᵉ ofᵉ theᵉ typeᵉ ofᵉ naturalᵉ numbersᵉ includingᵉ
negativeᵉ wholeᵉ numbers.ᵉ

## Definitions

### The type of integers

```agda
ℤᵉ : UUᵉ lzero
ℤᵉ = ℕᵉ +ᵉ (unitᵉ +ᵉ ℕᵉ)


```

### Inclusion of the negative integers

```agda
in-neg-ℤᵉ : ℕᵉ → ℤᵉ
in-neg-ℤᵉ nᵉ = inlᵉ nᵉ

neg-one-ℤᵉ : ℤᵉ
neg-one-ℤᵉ = in-neg-ℤᵉ zero-ℕᵉ

is-neg-one-ℤᵉ : ℤᵉ → UUᵉ lzero
is-neg-one-ℤᵉ xᵉ = (xᵉ ＝ᵉ neg-one-ℤᵉ)
```

### Zero

```agda
zero-ℤᵉ : ℤᵉ
zero-ℤᵉ = inrᵉ (inlᵉ starᵉ)

is-zero-ℤᵉ : ℤᵉ → UUᵉ lzero
is-zero-ℤᵉ xᵉ = (xᵉ ＝ᵉ zero-ℤᵉ)

eq-is-zero-ℤᵉ : {aᵉ bᵉ : ℤᵉ} → is-zero-ℤᵉ aᵉ → is-zero-ℤᵉ bᵉ → aᵉ ＝ᵉ bᵉ
eq-is-zero-ℤᵉ {aᵉ} {bᵉ} Hᵉ Kᵉ = Hᵉ ∙ᵉ invᵉ Kᵉ
```

### Inclusion of the positive integers

```agda
in-pos-ℤᵉ : ℕᵉ → ℤᵉ
in-pos-ℤᵉ nᵉ = inrᵉ (inrᵉ nᵉ)

one-ℤᵉ : ℤᵉ
one-ℤᵉ = in-pos-ℤᵉ zero-ℕᵉ

is-one-ℤᵉ : ℤᵉ → UUᵉ lzero
is-one-ℤᵉ xᵉ = (xᵉ ＝ᵉ one-ℤᵉ)
```

### Inclusion of the natural numbers

```agda
int-ℕᵉ : ℕᵉ → ℤᵉ
int-ℕᵉ zero-ℕᵉ = zero-ℤᵉ
int-ℕᵉ (succ-ℕᵉ nᵉ) = in-pos-ℤᵉ nᵉ

is-injective-int-ℕᵉ : is-injectiveᵉ int-ℕᵉ
is-injective-int-ℕᵉ {zero-ℕᵉ} {zero-ℕᵉ} reflᵉ = reflᵉ
is-injective-int-ℕᵉ {succ-ℕᵉ xᵉ} {succ-ℕᵉ yᵉ} reflᵉ = reflᵉ
```

### Induction principle on the type of integers

```agda
ind-ℤᵉ :
  {lᵉ : Level} (Pᵉ : ℤᵉ → UUᵉ lᵉ) →
  Pᵉ neg-one-ℤᵉ → ((nᵉ : ℕᵉ) → Pᵉ (inlᵉ nᵉ) → Pᵉ (inlᵉ (succ-ℕᵉ nᵉ))) →
  Pᵉ zero-ℤᵉ →
  Pᵉ one-ℤᵉ → ((nᵉ : ℕᵉ) → Pᵉ (inrᵉ (inrᵉ (nᵉ))) → Pᵉ (inrᵉ (inrᵉ (succ-ℕᵉ nᵉ)))) →
  (kᵉ : ℤᵉ) → Pᵉ kᵉ
ind-ℤᵉ Pᵉ p-1ᵉ p-Sᵉ p0ᵉ p1ᵉ pSᵉ (inlᵉ zero-ℕᵉ) = p-1ᵉ
ind-ℤᵉ Pᵉ p-1ᵉ p-Sᵉ p0ᵉ p1ᵉ pSᵉ (inlᵉ (succ-ℕᵉ xᵉ)) =
  p-Sᵉ xᵉ (ind-ℤᵉ Pᵉ p-1ᵉ p-Sᵉ p0ᵉ p1ᵉ pSᵉ (inlᵉ xᵉ))
ind-ℤᵉ Pᵉ p-1ᵉ p-Sᵉ p0ᵉ p1ᵉ pSᵉ (inrᵉ (inlᵉ starᵉ)) = p0ᵉ
ind-ℤᵉ Pᵉ p-1ᵉ p-Sᵉ p0ᵉ p1ᵉ pSᵉ (inrᵉ (inrᵉ zero-ℕᵉ)) = p1ᵉ
ind-ℤᵉ Pᵉ p-1ᵉ p-Sᵉ p0ᵉ p1ᵉ pSᵉ (inrᵉ (inrᵉ (succ-ℕᵉ xᵉ))) =
  pSᵉ xᵉ (ind-ℤᵉ Pᵉ p-1ᵉ p-Sᵉ p0ᵉ p1ᵉ pSᵉ (inrᵉ (inrᵉ (xᵉ))))
```

### The successor and predecessor functions on ℤ

```agda
succ-ℤᵉ : ℤᵉ → ℤᵉ
succ-ℤᵉ (inlᵉ zero-ℕᵉ) = zero-ℤᵉ
succ-ℤᵉ (inlᵉ (succ-ℕᵉ xᵉ)) = inlᵉ xᵉ
succ-ℤᵉ (inrᵉ (inlᵉ starᵉ)) = one-ℤᵉ
succ-ℤᵉ (inrᵉ (inrᵉ xᵉ)) = inrᵉ (inrᵉ (succ-ℕᵉ xᵉ))

pred-ℤᵉ : ℤᵉ → ℤᵉ
pred-ℤᵉ (inlᵉ xᵉ) = inlᵉ (succ-ℕᵉ xᵉ)
pred-ℤᵉ (inrᵉ (inlᵉ starᵉ)) = inlᵉ zero-ℕᵉ
pred-ℤᵉ (inrᵉ (inrᵉ zero-ℕᵉ)) = inrᵉ (inlᵉ starᵉ)
pred-ℤᵉ (inrᵉ (inrᵉ (succ-ℕᵉ xᵉ))) = inrᵉ (inrᵉ xᵉ)

ℤ-Type-With-Endomorphismᵉ : Type-With-Endomorphismᵉ lzero
pr1ᵉ ℤ-Type-With-Endomorphismᵉ = ℤᵉ
pr2ᵉ ℤ-Type-With-Endomorphismᵉ = succ-ℤᵉ
```

### The negative of an integer

```agda
neg-ℤᵉ : ℤᵉ → ℤᵉ
neg-ℤᵉ (inlᵉ xᵉ) = inrᵉ (inrᵉ xᵉ)
neg-ℤᵉ (inrᵉ (inlᵉ starᵉ)) = inrᵉ (inlᵉ starᵉ)
neg-ℤᵉ (inrᵉ (inrᵉ xᵉ)) = inlᵉ xᵉ
```

## Properties

### The type of integers is a set

```agda
abstract
  is-set-ℤᵉ : is-setᵉ ℤᵉ
  is-set-ℤᵉ = is-set-coproductᵉ is-set-ℕᵉ (is-set-coproductᵉ is-set-unitᵉ is-set-ℕᵉ)

ℤ-Setᵉ : Setᵉ lzero
pr1ᵉ ℤ-Setᵉ = ℤᵉ
pr2ᵉ ℤ-Setᵉ = is-set-ℤᵉ
```

### The successor and predecessor functions on ℤ are mutual inverses

```agda
abstract
  is-retraction-pred-ℤᵉ : is-retractionᵉ succ-ℤᵉ pred-ℤᵉ
  is-retraction-pred-ℤᵉ (inlᵉ zero-ℕᵉ) = reflᵉ
  is-retraction-pred-ℤᵉ (inlᵉ (succ-ℕᵉ xᵉ)) = reflᵉ
  is-retraction-pred-ℤᵉ (inrᵉ (inlᵉ _)) = reflᵉ
  is-retraction-pred-ℤᵉ (inrᵉ (inrᵉ zero-ℕᵉ)) = reflᵉ
  is-retraction-pred-ℤᵉ (inrᵉ (inrᵉ (succ-ℕᵉ xᵉ))) = reflᵉ

  is-section-pred-ℤᵉ : is-sectionᵉ succ-ℤᵉ pred-ℤᵉ
  is-section-pred-ℤᵉ (inlᵉ zero-ℕᵉ) = reflᵉ
  is-section-pred-ℤᵉ (inlᵉ (succ-ℕᵉ xᵉ)) = reflᵉ
  is-section-pred-ℤᵉ (inrᵉ (inlᵉ _)) = reflᵉ
  is-section-pred-ℤᵉ (inrᵉ (inrᵉ zero-ℕᵉ)) = reflᵉ
  is-section-pred-ℤᵉ (inrᵉ (inrᵉ (succ-ℕᵉ xᵉ))) = reflᵉ

abstract
  is-equiv-succ-ℤᵉ : is-equivᵉ succ-ℤᵉ
  pr1ᵉ (pr1ᵉ is-equiv-succ-ℤᵉ) = pred-ℤᵉ
  pr2ᵉ (pr1ᵉ is-equiv-succ-ℤᵉ) = is-section-pred-ℤᵉ
  pr1ᵉ (pr2ᵉ is-equiv-succ-ℤᵉ) = pred-ℤᵉ
  pr2ᵉ (pr2ᵉ is-equiv-succ-ℤᵉ) = is-retraction-pred-ℤᵉ

equiv-succ-ℤᵉ : ℤᵉ ≃ᵉ ℤᵉ
pr1ᵉ equiv-succ-ℤᵉ = succ-ℤᵉ
pr2ᵉ equiv-succ-ℤᵉ = is-equiv-succ-ℤᵉ

abstract
  is-equiv-pred-ℤᵉ : is-equivᵉ pred-ℤᵉ
  pr1ᵉ (pr1ᵉ is-equiv-pred-ℤᵉ) = succ-ℤᵉ
  pr2ᵉ (pr1ᵉ is-equiv-pred-ℤᵉ) = is-retraction-pred-ℤᵉ
  pr1ᵉ (pr2ᵉ is-equiv-pred-ℤᵉ) = succ-ℤᵉ
  pr2ᵉ (pr2ᵉ is-equiv-pred-ℤᵉ) = is-section-pred-ℤᵉ

equiv-pred-ℤᵉ : ℤᵉ ≃ᵉ ℤᵉ
pr1ᵉ equiv-pred-ℤᵉ = pred-ℤᵉ
pr2ᵉ equiv-pred-ℤᵉ = is-equiv-pred-ℤᵉ
```

### The successor function on ℤ is injective and has no fixed points

```agda
abstract
  is-injective-succ-ℤᵉ : is-injectiveᵉ succ-ℤᵉ
  is-injective-succ-ℤᵉ {xᵉ} {yᵉ} pᵉ =
    invᵉ (is-retraction-pred-ℤᵉ xᵉ) ∙ᵉ apᵉ pred-ℤᵉ pᵉ ∙ᵉ is-retraction-pred-ℤᵉ yᵉ

  has-no-fixed-points-succ-ℤᵉ : (xᵉ : ℤᵉ) → succ-ℤᵉ xᵉ ≠ᵉ xᵉ
  has-no-fixed-points-succ-ℤᵉ (inlᵉ zero-ℕᵉ) ()
  has-no-fixed-points-succ-ℤᵉ (inlᵉ (succ-ℕᵉ xᵉ)) ()
  has-no-fixed-points-succ-ℤᵉ (inrᵉ (inlᵉ starᵉ)) ()
```

### The negative function is an involution

```agda
abstract
  neg-neg-ℤᵉ : neg-ℤᵉ ∘ᵉ neg-ℤᵉ ~ᵉ idᵉ
  neg-neg-ℤᵉ (inlᵉ nᵉ) = reflᵉ
  neg-neg-ℤᵉ (inrᵉ (inlᵉ starᵉ)) = reflᵉ
  neg-neg-ℤᵉ (inrᵉ (inrᵉ nᵉ)) = reflᵉ

abstract
  is-equiv-neg-ℤᵉ : is-equivᵉ neg-ℤᵉ
  pr1ᵉ (pr1ᵉ is-equiv-neg-ℤᵉ) = neg-ℤᵉ
  pr2ᵉ (pr1ᵉ is-equiv-neg-ℤᵉ) = neg-neg-ℤᵉ
  pr1ᵉ (pr2ᵉ is-equiv-neg-ℤᵉ) = neg-ℤᵉ
  pr2ᵉ (pr2ᵉ is-equiv-neg-ℤᵉ) = neg-neg-ℤᵉ

equiv-neg-ℤᵉ : ℤᵉ ≃ᵉ ℤᵉ
pr1ᵉ equiv-neg-ℤᵉ = neg-ℤᵉ
pr2ᵉ equiv-neg-ℤᵉ = is-equiv-neg-ℤᵉ

abstract
  is-emb-neg-ℤᵉ : is-embᵉ neg-ℤᵉ
  is-emb-neg-ℤᵉ = is-emb-is-equivᵉ is-equiv-neg-ℤᵉ

emb-neg-ℤᵉ : ℤᵉ ↪ᵉ ℤᵉ
pr1ᵉ emb-neg-ℤᵉ = neg-ℤᵉ
pr2ᵉ emb-neg-ℤᵉ = is-emb-neg-ℤᵉ

abstract
  neg-pred-ℤᵉ : (kᵉ : ℤᵉ) → neg-ℤᵉ (pred-ℤᵉ kᵉ) ＝ᵉ succ-ℤᵉ (neg-ℤᵉ kᵉ)
  neg-pred-ℤᵉ (inlᵉ xᵉ) = reflᵉ
  neg-pred-ℤᵉ (inrᵉ (inlᵉ starᵉ)) = reflᵉ
  neg-pred-ℤᵉ (inrᵉ (inrᵉ zero-ℕᵉ)) = reflᵉ
  neg-pred-ℤᵉ (inrᵉ (inrᵉ (succ-ℕᵉ xᵉ))) = reflᵉ

  neg-succ-ℤᵉ : (xᵉ : ℤᵉ) → neg-ℤᵉ (succ-ℤᵉ xᵉ) ＝ᵉ pred-ℤᵉ (neg-ℤᵉ xᵉ)
  neg-succ-ℤᵉ (inlᵉ zero-ℕᵉ) = reflᵉ
  neg-succ-ℤᵉ (inlᵉ (succ-ℕᵉ xᵉ)) = reflᵉ
  neg-succ-ℤᵉ (inrᵉ (inlᵉ starᵉ)) = reflᵉ
  neg-succ-ℤᵉ (inrᵉ (inrᵉ xᵉ)) = reflᵉ

  pred-neg-ℤᵉ :
    (kᵉ : ℤᵉ) → pred-ℤᵉ (neg-ℤᵉ kᵉ) ＝ᵉ neg-ℤᵉ (succ-ℤᵉ kᵉ)
  pred-neg-ℤᵉ (inlᵉ zero-ℕᵉ) = reflᵉ
  pred-neg-ℤᵉ (inlᵉ (succ-ℕᵉ xᵉ)) = reflᵉ
  pred-neg-ℤᵉ (inrᵉ (inlᵉ starᵉ)) = reflᵉ
  pred-neg-ℤᵉ (inrᵉ (inrᵉ xᵉ)) = reflᵉ
```

### The negative function is injective

```agda
abstract
  is-injective-neg-ℤᵉ : is-injectiveᵉ neg-ℤᵉ
  is-injective-neg-ℤᵉ {xᵉ} {yᵉ} pᵉ = invᵉ (neg-neg-ℤᵉ xᵉ) ∙ᵉ apᵉ neg-ℤᵉ pᵉ ∙ᵉ neg-neg-ℤᵉ yᵉ
```

### The integer successor of a natural number is the successor of the natural number

```agda
abstract
  succ-int-ℕᵉ : (xᵉ : ℕᵉ) → succ-ℤᵉ (int-ℕᵉ xᵉ) ＝ᵉ int-ℕᵉ (succ-ℕᵉ xᵉ)
  succ-int-ℕᵉ zero-ℕᵉ = reflᵉ
  succ-int-ℕᵉ (succ-ℕᵉ xᵉ) = reflᵉ
```

### An integer is zero if its negative is zero

```agda
abstract
  is-zero-is-zero-neg-ℤᵉ : (xᵉ : ℤᵉ) → is-zero-ℤᵉ (neg-ℤᵉ xᵉ) → is-zero-ℤᵉ xᵉ
  is-zero-is-zero-neg-ℤᵉ (inrᵉ (inlᵉ starᵉ)) Hᵉ = reflᵉ
```

## See also

-ᵉ Weᵉ showᵉ in
  [`structured-types.initial-pointed-type-equipped-with-automorphism`](structured-types.initial-pointed-type-equipped-with-automorphism.mdᵉ)
  thatᵉ ℤᵉ isᵉ theᵉ initialᵉ pointedᵉ typeᵉ equippedᵉ with anᵉ automorphism.ᵉ
-ᵉ Theᵉ groupᵉ ofᵉ integersᵉ isᵉ constructedᵉ in
  [`elementary-number-theory.group-of-integers`](elementary-number-theory.group-of-integers.md).ᵉ