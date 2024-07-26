# Inequality on the integers

```agda
module elementary-number-theory.inequality-integersᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integersᵉ
open import elementary-number-theory.addition-positive-and-negative-integersᵉ
open import elementary-number-theory.difference-integersᵉ
open import elementary-number-theory.inequality-natural-numbersᵉ
open import elementary-number-theory.integersᵉ
open import elementary-number-theory.natural-numbersᵉ
open import elementary-number-theory.negative-integersᵉ
open import elementary-number-theory.nonnegative-integersᵉ
open import elementary-number-theory.nonpositive-integersᵉ
open import elementary-number-theory.positive-and-negative-integersᵉ
open import elementary-number-theory.positive-integersᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.coproduct-typesᵉ
open import foundation.decidable-propositionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-coproduct-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.negated-equalityᵉ
open import foundation.negationᵉ
open import foundation.propositionsᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import order-theory.posetsᵉ
open import order-theory.preordersᵉ
```

</details>

## Idea

Anᵉ [integer](elementary-number-theory.integers.mdᵉ) `x`ᵉ isᵉ _lessᵉ thanᵉ orᵉ equalᵉ_
to theᵉ integerᵉ `y`ᵉ ifᵉ theᵉ
[difference](elementary-number-theory.difference-integers.mdᵉ) `yᵉ -ᵉ x`ᵉ isᵉ
[nonnegative](elementary-number-theory.nonnegative-integers.md).ᵉ Thisᵉ relationᵉ
definesᵉ theᵉ
{{#conceptᵉ "standardᵉ ordering"ᵉ Disambiguation="integers"ᵉ Agda=leq-ℤᵉ}} onᵉ theᵉ
integers.ᵉ

## Definition

### Inequality on the integers

```agda
leq-ℤ-Propᵉ : ℤᵉ → ℤᵉ → Propᵉ lzero
leq-ℤ-Propᵉ xᵉ yᵉ = subtype-nonnegative-ℤᵉ (yᵉ -ℤᵉ xᵉ)

leq-ℤᵉ : ℤᵉ → ℤᵉ → UUᵉ lzero
leq-ℤᵉ xᵉ yᵉ = type-Propᵉ (leq-ℤ-Propᵉ xᵉ yᵉ)

is-prop-leq-ℤᵉ : (xᵉ yᵉ : ℤᵉ) → is-propᵉ (leq-ℤᵉ xᵉ yᵉ)
is-prop-leq-ℤᵉ xᵉ yᵉ = is-prop-type-Propᵉ (leq-ℤ-Propᵉ xᵉ yᵉ)

infix 30 _≤-ℤᵉ_
_≤-ℤᵉ_ = leq-ℤᵉ
```

## Properties

### Inequality on the integers is reflexive, antisymmetric and transitive

```agda
refl-leq-ℤᵉ : (kᵉ : ℤᵉ) → leq-ℤᵉ kᵉ kᵉ
refl-leq-ℤᵉ kᵉ = trᵉ is-nonnegative-ℤᵉ (invᵉ (right-inverse-law-add-ℤᵉ kᵉ)) starᵉ

antisymmetric-leq-ℤᵉ : {xᵉ yᵉ : ℤᵉ} → leq-ℤᵉ xᵉ yᵉ → leq-ℤᵉ yᵉ xᵉ → xᵉ ＝ᵉ yᵉ
antisymmetric-leq-ℤᵉ {xᵉ} {yᵉ} Hᵉ Kᵉ =
  eq-diff-ℤᵉ
    ( is-zero-is-nonnegative-neg-is-nonnegative-ℤᵉ Kᵉ
      ( is-nonnegative-eq-ℤᵉ (invᵉ (distributive-neg-diff-ℤᵉ xᵉ yᵉ)) Hᵉ))

transitive-leq-ℤᵉ : (kᵉ lᵉ mᵉ : ℤᵉ) → leq-ℤᵉ lᵉ mᵉ → leq-ℤᵉ kᵉ lᵉ → leq-ℤᵉ kᵉ mᵉ
transitive-leq-ℤᵉ kᵉ lᵉ mᵉ Hᵉ Kᵉ =
  is-nonnegative-eq-ℤᵉ
    ( triangle-diff-ℤᵉ mᵉ lᵉ kᵉ)
    ( is-nonnegative-add-ℤᵉ Hᵉ Kᵉ)
```

### Inequality on the integers is decidable

```agda
is-decidable-leq-ℤᵉ : (xᵉ yᵉ : ℤᵉ) → (leq-ℤᵉ xᵉ yᵉ) +ᵉ ¬ᵉ (leq-ℤᵉ xᵉ yᵉ)
is-decidable-leq-ℤᵉ xᵉ yᵉ = is-decidable-is-nonnegative-ℤᵉ (yᵉ -ℤᵉ xᵉ)

leq-ℤ-Decidable-Propᵉ : (xᵉ yᵉ : ℤᵉ) → Decidable-Propᵉ lzero
leq-ℤ-Decidable-Propᵉ xᵉ yᵉ =
  ( leq-ℤᵉ xᵉ yᵉ ,ᵉ
    is-prop-leq-ℤᵉ xᵉ yᵉ ,ᵉ
    is-decidable-leq-ℤᵉ xᵉ yᵉ)
```

### Inequality on the integers is linear

```agda
linear-leq-ℤᵉ : (xᵉ yᵉ : ℤᵉ) → (leq-ℤᵉ xᵉ yᵉ) +ᵉ (leq-ℤᵉ yᵉ xᵉ)
linear-leq-ℤᵉ xᵉ yᵉ =
  map-coproductᵉ
    ( λ Hᵉ →
      is-nonnegative-is-positive-ℤᵉ
        ( is-positive-eq-ℤᵉ
          ( distributive-neg-diff-ℤᵉ xᵉ yᵉ)
          ( is-positive-neg-is-negative-ℤᵉ Hᵉ)))
    ( idᵉ)
    ( decide-is-negative-is-nonnegative-ℤᵉ)
```

### An integer is lesser than its successor

```agda
succ-leq-ℤᵉ : (kᵉ : ℤᵉ) → leq-ℤᵉ kᵉ (succ-ℤᵉ kᵉ)
succ-leq-ℤᵉ kᵉ =
  is-nonnegative-eq-ℤᵉ
    ( invᵉ
      ( ( left-successor-law-add-ℤᵉ kᵉ (neg-ℤᵉ kᵉ)) ∙ᵉ
        ( apᵉ succ-ℤᵉ (right-inverse-law-add-ℤᵉ kᵉ))))
    ( starᵉ)

leq-ℤ-succ-leq-ℤᵉ : (kᵉ lᵉ : ℤᵉ) → leq-ℤᵉ kᵉ lᵉ → leq-ℤᵉ kᵉ (succ-ℤᵉ lᵉ)
leq-ℤ-succ-leq-ℤᵉ kᵉ lᵉ = transitive-leq-ℤᵉ kᵉ lᵉ (succ-ℤᵉ lᵉ) (succ-leq-ℤᵉ lᵉ)
```

### Chaining rules for equality and inequality

```agda
concatenate-eq-leq-eq-ℤᵉ :
  {x'ᵉ xᵉ yᵉ y'ᵉ : ℤᵉ} → x'ᵉ ＝ᵉ xᵉ → leq-ℤᵉ xᵉ yᵉ → yᵉ ＝ᵉ y'ᵉ → leq-ℤᵉ x'ᵉ y'ᵉ
concatenate-eq-leq-eq-ℤᵉ reflᵉ Hᵉ reflᵉ = Hᵉ

concatenate-leq-eq-ℤᵉ :
  (xᵉ : ℤᵉ) {yᵉ y'ᵉ : ℤᵉ} → leq-ℤᵉ xᵉ yᵉ → yᵉ ＝ᵉ y'ᵉ → leq-ℤᵉ xᵉ y'ᵉ
concatenate-leq-eq-ℤᵉ xᵉ Hᵉ reflᵉ = Hᵉ

concatenate-eq-leq-ℤᵉ :
  {xᵉ x'ᵉ : ℤᵉ} (yᵉ : ℤᵉ) → x'ᵉ ＝ᵉ xᵉ → leq-ℤᵉ xᵉ yᵉ → leq-ℤᵉ x'ᵉ yᵉ
concatenate-eq-leq-ℤᵉ yᵉ reflᵉ Hᵉ = Hᵉ
```

### Addition on the integers preserves inequality

```agda
preserves-leq-left-add-ℤᵉ :
  (zᵉ xᵉ yᵉ : ℤᵉ) → leq-ℤᵉ xᵉ yᵉ → leq-ℤᵉ (xᵉ +ℤᵉ zᵉ) (yᵉ +ℤᵉ zᵉ)
preserves-leq-left-add-ℤᵉ zᵉ xᵉ yᵉ =
  is-nonnegative-eq-ℤᵉ (invᵉ (right-translation-diff-ℤᵉ yᵉ xᵉ zᵉ))

preserves-leq-right-add-ℤᵉ :
  (zᵉ xᵉ yᵉ : ℤᵉ) → leq-ℤᵉ xᵉ yᵉ → leq-ℤᵉ (zᵉ +ℤᵉ xᵉ) (zᵉ +ℤᵉ yᵉ)
preserves-leq-right-add-ℤᵉ zᵉ xᵉ yᵉ =
  is-nonnegative-eq-ℤᵉ (invᵉ (left-translation-diff-ℤᵉ yᵉ xᵉ zᵉ))

preserves-leq-add-ℤᵉ :
  {aᵉ bᵉ cᵉ dᵉ : ℤᵉ} → leq-ℤᵉ aᵉ bᵉ → leq-ℤᵉ cᵉ dᵉ → leq-ℤᵉ (aᵉ +ℤᵉ cᵉ) (bᵉ +ℤᵉ dᵉ)
preserves-leq-add-ℤᵉ {aᵉ} {bᵉ} {cᵉ} {dᵉ} Hᵉ Kᵉ =
  transitive-leq-ℤᵉ
    ( aᵉ +ℤᵉ cᵉ)
    ( bᵉ +ℤᵉ cᵉ)
    ( bᵉ +ℤᵉ dᵉ)
    ( preserves-leq-right-add-ℤᵉ bᵉ cᵉ dᵉ Kᵉ)
    ( preserves-leq-left-add-ℤᵉ cᵉ aᵉ bᵉ Hᵉ)
```

### Addition on the integers reflects inequality

```agda
reflects-leq-left-add-ℤᵉ :
  (zᵉ xᵉ yᵉ : ℤᵉ) → leq-ℤᵉ (xᵉ +ℤᵉ zᵉ) (yᵉ +ℤᵉ zᵉ) → leq-ℤᵉ xᵉ yᵉ
reflects-leq-left-add-ℤᵉ zᵉ xᵉ yᵉ =
  is-nonnegative-eq-ℤᵉ (right-translation-diff-ℤᵉ yᵉ xᵉ zᵉ)

reflects-leq-right-add-ℤᵉ :
  (zᵉ xᵉ yᵉ : ℤᵉ) → leq-ℤᵉ (zᵉ +ℤᵉ xᵉ) (zᵉ +ℤᵉ yᵉ) → leq-ℤᵉ xᵉ yᵉ
reflects-leq-right-add-ℤᵉ zᵉ xᵉ yᵉ =
  is-nonnegative-eq-ℤᵉ (left-translation-diff-ℤᵉ yᵉ xᵉ zᵉ)
```

### The inclusion of ℕ into ℤ preserves inequality

```agda
leq-int-ℕᵉ : (xᵉ yᵉ : ℕᵉ) → leq-ℕᵉ xᵉ yᵉ → leq-ℤᵉ (int-ℕᵉ xᵉ) (int-ℕᵉ yᵉ)
leq-int-ℕᵉ zero-ℕᵉ yᵉ Hᵉ =
  trᵉ
    ( is-nonnegative-ℤᵉ)
    ( invᵉ (right-unit-law-add-ℤᵉ (int-ℕᵉ yᵉ)))
    ( is-nonnegative-int-ℕᵉ yᵉ)
leq-int-ℕᵉ (succ-ℕᵉ xᵉ) (succ-ℕᵉ yᵉ) Hᵉ = trᵉ (is-nonnegative-ℤᵉ)
  ( invᵉ (diff-succ-ℤᵉ (int-ℕᵉ yᵉ) (int-ℕᵉ xᵉ)) ∙ᵉ
    ( apᵉ (_-ℤᵉ (succ-ℤᵉ (int-ℕᵉ xᵉ))) (succ-int-ℕᵉ yᵉ) ∙ᵉ
      apᵉ ((int-ℕᵉ (succ-ℕᵉ yᵉ)) -ℤᵉ_) (succ-int-ℕᵉ xᵉ)))
  ( leq-int-ℕᵉ xᵉ yᵉ Hᵉ)
```

### The partially ordered set of integers ordered by inequality

```agda
ℤ-Preorderᵉ : Preorderᵉ lzero lzero
ℤ-Preorderᵉ =
  (ℤᵉ ,ᵉ leq-ℤ-Propᵉ ,ᵉ refl-leq-ℤᵉ ,ᵉ transitive-leq-ℤᵉ)

ℤ-Posetᵉ : Posetᵉ lzero lzero
ℤ-Posetᵉ = (ℤ-Preorderᵉ ,ᵉ λ xᵉ yᵉ → antisymmetric-leq-ℤᵉ)
```

### An integer `x` is nonnegative if and only if `0 ≤ x`

```agda
module _
  (xᵉ : ℤᵉ)
  where

  abstract
    leq-zero-is-nonnegative-ℤᵉ : is-nonnegative-ℤᵉ xᵉ → leq-ℤᵉ zero-ℤᵉ xᵉ
    leq-zero-is-nonnegative-ℤᵉ =
      is-nonnegative-eq-ℤᵉ (invᵉ (right-zero-law-diff-ℤᵉ xᵉ))

    is-nonnegative-leq-zero-ℤᵉ : leq-ℤᵉ zero-ℤᵉ xᵉ → is-nonnegative-ℤᵉ xᵉ
    is-nonnegative-leq-zero-ℤᵉ =
      is-nonnegative-eq-ℤᵉ (right-zero-law-diff-ℤᵉ xᵉ)
```

### An integer greater than or equal to a nonnegative integer is nonnegative

```agda
module _
  (xᵉ yᵉ : ℤᵉ) (Iᵉ : leq-ℤᵉ xᵉ yᵉ)
  where

  abstract
    is-nonnegative-leq-nonnegative-ℤᵉ : is-nonnegative-ℤᵉ xᵉ → is-nonnegative-ℤᵉ yᵉ
    is-nonnegative-leq-nonnegative-ℤᵉ Hᵉ =
      is-nonnegative-leq-zero-ℤᵉ yᵉ
        ( transitive-leq-ℤᵉ
          ( zero-ℤᵉ)
          ( xᵉ)
          ( yᵉ)
          ( Iᵉ)
          ( leq-zero-is-nonnegative-ℤᵉ xᵉ Hᵉ))
```

### An integer `x` is nonpositive if and only if `x ≤ 0`

```agda
module _
  (xᵉ : ℤᵉ)
  where

  abstract
    leq-zero-is-nonpositive-ℤᵉ : is-nonpositive-ℤᵉ xᵉ → leq-ℤᵉ xᵉ zero-ℤᵉ
    leq-zero-is-nonpositive-ℤᵉ = is-nonnegative-neg-is-nonpositive-ℤᵉ

    is-nonpositive-leq-zero-ℤᵉ : leq-ℤᵉ xᵉ zero-ℤᵉ → is-nonpositive-ℤᵉ xᵉ
    is-nonpositive-leq-zero-ℤᵉ Hᵉ =
      is-nonpositive-eq-ℤᵉ
        ( neg-neg-ℤᵉ xᵉ)
        ( is-nonpositive-neg-is-nonnegative-ℤᵉ Hᵉ)
```

### An integer less than or equal to a nonpositive integer is nonpositive

```agda
module _
  (xᵉ yᵉ : ℤᵉ) (Iᵉ : leq-ℤᵉ xᵉ yᵉ)
  where

  abstract
    is-nonpositive-leq-nonpositive-ℤᵉ : is-nonpositive-ℤᵉ yᵉ → is-nonpositive-ℤᵉ xᵉ
    is-nonpositive-leq-nonpositive-ℤᵉ Hᵉ =
      is-nonpositive-leq-zero-ℤᵉ xᵉ
        ( transitive-leq-ℤᵉ
          ( xᵉ)
          ( yᵉ)
          ( zero-ℤᵉ)
          ( leq-zero-is-nonpositive-ℤᵉ yᵉ Hᵉ)
          ( Iᵉ))
```

## See also

-ᵉ Theᵉ decidableᵉ totalᵉ orderᵉ onᵉ theᵉ integersᵉ isᵉ definedᵉ in
  [`decidable-total-order-integers`](elementary-number-theory.decidable-total-order-integers.mdᵉ)
-ᵉ Strictᵉ inequalityᵉ onᵉ theᵉ integersᵉ isᵉ definedᵉ in
  [`strict-inequality-integers`](elementary-number-theory.strict-inequality-integers.mdᵉ)