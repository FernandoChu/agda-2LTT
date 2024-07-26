# Divisibility of natural numbers

```agda
module elementary-number-theory.divisibility-natural-numbersᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbersᵉ
open import elementary-number-theory.distance-natural-numbersᵉ
open import elementary-number-theory.inequality-natural-numbersᵉ
open import elementary-number-theory.multiplication-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ
open import elementary-number-theory.strict-inequality-natural-numbersᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.binary-relationsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.empty-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.negated-equalityᵉ
open import foundation.negationᵉ
open import foundation.propositional-mapsᵉ
open import foundation.propositionsᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.type-arithmetic-empty-typeᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Aᵉ naturalᵉ numberᵉ `m`ᵉ isᵉ saidᵉ to **divide**ᵉ aᵉ naturalᵉ numberᵉ `n`ᵉ ifᵉ thereᵉ existsᵉ
aᵉ naturalᵉ numberᵉ `k`ᵉ equippedᵉ with anᵉ identificationᵉ `kmᵉ ＝ᵉ n`.ᵉ Usingᵉ theᵉ
Curry-Howardᵉ interpretationᵉ ofᵉ logicᵉ intoᵉ typeᵉ theory,ᵉ weᵉ expressᵉ divisibilityᵉ
asᵉ followsᵉ:

```text
  div-ℕᵉ mᵉ nᵉ :=ᵉ Σᵉ (kᵉ : ℕ),ᵉ kᵉ *ℕᵉ mᵉ ＝ᵉ n.ᵉ
```

Ifᵉ `n`ᵉ isᵉ aᵉ nonzeroᵉ naturalᵉ number,ᵉ thenᵉ `div-ℕᵉ mᵉ n`ᵉ isᵉ alwaysᵉ aᵉ propositionᵉ in
theᵉ senseᵉ thatᵉ theᵉ typeᵉ `div-ℕᵉ mᵉ n`ᵉ containsᵉ atᵉ mostᵉ oneᵉ element.ᵉ

## Definitions

```agda
div-ℕᵉ : ℕᵉ → ℕᵉ → UUᵉ lzero
div-ℕᵉ mᵉ nᵉ = Σᵉ ℕᵉ (λ kᵉ → kᵉ *ℕᵉ mᵉ ＝ᵉ nᵉ)

quotient-div-ℕᵉ : (xᵉ yᵉ : ℕᵉ) → div-ℕᵉ xᵉ yᵉ → ℕᵉ
quotient-div-ℕᵉ xᵉ yᵉ Hᵉ = pr1ᵉ Hᵉ

eq-quotient-div-ℕᵉ :
  (xᵉ yᵉ : ℕᵉ) (Hᵉ : div-ℕᵉ xᵉ yᵉ) → (quotient-div-ℕᵉ xᵉ yᵉ Hᵉ) *ℕᵉ xᵉ ＝ᵉ yᵉ
eq-quotient-div-ℕᵉ xᵉ yᵉ Hᵉ = pr2ᵉ Hᵉ

eq-quotient-div-ℕ'ᵉ :
  (xᵉ yᵉ : ℕᵉ) (Hᵉ : div-ℕᵉ xᵉ yᵉ) → xᵉ *ℕᵉ (quotient-div-ℕᵉ xᵉ yᵉ Hᵉ) ＝ᵉ yᵉ
eq-quotient-div-ℕ'ᵉ xᵉ yᵉ Hᵉ =
  commutative-mul-ℕᵉ xᵉ (quotient-div-ℕᵉ xᵉ yᵉ Hᵉ) ∙ᵉ eq-quotient-div-ℕᵉ xᵉ yᵉ Hᵉ

div-quotient-div-ℕᵉ :
  (dᵉ xᵉ : ℕᵉ) (Hᵉ : div-ℕᵉ dᵉ xᵉ) → div-ℕᵉ (quotient-div-ℕᵉ dᵉ xᵉ Hᵉ) xᵉ
pr1ᵉ (div-quotient-div-ℕᵉ dᵉ xᵉ (uᵉ ,ᵉ pᵉ)) = dᵉ
pr2ᵉ (div-quotient-div-ℕᵉ dᵉ xᵉ (uᵉ ,ᵉ pᵉ)) = commutative-mul-ℕᵉ dᵉ uᵉ ∙ᵉ pᵉ
```

### Concatenating equality and divisibility

```agda
concatenate-eq-div-ℕᵉ :
  {xᵉ yᵉ zᵉ : ℕᵉ} → xᵉ ＝ᵉ yᵉ → div-ℕᵉ yᵉ zᵉ → div-ℕᵉ xᵉ zᵉ
concatenate-eq-div-ℕᵉ reflᵉ pᵉ = pᵉ

concatenate-div-eq-ℕᵉ :
  {xᵉ yᵉ zᵉ : ℕᵉ} → div-ℕᵉ xᵉ yᵉ → yᵉ ＝ᵉ zᵉ → div-ℕᵉ xᵉ zᵉ
concatenate-div-eq-ℕᵉ pᵉ reflᵉ = pᵉ

concatenate-eq-div-eq-ℕᵉ :
  {xᵉ yᵉ zᵉ wᵉ : ℕᵉ} → xᵉ ＝ᵉ yᵉ → div-ℕᵉ yᵉ zᵉ → zᵉ ＝ᵉ wᵉ → div-ℕᵉ xᵉ wᵉ
concatenate-eq-div-eq-ℕᵉ reflᵉ pᵉ reflᵉ = pᵉ
```

## Properties

### The quotients of a natural number `n` by two natural numbers `p` and `q` are equal if `p` and `q` are equal

```agda
eq-quotient-div-eq-div-ℕᵉ :
  (xᵉ yᵉ zᵉ : ℕᵉ) → is-nonzero-ℕᵉ xᵉ → xᵉ ＝ᵉ yᵉ →
  (Hᵉ : div-ℕᵉ xᵉ zᵉ) → (Iᵉ : div-ℕᵉ yᵉ zᵉ) →
  quotient-div-ℕᵉ xᵉ zᵉ Hᵉ ＝ᵉ quotient-div-ℕᵉ yᵉ zᵉ Iᵉ
eq-quotient-div-eq-div-ℕᵉ xᵉ yᵉ zᵉ nᵉ eᵉ Hᵉ Iᵉ =
  is-injective-left-mul-ℕᵉ
    ( xᵉ)
    ( nᵉ)
  ( trᵉ
    ( λ pᵉ →
      xᵉ *ℕᵉ (quotient-div-ℕᵉ xᵉ zᵉ Hᵉ) ＝ᵉ
      pᵉ *ℕᵉ (quotient-div-ℕᵉ yᵉ zᵉ Iᵉ))
    ( invᵉ eᵉ)
    ( commutative-mul-ℕᵉ xᵉ (quotient-div-ℕᵉ xᵉ zᵉ Hᵉ) ∙ᵉ
      ( eq-quotient-div-ℕᵉ xᵉ zᵉ Hᵉ ∙ᵉ
        ( invᵉ (eq-quotient-div-ℕᵉ yᵉ zᵉ Iᵉ) ∙ᵉ
          commutative-mul-ℕᵉ (quotient-div-ℕᵉ yᵉ zᵉ Iᵉ) yᵉ))))
```

### Divisibility by a nonzero natural number is a property

```agda
is-prop-div-ℕᵉ : (kᵉ xᵉ : ℕᵉ) → is-nonzero-ℕᵉ kᵉ → is-propᵉ (div-ℕᵉ kᵉ xᵉ)
is-prop-div-ℕᵉ kᵉ xᵉ fᵉ = is-prop-map-is-embᵉ (is-emb-right-mul-ℕᵉ kᵉ fᵉ) xᵉ
```

### The divisibility relation is a partial order on the natural numbers

```agda
refl-div-ℕᵉ : is-reflexiveᵉ div-ℕᵉ
pr1ᵉ (refl-div-ℕᵉ xᵉ) = 1
pr2ᵉ (refl-div-ℕᵉ xᵉ) = left-unit-law-mul-ℕᵉ xᵉ

div-eq-ℕᵉ : (xᵉ yᵉ : ℕᵉ) → xᵉ ＝ᵉ yᵉ → div-ℕᵉ xᵉ yᵉ
div-eq-ℕᵉ xᵉ .xᵉ reflᵉ = refl-div-ℕᵉ xᵉ

antisymmetric-div-ℕᵉ : is-antisymmetricᵉ div-ℕᵉ
antisymmetric-div-ℕᵉ zero-ℕᵉ zero-ℕᵉ Hᵉ Kᵉ = reflᵉ
antisymmetric-div-ℕᵉ zero-ℕᵉ (succ-ℕᵉ yᵉ) (pairᵉ kᵉ pᵉ) Kᵉ =
  invᵉ (right-zero-law-mul-ℕᵉ kᵉ) ∙ᵉ pᵉ
antisymmetric-div-ℕᵉ (succ-ℕᵉ xᵉ) zero-ℕᵉ Hᵉ (pairᵉ lᵉ qᵉ) =
  invᵉ qᵉ ∙ᵉ right-zero-law-mul-ℕᵉ lᵉ
antisymmetric-div-ℕᵉ (succ-ℕᵉ xᵉ) (succ-ℕᵉ yᵉ) (pairᵉ kᵉ pᵉ) (pairᵉ lᵉ qᵉ) =
  ( invᵉ (left-unit-law-mul-ℕᵉ (succ-ℕᵉ xᵉ))) ∙ᵉ
  ( ( apᵉ
      ( _*ℕᵉ (succ-ℕᵉ xᵉ))
      ( invᵉ
        ( is-one-right-is-one-mul-ℕᵉ lᵉ kᵉ
          ( is-one-is-left-unit-mul-ℕᵉ (lᵉ *ℕᵉ kᵉ) xᵉ
            ( ( associative-mul-ℕᵉ lᵉ kᵉ (succ-ℕᵉ xᵉ)) ∙ᵉ
              ( apᵉ (lᵉ *ℕᵉ_) pᵉ ∙ᵉ qᵉ)))))) ∙ᵉ
    ( pᵉ))

transitive-div-ℕᵉ : is-transitiveᵉ div-ℕᵉ
pr1ᵉ (transitive-div-ℕᵉ xᵉ yᵉ zᵉ (pairᵉ lᵉ qᵉ) (pairᵉ kᵉ pᵉ)) = lᵉ *ℕᵉ kᵉ
pr2ᵉ (transitive-div-ℕᵉ xᵉ yᵉ zᵉ (pairᵉ lᵉ qᵉ) (pairᵉ kᵉ pᵉ)) =
  associative-mul-ℕᵉ lᵉ kᵉ xᵉ ∙ᵉ (apᵉ (lᵉ *ℕᵉ_) pᵉ ∙ᵉ qᵉ)
```

### If `x` is nonzero and `d | x`, then `d ≤ x`

```agda
leq-div-succ-ℕᵉ : (dᵉ xᵉ : ℕᵉ) → div-ℕᵉ dᵉ (succ-ℕᵉ xᵉ) → leq-ℕᵉ dᵉ (succ-ℕᵉ xᵉ)
leq-div-succ-ℕᵉ dᵉ xᵉ (pairᵉ (succ-ℕᵉ kᵉ) pᵉ) =
  concatenate-leq-eq-ℕᵉ dᵉ (leq-mul-ℕ'ᵉ kᵉ dᵉ) pᵉ

leq-div-ℕᵉ : (dᵉ xᵉ : ℕᵉ) → is-nonzero-ℕᵉ xᵉ → div-ℕᵉ dᵉ xᵉ → leq-ℕᵉ dᵉ xᵉ
leq-div-ℕᵉ dᵉ xᵉ fᵉ Hᵉ with is-successor-is-nonzero-ℕᵉ fᵉ
... | (pairᵉ yᵉ reflᵉ) = leq-div-succ-ℕᵉ dᵉ yᵉ Hᵉ

leq-quotient-div-ℕᵉ :
  (dᵉ xᵉ : ℕᵉ) → is-nonzero-ℕᵉ xᵉ → (Hᵉ : div-ℕᵉ dᵉ xᵉ) → leq-ℕᵉ (quotient-div-ℕᵉ dᵉ xᵉ Hᵉ) xᵉ
leq-quotient-div-ℕᵉ dᵉ xᵉ fᵉ Hᵉ =
  leq-div-ℕᵉ (quotient-div-ℕᵉ dᵉ xᵉ Hᵉ) xᵉ fᵉ (div-quotient-div-ℕᵉ dᵉ xᵉ Hᵉ)

leq-quotient-div-ℕ'ᵉ :
  (dᵉ xᵉ : ℕᵉ) → is-nonzero-ℕᵉ dᵉ → (Hᵉ : div-ℕᵉ dᵉ xᵉ) → leq-ℕᵉ (quotient-div-ℕᵉ dᵉ xᵉ Hᵉ) xᵉ
leq-quotient-div-ℕ'ᵉ dᵉ zero-ℕᵉ fᵉ (zero-ℕᵉ ,ᵉ pᵉ) = starᵉ
leq-quotient-div-ℕ'ᵉ dᵉ zero-ℕᵉ fᵉ (succ-ℕᵉ nᵉ ,ᵉ pᵉ) =
  fᵉ (is-zero-right-is-zero-add-ℕᵉ _ dᵉ pᵉ)
leq-quotient-div-ℕ'ᵉ dᵉ (succ-ℕᵉ xᵉ) fᵉ Hᵉ =
  leq-quotient-div-ℕᵉ dᵉ (succ-ℕᵉ xᵉ) (is-nonzero-succ-ℕᵉ xᵉ) Hᵉ
```

### If `x` is nonzero, if `d | x` and `d ≠ x`, then `d < x`

```agda
le-div-succ-ℕᵉ :
  (dᵉ xᵉ : ℕᵉ) → div-ℕᵉ dᵉ (succ-ℕᵉ xᵉ) → dᵉ ≠ᵉ succ-ℕᵉ xᵉ → le-ℕᵉ dᵉ (succ-ℕᵉ xᵉ)
le-div-succ-ℕᵉ dᵉ xᵉ Hᵉ fᵉ = le-leq-neq-ℕᵉ (leq-div-succ-ℕᵉ dᵉ xᵉ Hᵉ) fᵉ

le-div-ℕᵉ : (dᵉ xᵉ : ℕᵉ) → is-nonzero-ℕᵉ xᵉ → div-ℕᵉ dᵉ xᵉ → dᵉ ≠ᵉ xᵉ → le-ℕᵉ dᵉ xᵉ
le-div-ℕᵉ dᵉ xᵉ Hᵉ Kᵉ fᵉ = le-leq-neq-ℕᵉ (leq-div-ℕᵉ dᵉ xᵉ Hᵉ Kᵉ) fᵉ
```

### `1` divides any number

```agda
div-one-ℕᵉ :
  (xᵉ : ℕᵉ) → div-ℕᵉ 1 xᵉ
pr1ᵉ (div-one-ℕᵉ xᵉ) = xᵉ
pr2ᵉ (div-one-ℕᵉ xᵉ) = right-unit-law-mul-ℕᵉ xᵉ

div-is-one-ℕᵉ :
  (kᵉ xᵉ : ℕᵉ) → is-one-ℕᵉ kᵉ → div-ℕᵉ kᵉ xᵉ
div-is-one-ℕᵉ .1ᵉ xᵉ reflᵉ = div-one-ℕᵉ xᵉ
```

### `x | 1` implies `x ＝ 1`

```agda
is-one-div-one-ℕᵉ : (xᵉ : ℕᵉ) → div-ℕᵉ xᵉ 1 → is-one-ℕᵉ xᵉ
is-one-div-one-ℕᵉ xᵉ Hᵉ = antisymmetric-div-ℕᵉ xᵉ 1 Hᵉ (div-one-ℕᵉ xᵉ)
```

### Any number divides `0`

```agda
div-zero-ℕᵉ :
  (kᵉ : ℕᵉ) → div-ℕᵉ kᵉ 0
pr1ᵉ (div-zero-ℕᵉ kᵉ) = 0
pr2ᵉ (div-zero-ℕᵉ kᵉ) = left-zero-law-mul-ℕᵉ kᵉ

div-is-zero-ℕᵉ :
  (kᵉ xᵉ : ℕᵉ) → is-zero-ℕᵉ xᵉ → div-ℕᵉ kᵉ xᵉ
div-is-zero-ℕᵉ kᵉ .zero-ℕᵉ reflᵉ = div-zero-ℕᵉ kᵉ
```

### `0 | x` implies `x = 0` and `x | 1` implies `x = 1`

```agda
is-zero-div-zero-ℕᵉ : (xᵉ : ℕᵉ) → div-ℕᵉ zero-ℕᵉ xᵉ → is-zero-ℕᵉ xᵉ
is-zero-div-zero-ℕᵉ xᵉ Hᵉ = antisymmetric-div-ℕᵉ xᵉ zero-ℕᵉ (div-zero-ℕᵉ xᵉ) Hᵉ

is-zero-is-zero-div-ℕᵉ : (xᵉ yᵉ : ℕᵉ) → div-ℕᵉ xᵉ yᵉ → is-zero-ℕᵉ xᵉ → is-zero-ℕᵉ yᵉ
is-zero-is-zero-div-ℕᵉ .zero-ℕᵉ yᵉ dᵉ reflᵉ = is-zero-div-zero-ℕᵉ yᵉ dᵉ
```

### Any divisor of a nonzero number is nonzero

```agda
is-nonzero-div-ℕᵉ :
  (dᵉ xᵉ : ℕᵉ) → div-ℕᵉ dᵉ xᵉ → is-nonzero-ℕᵉ xᵉ → is-nonzero-ℕᵉ dᵉ
is-nonzero-div-ℕᵉ .zero-ℕᵉ xᵉ Hᵉ Kᵉ reflᵉ = Kᵉ (is-zero-div-zero-ℕᵉ xᵉ Hᵉ)
```

### Any divisor of a number at least `1` is at least `1`

```agda
leq-one-div-ℕᵉ :
  (dᵉ xᵉ : ℕᵉ) → div-ℕᵉ dᵉ xᵉ → leq-ℕᵉ 1 xᵉ → leq-ℕᵉ 1 dᵉ
leq-one-div-ℕᵉ dᵉ xᵉ Hᵉ Lᵉ =
  leq-one-is-nonzero-ℕᵉ dᵉ (is-nonzero-div-ℕᵉ dᵉ xᵉ Hᵉ (is-nonzero-leq-one-ℕᵉ xᵉ Lᵉ))
```

### If `x < d` and `d | x`, then `x` must be `0`

```agda
is-zero-div-ℕᵉ :
  (dᵉ xᵉ : ℕᵉ) → le-ℕᵉ xᵉ dᵉ → div-ℕᵉ dᵉ xᵉ → is-zero-ℕᵉ xᵉ
is-zero-div-ℕᵉ dᵉ zero-ℕᵉ Hᵉ Dᵉ = reflᵉ
is-zero-div-ℕᵉ dᵉ (succ-ℕᵉ xᵉ) Hᵉ (pairᵉ (succ-ℕᵉ kᵉ) pᵉ) =
  ex-falsoᵉ
    ( contradiction-le-ℕᵉ
      ( succ-ℕᵉ xᵉ) dᵉ Hᵉ
      ( concatenate-leq-eq-ℕᵉ dᵉ
        ( leq-add-ℕ'ᵉ dᵉ (kᵉ *ℕᵉ dᵉ)) pᵉ))
```

### If `x` divides `y` then `x` divides any multiple of `y`

```agda
div-mul-ℕᵉ :
  (kᵉ xᵉ yᵉ : ℕᵉ) → div-ℕᵉ xᵉ yᵉ → div-ℕᵉ xᵉ (kᵉ *ℕᵉ yᵉ)
div-mul-ℕᵉ kᵉ xᵉ yᵉ Hᵉ =
  transitive-div-ℕᵉ xᵉ yᵉ (kᵉ *ℕᵉ yᵉ) (pairᵉ kᵉ reflᵉ) Hᵉ

div-mul-ℕ'ᵉ :
  (kᵉ xᵉ yᵉ : ℕᵉ) → div-ℕᵉ xᵉ yᵉ → div-ℕᵉ xᵉ (yᵉ *ℕᵉ kᵉ)
div-mul-ℕ'ᵉ kᵉ xᵉ yᵉ Hᵉ =
  trᵉ (div-ℕᵉ xᵉ) (commutative-mul-ℕᵉ kᵉ yᵉ) (div-mul-ℕᵉ kᵉ xᵉ yᵉ Hᵉ)
```

### A 3-for-2 property of division with respect to addition

```agda
div-add-ℕᵉ :
  (dᵉ xᵉ yᵉ : ℕᵉ) → div-ℕᵉ dᵉ xᵉ → div-ℕᵉ dᵉ yᵉ → div-ℕᵉ dᵉ (xᵉ +ℕᵉ yᵉ)
pr1ᵉ (div-add-ℕᵉ dᵉ xᵉ yᵉ (pairᵉ nᵉ pᵉ) (pairᵉ mᵉ qᵉ)) = nᵉ +ℕᵉ mᵉ
pr2ᵉ (div-add-ℕᵉ dᵉ xᵉ yᵉ (pairᵉ nᵉ pᵉ) (pairᵉ mᵉ qᵉ)) =
  ( right-distributive-mul-add-ℕᵉ nᵉ mᵉ dᵉ) ∙ᵉ
  ( ap-add-ℕᵉ pᵉ qᵉ)

div-left-summand-ℕᵉ :
  (dᵉ xᵉ yᵉ : ℕᵉ) → div-ℕᵉ dᵉ yᵉ → div-ℕᵉ dᵉ (xᵉ +ℕᵉ yᵉ) → div-ℕᵉ dᵉ xᵉ
div-left-summand-ℕᵉ zero-ℕᵉ xᵉ yᵉ (pairᵉ mᵉ qᵉ) (pairᵉ nᵉ pᵉ) =
  pairᵉ zero-ℕᵉ
    ( ( invᵉ (right-zero-law-mul-ℕᵉ nᵉ)) ∙ᵉ
      ( pᵉ ∙ᵉ (apᵉ (xᵉ +ℕᵉ_) ((invᵉ qᵉ) ∙ᵉ (right-zero-law-mul-ℕᵉ mᵉ)))))
pr1ᵉ (div-left-summand-ℕᵉ (succ-ℕᵉ dᵉ) xᵉ yᵉ (pairᵉ mᵉ qᵉ) (pairᵉ nᵉ pᵉ)) = dist-ℕᵉ mᵉ nᵉ
pr2ᵉ (div-left-summand-ℕᵉ (succ-ℕᵉ dᵉ) xᵉ yᵉ (pairᵉ mᵉ qᵉ) (pairᵉ nᵉ pᵉ)) =
  is-injective-right-add-ℕᵉ (mᵉ *ℕᵉ (succ-ℕᵉ dᵉ))
    ( ( invᵉ
        ( ( right-distributive-mul-add-ℕᵉ mᵉ (dist-ℕᵉ mᵉ nᵉ) (succ-ℕᵉ dᵉ)) ∙ᵉ
          ( commutative-add-ℕᵉ
            ( mᵉ *ℕᵉ (succ-ℕᵉ dᵉ))
            ( (dist-ℕᵉ mᵉ nᵉ) *ℕᵉ (succ-ℕᵉ dᵉ))))) ∙ᵉ
      ( ( apᵉ
          ( _*ℕᵉ (succ-ℕᵉ dᵉ))
          ( is-additive-right-inverse-dist-ℕᵉ mᵉ nᵉ
            ( reflects-order-mul-ℕᵉ dᵉ mᵉ nᵉ
              ( concatenate-eq-leq-eq-ℕᵉ qᵉ
                ( leq-add-ℕ'ᵉ yᵉ xᵉ)
                ( invᵉ pᵉ))))) ∙ᵉ
        ( pᵉ ∙ᵉ (apᵉ (xᵉ +ℕᵉ_) (invᵉ qᵉ)))))

div-right-summand-ℕᵉ :
  (dᵉ xᵉ yᵉ : ℕᵉ) → div-ℕᵉ dᵉ xᵉ → div-ℕᵉ dᵉ (xᵉ +ℕᵉ yᵉ) → div-ℕᵉ dᵉ yᵉ
div-right-summand-ℕᵉ dᵉ xᵉ yᵉ H1ᵉ H2ᵉ =
  div-left-summand-ℕᵉ dᵉ yᵉ xᵉ H1ᵉ (concatenate-div-eq-ℕᵉ H2ᵉ (commutative-add-ℕᵉ xᵉ yᵉ))
```

### If `d` divides both `x` and `x + 1`, then `d ＝ 1`

```agda
is-one-div-ℕᵉ : (xᵉ yᵉ : ℕᵉ) → div-ℕᵉ xᵉ yᵉ → div-ℕᵉ xᵉ (succ-ℕᵉ yᵉ) → is-one-ℕᵉ xᵉ
is-one-div-ℕᵉ xᵉ yᵉ Hᵉ Kᵉ = is-one-div-one-ℕᵉ xᵉ (div-right-summand-ℕᵉ xᵉ yᵉ 1 Hᵉ Kᵉ)
```

### Multiplication preserves divisibility

```agda
preserves-div-mul-ℕᵉ :
  (kᵉ xᵉ yᵉ : ℕᵉ) → div-ℕᵉ xᵉ yᵉ → div-ℕᵉ (kᵉ *ℕᵉ xᵉ) (kᵉ *ℕᵉ yᵉ)
pr1ᵉ (preserves-div-mul-ℕᵉ kᵉ xᵉ yᵉ (pairᵉ qᵉ pᵉ)) = qᵉ
pr2ᵉ (preserves-div-mul-ℕᵉ kᵉ xᵉ yᵉ (pairᵉ qᵉ pᵉ)) =
  ( invᵉ (associative-mul-ℕᵉ qᵉ kᵉ xᵉ)) ∙ᵉ
    ( ( apᵉ (_*ℕᵉ xᵉ) (commutative-mul-ℕᵉ qᵉ kᵉ)) ∙ᵉ
      ( ( associative-mul-ℕᵉ kᵉ qᵉ xᵉ) ∙ᵉ
        ( apᵉ (kᵉ *ℕᵉ_) pᵉ)))
```

### Multiplication by a nonzero number reflects divisibility

```agda
reflects-div-mul-ℕᵉ :
  (kᵉ xᵉ yᵉ : ℕᵉ) → is-nonzero-ℕᵉ kᵉ → div-ℕᵉ (kᵉ *ℕᵉ xᵉ) (kᵉ *ℕᵉ yᵉ) → div-ℕᵉ xᵉ yᵉ
pr1ᵉ (reflects-div-mul-ℕᵉ kᵉ xᵉ yᵉ Hᵉ (pairᵉ qᵉ pᵉ)) = qᵉ
pr2ᵉ (reflects-div-mul-ℕᵉ kᵉ xᵉ yᵉ Hᵉ (pairᵉ qᵉ pᵉ)) =
  is-injective-left-mul-ℕᵉ kᵉ Hᵉ
    ( ( invᵉ (associative-mul-ℕᵉ kᵉ qᵉ xᵉ)) ∙ᵉ
      ( ( apᵉ (_*ℕᵉ xᵉ) (commutative-mul-ℕᵉ kᵉ qᵉ)) ∙ᵉ
        ( ( associative-mul-ℕᵉ qᵉ kᵉ xᵉ) ∙ᵉ
          ( pᵉ))))
```

### If a nonzero number `d` divides `y`, then `dx` divides `y` if and only if `x` divides the quotient `y/d`

```agda
div-quotient-div-div-ℕᵉ :
  (xᵉ yᵉ dᵉ : ℕᵉ) (Hᵉ : div-ℕᵉ dᵉ yᵉ) → is-nonzero-ℕᵉ dᵉ →
  div-ℕᵉ (dᵉ *ℕᵉ xᵉ) yᵉ → div-ℕᵉ xᵉ (quotient-div-ℕᵉ dᵉ yᵉ Hᵉ)
div-quotient-div-div-ℕᵉ xᵉ yᵉ dᵉ Hᵉ fᵉ Kᵉ =
  reflects-div-mul-ℕᵉ dᵉ xᵉ
    ( quotient-div-ℕᵉ dᵉ yᵉ Hᵉ)
    ( fᵉ)
    ( trᵉ (div-ℕᵉ (dᵉ *ℕᵉ xᵉ)) (invᵉ (eq-quotient-div-ℕ'ᵉ dᵉ yᵉ Hᵉ)) Kᵉ)

div-div-quotient-div-ℕᵉ :
  (xᵉ yᵉ dᵉ : ℕᵉ) (Hᵉ : div-ℕᵉ dᵉ yᵉ) →
  div-ℕᵉ xᵉ (quotient-div-ℕᵉ dᵉ yᵉ Hᵉ) → div-ℕᵉ (dᵉ *ℕᵉ xᵉ) yᵉ
div-div-quotient-div-ℕᵉ xᵉ yᵉ dᵉ Hᵉ Kᵉ =
  trᵉ
    ( div-ℕᵉ (dᵉ *ℕᵉ xᵉ))
    ( eq-quotient-div-ℕ'ᵉ dᵉ yᵉ Hᵉ)
    ( preserves-div-mul-ℕᵉ dᵉ xᵉ (quotient-div-ℕᵉ dᵉ yᵉ Hᵉ) Kᵉ)
```

### If `d` divides a nonzero number `x`, then the quotient `x/d` is also nonzero

```agda
is-nonzero-quotient-div-ℕᵉ :
  {dᵉ xᵉ : ℕᵉ} (Hᵉ : div-ℕᵉ dᵉ xᵉ) →
  is-nonzero-ℕᵉ xᵉ → is-nonzero-ℕᵉ (quotient-div-ℕᵉ dᵉ xᵉ Hᵉ)
is-nonzero-quotient-div-ℕᵉ {dᵉ} {.(kᵉ *ℕᵉ dᵉ)} (pairᵉ kᵉ reflᵉ) =
  is-nonzero-left-factor-mul-ℕᵉ kᵉ dᵉ
```

### If `d` divides a number `1 ≤ x`, then `1 ≤ x/d`

```agda
leq-one-quotient-div-ℕᵉ :
  (dᵉ xᵉ : ℕᵉ) (Hᵉ : div-ℕᵉ dᵉ xᵉ) → leq-ℕᵉ 1 xᵉ → leq-ℕᵉ 1 (quotient-div-ℕᵉ dᵉ xᵉ Hᵉ)
leq-one-quotient-div-ℕᵉ dᵉ xᵉ Hᵉ Kᵉ =
  leq-one-div-ℕᵉ
    ( quotient-div-ℕᵉ dᵉ xᵉ Hᵉ)
    ( xᵉ)
    ( div-quotient-div-ℕᵉ dᵉ xᵉ Hᵉ)
    ( Kᵉ)
```

### `a/a ＝ 1`

```agda
is-idempotent-quotient-div-ℕᵉ :
  (aᵉ : ℕᵉ) → is-nonzero-ℕᵉ aᵉ → (Hᵉ : div-ℕᵉ aᵉ aᵉ) → is-one-ℕᵉ (quotient-div-ℕᵉ aᵉ aᵉ Hᵉ)
is-idempotent-quotient-div-ℕᵉ zero-ℕᵉ nzᵉ (uᵉ ,ᵉ pᵉ) = ex-falsoᵉ (nzᵉ reflᵉ)
is-idempotent-quotient-div-ℕᵉ (succ-ℕᵉ aᵉ) nzᵉ (uᵉ ,ᵉ pᵉ) =
  is-one-is-left-unit-mul-ℕᵉ uᵉ aᵉ pᵉ
```

### If `b` divides `a` and `c` divides `b` and `c` is nonzero, then `a/b · b/c ＝ a/c`

```agda
simplify-mul-quotient-div-ℕᵉ :
  {aᵉ bᵉ cᵉ : ℕᵉ} → is-nonzero-ℕᵉ cᵉ →
  (Hᵉ : div-ℕᵉ bᵉ aᵉ) (Kᵉ : div-ℕᵉ cᵉ bᵉ) (Lᵉ : div-ℕᵉ cᵉ aᵉ) →
  ( (quotient-div-ℕᵉ bᵉ aᵉ Hᵉ) *ℕᵉ (quotient-div-ℕᵉ cᵉ bᵉ Kᵉ)) ＝ᵉ
  ( quotient-div-ℕᵉ cᵉ aᵉ Lᵉ)
simplify-mul-quotient-div-ℕᵉ {aᵉ} {bᵉ} {cᵉ} nzᵉ Hᵉ Kᵉ Lᵉ =
  is-injective-right-mul-ℕᵉ cᵉ nzᵉ
    ( equational-reasoningᵉ
      (a/bᵉ *ℕᵉ b/cᵉ) *ℕᵉ cᵉ
      ＝ᵉ a/bᵉ *ℕᵉ (b/cᵉ *ℕᵉ cᵉ)
        byᵉ associative-mul-ℕᵉ a/bᵉ b/cᵉ cᵉ
      ＝ᵉ a/bᵉ *ℕᵉ bᵉ
        byᵉ apᵉ (a/bᵉ *ℕᵉ_) (eq-quotient-div-ℕᵉ cᵉ bᵉ Kᵉ)
      ＝ᵉ aᵉ
        byᵉ eq-quotient-div-ℕᵉ bᵉ aᵉ Hᵉ
      ＝ᵉ a/cᵉ *ℕᵉ cᵉ
        byᵉ invᵉ (eq-quotient-div-ℕᵉ cᵉ aᵉ Lᵉ))
  where
  a/bᵉ : ℕᵉ
  a/bᵉ = quotient-div-ℕᵉ bᵉ aᵉ Hᵉ
  b/cᵉ : ℕᵉ
  b/cᵉ = quotient-div-ℕᵉ cᵉ bᵉ Kᵉ
  a/cᵉ : ℕᵉ
  a/cᵉ = quotient-div-ℕᵉ cᵉ aᵉ Lᵉ
```

### If `d | a` and `d` is nonzero, then `x | a/d` if and only if `xd | a`

```agda
simplify-div-quotient-div-ℕᵉ :
  {aᵉ dᵉ xᵉ : ℕᵉ} → is-nonzero-ℕᵉ dᵉ → (Hᵉ : div-ℕᵉ dᵉ aᵉ) →
  (div-ℕᵉ xᵉ (quotient-div-ℕᵉ dᵉ aᵉ Hᵉ)) ↔ᵉ (div-ℕᵉ (xᵉ *ℕᵉ dᵉ) aᵉ)
pr1ᵉ (pr1ᵉ (simplify-div-quotient-div-ℕᵉ nzᵉ Hᵉ) (uᵉ ,ᵉ pᵉ)) = uᵉ
pr2ᵉ (pr1ᵉ (simplify-div-quotient-div-ℕᵉ {aᵉ} {dᵉ} {xᵉ} nzᵉ Hᵉ) (uᵉ ,ᵉ pᵉ)) =
  equational-reasoningᵉ
    uᵉ *ℕᵉ (xᵉ *ℕᵉ dᵉ)
    ＝ᵉ (uᵉ *ℕᵉ xᵉ) *ℕᵉ dᵉ
      byᵉ invᵉ (associative-mul-ℕᵉ uᵉ xᵉ dᵉ)
    ＝ᵉ (quotient-div-ℕᵉ dᵉ aᵉ Hᵉ) *ℕᵉ dᵉ
      byᵉ apᵉ (_*ℕᵉ dᵉ) pᵉ
    ＝ᵉ aᵉ
      byᵉ eq-quotient-div-ℕᵉ dᵉ aᵉ Hᵉ
pr1ᵉ (pr2ᵉ (simplify-div-quotient-div-ℕᵉ nzᵉ Hᵉ) (uᵉ ,ᵉ pᵉ)) = uᵉ
pr2ᵉ (pr2ᵉ (simplify-div-quotient-div-ℕᵉ {aᵉ} {dᵉ} {xᵉ} nzᵉ Hᵉ) (uᵉ ,ᵉ pᵉ)) =
  is-injective-right-mul-ℕᵉ dᵉ nzᵉ
    ( equational-reasoningᵉ
        (uᵉ *ℕᵉ xᵉ) *ℕᵉ dᵉ
        ＝ᵉ uᵉ *ℕᵉ (xᵉ *ℕᵉ dᵉ)
          byᵉ associative-mul-ℕᵉ uᵉ xᵉ dᵉ
        ＝ᵉ aᵉ
          byᵉ pᵉ
        ＝ᵉ (quotient-div-ℕᵉ dᵉ aᵉ Hᵉ) *ℕᵉ dᵉ
          byᵉ invᵉ (eq-quotient-div-ℕᵉ dᵉ aᵉ Hᵉ))
```

### Suppose `H : b | a` and `K : c | b`, where `c` is nonzero. If `d` divides `b/c` then `d` divides `a/c`

```agda
div-quotient-div-div-quotient-div-ℕᵉ :
  {aᵉ bᵉ cᵉ dᵉ : ℕᵉ} → is-nonzero-ℕᵉ cᵉ → (Hᵉ : div-ℕᵉ bᵉ aᵉ)
  (Kᵉ : div-ℕᵉ cᵉ bᵉ) (Lᵉ : div-ℕᵉ cᵉ aᵉ) →
  div-ℕᵉ dᵉ (quotient-div-ℕᵉ cᵉ bᵉ Kᵉ) →
  div-ℕᵉ dᵉ (quotient-div-ℕᵉ cᵉ aᵉ Lᵉ)
div-quotient-div-div-quotient-div-ℕᵉ {aᵉ} {bᵉ} {cᵉ} {dᵉ} nzᵉ Hᵉ Kᵉ Lᵉ Mᵉ =
  trᵉ
    ( div-ℕᵉ dᵉ)
    ( simplify-mul-quotient-div-ℕᵉ nzᵉ Hᵉ Kᵉ Lᵉ)
    ( div-mul-ℕᵉ
      ( quotient-div-ℕᵉ bᵉ aᵉ Hᵉ)
      ( dᵉ)
      ( quotient-div-ℕᵉ cᵉ bᵉ Kᵉ)
      ( Mᵉ))
```

### If `x` is nonzero and `d | x`, then `x/d ＝ 1` if and only if `d ＝ x`

```agda
is-one-quotient-div-ℕᵉ :
  (dᵉ xᵉ : ℕᵉ) → is-nonzero-ℕᵉ xᵉ → (Hᵉ : div-ℕᵉ dᵉ xᵉ) → (dᵉ ＝ᵉ xᵉ) →
  is-one-ℕᵉ (quotient-div-ℕᵉ dᵉ xᵉ Hᵉ)
is-one-quotient-div-ℕᵉ dᵉ .dᵉ fᵉ Hᵉ reflᵉ = is-idempotent-quotient-div-ℕᵉ dᵉ fᵉ Hᵉ

eq-is-one-quotient-div-ℕᵉ :
  (dᵉ xᵉ : ℕᵉ) → (Hᵉ : div-ℕᵉ dᵉ xᵉ) → is-one-ℕᵉ (quotient-div-ℕᵉ dᵉ xᵉ Hᵉ) → dᵉ ＝ᵉ xᵉ
eq-is-one-quotient-div-ℕᵉ dᵉ xᵉ (.1ᵉ ,ᵉ qᵉ) reflᵉ = invᵉ (left-unit-law-mul-ℕᵉ dᵉ) ∙ᵉ qᵉ
```

### If `x` is nonzero and `d | x`, then `x/d ＝ x` if and only if `d ＝ 1`

```agda
compute-quotient-div-is-one-ℕᵉ :
  (dᵉ xᵉ : ℕᵉ) → (Hᵉ : div-ℕᵉ dᵉ xᵉ) → is-one-ℕᵉ dᵉ → quotient-div-ℕᵉ dᵉ xᵉ Hᵉ ＝ᵉ xᵉ
compute-quotient-div-is-one-ℕᵉ .1ᵉ xᵉ (uᵉ ,ᵉ qᵉ) reflᵉ =
  invᵉ (right-unit-law-mul-ℕᵉ uᵉ) ∙ᵉ qᵉ

is-one-divisor-ℕᵉ :
  (dᵉ xᵉ : ℕᵉ) → is-nonzero-ℕᵉ xᵉ → (Hᵉ : div-ℕᵉ dᵉ xᵉ) →
  quotient-div-ℕᵉ dᵉ xᵉ Hᵉ ＝ᵉ xᵉ → is-one-ℕᵉ dᵉ
is-one-divisor-ℕᵉ dᵉ xᵉ fᵉ (.xᵉ ,ᵉ qᵉ) reflᵉ =
  is-injective-left-mul-ℕᵉ xᵉ fᵉ (qᵉ ∙ᵉ invᵉ (right-unit-law-mul-ℕᵉ xᵉ))
```

### If `x` is nonzero and `d | x` is a nontrivial divisor, then `x/d < x`

```agda
le-quotient-div-ℕᵉ :
  (dᵉ xᵉ : ℕᵉ) → is-nonzero-ℕᵉ xᵉ → (Hᵉ : div-ℕᵉ dᵉ xᵉ) → ¬ᵉ (is-one-ℕᵉ dᵉ) →
  le-ℕᵉ (quotient-div-ℕᵉ dᵉ xᵉ Hᵉ) xᵉ
le-quotient-div-ℕᵉ dᵉ xᵉ fᵉ Hᵉ gᵉ =
  map-left-unit-law-coproduct-is-emptyᵉ
    ( quotient-div-ℕᵉ dᵉ xᵉ Hᵉ ＝ᵉ xᵉ)
    ( le-ℕᵉ (quotient-div-ℕᵉ dᵉ xᵉ Hᵉ) xᵉ)
    ( map-negᵉ (is-one-divisor-ℕᵉ dᵉ xᵉ fᵉ Hᵉ) gᵉ)
    ( eq-or-le-leq-ℕᵉ
      ( quotient-div-ℕᵉ dᵉ xᵉ Hᵉ)
      ( xᵉ)
      ( leq-quotient-div-ℕᵉ dᵉ xᵉ fᵉ Hᵉ))
```