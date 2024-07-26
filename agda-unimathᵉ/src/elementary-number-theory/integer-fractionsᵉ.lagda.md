# Integer fractions

```agda
module elementary-number-theory.integer-fractionsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.greatest-common-divisor-integersᵉ
open import elementary-number-theory.integersᵉ
open import elementary-number-theory.multiplication-integersᵉ
open import elementary-number-theory.nonzero-integersᵉ
open import elementary-number-theory.positive-and-negative-integersᵉ
open import elementary-number-theory.positive-integersᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.binary-relationsᵉ
open import foundation.cartesian-product-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalence-relationsᵉ
open import foundation.identity-typesᵉ
open import foundation.negationᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Theᵉ typeᵉ ofᵉ integerᵉ fractionsᵉ isᵉ theᵉ typeᵉ ofᵉ pairsᵉ `n/m`ᵉ consistingᵉ ofᵉ anᵉ
integerᵉ `n`ᵉ andᵉ aᵉ positiveᵉ integerᵉ `m`.ᵉ Theᵉ typeᵉ ofᵉ rationalᵉ numbersᵉ isᵉ aᵉ
retractᵉ ofᵉ theᵉ typeᵉ ofᵉ fractions.ᵉ

## Definitions

### The type of fractions

```agda
fraction-ℤᵉ : UUᵉ lzero
fraction-ℤᵉ = ℤᵉ ×ᵉ positive-ℤᵉ
```

### The numerator of a fraction

```agda
numerator-fraction-ℤᵉ : fraction-ℤᵉ → ℤᵉ
numerator-fraction-ℤᵉ xᵉ = pr1ᵉ xᵉ
```

### The denominator of a fraction

```agda
positive-denominator-fraction-ℤᵉ : fraction-ℤᵉ → positive-ℤᵉ
positive-denominator-fraction-ℤᵉ xᵉ = pr2ᵉ xᵉ

denominator-fraction-ℤᵉ : fraction-ℤᵉ → ℤᵉ
denominator-fraction-ℤᵉ xᵉ = pr1ᵉ (positive-denominator-fraction-ℤᵉ xᵉ)

is-positive-denominator-fraction-ℤᵉ :
  (xᵉ : fraction-ℤᵉ) → is-positive-ℤᵉ (denominator-fraction-ℤᵉ xᵉ)
is-positive-denominator-fraction-ℤᵉ xᵉ = pr2ᵉ (positive-denominator-fraction-ℤᵉ xᵉ)
```

### Inclusion of the integers

```agda
in-fraction-ℤᵉ : ℤᵉ → fraction-ℤᵉ
pr1ᵉ (in-fraction-ℤᵉ xᵉ) = xᵉ
pr2ᵉ (in-fraction-ℤᵉ xᵉ) = one-positive-ℤᵉ
```

### Negative one, zero and one

```agda
neg-one-fraction-ℤᵉ : fraction-ℤᵉ
neg-one-fraction-ℤᵉ = in-fraction-ℤᵉ neg-one-ℤᵉ

is-neg-one-fraction-ℤᵉ : fraction-ℤᵉ → UUᵉ lzero
is-neg-one-fraction-ℤᵉ xᵉ = (xᵉ ＝ᵉ neg-one-fraction-ℤᵉ)

zero-fraction-ℤᵉ : fraction-ℤᵉ
zero-fraction-ℤᵉ = in-fraction-ℤᵉ zero-ℤᵉ

is-zero-fraction-ℤᵉ : fraction-ℤᵉ → UUᵉ lzero
is-zero-fraction-ℤᵉ xᵉ = (xᵉ ＝ᵉ zero-fraction-ℤᵉ)

is-nonzero-fraction-ℤᵉ : fraction-ℤᵉ → UUᵉ lzero
is-nonzero-fraction-ℤᵉ kᵉ = ¬ᵉ (is-zero-fraction-ℤᵉ kᵉ)

one-fraction-ℤᵉ : fraction-ℤᵉ
one-fraction-ℤᵉ = in-fraction-ℤᵉ one-ℤᵉ

is-one-fraction-ℤᵉ : fraction-ℤᵉ → UUᵉ lzero
is-one-fraction-ℤᵉ xᵉ = (xᵉ ＝ᵉ one-fraction-ℤᵉ)
```

### The negative of an integer fraction

```agda
neg-fraction-ℤᵉ : fraction-ℤᵉ → fraction-ℤᵉ
neg-fraction-ℤᵉ (dᵉ ,ᵉ nᵉ) = (neg-ℤᵉ dᵉ ,ᵉ nᵉ)
```

## Properties

### Denominators are nonzero

```agda
abstract
  is-nonzero-denominator-fraction-ℤᵉ :
    (xᵉ : fraction-ℤᵉ) → is-nonzero-ℤᵉ (denominator-fraction-ℤᵉ xᵉ)
  is-nonzero-denominator-fraction-ℤᵉ xᵉ =
    is-nonzero-is-positive-ℤᵉ (is-positive-denominator-fraction-ℤᵉ xᵉ)
```

### The type of fractions is a set

```agda
abstract
  is-set-fraction-ℤᵉ : is-setᵉ fraction-ℤᵉ
  is-set-fraction-ℤᵉ = is-set-Σᵉ is-set-ℤᵉ (λ _ → is-set-positive-ℤᵉ)
```

```agda
sim-fraction-ℤ-Propᵉ : fraction-ℤᵉ → fraction-ℤᵉ → Propᵉ lzero
sim-fraction-ℤ-Propᵉ xᵉ yᵉ =
  Id-Propᵉ ℤ-Setᵉ
    ((numerator-fraction-ℤᵉ xᵉ) *ℤᵉ (denominator-fraction-ℤᵉ yᵉ))
    ((numerator-fraction-ℤᵉ yᵉ) *ℤᵉ (denominator-fraction-ℤᵉ xᵉ))

sim-fraction-ℤᵉ : fraction-ℤᵉ → fraction-ℤᵉ → UUᵉ lzero
sim-fraction-ℤᵉ xᵉ yᵉ = type-Propᵉ (sim-fraction-ℤ-Propᵉ xᵉ yᵉ)

is-prop-sim-fraction-ℤᵉ : (xᵉ yᵉ : fraction-ℤᵉ) → is-propᵉ (sim-fraction-ℤᵉ xᵉ yᵉ)
is-prop-sim-fraction-ℤᵉ xᵉ yᵉ = is-prop-type-Propᵉ (sim-fraction-ℤ-Propᵉ xᵉ yᵉ)

refl-sim-fraction-ℤᵉ : is-reflexiveᵉ sim-fraction-ℤᵉ
refl-sim-fraction-ℤᵉ xᵉ = reflᵉ

symmetric-sim-fraction-ℤᵉ : is-symmetricᵉ sim-fraction-ℤᵉ
symmetric-sim-fraction-ℤᵉ xᵉ yᵉ rᵉ = invᵉ rᵉ

abstract
  transitive-sim-fraction-ℤᵉ : is-transitiveᵉ sim-fraction-ℤᵉ
  transitive-sim-fraction-ℤᵉ xᵉ yᵉ zᵉ sᵉ rᵉ =
    is-injective-right-mul-ℤᵉ
      ( denominator-fraction-ℤᵉ yᵉ)
      ( is-nonzero-denominator-fraction-ℤᵉ yᵉ)
      ( ( associative-mul-ℤᵉ
          ( numerator-fraction-ℤᵉ xᵉ)
          ( denominator-fraction-ℤᵉ zᵉ)
          ( denominator-fraction-ℤᵉ yᵉ)) ∙ᵉ
        ( apᵉ
          ( (numerator-fraction-ℤᵉ xᵉ) *ℤᵉ_)
          ( commutative-mul-ℤᵉ
            ( denominator-fraction-ℤᵉ zᵉ)
            ( denominator-fraction-ℤᵉ yᵉ))) ∙ᵉ
        ( invᵉ
          ( associative-mul-ℤᵉ
            ( numerator-fraction-ℤᵉ xᵉ)
            ( denominator-fraction-ℤᵉ yᵉ)
            ( denominator-fraction-ℤᵉ zᵉ))) ∙ᵉ
        ( apᵉ ( _*ℤᵉ (denominator-fraction-ℤᵉ zᵉ)) rᵉ) ∙ᵉ
        ( associative-mul-ℤᵉ
          ( numerator-fraction-ℤᵉ yᵉ)
          ( denominator-fraction-ℤᵉ xᵉ)
          ( denominator-fraction-ℤᵉ zᵉ)) ∙ᵉ
        ( apᵉ
          ( (numerator-fraction-ℤᵉ yᵉ) *ℤᵉ_)
          ( commutative-mul-ℤᵉ
            ( denominator-fraction-ℤᵉ xᵉ)
            ( denominator-fraction-ℤᵉ zᵉ))) ∙ᵉ
        ( invᵉ
          ( associative-mul-ℤᵉ
            ( numerator-fraction-ℤᵉ yᵉ)
            ( denominator-fraction-ℤᵉ zᵉ)
            ( denominator-fraction-ℤᵉ xᵉ))) ∙ᵉ
        ( apᵉ (_*ℤᵉ (denominator-fraction-ℤᵉ xᵉ)) sᵉ) ∙ᵉ
        ( associative-mul-ℤᵉ
          ( numerator-fraction-ℤᵉ zᵉ)
          ( denominator-fraction-ℤᵉ yᵉ)
          ( denominator-fraction-ℤᵉ xᵉ)) ∙ᵉ
        ( apᵉ
          ( (numerator-fraction-ℤᵉ zᵉ) *ℤᵉ_)
          ( commutative-mul-ℤᵉ
            ( denominator-fraction-ℤᵉ yᵉ)
            ( denominator-fraction-ℤᵉ xᵉ))) ∙ᵉ
        ( invᵉ
          ( associative-mul-ℤᵉ
            ( numerator-fraction-ℤᵉ zᵉ)
            ( denominator-fraction-ℤᵉ xᵉ)
            ( denominator-fraction-ℤᵉ yᵉ))))

equivalence-relation-sim-fraction-ℤᵉ : equivalence-relationᵉ lzero fraction-ℤᵉ
pr1ᵉ equivalence-relation-sim-fraction-ℤᵉ = sim-fraction-ℤ-Propᵉ
pr1ᵉ (pr2ᵉ equivalence-relation-sim-fraction-ℤᵉ) = refl-sim-fraction-ℤᵉ
pr1ᵉ (pr2ᵉ (pr2ᵉ equivalence-relation-sim-fraction-ℤᵉ)) = symmetric-sim-fraction-ℤᵉ
pr2ᵉ (pr2ᵉ (pr2ᵉ equivalence-relation-sim-fraction-ℤᵉ)) = transitive-sim-fraction-ℤᵉ
```

### The negatives of two similar integer fractions are similar

```agda
module _
  (xᵉ yᵉ : fraction-ℤᵉ)
  where

  abstract
    preserves-sim-neg-fraction-ℤᵉ :
      sim-fraction-ℤᵉ xᵉ yᵉ → sim-fraction-ℤᵉ (neg-fraction-ℤᵉ xᵉ) (neg-fraction-ℤᵉ yᵉ)
    preserves-sim-neg-fraction-ℤᵉ Hᵉ =
      ( left-negative-law-mul-ℤᵉ
        ( numerator-fraction-ℤᵉ xᵉ)
        ( denominator-fraction-ℤᵉ yᵉ)) ∙ᵉ
      ( apᵉ neg-ℤᵉ Hᵉ) ∙ᵉ
      ( invᵉ
        ( left-negative-law-mul-ℤᵉ
          ( numerator-fraction-ℤᵉ yᵉ)
          ( denominator-fraction-ℤᵉ xᵉ)))
```

### Two integer fractions with zero numerator are similar

```agda
abstract
  sim-is-zero-numerator-fraction-ℤᵉ :
    (xᵉ yᵉ : fraction-ℤᵉ) →
    is-zero-ℤᵉ (numerator-fraction-ℤᵉ xᵉ) →
    is-zero-ℤᵉ (numerator-fraction-ℤᵉ yᵉ) →
    sim-fraction-ℤᵉ xᵉ yᵉ
  sim-is-zero-numerator-fraction-ℤᵉ xᵉ yᵉ Hᵉ Kᵉ =
    eq-is-zero-ℤᵉ
    ( apᵉ (_*ℤᵉ (denominator-fraction-ℤᵉ yᵉ)) Hᵉ ∙ᵉ
      left-zero-law-mul-ℤᵉ (denominator-fraction-ℤᵉ yᵉ))
    ( apᵉ (_*ℤᵉ (denominator-fraction-ℤᵉ xᵉ)) Kᵉ ∙ᵉ
      left-zero-law-mul-ℤᵉ (denominator-fraction-ℤᵉ xᵉ))
```

### The greatest common divisor of the numerator and a denominator of a fraction is always a positive integer

```agda
abstract
  is-positive-gcd-numerator-denominator-fraction-ℤᵉ :
    (xᵉ : fraction-ℤᵉ) →
    is-positive-ℤᵉ (gcd-ℤᵉ (numerator-fraction-ℤᵉ xᵉ) (denominator-fraction-ℤᵉ xᵉ))
  is-positive-gcd-numerator-denominator-fraction-ℤᵉ xᵉ =
    is-positive-gcd-is-positive-right-ℤᵉ
      ( numerator-fraction-ℤᵉ xᵉ)
      ( denominator-fraction-ℤᵉ xᵉ)
      ( is-positive-denominator-fraction-ℤᵉ xᵉ)

abstract
  is-nonzero-gcd-numerator-denominator-fraction-ℤᵉ :
    (xᵉ : fraction-ℤᵉ) →
    is-nonzero-ℤᵉ (gcd-ℤᵉ (numerator-fraction-ℤᵉ xᵉ) (denominator-fraction-ℤᵉ xᵉ))
  is-nonzero-gcd-numerator-denominator-fraction-ℤᵉ xᵉ =
    is-nonzero-is-positive-ℤᵉ
      ( is-positive-gcd-numerator-denominator-fraction-ℤᵉ xᵉ)
```