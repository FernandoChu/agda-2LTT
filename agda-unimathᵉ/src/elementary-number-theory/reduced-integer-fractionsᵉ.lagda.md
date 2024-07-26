# Reduced integer fractions

```agda
module elementary-number-theory.reduced-integer-fractionsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.bezouts-lemma-integersᵉ
open import elementary-number-theory.divisibility-integersᵉ
open import elementary-number-theory.equality-integersᵉ
open import elementary-number-theory.greatest-common-divisor-integersᵉ
open import elementary-number-theory.integer-fractionsᵉ
open import elementary-number-theory.integersᵉ
open import elementary-number-theory.multiplication-integersᵉ
open import elementary-number-theory.multiplication-positive-and-negative-integersᵉ
open import elementary-number-theory.natural-numbersᵉ
open import elementary-number-theory.positive-and-negative-integersᵉ
open import elementary-number-theory.positive-integersᵉ
open import elementary-number-theory.relatively-prime-integersᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.coproduct-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.empty-typesᵉ
open import foundation.equality-cartesian-product-typesᵉ
open import foundation.equality-dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.negationᵉ
open import foundation.propositionsᵉ
open import foundation.subtypesᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Aᵉ reducedᵉ fractionᵉ isᵉ aᵉ fractionᵉ in whichᵉ itsᵉ numeratorᵉ andᵉ denominatorᵉ areᵉ
coprime.ᵉ

## Definitions

### Reduced fraction

```agda
is-reduced-fraction-ℤᵉ : fraction-ℤᵉ → UUᵉ lzero
is-reduced-fraction-ℤᵉ xᵉ =
  is-relative-prime-ℤᵉ (numerator-fraction-ℤᵉ xᵉ) (denominator-fraction-ℤᵉ xᵉ)
```

## Properties and constructions

### Being a reduced fraction is a proposition

```agda
is-prop-is-reduced-fraction-ℤᵉ :
  (xᵉ : fraction-ℤᵉ) → is-propᵉ (is-reduced-fraction-ℤᵉ xᵉ)
is-prop-is-reduced-fraction-ℤᵉ xᵉ =
  is-prop-is-relative-prime-ℤᵉ
    ( numerator-fraction-ℤᵉ xᵉ)
    ( denominator-fraction-ℤᵉ xᵉ)
```

### The negative of a reduced integer fraction is reduced

```agda
is-reduced-neg-fraction-ℤᵉ :
  (xᵉ : fraction-ℤᵉ) →
  is-reduced-fraction-ℤᵉ xᵉ →
  is-reduced-fraction-ℤᵉ (neg-fraction-ℤᵉ xᵉ)
is-reduced-neg-fraction-ℤᵉ xᵉ =
  trᵉ
    ( is-one-ℤᵉ)
    ( invᵉ
      ( preserves-gcd-left-neg-ℤᵉ
        ( numerator-fraction-ℤᵉ xᵉ)
        ( denominator-fraction-ℤᵉ xᵉ)))
```

### Any fraction can be reduced

```agda
reduce-numerator-fraction-ℤᵉ :
  (xᵉ : fraction-ℤᵉ) →
  div-ℤᵉ
    ( gcd-ℤᵉ (numerator-fraction-ℤᵉ xᵉ) (denominator-fraction-ℤᵉ xᵉ))
    ( numerator-fraction-ℤᵉ xᵉ)
reduce-numerator-fraction-ℤᵉ xᵉ =
  div-left-gcd-ℤᵉ (numerator-fraction-ℤᵉ xᵉ) (denominator-fraction-ℤᵉ xᵉ)

int-reduce-numerator-fraction-ℤᵉ : fraction-ℤᵉ → ℤᵉ
int-reduce-numerator-fraction-ℤᵉ xᵉ = pr1ᵉ (reduce-numerator-fraction-ℤᵉ xᵉ)

eq-reduce-numerator-fraction-ℤᵉ :
  (xᵉ : fraction-ℤᵉ) →
  ( mul-ℤᵉ
    ( int-reduce-numerator-fraction-ℤᵉ xᵉ)
    ( gcd-ℤᵉ (numerator-fraction-ℤᵉ xᵉ) (denominator-fraction-ℤᵉ xᵉ))) ＝ᵉ
  ( numerator-fraction-ℤᵉ xᵉ)
eq-reduce-numerator-fraction-ℤᵉ xᵉ = pr2ᵉ (reduce-numerator-fraction-ℤᵉ xᵉ)

reduce-denominator-fraction-ℤᵉ :
  (xᵉ : fraction-ℤᵉ) →
  div-ℤᵉ
    ( gcd-ℤᵉ (numerator-fraction-ℤᵉ xᵉ) (denominator-fraction-ℤᵉ xᵉ))
    ( denominator-fraction-ℤᵉ xᵉ)
reduce-denominator-fraction-ℤᵉ xᵉ =
  div-right-gcd-ℤᵉ (numerator-fraction-ℤᵉ xᵉ) (denominator-fraction-ℤᵉ xᵉ)

int-reduce-denominator-fraction-ℤᵉ : fraction-ℤᵉ → ℤᵉ
int-reduce-denominator-fraction-ℤᵉ xᵉ =
  pr1ᵉ (reduce-denominator-fraction-ℤᵉ xᵉ)

eq-reduce-denominator-fraction-ℤᵉ :
  (xᵉ : fraction-ℤᵉ) →
  ( mul-ℤᵉ
    ( int-reduce-denominator-fraction-ℤᵉ xᵉ)
    ( gcd-ℤᵉ (numerator-fraction-ℤᵉ xᵉ) (denominator-fraction-ℤᵉ xᵉ))) ＝ᵉ
  ( denominator-fraction-ℤᵉ xᵉ)
eq-reduce-denominator-fraction-ℤᵉ xᵉ =
  pr2ᵉ (reduce-denominator-fraction-ℤᵉ xᵉ)

is-positive-int-reduce-denominator-fraction-ℤᵉ :
  (xᵉ : fraction-ℤᵉ) → is-positive-ℤᵉ (int-reduce-denominator-fraction-ℤᵉ xᵉ)
is-positive-int-reduce-denominator-fraction-ℤᵉ xᵉ =
  is-positive-left-factor-mul-ℤᵉ
    ( is-positive-eq-ℤᵉ
      ( invᵉ (eq-reduce-denominator-fraction-ℤᵉ xᵉ))
      ( is-positive-denominator-fraction-ℤᵉ xᵉ))
    ( is-positive-gcd-is-positive-right-ℤᵉ
      ( numerator-fraction-ℤᵉ xᵉ)
      ( denominator-fraction-ℤᵉ xᵉ)
      ( is-positive-denominator-fraction-ℤᵉ xᵉ))

reduce-fraction-ℤᵉ : fraction-ℤᵉ → fraction-ℤᵉ
reduce-fraction-ℤᵉ xᵉ =
  pairᵉ
    ( int-reduce-numerator-fraction-ℤᵉ xᵉ)
    ( pairᵉ
      ( int-reduce-denominator-fraction-ℤᵉ xᵉ)
      ( is-positive-int-reduce-denominator-fraction-ℤᵉ xᵉ))

is-reduced-reduce-fraction-ℤᵉ :
  (xᵉ : fraction-ℤᵉ) → is-reduced-fraction-ℤᵉ (reduce-fraction-ℤᵉ xᵉ)
is-reduced-reduce-fraction-ℤᵉ xᵉ =
  is-zero-gcd-case-splitᵉ
    ( is-decidable-is-zero-ℤᵉ
      ( gcd-ℤᵉ
        ( numerator-fraction-ℤᵉ (reduce-fraction-ℤᵉ xᵉ))
        ( denominator-fraction-ℤᵉ (reduce-fraction-ℤᵉ xᵉ))))
  where
  is-zero-gcd-case-splitᵉ :
    ( is-zero-ℤᵉ
      ( gcd-ℤᵉ
        ( numerator-fraction-ℤᵉ (reduce-fraction-ℤᵉ xᵉ))
        ( denominator-fraction-ℤᵉ (reduce-fraction-ℤᵉ xᵉ))) +ᵉ
      ¬ᵉ (is-zero-ℤᵉ
        ( gcd-ℤᵉ
          ( numerator-fraction-ℤᵉ (reduce-fraction-ℤᵉ xᵉ))
          ( denominator-fraction-ℤᵉ (reduce-fraction-ℤᵉ xᵉ))))) →
    is-reduced-fraction-ℤᵉ (reduce-fraction-ℤᵉ xᵉ)
  is-zero-gcd-case-splitᵉ (inlᵉ zᵉ) =
    ex-falsoᵉ (trᵉ is-positive-ℤᵉ
      ( is-zero-right-is-zero-gcd-ℤᵉ
        ( numerator-fraction-ℤᵉ (reduce-fraction-ℤᵉ xᵉ))
          ( denominator-fraction-ℤᵉ (reduce-fraction-ℤᵉ xᵉ)) zᵉ)
          ( is-positive-denominator-fraction-ℤᵉ (reduce-fraction-ℤᵉ xᵉ)))
  is-zero-gcd-case-splitᵉ (inrᵉ nzᵉ) =
    is-plus-or-minus-case-splitᵉ
      ( is-plus-or-minus-sim-unit-ℤᵉ
      ( antisymmetric-div-ℤᵉ (alphaᵉ *ℤᵉ dᵉ) dᵉ
        ( div-gcd-is-common-divisor-ℤᵉ
          ( numerator-fraction-ℤᵉ xᵉ)
          ( denominator-fraction-ℤᵉ xᵉ)
          ( alphaᵉ *ℤᵉ dᵉ)
          ( pairᵉ
            --ᵉ alphaᵉ *ᵉ dᵉ dividesᵉ theᵉ numeratorᵉ ofᵉ xᵉ
            ( trᵉ
              ( λ uᵉ → div-ℤᵉ uᵉ (numerator-fraction-ℤᵉ xᵉ))
              ( commutative-mul-ℤᵉ dᵉ alphaᵉ)
              ( div-div-quotient-div-ℤᵉ alphaᵉ (numerator-fraction-ℤᵉ xᵉ) dᵉ
                ( pr1ᵉ ( is-common-divisor-gcd-ℤᵉ
                  ( numerator-fraction-ℤᵉ xᵉ)
                  ( denominator-fraction-ℤᵉ xᵉ)))
                ( pr1ᵉ ( is-common-divisor-gcd-ℤᵉ
                  ( numerator-fraction-ℤᵉ (reduce-fraction-ℤᵉ xᵉ))
                  ( denominator-fraction-ℤᵉ (reduce-fraction-ℤᵉ xᵉ))))))
            --ᵉ alphaᵉ *ᵉ dᵉ dividesᵉ theᵉ denominatorᵉ ofᵉ xᵉ
            ( trᵉ
              ( λ uᵉ → div-ℤᵉ uᵉ (denominator-fraction-ℤᵉ xᵉ))
              ( commutative-mul-ℤᵉ dᵉ alphaᵉ)
              ( div-div-quotient-div-ℤᵉ alphaᵉ (denominator-fraction-ℤᵉ xᵉ) dᵉ
                ( pr2ᵉ ( is-common-divisor-gcd-ℤᵉ
                  ( numerator-fraction-ℤᵉ xᵉ)
                  ( denominator-fraction-ℤᵉ xᵉ)))
                ( pr2ᵉ ( is-common-divisor-gcd-ℤᵉ
                  ( numerator-fraction-ℤᵉ (reduce-fraction-ℤᵉ xᵉ))
                  ( denominator-fraction-ℤᵉ (reduce-fraction-ℤᵉ xᵉ))))))))
        (pairᵉ ( gcd-ℤᵉ ( numerator-fraction-ℤᵉ (reduce-fraction-ℤᵉ xᵉ))
          ( denominator-fraction-ℤᵉ (reduce-fraction-ℤᵉ xᵉ))) reflᵉ)))
    where
    alphaᵉ : ℤᵉ
    alphaᵉ =
      gcd-ℤᵉ
        ( numerator-fraction-ℤᵉ (reduce-fraction-ℤᵉ xᵉ))
        ( denominator-fraction-ℤᵉ (reduce-fraction-ℤᵉ xᵉ))
    dᵉ : ℤᵉ
    dᵉ = gcd-ℤᵉ (numerator-fraction-ℤᵉ xᵉ) (denominator-fraction-ℤᵉ xᵉ)
    is-plus-or-minus-case-splitᵉ :
      (is-plus-or-minus-ℤᵉ (alphaᵉ *ℤᵉ dᵉ) dᵉ) →
      is-reduced-fraction-ℤᵉ (reduce-fraction-ℤᵉ xᵉ)
    is-plus-or-minus-case-splitᵉ (inlᵉ posᵉ) =
      ( is-injective-right-mul-ℤᵉ dᵉ
        ( λ rᵉ → trᵉ is-positive-ℤᵉ rᵉ
          ( is-positive-gcd-is-positive-right-ℤᵉ
            ( numerator-fraction-ℤᵉ xᵉ) ( denominator-fraction-ℤᵉ xᵉ)
            ( is-positive-denominator-fraction-ℤᵉ xᵉ)))) posᵉ
    is-plus-or-minus-case-splitᵉ (inrᵉ negᵉ) =
      (ex-falsoᵉ
        ( trᵉ is-positive-ℤᵉ {yᵉ = neg-ℤᵉ one-ℤᵉ}
          ( invᵉ
            ( neg-neg-ℤᵉ
              ( gcd-ℤᵉ
                ( numerator-fraction-ℤᵉ (reduce-fraction-ℤᵉ xᵉ))
                ( denominator-fraction-ℤᵉ (reduce-fraction-ℤᵉ xᵉ)))) ∙ᵉ
            ( apᵉ neg-ℤᵉ
              ( is-injective-right-mul-ℤᵉ dᵉ
                ( λ rᵉ →
                  trᵉ is-positive-ℤᵉ rᵉ
                    ( is-positive-gcd-is-positive-right-ℤᵉ
                      ( numerator-fraction-ℤᵉ xᵉ)
                      ( denominator-fraction-ℤᵉ xᵉ)
                      ( is-positive-denominator-fraction-ℤᵉ xᵉ)))
                ( associative-mul-ℤᵉ
                  ( neg-one-ℤᵉ)
                  ( gcd-ℤᵉ ( numerator-fraction-ℤᵉ (reduce-fraction-ℤᵉ xᵉ))
              ( denominator-fraction-ℤᵉ (reduce-fraction-ℤᵉ xᵉ)))
              dᵉ ∙ᵉ negᵉ))))
          ( is-positive-gcd-ℤᵉ
            ( numerator-fraction-ℤᵉ (reduce-fraction-ℤᵉ xᵉ))
            ( denominator-fraction-ℤᵉ (reduce-fraction-ℤᵉ xᵉ))
            ( inrᵉ (is-positive-denominator-fraction-ℤᵉ (reduce-fraction-ℤᵉ xᵉ))))))

sim-reduced-fraction-ℤᵉ :
  (xᵉ : fraction-ℤᵉ) → (sim-fraction-ℤᵉ xᵉ (reduce-fraction-ℤᵉ xᵉ))
sim-reduced-fraction-ℤᵉ xᵉ =
  equational-reasoningᵉ
    (numerator-fraction-ℤᵉ xᵉ) *ℤᵉ (denominator-fraction-ℤᵉ (reduce-fraction-ℤᵉ xᵉ))
    ＝ᵉ ((numerator-fraction-ℤᵉ (reduce-fraction-ℤᵉ xᵉ)) *ℤᵉ
        (gcd-ℤᵉ (numerator-fraction-ℤᵉ xᵉ) (denominator-fraction-ℤᵉ xᵉ))) *ℤᵉ
        (denominator-fraction-ℤᵉ (reduce-fraction-ℤᵉ xᵉ))
      byᵉ apᵉ (_*ℤᵉ (denominator-fraction-ℤᵉ (reduce-fraction-ℤᵉ xᵉ)))
          (invᵉ (eq-reduce-numerator-fraction-ℤᵉ xᵉ))
    ＝ᵉ (numerator-fraction-ℤᵉ (reduce-fraction-ℤᵉ xᵉ)) *ℤᵉ
      ((gcd-ℤᵉ (numerator-fraction-ℤᵉ xᵉ) (denominator-fraction-ℤᵉ xᵉ)) *ℤᵉ
        (denominator-fraction-ℤᵉ (reduce-fraction-ℤᵉ xᵉ)))
      byᵉ associative-mul-ℤᵉ (numerator-fraction-ℤᵉ (reduce-fraction-ℤᵉ xᵉ))
        (gcd-ℤᵉ (numerator-fraction-ℤᵉ xᵉ) (denominator-fraction-ℤᵉ xᵉ))
        (denominator-fraction-ℤᵉ (reduce-fraction-ℤᵉ xᵉ))
    ＝ᵉ (numerator-fraction-ℤᵉ (reduce-fraction-ℤᵉ xᵉ)) *ℤᵉ (denominator-fraction-ℤᵉ xᵉ)
      byᵉ
        apᵉ
        ( (numerator-fraction-ℤᵉ (reduce-fraction-ℤᵉ xᵉ)) *ℤᵉ_)
        ( ( commutative-mul-ℤᵉ
            ( gcd-ℤᵉ (numerator-fraction-ℤᵉ xᵉ) (denominator-fraction-ℤᵉ xᵉ))
            ( denominator-fraction-ℤᵉ (reduce-fraction-ℤᵉ xᵉ))) ∙ᵉ
          ( eq-reduce-denominator-fraction-ℤᵉ xᵉ))

reduce-preserves-sim-ℤᵉ :
  (xᵉ yᵉ : fraction-ℤᵉ) (Hᵉ : sim-fraction-ℤᵉ xᵉ yᵉ) →
  sim-fraction-ℤᵉ (reduce-fraction-ℤᵉ xᵉ) (reduce-fraction-ℤᵉ yᵉ)
reduce-preserves-sim-ℤᵉ xᵉ yᵉ Hᵉ =
  transitive-sim-fraction-ℤᵉ
    ( reduce-fraction-ℤᵉ xᵉ)
    ( yᵉ)
    ( reduce-fraction-ℤᵉ yᵉ)
    ( sim-reduced-fraction-ℤᵉ yᵉ)
    ( transitive-sim-fraction-ℤᵉ
      ( reduce-fraction-ℤᵉ xᵉ)
      ( xᵉ)
      ( yᵉ)
      ( Hᵉ)
      ( symmetric-sim-fraction-ℤᵉ
        ( xᵉ)
        ( reduce-fraction-ℤᵉ xᵉ)
        ( sim-reduced-fraction-ℤᵉ xᵉ)))
```

### Two similar fractions have equal reduced form

```agda
sim-unique-numerator-reduce-fraction-ℤᵉ :
  ( xᵉ yᵉ : fraction-ℤᵉ) →
  ( Hᵉ : sim-fraction-ℤᵉ xᵉ yᵉ) →
  sim-unit-ℤᵉ
    ( int-reduce-numerator-fraction-ℤᵉ xᵉ)
    ( int-reduce-numerator-fraction-ℤᵉ yᵉ)
sim-unique-numerator-reduce-fraction-ℤᵉ xᵉ yᵉ Hᵉ =
  antisymmetric-div-ℤᵉ
    ( int-reduce-numerator-fraction-ℤᵉ xᵉ)
    ( int-reduce-numerator-fraction-ℤᵉ yᵉ)
    ( div-red-x-red-yᵉ)
    ( div-red-y-red-xᵉ)
  where
  reduced-eqnᵉ :
    mul-ℤᵉ
      ( int-reduce-numerator-fraction-ℤᵉ xᵉ)
      ( int-reduce-denominator-fraction-ℤᵉ yᵉ) ＝ᵉ
    mul-ℤᵉ
      ( int-reduce-numerator-fraction-ℤᵉ yᵉ)
      ( int-reduce-denominator-fraction-ℤᵉ xᵉ)
  reduced-eqnᵉ = reduce-preserves-sim-ℤᵉ xᵉ yᵉ Hᵉ
  div-red-x-numᵉ :
    div-ℤᵉ
      ( int-reduce-numerator-fraction-ℤᵉ xᵉ)
      ( mul-ℤᵉ
        ( int-reduce-denominator-fraction-ℤᵉ xᵉ)
        ( int-reduce-numerator-fraction-ℤᵉ yᵉ))
  div-red-x-numᵉ =
    pairᵉ
      ( int-reduce-denominator-fraction-ℤᵉ yᵉ)
      ( commutative-mul-ℤᵉ
        ( int-reduce-denominator-fraction-ℤᵉ yᵉ)
        ( int-reduce-numerator-fraction-ℤᵉ xᵉ) ∙ᵉ
        ( reduced-eqnᵉ ∙ᵉ
          commutative-mul-ℤᵉ
            ( int-reduce-numerator-fraction-ℤᵉ yᵉ)
            ( int-reduce-denominator-fraction-ℤᵉ xᵉ)))
  red-x-coprimeᵉ :
    gcd-ℤᵉ
      ( int-reduce-numerator-fraction-ℤᵉ xᵉ)
      ( int-reduce-denominator-fraction-ℤᵉ xᵉ) ＝ᵉ
    one-ℤᵉ
  red-x-coprimeᵉ = is-reduced-reduce-fraction-ℤᵉ xᵉ
  div-red-x-red-yᵉ :
    div-ℤᵉ
      ( int-reduce-numerator-fraction-ℤᵉ xᵉ)
      ( int-reduce-numerator-fraction-ℤᵉ yᵉ)
  div-red-x-red-yᵉ = div-right-factor-coprime-ℤᵉ
    (int-reduce-numerator-fraction-ℤᵉ xᵉ)
    (int-reduce-denominator-fraction-ℤᵉ xᵉ)
    (int-reduce-numerator-fraction-ℤᵉ yᵉ)
    div-red-x-numᵉ red-x-coprimeᵉ
  div-red-y-numᵉ :
    div-ℤᵉ
      ( int-reduce-numerator-fraction-ℤᵉ yᵉ)
      ( mul-ℤᵉ
        ( int-reduce-denominator-fraction-ℤᵉ yᵉ)
        ( int-reduce-numerator-fraction-ℤᵉ xᵉ))
  div-red-y-numᵉ = pairᵉ (int-reduce-denominator-fraction-ℤᵉ xᵉ)
    ( commutative-mul-ℤᵉ
      ( int-reduce-denominator-fraction-ℤᵉ xᵉ)
      ( int-reduce-numerator-fraction-ℤᵉ yᵉ) ∙ᵉ
      ( invᵉ (reduced-eqnᵉ) ∙ᵉ
        commutative-mul-ℤᵉ
          ( int-reduce-numerator-fraction-ℤᵉ xᵉ)
          ( int-reduce-denominator-fraction-ℤᵉ yᵉ)))
  red-y-coprimeᵉ :
    gcd-ℤᵉ
      ( int-reduce-numerator-fraction-ℤᵉ yᵉ)
      ( int-reduce-denominator-fraction-ℤᵉ yᵉ) ＝ᵉ
    one-ℤᵉ
  red-y-coprimeᵉ = is-reduced-reduce-fraction-ℤᵉ yᵉ
  div-red-y-red-xᵉ :
    div-ℤᵉ
      ( int-reduce-numerator-fraction-ℤᵉ yᵉ)
      ( int-reduce-numerator-fraction-ℤᵉ xᵉ)
  div-red-y-red-xᵉ = div-right-factor-coprime-ℤᵉ
    (int-reduce-numerator-fraction-ℤᵉ yᵉ)
    (int-reduce-denominator-fraction-ℤᵉ yᵉ)
    (int-reduce-numerator-fraction-ℤᵉ xᵉ)
    div-red-y-numᵉ red-y-coprimeᵉ

unique-numerator-reduce-fraction-ℤᵉ :
  ( xᵉ yᵉ : fraction-ℤᵉ) →
  ( Hᵉ : sim-fraction-ℤᵉ xᵉ yᵉ) →
  int-reduce-numerator-fraction-ℤᵉ xᵉ ＝ᵉ
  int-reduce-numerator-fraction-ℤᵉ yᵉ
unique-numerator-reduce-fraction-ℤᵉ xᵉ yᵉ Hᵉ =
  is-zero-num-case-splitᵉ
    (is-decidable-is-zero-ℤᵉ (int-reduce-numerator-fraction-ℤᵉ xᵉ))
  where
  is-zero-num-case-splitᵉ :
    ( is-zero-ℤᵉ (int-reduce-numerator-fraction-ℤᵉ xᵉ) +ᵉ
      ¬ᵉ (is-zero-ℤᵉ (int-reduce-numerator-fraction-ℤᵉ xᵉ))) →
    int-reduce-numerator-fraction-ℤᵉ xᵉ ＝ᵉ int-reduce-numerator-fraction-ℤᵉ yᵉ
  is-zero-num-case-splitᵉ (inlᵉ zᵉ) =
    zᵉ ∙ᵉ
    invᵉ (is-zero-sim-unit-ℤᵉ (sim-unique-numerator-reduce-fraction-ℤᵉ xᵉ yᵉ Hᵉ) zᵉ)
  is-zero-num-case-splitᵉ (inrᵉ nzᵉ) =
    is-plus-or-minus-case-splitᵉ
      ( is-plus-or-minus-sim-unit-ℤᵉ
        ( sim-unique-numerator-reduce-fraction-ℤᵉ xᵉ yᵉ Hᵉ))
    where
    is-plus-or-minus-case-splitᵉ :
      is-plus-or-minus-ℤᵉ
        ( int-reduce-numerator-fraction-ℤᵉ xᵉ)
        ( int-reduce-numerator-fraction-ℤᵉ yᵉ) →
      int-reduce-numerator-fraction-ℤᵉ xᵉ ＝ᵉ int-reduce-numerator-fraction-ℤᵉ yᵉ
    is-plus-or-minus-case-splitᵉ (inlᵉ posᵉ) = posᵉ
    is-plus-or-minus-case-splitᵉ (inrᵉ negᵉ) =
      ex-falsoᵉ (Eq-eq-ℤᵉ contraᵉ)
      where
      lemᵉ : (wᵉ : ℤᵉ) → is-positive-ℤᵉ wᵉ → Σᵉ ℕᵉ (λ nᵉ → wᵉ ＝ᵉ inrᵉ (inrᵉ nᵉ))
      lemᵉ (inrᵉ (inrᵉ nᵉ)) Hᵉ = pairᵉ nᵉ reflᵉ

      reduced-eqnᵉ :
        mul-ℤᵉ
          ( int-reduce-numerator-fraction-ℤᵉ xᵉ)
          ( int-reduce-denominator-fraction-ℤᵉ yᵉ) ＝ᵉ
        mul-ℤᵉ
          ( int-reduce-numerator-fraction-ℤᵉ xᵉ)
          ( neg-one-ℤᵉ *ℤᵉ (int-reduce-denominator-fraction-ℤᵉ xᵉ))
      reduced-eqnᵉ =
        equational-reasoningᵉ
          mul-ℤᵉ
            ( int-reduce-numerator-fraction-ℤᵉ xᵉ)
            ( int-reduce-denominator-fraction-ℤᵉ yᵉ)
          ＝ᵉ mul-ℤᵉ
              ( int-reduce-numerator-fraction-ℤᵉ yᵉ)
              ( int-reduce-denominator-fraction-ℤᵉ xᵉ)
            byᵉ reduce-preserves-sim-ℤᵉ xᵉ yᵉ Hᵉ
          ＝ᵉ mul-ℤᵉ
              ( (int-reduce-numerator-fraction-ℤᵉ xᵉ) *ℤᵉ neg-one-ℤᵉ)
              ( int-reduce-denominator-fraction-ℤᵉ xᵉ)
            byᵉ
              apᵉ
                ( _*ℤᵉ (int-reduce-denominator-fraction-ℤᵉ xᵉ))
                ( invᵉ negᵉ ∙ᵉ
                  commutative-mul-ℤᵉ
                    ( neg-one-ℤᵉ)
                    ( int-reduce-numerator-fraction-ℤᵉ xᵉ))
          ＝ᵉ mul-ℤᵉ
              ( int-reduce-numerator-fraction-ℤᵉ xᵉ)
              ( neg-one-ℤᵉ *ℤᵉ (int-reduce-denominator-fraction-ℤᵉ xᵉ))
            byᵉ
              associative-mul-ℤᵉ
                ( int-reduce-numerator-fraction-ℤᵉ xᵉ)
                ( neg-one-ℤᵉ)
                ( int-reduce-denominator-fraction-ℤᵉ xᵉ)

      x-natᵉ : ℕᵉ
      x-natᵉ =
        pr1ᵉ
          ( lemᵉ
            ( int-reduce-denominator-fraction-ℤᵉ xᵉ)
            ( is-positive-int-reduce-denominator-fraction-ℤᵉ xᵉ))

      y-natᵉ : ℕᵉ
      y-natᵉ =
        pr1ᵉ
          ( lemᵉ
            ( int-reduce-denominator-fraction-ℤᵉ yᵉ)
            ( is-positive-int-reduce-denominator-fraction-ℤᵉ yᵉ))

      contraᵉ : inrᵉ (inrᵉ y-natᵉ) ＝ᵉ neg-ℤᵉ (inrᵉ (inrᵉ x-natᵉ))
      contraᵉ =
        equational-reasoningᵉ
          inrᵉ (inrᵉ y-natᵉ)
          ＝ᵉ (int-reduce-denominator-fraction-ℤᵉ yᵉ)
            byᵉ
              invᵉ
                ( pr2ᵉ
                  ( lemᵉ
                    ( int-reduce-denominator-fraction-ℤᵉ yᵉ)
                    ( is-positive-int-reduce-denominator-fraction-ℤᵉ yᵉ)))
          ＝ᵉ neg-ℤᵉ (int-reduce-denominator-fraction-ℤᵉ xᵉ)
            byᵉ
              is-injective-left-mul-ℤᵉ
                ( int-reduce-numerator-fraction-ℤᵉ xᵉ)
                ( nzᵉ)
                ( reduced-eqnᵉ)
          ＝ᵉ neg-ℤᵉ (inrᵉ (inrᵉ x-natᵉ))
            byᵉ
              apᵉ
                ( neg-ℤᵉ)
                ( pr2ᵉ
                  ( lemᵉ
                    ( int-reduce-denominator-fraction-ℤᵉ xᵉ)
                    ( is-positive-int-reduce-denominator-fraction-ℤᵉ xᵉ)))

sim-unique-denominator-reduce-fraction-ℤᵉ :
  ( xᵉ yᵉ : fraction-ℤᵉ) →
  ( Hᵉ : sim-fraction-ℤᵉ xᵉ yᵉ) →
  sim-unit-ℤᵉ
    ( int-reduce-denominator-fraction-ℤᵉ xᵉ)
    ( int-reduce-denominator-fraction-ℤᵉ yᵉ)
sim-unique-denominator-reduce-fraction-ℤᵉ xᵉ yᵉ Hᵉ = antisymmetric-div-ℤᵉ
  (int-reduce-denominator-fraction-ℤᵉ xᵉ)
  (int-reduce-denominator-fraction-ℤᵉ yᵉ)
  div-red-x-red-yᵉ div-red-y-red-xᵉ
  where
  reduced-eqnᵉ :
    mul-ℤᵉ
      ( int-reduce-numerator-fraction-ℤᵉ xᵉ)
      ( int-reduce-denominator-fraction-ℤᵉ yᵉ) ＝ᵉ
    mul-ℤᵉ
      ( int-reduce-numerator-fraction-ℤᵉ yᵉ)
      ( int-reduce-denominator-fraction-ℤᵉ xᵉ)
  reduced-eqnᵉ = reduce-preserves-sim-ℤᵉ xᵉ yᵉ Hᵉ
  div-red-x-numᵉ :
    div-ℤᵉ
      ( int-reduce-denominator-fraction-ℤᵉ xᵉ)
      ( mul-ℤᵉ
        ( int-reduce-numerator-fraction-ℤᵉ xᵉ)
        ( int-reduce-denominator-fraction-ℤᵉ yᵉ))
  div-red-x-numᵉ = pairᵉ (int-reduce-numerator-fraction-ℤᵉ yᵉ)
    (invᵉ (reduced-eqnᵉ))
  red-x-coprimeᵉ :
    gcd-ℤᵉ
      ( int-reduce-denominator-fraction-ℤᵉ xᵉ)
      ( int-reduce-numerator-fraction-ℤᵉ xᵉ) ＝ᵉ
    one-ℤᵉ
  red-x-coprimeᵉ =
    is-commutative-gcd-ℤᵉ
      ( int-reduce-denominator-fraction-ℤᵉ xᵉ)
      ( int-reduce-numerator-fraction-ℤᵉ xᵉ) ∙ᵉ
    is-reduced-reduce-fraction-ℤᵉ xᵉ
  div-red-x-red-yᵉ :
    div-ℤᵉ
      ( int-reduce-denominator-fraction-ℤᵉ xᵉ)
      ( int-reduce-denominator-fraction-ℤᵉ yᵉ)
  div-red-x-red-yᵉ = div-right-factor-coprime-ℤᵉ
    (int-reduce-denominator-fraction-ℤᵉ xᵉ)
    (int-reduce-numerator-fraction-ℤᵉ xᵉ)
    (int-reduce-denominator-fraction-ℤᵉ yᵉ)
    div-red-x-numᵉ red-x-coprimeᵉ
  div-red-y-numᵉ :
    div-ℤᵉ
      ( int-reduce-denominator-fraction-ℤᵉ yᵉ)
      ( mul-ℤᵉ
        ( int-reduce-numerator-fraction-ℤᵉ yᵉ)
        ( int-reduce-denominator-fraction-ℤᵉ xᵉ))
  div-red-y-numᵉ = pairᵉ (int-reduce-numerator-fraction-ℤᵉ xᵉ)
    (reduced-eqnᵉ)
  red-y-coprimeᵉ :
    gcd-ℤᵉ
      ( int-reduce-denominator-fraction-ℤᵉ yᵉ)
      ( int-reduce-numerator-fraction-ℤᵉ yᵉ) ＝ᵉ
    one-ℤᵉ
  red-y-coprimeᵉ =
    is-commutative-gcd-ℤᵉ
      ( int-reduce-denominator-fraction-ℤᵉ yᵉ)
      ( int-reduce-numerator-fraction-ℤᵉ yᵉ) ∙ᵉ
    is-reduced-reduce-fraction-ℤᵉ yᵉ
  div-red-y-red-xᵉ :
    div-ℤᵉ
      ( int-reduce-denominator-fraction-ℤᵉ yᵉ)
      ( int-reduce-denominator-fraction-ℤᵉ xᵉ)
  div-red-y-red-xᵉ = div-right-factor-coprime-ℤᵉ
    (int-reduce-denominator-fraction-ℤᵉ yᵉ)
    (int-reduce-numerator-fraction-ℤᵉ yᵉ)
    (int-reduce-denominator-fraction-ℤᵉ xᵉ)
    div-red-y-numᵉ red-y-coprimeᵉ

unique-denominator-reduce-fraction-ℤᵉ :
  (xᵉ yᵉ : fraction-ℤᵉ) → (Hᵉ : sim-fraction-ℤᵉ xᵉ yᵉ) →
  int-reduce-denominator-fraction-ℤᵉ xᵉ ＝ᵉ int-reduce-denominator-fraction-ℤᵉ yᵉ
unique-denominator-reduce-fraction-ℤᵉ xᵉ yᵉ Hᵉ =
  eq-sim-unit-is-nonnegative-ℤᵉ
    ( is-nonnegative-is-positive-ℤᵉ
      ( is-positive-int-reduce-denominator-fraction-ℤᵉ xᵉ))
    ( is-nonnegative-is-positive-ℤᵉ
      ( is-positive-int-reduce-denominator-fraction-ℤᵉ yᵉ))
    (sim-unique-denominator-reduce-fraction-ℤᵉ xᵉ yᵉ Hᵉ)

unique-reduce-fraction-ℤᵉ :
  (xᵉ yᵉ : fraction-ℤᵉ) → (Hᵉ : sim-fraction-ℤᵉ xᵉ yᵉ) →
  reduce-fraction-ℤᵉ xᵉ ＝ᵉ reduce-fraction-ℤᵉ yᵉ
unique-reduce-fraction-ℤᵉ xᵉ yᵉ Hᵉ =
  eq-pair'ᵉ
    ( pairᵉ
      ( unique-numerator-reduce-fraction-ℤᵉ xᵉ yᵉ Hᵉ)
      ( eq-pair-Σ'ᵉ
        ( pairᵉ
          ( unique-denominator-reduce-fraction-ℤᵉ xᵉ yᵉ Hᵉ)
          ( eq-is-propᵉ
            ( is-prop-is-positive-ℤᵉ (int-reduce-denominator-fraction-ℤᵉ yᵉ))))))
```