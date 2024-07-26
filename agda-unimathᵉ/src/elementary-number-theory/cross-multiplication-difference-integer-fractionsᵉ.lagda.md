# The cross-multiplication difference of two integer fractions

```agda
module elementary-number-theory.cross-multiplication-difference-integer-fractionsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integersᵉ
open import elementary-number-theory.difference-integersᵉ
open import elementary-number-theory.integer-fractionsᵉ
open import elementary-number-theory.integersᵉ
open import elementary-number-theory.multiplication-integersᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.negationᵉ
open import foundation.propositionsᵉ
```

</details>

## Idea

Theᵉ
{{#conceptᵉ "cross-multiplicationᵉ difference"ᵉ Agda=cross-mul-diff-fraction-ℤᵉ}} ofᵉ
twoᵉ [integerᵉ fractions](elementary-number-theory.integer-fractions.mdᵉ) `a/b`ᵉ andᵉ
`c/d`ᵉ isᵉ theᵉ [difference](elementary-number-theory.difference-integers.mdᵉ) ofᵉ
theᵉ [products](elementary-number-theory.multiplication-integers.mdᵉ) ofᵉ theᵉ
numeratorᵉ ofᵉ eachᵉ fractionᵉ with theᵉ denominatorᵉ ofᵉ theᵉ otherᵉ: `cᵉ *ᵉ bᵉ -ᵉ aᵉ *ᵉ d`.ᵉ

## Definitions

### The cross-multiplication difference of two fractions

```agda
cross-mul-diff-fraction-ℤᵉ : fraction-ℤᵉ → fraction-ℤᵉ → ℤᵉ
cross-mul-diff-fraction-ℤᵉ xᵉ yᵉ =
  diff-ℤᵉ
    ( numerator-fraction-ℤᵉ yᵉ *ℤᵉ denominator-fraction-ℤᵉ xᵉ)
    ( numerator-fraction-ℤᵉ xᵉ *ℤᵉ denominator-fraction-ℤᵉ yᵉ)
```

## Properties

### Swapping the fractions changes the sign of the cross-multiplication difference

```agda
abstract
  skew-commutative-cross-mul-diff-fraction-ℤᵉ :
    (xᵉ yᵉ : fraction-ℤᵉ) →
    Idᵉ
      ( neg-ℤᵉ (cross-mul-diff-fraction-ℤᵉ xᵉ yᵉ))
      ( cross-mul-diff-fraction-ℤᵉ yᵉ xᵉ)
  skew-commutative-cross-mul-diff-fraction-ℤᵉ xᵉ yᵉ =
    distributive-neg-diff-ℤᵉ
      ( numerator-fraction-ℤᵉ yᵉ *ℤᵉ denominator-fraction-ℤᵉ xᵉ)
      ( numerator-fraction-ℤᵉ xᵉ *ℤᵉ denominator-fraction-ℤᵉ yᵉ)
```

### The cross multiplication difference of zero and an integer fraction is its numerator

```agda
module _
  (xᵉ : fraction-ℤᵉ)
  where

  abstract
    cross-mul-diff-zero-fraction-ℤᵉ :
      cross-mul-diff-fraction-ℤᵉ zero-fraction-ℤᵉ xᵉ ＝ᵉ numerator-fraction-ℤᵉ xᵉ
    cross-mul-diff-zero-fraction-ℤᵉ =
      ( right-unit-law-add-ℤᵉ (numerator-fraction-ℤᵉ xᵉ *ℤᵉ one-ℤᵉ)) ∙ᵉ
      ( right-unit-law-mul-ℤᵉ (numerator-fraction-ℤᵉ xᵉ))
```

### The cross multiplication difference of one and an integer fraction is the difference of its numerator and denominator

```agda
module _
  (xᵉ : fraction-ℤᵉ)
  where

  abstract
    cross-mul-diff-one-fraction-ℤᵉ :
      Idᵉ
        ( cross-mul-diff-fraction-ℤᵉ one-fraction-ℤᵉ xᵉ)
        ( (numerator-fraction-ℤᵉ xᵉ) -ℤᵉ (denominator-fraction-ℤᵉ xᵉ))
    cross-mul-diff-one-fraction-ℤᵉ =
      ap-diff-ℤᵉ
        ( right-unit-law-mul-ℤᵉ (numerator-fraction-ℤᵉ xᵉ))
        ( left-unit-law-mul-ℤᵉ (denominator-fraction-ℤᵉ xᵉ))
```

### Two fractions are similar when their cross-multiplication difference is zero

```agda
module _
  (xᵉ yᵉ : fraction-ℤᵉ)
  where

  abstract
    is-zero-cross-mul-diff-sim-fraction-ℤᵉ :
      sim-fraction-ℤᵉ xᵉ yᵉ →
      is-zero-ℤᵉ (cross-mul-diff-fraction-ℤᵉ xᵉ yᵉ)
    is-zero-cross-mul-diff-sim-fraction-ℤᵉ Hᵉ =
      is-zero-diff-ℤᵉ (invᵉ Hᵉ)

    sim-is-zero-coss-mul-diff-fraction-ℤᵉ :
      is-zero-ℤᵉ (cross-mul-diff-fraction-ℤᵉ xᵉ yᵉ) →
      sim-fraction-ℤᵉ xᵉ yᵉ
    sim-is-zero-coss-mul-diff-fraction-ℤᵉ Hᵉ = invᵉ (eq-diff-ℤᵉ Hᵉ)
```

## The transitive-additive property for the cross-multiplication difference

Givenᵉ threeᵉ fractionsᵉ `a/b`,ᵉ `x/y`ᵉ andᵉ `m/n`,ᵉ theᵉ pairwiseᵉ cross-multiplicationᵉ
differencesᵉ satisfyᵉ aᵉ transitive-additiveᵉ propertyᵉ:

```text
  yᵉ *ᵉ (mᵉ *ᵉ bᵉ -ᵉ aᵉ *ᵉ nᵉ) = bᵉ *ᵉ (mᵉ *ᵉ yᵉ -ᵉ xᵉ *ᵉ nᵉ) +ᵉ nᵉ *ᵉ (xᵉ *ᵉ bᵉ -ᵉ aᵉ *ᵉ yᵉ)
```

```agda
abstract
  lemma-add-cross-mul-diff-fraction-ℤᵉ :
    (pᵉ qᵉ rᵉ : fraction-ℤᵉ) →
    Idᵉ
      ( add-ℤᵉ
        ( denominator-fraction-ℤᵉ pᵉ *ℤᵉ cross-mul-diff-fraction-ℤᵉ qᵉ rᵉ)
        ( denominator-fraction-ℤᵉ rᵉ *ℤᵉ cross-mul-diff-fraction-ℤᵉ pᵉ qᵉ))
      ( denominator-fraction-ℤᵉ qᵉ *ℤᵉ cross-mul-diff-fraction-ℤᵉ pᵉ rᵉ)
  lemma-add-cross-mul-diff-fraction-ℤᵉ
    (npᵉ ,ᵉ dpᵉ ,ᵉ hpᵉ)
    (nqᵉ ,ᵉ dqᵉ ,ᵉ hqᵉ)
    (nrᵉ ,ᵉ drᵉ ,ᵉ hrᵉ) =
    equational-reasoningᵉ
    add-ℤᵉ
      (dpᵉ *ℤᵉ (nrᵉ *ℤᵉ dqᵉ -ℤᵉ nqᵉ *ℤᵉ drᵉ))
      (drᵉ *ℤᵉ (nqᵉ *ℤᵉ dpᵉ -ℤᵉ npᵉ *ℤᵉ dqᵉ))
    ＝ᵉ add-ℤᵉ
        (dpᵉ *ℤᵉ (nrᵉ *ℤᵉ dqᵉ) -ℤᵉ dpᵉ *ℤᵉ (nqᵉ *ℤᵉ drᵉ))
        (drᵉ *ℤᵉ (nqᵉ *ℤᵉ dpᵉ) -ℤᵉ drᵉ *ℤᵉ (npᵉ *ℤᵉ dqᵉ))
      byᵉ
        ap-add-ℤᵉ
          ( left-distributive-mul-diff-ℤᵉ dpᵉ (nrᵉ *ℤᵉ dqᵉ) (nqᵉ *ℤᵉ drᵉ))
          ( left-distributive-mul-diff-ℤᵉ drᵉ (nqᵉ *ℤᵉ dpᵉ) (npᵉ *ℤᵉ dqᵉ))
    ＝ᵉ diff-ℤᵉ
        (dpᵉ *ℤᵉ (nrᵉ *ℤᵉ dqᵉ) +ℤᵉ drᵉ *ℤᵉ (nqᵉ *ℤᵉ dpᵉ))
        (dpᵉ *ℤᵉ (nqᵉ *ℤᵉ drᵉ) +ℤᵉ drᵉ *ℤᵉ (npᵉ *ℤᵉ dqᵉ))
      byᵉ
        interchange-law-add-diff-ℤᵉ
          ( mul-ℤᵉ dpᵉ ( mul-ℤᵉ nrᵉ dqᵉ))
          ( mul-ℤᵉ dpᵉ ( mul-ℤᵉ nqᵉ drᵉ))
          ( mul-ℤᵉ drᵉ ( mul-ℤᵉ nqᵉ dpᵉ))
          ( mul-ℤᵉ drᵉ ( mul-ℤᵉ npᵉ dqᵉ))
    ＝ᵉ diff-ℤᵉ
        (dqᵉ *ℤᵉ (nrᵉ *ℤᵉ dpᵉ) +ℤᵉ drᵉ *ℤᵉ (nqᵉ *ℤᵉ dpᵉ))
        (drᵉ *ℤᵉ (nqᵉ *ℤᵉ dpᵉ) +ℤᵉ dqᵉ *ℤᵉ (npᵉ *ℤᵉ drᵉ))
      byᵉ
        ap-diff-ℤᵉ
          ( ap-add-ℤᵉ
            ( lemma-interchange-mul-ℤᵉ dpᵉ nrᵉ dqᵉ)
            ( reflᵉ))
          ( ap-add-ℤᵉ
            ( lemma-interchange-mul-ℤᵉ dpᵉ nqᵉ drᵉ)
            ( lemma-interchange-mul-ℤᵉ drᵉ npᵉ dqᵉ))
    ＝ᵉ diff-ℤᵉ
        (dqᵉ *ℤᵉ (nrᵉ *ℤᵉ dpᵉ) +ℤᵉ drᵉ *ℤᵉ (nqᵉ *ℤᵉ dpᵉ))
        ((dqᵉ *ℤᵉ (npᵉ *ℤᵉ drᵉ)) +ℤᵉ (drᵉ *ℤᵉ (nqᵉ *ℤᵉ dpᵉ)))
      byᵉ
        apᵉ
          ( diff-ℤᵉ (dqᵉ *ℤᵉ (nrᵉ *ℤᵉ dpᵉ) +ℤᵉ drᵉ *ℤᵉ (nqᵉ *ℤᵉ dpᵉ)))
          ( commutative-add-ℤᵉ (drᵉ *ℤᵉ (nqᵉ *ℤᵉ dpᵉ)) (dqᵉ *ℤᵉ (npᵉ *ℤᵉ drᵉ)))
    ＝ᵉ (dqᵉ *ℤᵉ (nrᵉ *ℤᵉ dpᵉ)) -ℤᵉ (dqᵉ *ℤᵉ (npᵉ *ℤᵉ drᵉ))
      byᵉ
        right-translation-diff-ℤᵉ
          (dqᵉ *ℤᵉ (nrᵉ *ℤᵉ dpᵉ))
          (dqᵉ *ℤᵉ (npᵉ *ℤᵉ drᵉ))
          (drᵉ *ℤᵉ (nqᵉ *ℤᵉ dpᵉ))
    ＝ᵉ dqᵉ *ℤᵉ (nrᵉ *ℤᵉ dpᵉ -ℤᵉ npᵉ *ℤᵉ drᵉ)
      byᵉ invᵉ (left-distributive-mul-diff-ℤᵉ dqᵉ (nrᵉ *ℤᵉ dpᵉ) (npᵉ *ℤᵉ drᵉ))
    where
    lemma-interchange-mul-ℤᵉ : (aᵉ bᵉ cᵉ : ℤᵉ) → (aᵉ *ℤᵉ (bᵉ *ℤᵉ cᵉ)) ＝ᵉ (cᵉ *ℤᵉ (bᵉ *ℤᵉ aᵉ))
    lemma-interchange-mul-ℤᵉ aᵉ bᵉ cᵉ =
      invᵉ (associative-mul-ℤᵉ aᵉ bᵉ cᵉ) ∙ᵉ
      apᵉ (mul-ℤ'ᵉ cᵉ) (commutative-mul-ℤᵉ aᵉ bᵉ) ∙ᵉ
      commutative-mul-ℤᵉ (bᵉ *ℤᵉ aᵉ) cᵉ

  lemma-left-sim-cross-mul-diff-fraction-ℤᵉ :
    (aᵉ a'ᵉ bᵉ : fraction-ℤᵉ) →
    sim-fraction-ℤᵉ aᵉ a'ᵉ →
    Idᵉ
      ( denominator-fraction-ℤᵉ aᵉ *ℤᵉ cross-mul-diff-fraction-ℤᵉ a'ᵉ bᵉ)
      ( denominator-fraction-ℤᵉ a'ᵉ *ℤᵉ cross-mul-diff-fraction-ℤᵉ aᵉ bᵉ)
  lemma-left-sim-cross-mul-diff-fraction-ℤᵉ aᵉ a'ᵉ bᵉ Hᵉ =
    equational-reasoningᵉ
    ( denominator-fraction-ℤᵉ aᵉ *ℤᵉ cross-mul-diff-fraction-ℤᵉ a'ᵉ bᵉ)
    ＝ᵉ ( add-ℤᵉ
          ( denominator-fraction-ℤᵉ a'ᵉ *ℤᵉ cross-mul-diff-fraction-ℤᵉ aᵉ bᵉ)
          ( denominator-fraction-ℤᵉ bᵉ *ℤᵉ cross-mul-diff-fraction-ℤᵉ a'ᵉ aᵉ))
      byᵉ invᵉ (lemma-add-cross-mul-diff-fraction-ℤᵉ a'ᵉ aᵉ bᵉ)
    ＝ᵉ ( add-ℤᵉ
        ( denominator-fraction-ℤᵉ a'ᵉ *ℤᵉ cross-mul-diff-fraction-ℤᵉ aᵉ bᵉ)
        ( zero-ℤᵉ))
      byᵉ
        apᵉ
          ( add-ℤᵉ
            ( denominator-fraction-ℤᵉ a'ᵉ *ℤᵉ cross-mul-diff-fraction-ℤᵉ aᵉ bᵉ))
            ( ( apᵉ
                ( mul-ℤᵉ (denominator-fraction-ℤᵉ bᵉ))
                ( is-zero-cross-mul-diff-sim-fraction-ℤᵉ a'ᵉ aᵉ H'ᵉ)) ∙ᵉ
              ( right-zero-law-mul-ℤᵉ (denominator-fraction-ℤᵉ bᵉ)))
    ＝ᵉ denominator-fraction-ℤᵉ a'ᵉ *ℤᵉ cross-mul-diff-fraction-ℤᵉ aᵉ bᵉ
      byᵉ
        right-unit-law-add-ℤᵉ
          ( denominator-fraction-ℤᵉ a'ᵉ *ℤᵉ cross-mul-diff-fraction-ℤᵉ aᵉ bᵉ)
    where
    H'ᵉ : sim-fraction-ℤᵉ a'ᵉ aᵉ
    H'ᵉ = symmetric-sim-fraction-ℤᵉ aᵉ a'ᵉ Hᵉ

  lemma-right-sim-cross-mul-diff-fraction-ℤᵉ :
    (aᵉ bᵉ b'ᵉ : fraction-ℤᵉ) →
    sim-fraction-ℤᵉ bᵉ b'ᵉ →
    Idᵉ
      ( denominator-fraction-ℤᵉ bᵉ *ℤᵉ cross-mul-diff-fraction-ℤᵉ aᵉ b'ᵉ)
      ( denominator-fraction-ℤᵉ b'ᵉ *ℤᵉ cross-mul-diff-fraction-ℤᵉ aᵉ bᵉ)
  lemma-right-sim-cross-mul-diff-fraction-ℤᵉ aᵉ bᵉ b'ᵉ Hᵉ =
    equational-reasoningᵉ
    ( denominator-fraction-ℤᵉ bᵉ *ℤᵉ cross-mul-diff-fraction-ℤᵉ aᵉ b'ᵉ)
    ＝ᵉ ( add-ℤᵉ
        ( denominator-fraction-ℤᵉ aᵉ *ℤᵉ cross-mul-diff-fraction-ℤᵉ bᵉ b'ᵉ)
        ( denominator-fraction-ℤᵉ b'ᵉ *ℤᵉ cross-mul-diff-fraction-ℤᵉ aᵉ bᵉ))
      byᵉ invᵉ (lemma-add-cross-mul-diff-fraction-ℤᵉ aᵉ bᵉ b'ᵉ)
    ＝ᵉ ( add-ℤᵉ
        ( zero-ℤᵉ)
        ( denominator-fraction-ℤᵉ b'ᵉ *ℤᵉ cross-mul-diff-fraction-ℤᵉ aᵉ bᵉ))
      byᵉ
        apᵉ
          ( add-ℤ'ᵉ (denominator-fraction-ℤᵉ b'ᵉ *ℤᵉ cross-mul-diff-fraction-ℤᵉ aᵉ bᵉ))
          ( ( apᵉ
            ( mul-ℤᵉ (denominator-fraction-ℤᵉ aᵉ))
            ( is-zero-cross-mul-diff-sim-fraction-ℤᵉ bᵉ b'ᵉ Hᵉ)) ∙ᵉ
            ( right-zero-law-mul-ℤᵉ (denominator-fraction-ℤᵉ aᵉ)))
    ＝ᵉ denominator-fraction-ℤᵉ b'ᵉ *ℤᵉ cross-mul-diff-fraction-ℤᵉ aᵉ bᵉ
      byᵉ
        left-unit-law-add-ℤᵉ
          ( denominator-fraction-ℤᵉ b'ᵉ *ℤᵉ cross-mul-diff-fraction-ℤᵉ aᵉ bᵉ)
```

## External links

-ᵉ [Cross-multiplication](https://en.wikipedia.org/wiki/Cross-multiplicationᵉ) atᵉ
  Wikipediaᵉ