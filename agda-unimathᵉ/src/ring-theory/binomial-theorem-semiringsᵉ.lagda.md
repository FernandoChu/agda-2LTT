# The binomial theorem for semirings

```agda
module ring-theory.binomial-theorem-semiringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbersᵉ
open import elementary-number-theory.binomial-coefficientsᵉ
open import elementary-number-theory.distance-natural-numbersᵉ
open import elementary-number-theory.inequality-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ

open import foundation.action-on-identifications-binary-functionsᵉ
open import foundation.action-on-identifications-functionsᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ

open import linear-algebra.vectors-on-semiringsᵉ

open import ring-theory.powers-of-elements-semiringsᵉ
open import ring-theory.semiringsᵉ
open import ring-theory.sums-semiringsᵉ

open import univalent-combinatorics.coproduct-typesᵉ
open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Theᵉ binomialᵉ theoremᵉ in semiringsᵉ assertsᵉ thatᵉ forᵉ anyᵉ twoᵉ elementsᵉ `x`ᵉ andᵉ `y`ᵉ
ofᵉ aᵉ commutativeᵉ ringᵉ `R`ᵉ andᵉ anyᵉ naturalᵉ numberᵉ `n`,ᵉ ifᵉ `xyᵉ = yx`ᵉ holdsᵉ thenᵉ weᵉ
haveᵉ

```text
  (xᵉ +ᵉ y)ⁿᵉ = ∑_{0ᵉ ≤ᵉ iᵉ <ᵉ n+1ᵉ} (nᵉ chooseᵉ iᵉ) xⁱᵉ yⁿ⁻ⁱ.ᵉ
```

## Definitions

### Binomial sums

```agda
binomial-sum-Semiringᵉ :
  {lᵉ : Level} (Rᵉ : Semiringᵉ lᵉ)
  (nᵉ : ℕᵉ) (fᵉ : functional-vec-Semiringᵉ Rᵉ (succ-ℕᵉ nᵉ)) →
  type-Semiringᵉ Rᵉ
binomial-sum-Semiringᵉ Rᵉ nᵉ fᵉ =
  sum-Semiringᵉ Rᵉ (succ-ℕᵉ nᵉ)
    ( λ iᵉ →
      mul-nat-scalar-Semiringᵉ Rᵉ
        ( binomial-coefficient-Finᵉ nᵉ iᵉ)
        ( fᵉ iᵉ))
```

## Properties

### Binomial sums of one and two elements

```agda
module _
  {lᵉ : Level} (Rᵉ : Semiringᵉ lᵉ)
  where

  binomial-sum-one-element-Semiringᵉ :
    (fᵉ : functional-vec-Semiringᵉ Rᵉ 1ᵉ) →
    binomial-sum-Semiringᵉ Rᵉ 0 fᵉ ＝ᵉ
    head-functional-vec-Semiringᵉ Rᵉ 0 fᵉ
  binomial-sum-one-element-Semiringᵉ fᵉ =
    ( sum-one-element-Semiringᵉ Rᵉ
      ( λ iᵉ →
        mul-nat-scalar-Semiringᵉ Rᵉ
          ( binomial-coefficient-Finᵉ 0 iᵉ)
          ( fᵉ iᵉ))) ∙ᵉ
    ( left-unit-law-mul-nat-scalar-Semiringᵉ Rᵉ
      ( head-functional-vec-Semiringᵉ Rᵉ 0 fᵉ))

  binomial-sum-two-elements-Semiringᵉ :
    (fᵉ : functional-vec-Semiringᵉ Rᵉ 2ᵉ) →
    binomial-sum-Semiringᵉ Rᵉ 1 fᵉ ＝ᵉ
    add-Semiringᵉ Rᵉ (fᵉ (zero-Finᵉ 1ᵉ)) (fᵉ (one-Finᵉ 1ᵉ))
  binomial-sum-two-elements-Semiringᵉ fᵉ =
    sum-two-elements-Semiringᵉ Rᵉ
      ( λ iᵉ → mul-nat-scalar-Semiringᵉ Rᵉ (binomial-coefficient-Finᵉ 1 iᵉ) (fᵉ iᵉ)) ∙ᵉ
      ( ap-binaryᵉ
        ( add-Semiringᵉ Rᵉ)
        ( left-unit-law-mul-nat-scalar-Semiringᵉ Rᵉ (fᵉ (zero-Finᵉ 1ᵉ)))
        ( left-unit-law-mul-nat-scalar-Semiringᵉ Rᵉ (fᵉ (one-Finᵉ 1ᵉ))))
```

### Binomial sums are homotopy invariant

```agda
module _
  {lᵉ : Level} (Rᵉ : Semiringᵉ lᵉ)
  where

  htpy-binomial-sum-Semiringᵉ :
    (nᵉ : ℕᵉ) {fᵉ gᵉ : functional-vec-Semiringᵉ Rᵉ (succ-ℕᵉ nᵉ)} →
    (fᵉ ~ᵉ gᵉ) →
    binomial-sum-Semiringᵉ Rᵉ nᵉ fᵉ ＝ᵉ binomial-sum-Semiringᵉ Rᵉ nᵉ gᵉ
  htpy-binomial-sum-Semiringᵉ nᵉ Hᵉ =
    htpy-sum-Semiringᵉ Rᵉ
      ( succ-ℕᵉ nᵉ)
      ( λ iᵉ →
        apᵉ
          ( mul-nat-scalar-Semiringᵉ Rᵉ (binomial-coefficient-Finᵉ nᵉ iᵉ))
          ( Hᵉ iᵉ))
```

### Multiplication distributes over sums

```agda
module _
  {lᵉ : Level} (Rᵉ : Semiringᵉ lᵉ)
  where

  left-distributive-mul-binomial-sum-Semiringᵉ :
    (nᵉ : ℕᵉ) (xᵉ : type-Semiringᵉ Rᵉ)
    (fᵉ : functional-vec-Semiringᵉ Rᵉ (succ-ℕᵉ nᵉ)) →
    mul-Semiringᵉ Rᵉ xᵉ (binomial-sum-Semiringᵉ Rᵉ nᵉ fᵉ) ＝ᵉ
    binomial-sum-Semiringᵉ Rᵉ nᵉ (λ iᵉ → mul-Semiringᵉ Rᵉ xᵉ (fᵉ iᵉ))
  left-distributive-mul-binomial-sum-Semiringᵉ nᵉ xᵉ fᵉ =
    ( left-distributive-mul-sum-Semiringᵉ Rᵉ
      ( succ-ℕᵉ nᵉ)
      ( xᵉ)
      ( λ iᵉ →
        mul-nat-scalar-Semiringᵉ Rᵉ (binomial-coefficient-Finᵉ nᵉ iᵉ) (fᵉ iᵉ))) ∙ᵉ
    ( htpy-sum-Semiringᵉ Rᵉ
      ( succ-ℕᵉ nᵉ)
      ( λ iᵉ →
        right-nat-scalar-law-mul-Semiringᵉ Rᵉ
          ( binomial-coefficient-Finᵉ nᵉ iᵉ)
          ( xᵉ)
          ( fᵉ iᵉ)))

  right-distributive-mul-binomial-sum-Semiringᵉ :
    (nᵉ : ℕᵉ) (fᵉ : functional-vec-Semiringᵉ Rᵉ (succ-ℕᵉ nᵉ)) →
    (xᵉ : type-Semiringᵉ Rᵉ) →
    mul-Semiringᵉ Rᵉ (binomial-sum-Semiringᵉ Rᵉ nᵉ fᵉ) xᵉ ＝ᵉ
    binomial-sum-Semiringᵉ Rᵉ nᵉ (λ iᵉ → mul-Semiringᵉ Rᵉ (fᵉ iᵉ) xᵉ)
  right-distributive-mul-binomial-sum-Semiringᵉ nᵉ fᵉ xᵉ =
    ( right-distributive-mul-sum-Semiringᵉ Rᵉ
      ( succ-ℕᵉ nᵉ)
      ( λ iᵉ →
        mul-nat-scalar-Semiringᵉ Rᵉ (binomial-coefficient-Finᵉ nᵉ iᵉ) (fᵉ iᵉ))
      ( xᵉ)) ∙ᵉ
    ( htpy-sum-Semiringᵉ Rᵉ
      ( succ-ℕᵉ nᵉ)
      ( λ iᵉ →
        left-nat-scalar-law-mul-Semiringᵉ Rᵉ
          ( binomial-coefficient-Finᵉ nᵉ iᵉ)
          ( fᵉ iᵉ)
          ( xᵉ)))
```

## Lemmas

### Computing a left summand that will appear in the proof of the binomial theorem

```agda
module _
  {lᵉ : Level} (Rᵉ : Semiringᵉ lᵉ)
  where

  left-summand-binomial-theorem-Semiringᵉ :
    (nᵉ : ℕᵉ) (xᵉ yᵉ : type-Semiringᵉ Rᵉ) →
    (Hᵉ : mul-Semiringᵉ Rᵉ xᵉ yᵉ ＝ᵉ mul-Semiringᵉ Rᵉ yᵉ xᵉ) →
    ( mul-Semiringᵉ Rᵉ
      ( binomial-sum-Semiringᵉ Rᵉ
        ( succ-ℕᵉ nᵉ)
        ( λ iᵉ →
          mul-Semiringᵉ Rᵉ
            ( power-Semiringᵉ Rᵉ (nat-Finᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)) iᵉ) xᵉ)
            ( power-Semiringᵉ Rᵉ
              ( dist-ℕᵉ (nat-Finᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)) iᵉ) (succ-ℕᵉ nᵉ)) yᵉ)))
      ( xᵉ)) ＝ᵉ
    ( add-Semiringᵉ Rᵉ
      ( power-Semiringᵉ Rᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)) xᵉ)
      ( sum-Semiringᵉ Rᵉ
        ( succ-ℕᵉ nᵉ)
        ( λ iᵉ →
          mul-nat-scalar-Semiringᵉ Rᵉ
            ( binomial-coefficient-Finᵉ (succ-ℕᵉ nᵉ) (inl-Finᵉ (succ-ℕᵉ nᵉ) iᵉ))
            ( mul-Semiringᵉ Rᵉ
              ( power-Semiringᵉ Rᵉ
                ( succ-ℕᵉ (nat-Finᵉ (succ-ℕᵉ nᵉ) iᵉ))
                ( xᵉ))
              ( power-Semiringᵉ Rᵉ
                ( dist-ℕᵉ (nat-Finᵉ (succ-ℕᵉ nᵉ) iᵉ) (succ-ℕᵉ nᵉ))
                ( yᵉ))))))
  left-summand-binomial-theorem-Semiringᵉ nᵉ xᵉ yᵉ Hᵉ =
    ( right-distributive-mul-binomial-sum-Semiringᵉ Rᵉ
      ( succ-ℕᵉ nᵉ)
      ( λ iᵉ →
        mul-Semiringᵉ Rᵉ
          ( power-Semiringᵉ Rᵉ
            ( nat-Finᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)) iᵉ)
            ( xᵉ))
          ( power-Semiringᵉ Rᵉ
            ( dist-ℕᵉ (nat-Finᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)) iᵉ) (succ-ℕᵉ nᵉ))
            ( yᵉ)))
      ( xᵉ)) ∙ᵉ
    ( ( htpy-binomial-sum-Semiringᵉ Rᵉ
        ( succ-ℕᵉ nᵉ)
        ( λ iᵉ →
          ( ( associative-mul-Semiringᵉ Rᵉ
              ( power-Semiringᵉ Rᵉ (nat-Finᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)) iᵉ) xᵉ)
              ( power-Semiringᵉ Rᵉ
                ( dist-ℕᵉ (nat-Finᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)) iᵉ) (succ-ℕᵉ nᵉ))
                ( yᵉ))
              ( xᵉ)) ∙ᵉ
            ( ( apᵉ
                ( mul-Semiringᵉ Rᵉ
                  ( power-Semiringᵉ Rᵉ (nat-Finᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)) iᵉ) xᵉ))
                ( commute-powers-Semiring'ᵉ Rᵉ
                  ( dist-ℕᵉ (nat-Finᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)) iᵉ) (succ-ℕᵉ nᵉ))
                  ( invᵉ Hᵉ))) ∙ᵉ
              ( invᵉ
                ( associative-mul-Semiringᵉ Rᵉ
                  ( power-Semiringᵉ Rᵉ (nat-Finᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)) iᵉ) xᵉ)
                  ( xᵉ)
                  ( power-Semiringᵉ Rᵉ
                    ( dist-ℕᵉ (nat-Finᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)) iᵉ) (succ-ℕᵉ nᵉ))
                    ( yᵉ)))))) ∙ᵉ
          ( apᵉ
            ( mul-Semiring'ᵉ Rᵉ
              ( power-Semiringᵉ Rᵉ
                ( dist-ℕᵉ (nat-Finᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)) iᵉ) (succ-ℕᵉ nᵉ))
                ( yᵉ)))
            ( invᵉ
              ( power-succ-Semiringᵉ Rᵉ
                ( nat-Finᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)) iᵉ)
                ( xᵉ)))))) ∙ᵉ
      ( ( apᵉ
          ( add-Semiringᵉ Rᵉ _)
          ( ( ap-mul-nat-scalar-Semiringᵉ Rᵉ
              ( is-one-on-diagonal-binomial-coefficient-ℕᵉ (succ-ℕᵉ nᵉ))
              ( apᵉ
                ( λ tᵉ →
                  mul-Semiringᵉ Rᵉ
                    ( power-Semiringᵉ Rᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)) xᵉ)
                    ( power-Semiringᵉ Rᵉ tᵉ yᵉ))
                ( dist-eq-ℕ'ᵉ (succ-ℕᵉ nᵉ)))) ∙ᵉ
            ( ( left-unit-law-mul-nat-scalar-Semiringᵉ Rᵉ
                ( mul-Semiringᵉ Rᵉ
                  ( power-Semiringᵉ Rᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)) xᵉ)
                  ( one-Semiringᵉ Rᵉ))) ∙ᵉ
              ( right-unit-law-mul-Semiringᵉ Rᵉ
                ( power-Semiringᵉ Rᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)) xᵉ))))) ∙ᵉ
        ( commutative-add-Semiringᵉ Rᵉ
          ( sum-Semiringᵉ Rᵉ
            ( succ-ℕᵉ nᵉ)
            ( λ iᵉ →
              mul-nat-scalar-Semiringᵉ Rᵉ
                ( binomial-coefficient-Finᵉ (succ-ℕᵉ nᵉ) (inl-Finᵉ (succ-ℕᵉ nᵉ) iᵉ))
                ( mul-Semiringᵉ Rᵉ
                  ( power-Semiringᵉ Rᵉ
                    ( succ-ℕᵉ (nat-Finᵉ (succ-ℕᵉ nᵉ) iᵉ))
                    ( xᵉ))
                  ( power-Semiringᵉ Rᵉ
                    ( dist-ℕᵉ (nat-Finᵉ (succ-ℕᵉ nᵉ) iᵉ) (succ-ℕᵉ nᵉ))
                    ( yᵉ)))))
          ( power-Semiringᵉ Rᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)) xᵉ))))
```

### Computing a right summand that will appear in the proof of the binomial theorem

```agda
  right-summand-binomial-theorem-Semiringᵉ :
    (nᵉ : ℕᵉ) (xᵉ yᵉ : type-Semiringᵉ Rᵉ) →
    ( mul-Semiringᵉ Rᵉ
      ( binomial-sum-Semiringᵉ Rᵉ
        ( succ-ℕᵉ nᵉ)
        ( λ iᵉ →
          mul-Semiringᵉ Rᵉ
            ( power-Semiringᵉ Rᵉ
              ( nat-Finᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)) iᵉ)
              ( xᵉ))
            ( power-Semiringᵉ Rᵉ
              ( dist-ℕᵉ (nat-Finᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)) iᵉ) (succ-ℕᵉ nᵉ))
              ( yᵉ))))
      ( yᵉ)) ＝ᵉ
    ( add-Semiringᵉ Rᵉ
      ( power-Semiringᵉ Rᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)) yᵉ)
      ( sum-Semiringᵉ Rᵉ
        ( succ-ℕᵉ nᵉ)
        ( λ iᵉ →
          mul-nat-scalar-Semiringᵉ Rᵉ
            ( binomial-coefficient-ℕᵉ
              ( succ-ℕᵉ nᵉ)
              ( succ-ℕᵉ (nat-Finᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)) (inl-Finᵉ (succ-ℕᵉ nᵉ) iᵉ))))
            ( mul-Semiringᵉ Rᵉ
              ( power-Semiringᵉ Rᵉ
                ( succ-ℕᵉ (nat-Finᵉ (succ-ℕᵉ nᵉ) iᵉ))
                ( xᵉ))
              ( power-Semiringᵉ Rᵉ
                ( dist-ℕᵉ (nat-Finᵉ (succ-ℕᵉ nᵉ) iᵉ) (succ-ℕᵉ nᵉ))
                ( yᵉ))))))
  right-summand-binomial-theorem-Semiringᵉ nᵉ xᵉ yᵉ =
    ( right-distributive-mul-binomial-sum-Semiringᵉ Rᵉ
      ( succ-ℕᵉ nᵉ)
      ( λ iᵉ →
        mul-Semiringᵉ Rᵉ
          ( power-Semiringᵉ Rᵉ
            ( nat-Finᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)) iᵉ)
            ( xᵉ))
          ( power-Semiringᵉ Rᵉ
            ( dist-ℕᵉ (nat-Finᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)) iᵉ) (succ-ℕᵉ nᵉ))
            ( yᵉ)))
      ( yᵉ)) ∙ᵉ
    ( ( htpy-binomial-sum-Semiringᵉ Rᵉ
        ( succ-ℕᵉ nᵉ)
        ( λ iᵉ →
          ( associative-mul-Semiringᵉ Rᵉ
            ( power-Semiringᵉ Rᵉ
              ( nat-Finᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)) iᵉ)
              ( xᵉ))
            ( power-Semiringᵉ Rᵉ
              ( dist-ℕᵉ (nat-Finᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)) iᵉ) (succ-ℕᵉ nᵉ))
              ( yᵉ))
            ( yᵉ)) ∙ᵉ
          ( apᵉ
            ( mul-Semiringᵉ Rᵉ
              ( power-Semiringᵉ Rᵉ
                ( nat-Finᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)) iᵉ)
                ( xᵉ)))
            ( invᵉ
              ( apᵉ
                ( λ mᵉ → power-Semiringᵉ Rᵉ mᵉ yᵉ)
                ( right-successor-law-dist-ℕᵉ
                  ( nat-Finᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)) iᵉ)
                  ( succ-ℕᵉ nᵉ)
                  ( upper-bound-nat-Finᵉ (succ-ℕᵉ nᵉ) iᵉ)) ∙ᵉ
                ( power-succ-Semiringᵉ Rᵉ
                  ( dist-ℕᵉ (nat-Finᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)) iᵉ) (succ-ℕᵉ nᵉ))
                  ( yᵉ))))))) ∙ᵉ
      ( ( snoc-sum-Semiringᵉ Rᵉ
          ( succ-ℕᵉ nᵉ)
          ( λ iᵉ →
            mul-nat-scalar-Semiringᵉ Rᵉ
              ( binomial-coefficient-Finᵉ (succ-ℕᵉ nᵉ) iᵉ)
              ( mul-Semiringᵉ Rᵉ
                ( power-Semiringᵉ Rᵉ
                  ( nat-Finᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)) iᵉ)
                  ( xᵉ))
                ( power-Semiringᵉ Rᵉ
                  ( dist-ℕᵉ (nat-Finᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)) iᵉ) (succ-ℕᵉ (succ-ℕᵉ nᵉ)))
                  ( yᵉ))))
          ( ( apᵉ
              ( λ mᵉ →
                mul-nat-scalar-Semiringᵉ Rᵉ
                  ( binomial-coefficient-ℕᵉ (succ-ℕᵉ nᵉ) mᵉ)
                  ( mul-Semiringᵉ Rᵉ
                    ( power-Semiringᵉ Rᵉ mᵉ xᵉ)
                    ( power-Semiringᵉ Rᵉ
                      ( dist-ℕᵉ mᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)))
                      ( yᵉ))))
              ( is-zero-nat-zero-Finᵉ {nᵉ})) ∙ᵉ
            ( ( left-unit-law-mul-nat-scalar-Semiringᵉ Rᵉ
                ( mul-Semiringᵉ Rᵉ
                  ( one-Semiringᵉ Rᵉ)
                  ( power-Semiringᵉ Rᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)) yᵉ))) ∙ᵉ
              ( left-unit-law-mul-Semiringᵉ Rᵉ
                ( power-Semiringᵉ Rᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)) yᵉ))))) ∙ᵉ
        ( ap-add-Semiringᵉ Rᵉ
          ( reflᵉ)
          ( htpy-sum-Semiringᵉ Rᵉ
            ( succ-ℕᵉ nᵉ)
            ( λ iᵉ →
              ( apᵉ
                ( λ mᵉ →
                  mul-nat-scalar-Semiringᵉ Rᵉ
                    ( binomial-coefficient-ℕᵉ (succ-ℕᵉ nᵉ) mᵉ)
                    ( mul-Semiringᵉ Rᵉ
                      ( power-Semiringᵉ Rᵉ mᵉ xᵉ)
                      ( power-Semiringᵉ Rᵉ
                        ( dist-ℕᵉ mᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)))
                        ( yᵉ))))
                ( nat-inr-Finᵉ (succ-ℕᵉ nᵉ) iᵉ)))))))
```

## Theorem

### Binomial theorem for semirings

```agda
binomial-theorem-Semiringᵉ :
  {lᵉ : Level} (Rᵉ : Semiringᵉ lᵉ) (nᵉ : ℕᵉ) (xᵉ yᵉ : type-Semiringᵉ Rᵉ) →
  mul-Semiringᵉ Rᵉ xᵉ yᵉ ＝ᵉ mul-Semiringᵉ Rᵉ yᵉ xᵉ →
  power-Semiringᵉ Rᵉ nᵉ (add-Semiringᵉ Rᵉ xᵉ yᵉ) ＝ᵉ
  binomial-sum-Semiringᵉ Rᵉ nᵉ
    ( λ iᵉ →
      mul-Semiringᵉ Rᵉ
      ( power-Semiringᵉ Rᵉ (nat-Finᵉ (succ-ℕᵉ nᵉ) iᵉ) xᵉ)
      ( power-Semiringᵉ Rᵉ (dist-ℕᵉ (nat-Finᵉ (succ-ℕᵉ nᵉ) iᵉ) nᵉ) yᵉ))
binomial-theorem-Semiringᵉ Rᵉ zero-ℕᵉ xᵉ yᵉ Hᵉ =
  invᵉ
    ( ( sum-one-element-Semiringᵉ Rᵉ
        ( λ iᵉ →
          mul-nat-scalar-Semiringᵉ Rᵉ
            ( binomial-coefficient-Finᵉ 0 iᵉ)
            ( mul-Semiringᵉ Rᵉ
              ( power-Semiringᵉ Rᵉ (nat-Finᵉ 1 iᵉ) xᵉ)
              ( power-Semiringᵉ Rᵉ (dist-ℕᵉ (nat-Finᵉ 1 iᵉ) 0ᵉ) yᵉ)))) ∙ᵉ
      ( ( left-unit-law-mul-nat-scalar-Semiringᵉ Rᵉ
          ( mul-Semiringᵉ Rᵉ
            ( one-Semiringᵉ Rᵉ)
            ( one-Semiringᵉ Rᵉ))) ∙ᵉ
        ( left-unit-law-mul-Semiringᵉ Rᵉ (one-Semiringᵉ Rᵉ))))
binomial-theorem-Semiringᵉ Rᵉ (succ-ℕᵉ zero-ℕᵉ) xᵉ yᵉ Hᵉ =
  ( commutative-add-Semiringᵉ Rᵉ xᵉ yᵉ) ∙ᵉ
  ( ( ap-binaryᵉ
      ( add-Semiringᵉ Rᵉ)
      ( ( invᵉ (left-unit-law-mul-Semiringᵉ Rᵉ yᵉ)) ∙ᵉ
        ( invᵉ
          ( left-unit-law-mul-nat-scalar-Semiringᵉ Rᵉ
            ( mul-Semiringᵉ Rᵉ (one-Semiringᵉ Rᵉ) yᵉ))))
      ( ( invᵉ (right-unit-law-mul-Semiringᵉ Rᵉ xᵉ)) ∙ᵉ
        ( invᵉ
          ( left-unit-law-mul-nat-scalar-Semiringᵉ Rᵉ
            ( mul-Semiringᵉ Rᵉ xᵉ (one-Semiringᵉ Rᵉ)))))) ∙ᵉ
    ( invᵉ
      ( sum-two-elements-Semiringᵉ Rᵉ
        ( λ iᵉ →
          mul-nat-scalar-Semiringᵉ Rᵉ
          ( binomial-coefficient-Finᵉ 1 iᵉ)
          ( mul-Semiringᵉ Rᵉ
            ( power-Semiringᵉ Rᵉ (nat-Finᵉ 2 iᵉ) xᵉ)
            ( power-Semiringᵉ Rᵉ (dist-ℕᵉ (nat-Finᵉ 2 iᵉ) 1ᵉ) yᵉ))))))
binomial-theorem-Semiringᵉ Rᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)) xᵉ yᵉ Hᵉ =
  ( apᵉ
    ( λ rᵉ → mul-Semiringᵉ Rᵉ rᵉ (add-Semiringᵉ Rᵉ xᵉ yᵉ))
    ( binomial-theorem-Semiringᵉ Rᵉ (succ-ℕᵉ nᵉ) xᵉ yᵉ Hᵉ)) ∙ᵉ
  ( ( left-distributive-mul-add-Semiringᵉ Rᵉ _ xᵉ yᵉ) ∙ᵉ
    ( ( ap-add-Semiringᵉ Rᵉ
        ( left-summand-binomial-theorem-Semiringᵉ Rᵉ nᵉ xᵉ yᵉ Hᵉ)
        ( right-summand-binomial-theorem-Semiringᵉ Rᵉ nᵉ xᵉ yᵉ)) ∙ᵉ
      ( ( interchange-add-add-Semiringᵉ Rᵉ
          ( power-Semiringᵉ Rᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)) xᵉ)
          ( sum-Semiringᵉ Rᵉ
            ( succ-ℕᵉ nᵉ)
            ( λ iᵉ →
              mul-nat-scalar-Semiringᵉ Rᵉ
              ( binomial-coefficient-Finᵉ (succ-ℕᵉ nᵉ) (inl-Finᵉ (succ-ℕᵉ nᵉ) iᵉ))
              ( mul-Semiringᵉ Rᵉ
                ( power-Semiringᵉ Rᵉ
                  ( succ-ℕᵉ (nat-Finᵉ (succ-ℕᵉ nᵉ) iᵉ))
                  ( xᵉ))
                ( power-Semiringᵉ Rᵉ
                  ( dist-ℕᵉ (nat-Finᵉ (succ-ℕᵉ nᵉ) iᵉ) (succ-ℕᵉ nᵉ))
                  ( yᵉ)))))
          ( power-Semiringᵉ Rᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)) yᵉ)
          ( sum-Semiringᵉ Rᵉ
            ( succ-ℕᵉ nᵉ)
            ( λ iᵉ →
              mul-nat-scalar-Semiringᵉ Rᵉ
              ( binomial-coefficient-ℕᵉ
                ( succ-ℕᵉ nᵉ)
                ( succ-ℕᵉ (nat-Finᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)) (inl-Finᵉ (succ-ℕᵉ nᵉ) iᵉ))))
              ( mul-Semiringᵉ Rᵉ
                ( power-Semiringᵉ Rᵉ
                  ( succ-ℕᵉ (nat-Finᵉ (succ-ℕᵉ nᵉ) iᵉ))
                  ( xᵉ))
                ( power-Semiringᵉ Rᵉ
                  ( dist-ℕᵉ (nat-Finᵉ (succ-ℕᵉ nᵉ) iᵉ) (succ-ℕᵉ nᵉ))
                  ( yᵉ)))))) ∙ᵉ
        ( ( ap-add-Semiringᵉ Rᵉ
            ( commutative-add-Semiringᵉ Rᵉ
              ( power-Semiringᵉ Rᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)) xᵉ)
              ( power-Semiringᵉ Rᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)) yᵉ))
            ( ( interchange-add-sum-Semiringᵉ Rᵉ
                ( succ-ℕᵉ nᵉ)
                ( λ iᵉ →
                  mul-nat-scalar-Semiringᵉ Rᵉ
                  ( binomial-coefficient-Finᵉ (succ-ℕᵉ nᵉ) (inl-Finᵉ (succ-ℕᵉ nᵉ) iᵉ))
                  ( mul-Semiringᵉ Rᵉ
                    ( power-Semiringᵉ Rᵉ
                      ( succ-ℕᵉ (nat-Finᵉ (succ-ℕᵉ nᵉ) iᵉ))
                      ( xᵉ))
                    ( power-Semiringᵉ Rᵉ
                      ( dist-ℕᵉ (nat-Finᵉ (succ-ℕᵉ nᵉ) iᵉ) (succ-ℕᵉ nᵉ))
                      ( yᵉ))))
                ( λ iᵉ →
                  mul-nat-scalar-Semiringᵉ Rᵉ
                  ( binomial-coefficient-ℕᵉ
                    ( succ-ℕᵉ nᵉ)
                    ( succ-ℕᵉ
                      ( nat-Finᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)) (inl-Finᵉ (succ-ℕᵉ nᵉ) iᵉ))))
                    ( mul-Semiringᵉ Rᵉ
                      ( power-Semiringᵉ Rᵉ
                        ( succ-ℕᵉ (nat-Finᵉ (succ-ℕᵉ nᵉ) iᵉ))
                        ( xᵉ))
                      ( power-Semiringᵉ Rᵉ
                        ( dist-ℕᵉ (nat-Finᵉ (succ-ℕᵉ nᵉ) iᵉ) (succ-ℕᵉ nᵉ))
                        ( yᵉ))))) ∙ᵉ
              ( htpy-sum-Semiringᵉ Rᵉ
                ( succ-ℕᵉ nᵉ)
                ( λ iᵉ →
                  ( invᵉ
                    ( right-distributive-mul-nat-scalar-add-Semiringᵉ Rᵉ
                      ( binomial-coefficient-ℕᵉ
                        ( succ-ℕᵉ nᵉ)
                        ( nat-Finᵉ (succ-ℕᵉ nᵉ) iᵉ))
                      ( binomial-coefficient-ℕᵉ
                        ( succ-ℕᵉ nᵉ)
                        ( succ-ℕᵉ (nat-Finᵉ (succ-ℕᵉ nᵉ) iᵉ)))
                      ( mul-Semiringᵉ Rᵉ
                        ( power-Semiringᵉ Rᵉ
                          ( succ-ℕᵉ (nat-Finᵉ (succ-ℕᵉ nᵉ) iᵉ))
                          ( xᵉ))
                        ( power-Semiringᵉ Rᵉ
                          ( dist-ℕᵉ (nat-Finᵉ (succ-ℕᵉ nᵉ) iᵉ) (succ-ℕᵉ nᵉ))
                          ( yᵉ))))) ∙ᵉ
                  ( apᵉ
                    ( λ mᵉ →
                      mul-nat-scalar-Semiringᵉ Rᵉ
                        ( binomial-coefficient-ℕᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)) mᵉ)
                        ( mul-Semiringᵉ Rᵉ
                          ( power-Semiringᵉ Rᵉ mᵉ xᵉ)
                          ( power-Semiringᵉ Rᵉ
                            ( dist-ℕᵉ mᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)))
                            ( yᵉ))))
                    ( invᵉ (nat-inr-Finᵉ (succ-ℕᵉ nᵉ) iᵉ))))))) ∙ᵉ
          ( ( right-swap-add-Semiringᵉ Rᵉ
              ( power-Semiringᵉ Rᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)) yᵉ)
              ( power-Semiringᵉ Rᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)) xᵉ)
              ( _)) ∙ᵉ
            ( ( apᵉ
                ( add-Semiring'ᵉ Rᵉ
                  ( power-Semiringᵉ Rᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)) xᵉ))
                ( invᵉ
                  ( snoc-sum-Semiringᵉ Rᵉ
                    ( succ-ℕᵉ nᵉ)
                    ( λ iᵉ →
                      mul-nat-scalar-Semiringᵉ Rᵉ
                        ( binomial-coefficient-ℕᵉ
                          ( succ-ℕᵉ (succ-ℕᵉ nᵉ))
                          ( nat-Finᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)) iᵉ))
                        ( mul-Semiringᵉ Rᵉ
                          ( power-Semiringᵉ Rᵉ
                            ( nat-Finᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)) iᵉ)
                            ( xᵉ))
                          ( power-Semiringᵉ Rᵉ
                            ( dist-ℕᵉ
                              ( nat-Finᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)) iᵉ)
                              ( succ-ℕᵉ (succ-ℕᵉ nᵉ)))
                            ( yᵉ))))
                    ( ( apᵉ
                        ( λ mᵉ →
                          mul-nat-scalar-Semiringᵉ Rᵉ
                            ( binomial-coefficient-ℕᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)) mᵉ)
                            ( mul-Semiringᵉ Rᵉ
                              ( power-Semiringᵉ Rᵉ mᵉ xᵉ)
                              ( power-Semiringᵉ Rᵉ
                                ( dist-ℕᵉ mᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)))
                                ( yᵉ))))
                        ( is-zero-nat-zero-Finᵉ {nᵉ})) ∙ᵉ
                      ( ( left-unit-law-mul-nat-scalar-Semiringᵉ Rᵉ
                          ( mul-Semiringᵉ Rᵉ
                            ( one-Semiringᵉ Rᵉ)
                            ( power-Semiringᵉ Rᵉ
                              ( succ-ℕᵉ (succ-ℕᵉ nᵉ))
                              ( yᵉ)))) ∙ᵉ
                        ( left-unit-law-mul-Semiringᵉ Rᵉ
                          ( power-Semiringᵉ Rᵉ
                            ( succ-ℕᵉ (succ-ℕᵉ nᵉ))
                            ( yᵉ)))))))) ∙ᵉ
              ( invᵉ
                ( cons-sum-Semiringᵉ Rᵉ
                  ( succ-ℕᵉ (succ-ℕᵉ nᵉ))
                  ( λ iᵉ →
                    mul-nat-scalar-Semiringᵉ Rᵉ
                      ( binomial-coefficient-Finᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)) iᵉ)
                      ( mul-Semiringᵉ Rᵉ
                        ( power-Semiringᵉ Rᵉ
                          ( nat-Finᵉ (succ-ℕᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ))) iᵉ)
                          ( xᵉ))
                        ( power-Semiringᵉ Rᵉ
                          ( dist-ℕᵉ
                            ( nat-Finᵉ (succ-ℕᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ))) iᵉ)
                            ( succ-ℕᵉ (succ-ℕᵉ nᵉ)))
                          ( yᵉ))))
                  ( ( ap-mul-nat-scalar-Semiringᵉ Rᵉ
                      ( is-one-on-diagonal-binomial-coefficient-ℕᵉ
                        ( succ-ℕᵉ (succ-ℕᵉ nᵉ)))
                      ( ( apᵉ
                          ( mul-Semiringᵉ Rᵉ
                            ( power-Semiringᵉ Rᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)) xᵉ))
                          ( apᵉ
                            ( λ mᵉ → power-Semiringᵉ Rᵉ mᵉ yᵉ)
                            ( dist-eq-ℕ'ᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ))))) ∙ᵉ
                        ( right-unit-law-mul-Semiringᵉ Rᵉ
                          ( power-Semiringᵉ Rᵉ (succ-ℕᵉ (succ-ℕᵉ nᵉ)) xᵉ)))) ∙ᵉ
                    ( left-unit-law-mul-nat-scalar-Semiringᵉ Rᵉ
                      ( power-Semiringᵉ Rᵉ
                        ( succ-ℕᵉ (succ-ℕᵉ nᵉ))
                        ( xᵉ))))))))))))
```

## Corollaries

### If `x` commutes with `y`, then we can compute `(x+y)ⁿ⁺ᵐ` as a linear combination of `xⁿ` and `yᵐ`

```agda
is-linear-combination-power-add-Semiringᵉ :
  {lᵉ : Level} (Rᵉ : Semiringᵉ lᵉ) (nᵉ mᵉ : ℕᵉ) (xᵉ yᵉ : type-Semiringᵉ Rᵉ) →
  mul-Semiringᵉ Rᵉ xᵉ yᵉ ＝ᵉ mul-Semiringᵉ Rᵉ yᵉ xᵉ →
  power-Semiringᵉ Rᵉ (nᵉ +ℕᵉ mᵉ) (add-Semiringᵉ Rᵉ xᵉ yᵉ) ＝ᵉ
  add-Semiringᵉ Rᵉ
    ( mul-Semiringᵉ Rᵉ
      ( power-Semiringᵉ Rᵉ mᵉ yᵉ)
      ( sum-Semiringᵉ Rᵉ nᵉ
        ( λ iᵉ →
          mul-nat-scalar-Semiringᵉ Rᵉ
            ( binomial-coefficient-ℕᵉ (nᵉ +ℕᵉ mᵉ) (nat-Finᵉ nᵉ iᵉ))
            ( mul-Semiringᵉ Rᵉ
              ( power-Semiringᵉ Rᵉ (nat-Finᵉ nᵉ iᵉ) xᵉ)
              ( power-Semiringᵉ Rᵉ (dist-ℕᵉ (nat-Finᵉ nᵉ iᵉ) nᵉ) yᵉ)))))
    ( mul-Semiringᵉ Rᵉ
      ( power-Semiringᵉ Rᵉ nᵉ xᵉ)
      ( sum-Semiringᵉ Rᵉ
        ( succ-ℕᵉ mᵉ)
        ( λ iᵉ →
          mul-nat-scalar-Semiringᵉ Rᵉ
            ( binomial-coefficient-ℕᵉ
              ( nᵉ +ℕᵉ mᵉ)
              ( nᵉ +ℕᵉ (nat-Finᵉ (succ-ℕᵉ mᵉ) iᵉ)))
            ( mul-Semiringᵉ Rᵉ
              ( power-Semiringᵉ Rᵉ (nat-Finᵉ (succ-ℕᵉ mᵉ) iᵉ) xᵉ)
              ( power-Semiringᵉ Rᵉ (dist-ℕᵉ (nat-Finᵉ (succ-ℕᵉ mᵉ) iᵉ) mᵉ) yᵉ)))))
is-linear-combination-power-add-Semiringᵉ Rᵉ nᵉ mᵉ xᵉ yᵉ Hᵉ =
  ( binomial-theorem-Semiringᵉ Rᵉ (nᵉ +ℕᵉ mᵉ) xᵉ yᵉ Hᵉ) ∙ᵉ
  ( ( split-sum-Semiringᵉ Rᵉ nᵉ
      ( succ-ℕᵉ mᵉ)
      ( λ iᵉ →
        mul-nat-scalar-Semiringᵉ Rᵉ
          ( binomial-coefficient-ℕᵉ
            ( nᵉ +ℕᵉ mᵉ)
            ( nat-Finᵉ (nᵉ +ℕᵉ (succ-ℕᵉ mᵉ)) iᵉ))
          ( mul-Semiringᵉ Rᵉ
            ( power-Semiringᵉ Rᵉ
              ( nat-Finᵉ (nᵉ +ℕᵉ (succ-ℕᵉ mᵉ)) iᵉ)
              ( xᵉ))
            ( power-Semiringᵉ Rᵉ
              ( dist-ℕᵉ
                ( nat-Finᵉ (nᵉ +ℕᵉ (succ-ℕᵉ mᵉ)) iᵉ)
                ( nᵉ +ℕᵉ mᵉ))
              ( yᵉ))))) ∙ᵉ
    ( ( ap-add-Semiringᵉ Rᵉ
        ( ( htpy-sum-Semiringᵉ Rᵉ nᵉ
            ( λ iᵉ →
              ( apᵉ
                ( λ uᵉ →
                  mul-nat-scalar-Semiringᵉ Rᵉ
                    ( binomial-coefficient-ℕᵉ (nᵉ +ℕᵉ mᵉ) uᵉ)
                    ( mul-Semiringᵉ Rᵉ
                      ( power-Semiringᵉ Rᵉ uᵉ xᵉ)
                      ( power-Semiringᵉ Rᵉ
                        ( dist-ℕᵉ uᵉ (nᵉ +ℕᵉ mᵉ))
                        ( yᵉ))))
                ( nat-inl-coproduct-Finᵉ nᵉ mᵉ iᵉ)) ∙ᵉ
              ( ( ( apᵉ
                    ( mul-nat-scalar-Semiringᵉ Rᵉ
                      ( binomial-coefficient-ℕᵉ
                        ( nᵉ +ℕᵉ mᵉ)
                        ( nat-Finᵉ nᵉ iᵉ)))
                    ( ( apᵉ
                        ( mul-Semiringᵉ Rᵉ
                          ( power-Semiringᵉ Rᵉ
                            ( nat-Finᵉ nᵉ iᵉ)
                            ( xᵉ)))
                        ( ( apᵉ
                            ( λ uᵉ → power-Semiringᵉ Rᵉ uᵉ yᵉ)
                            ( ( invᵉ
                                ( triangle-equality-dist-ℕᵉ
                                  ( nat-Finᵉ nᵉ iᵉ)
                                  ( nᵉ)
                                  ( nᵉ +ℕᵉ mᵉ)
                                  ( upper-bound-nat-Fin'ᵉ nᵉ iᵉ)
                                  ( leq-add-ℕᵉ nᵉ mᵉ)) ∙ᵉ
                                ( apᵉ
                                  ( (dist-ℕᵉ (nat-Finᵉ nᵉ iᵉ) nᵉ) +ℕᵉ_)
                                  ( dist-add-ℕᵉ nᵉ mᵉ))) ∙ᵉ
                              ( commutative-add-ℕᵉ
                                ( dist-ℕᵉ (nat-Finᵉ nᵉ iᵉ) nᵉ)
                                ( mᵉ)))) ∙ᵉ
                          ( ( distributive-power-add-Semiringᵉ Rᵉ mᵉ
                              ( dist-ℕᵉ (nat-Finᵉ nᵉ iᵉ) nᵉ))))) ∙ᵉ
                      ( ( invᵉ
                          ( associative-mul-Semiringᵉ Rᵉ
                            ( power-Semiringᵉ Rᵉ (nat-Finᵉ nᵉ iᵉ) xᵉ)
                            ( power-Semiringᵉ Rᵉ mᵉ yᵉ)
                            ( power-Semiringᵉ Rᵉ (dist-ℕᵉ (nat-Finᵉ nᵉ iᵉ) nᵉ) yᵉ))) ∙ᵉ
                        ( ( apᵉ
                            ( mul-Semiring'ᵉ Rᵉ
                              ( power-Semiringᵉ Rᵉ (dist-ℕᵉ (nat-Finᵉ nᵉ iᵉ) nᵉ) yᵉ))
                            ( commute-powers-Semiringᵉ Rᵉ (nat-Finᵉ nᵉ iᵉ) mᵉ Hᵉ)) ∙ᵉ
                          ( associative-mul-Semiringᵉ Rᵉ
                            ( power-Semiringᵉ Rᵉ mᵉ yᵉ)
                            ( power-Semiringᵉ Rᵉ (nat-Finᵉ nᵉ iᵉ) xᵉ)
                            ( power-Semiringᵉ Rᵉ
                              ( dist-ℕᵉ (nat-Finᵉ nᵉ iᵉ) nᵉ)
                              ( yᵉ))))))) ∙ᵉ
                  ( invᵉ
                    ( right-nat-scalar-law-mul-Semiringᵉ Rᵉ
                      ( binomial-coefficient-ℕᵉ
                        ( nᵉ +ℕᵉ mᵉ)
                        ( nat-Finᵉ nᵉ iᵉ))
                      ( power-Semiringᵉ Rᵉ mᵉ yᵉ)
                      ( mul-Semiringᵉ Rᵉ
                        ( power-Semiringᵉ Rᵉ (nat-Finᵉ nᵉ iᵉ) xᵉ)
                        ( power-Semiringᵉ Rᵉ
                          ( dist-ℕᵉ (nat-Finᵉ nᵉ iᵉ) nᵉ)
                          ( yᵉ))))))))) ∙ᵉ
          ( ( invᵉ
              ( left-distributive-mul-sum-Semiringᵉ Rᵉ nᵉ
                ( power-Semiringᵉ Rᵉ mᵉ yᵉ)
                ( λ iᵉ →
                  mul-nat-scalar-Semiringᵉ Rᵉ
                    ( binomial-coefficient-ℕᵉ (nᵉ +ℕᵉ mᵉ) (nat-Finᵉ nᵉ iᵉ))
                    ( mul-Semiringᵉ Rᵉ
                      ( power-Semiringᵉ Rᵉ (nat-Finᵉ nᵉ iᵉ) xᵉ)
                      ( power-Semiringᵉ Rᵉ (dist-ℕᵉ (nat-Finᵉ nᵉ iᵉ) nᵉ) yᵉ)))))))
        ( ( htpy-sum-Semiringᵉ Rᵉ
            ( succ-ℕᵉ mᵉ)
            ( λ iᵉ →
              ( apᵉ
                ( λ uᵉ →
                  mul-nat-scalar-Semiringᵉ Rᵉ
                    ( binomial-coefficient-ℕᵉ (nᵉ +ℕᵉ mᵉ) uᵉ)
                    ( mul-Semiringᵉ Rᵉ
                      ( power-Semiringᵉ Rᵉ uᵉ xᵉ)
                      ( power-Semiringᵉ Rᵉ
                        ( dist-ℕᵉ uᵉ (nᵉ +ℕᵉ mᵉ))
                        ( yᵉ))))
                ( nat-inr-coproduct-Finᵉ nᵉ (succ-ℕᵉ mᵉ) iᵉ)) ∙ᵉ
              ( ( apᵉ
                  ( mul-nat-scalar-Semiringᵉ Rᵉ
                    ( binomial-coefficient-ℕᵉ
                      ( nᵉ +ℕᵉ mᵉ)
                      ( nᵉ +ℕᵉ (nat-Finᵉ (succ-ℕᵉ mᵉ) iᵉ))))
                  ( ap-mul-Semiringᵉ Rᵉ
                    ( distributive-power-add-Semiringᵉ Rᵉ nᵉ
                      ( nat-Finᵉ (succ-ℕᵉ mᵉ) iᵉ))
                    ( apᵉ
                      ( λ uᵉ → power-Semiringᵉ Rᵉ uᵉ yᵉ)
                      ( translation-invariant-dist-ℕᵉ
                        ( nᵉ)
                        ( nat-Finᵉ (succ-ℕᵉ mᵉ) iᵉ)
                        ( mᵉ))) ∙ᵉ
                    ( associative-mul-Semiringᵉ Rᵉ
                      ( power-Semiringᵉ Rᵉ nᵉ xᵉ)
                      ( power-Semiringᵉ Rᵉ (nat-Finᵉ (succ-ℕᵉ mᵉ) iᵉ) xᵉ)
                      ( power-Semiringᵉ Rᵉ
                        ( dist-ℕᵉ (nat-Finᵉ (succ-ℕᵉ mᵉ) iᵉ) mᵉ)
                        ( yᵉ))))) ∙ᵉ
                ( invᵉ
                  ( right-nat-scalar-law-mul-Semiringᵉ Rᵉ
                    ( binomial-coefficient-ℕᵉ
                      ( nᵉ +ℕᵉ mᵉ)
                      ( nᵉ +ℕᵉ (nat-Finᵉ (succ-ℕᵉ mᵉ) iᵉ)))
                    ( power-Semiringᵉ Rᵉ nᵉ xᵉ)
                    ( mul-Semiringᵉ Rᵉ
                      ( power-Semiringᵉ Rᵉ (nat-Finᵉ (succ-ℕᵉ mᵉ) iᵉ) xᵉ)
                      ( power-Semiringᵉ Rᵉ
                        ( dist-ℕᵉ (nat-Finᵉ (succ-ℕᵉ mᵉ) iᵉ) mᵉ)
                        ( yᵉ)))))))) ∙ᵉ
          ( invᵉ
            ( left-distributive-mul-sum-Semiringᵉ Rᵉ
              ( succ-ℕᵉ mᵉ)
              ( power-Semiringᵉ Rᵉ nᵉ xᵉ)
              ( λ iᵉ →
                mul-nat-scalar-Semiringᵉ Rᵉ
                  ( binomial-coefficient-ℕᵉ
                    ( nᵉ +ℕᵉ mᵉ)
                    ( nᵉ +ℕᵉ (nat-Finᵉ (succ-ℕᵉ mᵉ) iᵉ)))
                  ( mul-Semiringᵉ Rᵉ
                    ( power-Semiringᵉ Rᵉ (nat-Finᵉ (succ-ℕᵉ mᵉ) iᵉ) xᵉ)
                    ( power-Semiringᵉ Rᵉ
                      ( dist-ℕᵉ (nat-Finᵉ (succ-ℕᵉ mᵉ) iᵉ) mᵉ)
                      ( yᵉ))))))))))
```