# The binomial theorem in commutative semirings

```agda
module commutative-algebra.binomial-theorem-commutative-semiringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-semiringsᵉ
open import commutative-algebra.powers-of-elements-commutative-semiringsᵉ
open import commutative-algebra.sums-commutative-semiringsᵉ

open import elementary-number-theory.addition-natural-numbersᵉ
open import elementary-number-theory.binomial-coefficientsᵉ
open import elementary-number-theory.distance-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ

open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ

open import linear-algebra.vectors-on-commutative-semiringsᵉ

open import ring-theory.binomial-theorem-semiringsᵉ

open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Theᵉ **binomialᵉ theorem**ᵉ in commutativeᵉ semiringsᵉ assertsᵉ thatᵉ forᵉ anyᵉ twoᵉ
elementsᵉ `x`ᵉ andᵉ `y`ᵉ ofᵉ aᵉ commutativeᵉ semiringᵉ `A`ᵉ andᵉ anyᵉ naturalᵉ numberᵉ `n`,ᵉ
weᵉ haveᵉ

```text
  (xᵉ +ᵉ y)ⁿᵉ = ∑_{0ᵉ ≤ᵉ iᵉ <ᵉ n+1ᵉ} (nᵉ chooseᵉ iᵉ) xⁱᵉ yⁿ⁻ⁱ.ᵉ
```

## Definitions

### Binomial sums

```agda
binomial-sum-Commutative-Semiringᵉ :
  {lᵉ : Level} (Aᵉ : Commutative-Semiringᵉ lᵉ)
  (nᵉ : ℕᵉ) (fᵉ : functional-vec-Commutative-Semiringᵉ Aᵉ (succ-ℕᵉ nᵉ)) →
  type-Commutative-Semiringᵉ Aᵉ
binomial-sum-Commutative-Semiringᵉ Aᵉ =
  binomial-sum-Semiringᵉ (semiring-Commutative-Semiringᵉ Aᵉ)
```

## Properties

### Binomial sums of one and two elements

```agda
module _
  {lᵉ : Level} (Aᵉ : Commutative-Semiringᵉ lᵉ)
  where

  binomial-sum-one-element-Commutative-Semiringᵉ :
    (fᵉ : functional-vec-Commutative-Semiringᵉ Aᵉ 1ᵉ) →
    binomial-sum-Commutative-Semiringᵉ Aᵉ 0 fᵉ ＝ᵉ
    head-functional-vec-Commutative-Semiringᵉ Aᵉ 0 fᵉ
  binomial-sum-one-element-Commutative-Semiringᵉ =
    binomial-sum-one-element-Semiringᵉ (semiring-Commutative-Semiringᵉ Aᵉ)

  binomial-sum-two-elements-Commutative-Semiringᵉ :
    (fᵉ : functional-vec-Commutative-Semiringᵉ Aᵉ 2ᵉ) →
    binomial-sum-Commutative-Semiringᵉ Aᵉ 1 fᵉ ＝ᵉ
    add-Commutative-Semiringᵉ Aᵉ (fᵉ (zero-Finᵉ 1ᵉ)) (fᵉ (one-Finᵉ 1ᵉ))
  binomial-sum-two-elements-Commutative-Semiringᵉ =
    binomial-sum-two-elements-Semiringᵉ (semiring-Commutative-Semiringᵉ Aᵉ)
```

### Binomial sums are homotopy invariant

```agda
module _
  {lᵉ : Level} (Aᵉ : Commutative-Semiringᵉ lᵉ)
  where

  htpy-binomial-sum-Commutative-Semiringᵉ :
    (nᵉ : ℕᵉ) {fᵉ gᵉ : functional-vec-Commutative-Semiringᵉ Aᵉ (succ-ℕᵉ nᵉ)} →
    (fᵉ ~ᵉ gᵉ) →
    binomial-sum-Commutative-Semiringᵉ Aᵉ nᵉ fᵉ ＝ᵉ
    binomial-sum-Commutative-Semiringᵉ Aᵉ nᵉ gᵉ
  htpy-binomial-sum-Commutative-Semiringᵉ =
    htpy-binomial-sum-Semiringᵉ (semiring-Commutative-Semiringᵉ Aᵉ)
```

### Multiplication distributes over sums

```agda
module _
  {lᵉ : Level} (Aᵉ : Commutative-Semiringᵉ lᵉ)
  where

  left-distributive-mul-binomial-sum-Commutative-Semiringᵉ :
    (nᵉ : ℕᵉ) (xᵉ : type-Commutative-Semiringᵉ Aᵉ)
    (fᵉ : functional-vec-Commutative-Semiringᵉ Aᵉ (succ-ℕᵉ nᵉ)) →
    mul-Commutative-Semiringᵉ Aᵉ xᵉ (binomial-sum-Commutative-Semiringᵉ Aᵉ nᵉ fᵉ) ＝ᵉ
    binomial-sum-Commutative-Semiringᵉ Aᵉ nᵉ
      ( λ iᵉ → mul-Commutative-Semiringᵉ Aᵉ xᵉ (fᵉ iᵉ))
  left-distributive-mul-binomial-sum-Commutative-Semiringᵉ =
    left-distributive-mul-binomial-sum-Semiringᵉ
      ( semiring-Commutative-Semiringᵉ Aᵉ)

  right-distributive-mul-binomial-sum-Commutative-Semiringᵉ :
    (nᵉ : ℕᵉ) (fᵉ : functional-vec-Commutative-Semiringᵉ Aᵉ (succ-ℕᵉ nᵉ)) →
    (xᵉ : type-Commutative-Semiringᵉ Aᵉ) →
    mul-Commutative-Semiringᵉ Aᵉ (binomial-sum-Commutative-Semiringᵉ Aᵉ nᵉ fᵉ) xᵉ ＝ᵉ
    binomial-sum-Commutative-Semiringᵉ Aᵉ nᵉ
      ( λ iᵉ → mul-Commutative-Semiringᵉ Aᵉ (fᵉ iᵉ) xᵉ)
  right-distributive-mul-binomial-sum-Commutative-Semiringᵉ =
    right-distributive-mul-binomial-sum-Semiringᵉ
      ( semiring-Commutative-Semiringᵉ Aᵉ)
```

## Theorem

### Binomial theorem for commutative rings

```agda
binomial-theorem-Commutative-Semiringᵉ :
  {lᵉ : Level} (Aᵉ : Commutative-Semiringᵉ lᵉ) →
  (nᵉ : ℕᵉ) (xᵉ yᵉ : type-Commutative-Semiringᵉ Aᵉ) →
  power-Commutative-Semiringᵉ Aᵉ nᵉ (add-Commutative-Semiringᵉ Aᵉ xᵉ yᵉ) ＝ᵉ
  binomial-sum-Commutative-Semiringᵉ Aᵉ nᵉ
    ( λ iᵉ →
      mul-Commutative-Semiringᵉ Aᵉ
      ( power-Commutative-Semiringᵉ Aᵉ (nat-Finᵉ (succ-ℕᵉ nᵉ) iᵉ) xᵉ)
      ( power-Commutative-Semiringᵉ Aᵉ (dist-ℕᵉ (nat-Finᵉ (succ-ℕᵉ nᵉ) iᵉ) nᵉ) yᵉ))
binomial-theorem-Commutative-Semiringᵉ Aᵉ nᵉ xᵉ yᵉ =
  binomial-theorem-Semiringᵉ
    ( semiring-Commutative-Semiringᵉ Aᵉ)
    ( nᵉ)
    ( xᵉ)
    ( yᵉ)
    ( commutative-mul-Commutative-Semiringᵉ Aᵉ xᵉ yᵉ)
```

## Corollaries

### Computing `(x+y)ⁿ⁺ᵐ` as a linear combination of `xⁿ` and `yᵐ`

```agda
is-linear-combination-power-add-Commutative-Semiringᵉ :
  {lᵉ : Level} (Aᵉ : Commutative-Semiringᵉ lᵉ) (nᵉ mᵉ : ℕᵉ)
  (xᵉ yᵉ : type-Commutative-Semiringᵉ Aᵉ) →
  power-Commutative-Semiringᵉ Aᵉ (nᵉ +ℕᵉ mᵉ) (add-Commutative-Semiringᵉ Aᵉ xᵉ yᵉ) ＝ᵉ
  add-Commutative-Semiringᵉ Aᵉ
    ( mul-Commutative-Semiringᵉ Aᵉ
      ( power-Commutative-Semiringᵉ Aᵉ mᵉ yᵉ)
      ( sum-Commutative-Semiringᵉ Aᵉ nᵉ
        ( λ iᵉ →
          mul-nat-scalar-Commutative-Semiringᵉ Aᵉ
            ( binomial-coefficient-ℕᵉ (nᵉ +ℕᵉ mᵉ) (nat-Finᵉ nᵉ iᵉ))
            ( mul-Commutative-Semiringᵉ Aᵉ
              ( power-Commutative-Semiringᵉ Aᵉ (nat-Finᵉ nᵉ iᵉ) xᵉ)
              ( power-Commutative-Semiringᵉ Aᵉ (dist-ℕᵉ (nat-Finᵉ nᵉ iᵉ) nᵉ) yᵉ)))))
    ( mul-Commutative-Semiringᵉ Aᵉ
      ( power-Commutative-Semiringᵉ Aᵉ nᵉ xᵉ)
      ( sum-Commutative-Semiringᵉ Aᵉ
        ( succ-ℕᵉ mᵉ)
        ( λ iᵉ →
          mul-nat-scalar-Commutative-Semiringᵉ Aᵉ
            ( binomial-coefficient-ℕᵉ
              ( nᵉ +ℕᵉ mᵉ)
              ( nᵉ +ℕᵉ (nat-Finᵉ (succ-ℕᵉ mᵉ) iᵉ)))
            ( mul-Commutative-Semiringᵉ Aᵉ
              ( power-Commutative-Semiringᵉ Aᵉ (nat-Finᵉ (succ-ℕᵉ mᵉ) iᵉ) xᵉ)
              ( power-Commutative-Semiringᵉ Aᵉ
                ( dist-ℕᵉ (nat-Finᵉ (succ-ℕᵉ mᵉ) iᵉ) mᵉ)
                ( yᵉ))))))
is-linear-combination-power-add-Commutative-Semiringᵉ Aᵉ nᵉ mᵉ xᵉ yᵉ =
  is-linear-combination-power-add-Semiringᵉ
    ( semiring-Commutative-Semiringᵉ Aᵉ)
    ( nᵉ)
    ( mᵉ)
    ( xᵉ)
    ( yᵉ)
    ( commutative-mul-Commutative-Semiringᵉ Aᵉ xᵉ yᵉ)
```