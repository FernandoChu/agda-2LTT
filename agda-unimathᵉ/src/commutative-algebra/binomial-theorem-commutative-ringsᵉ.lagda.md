# The binomial theorem in commutative rings

```agda
module commutative-algebra.binomial-theorem-commutative-ringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.binomial-theorem-commutative-semiringsᵉ
open import commutative-algebra.commutative-ringsᵉ
open import commutative-algebra.powers-of-elements-commutative-ringsᵉ
open import commutative-algebra.sums-commutative-ringsᵉ

open import elementary-number-theory.addition-natural-numbersᵉ
open import elementary-number-theory.binomial-coefficientsᵉ
open import elementary-number-theory.distance-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ

open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ

open import linear-algebra.vectors-on-commutative-ringsᵉ

open import ring-theory.binomial-theorem-ringsᵉ

open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Theᵉ **binomialᵉ theorem**ᵉ in commutativeᵉ ringsᵉ assertsᵉ thatᵉ forᵉ anyᵉ twoᵉ elementsᵉ
`x`ᵉ andᵉ `y`ᵉ ofᵉ aᵉ commutativeᵉ ringᵉ `A`ᵉ andᵉ anyᵉ naturalᵉ numberᵉ `n`,ᵉ weᵉ haveᵉ

```text
  (xᵉ +ᵉ y)ⁿᵉ = ∑_{0ᵉ ≤ᵉ iᵉ <ᵉ n+1ᵉ} (nᵉ chooseᵉ iᵉ) xⁱᵉ yⁿ⁻ⁱ.ᵉ
```

## Definitions

### Binomial sums

```agda
binomial-sum-Commutative-Ringᵉ :
  {lᵉ : Level} (Aᵉ : Commutative-Ringᵉ lᵉ)
  (nᵉ : ℕᵉ) (fᵉ : functional-vec-Commutative-Ringᵉ Aᵉ (succ-ℕᵉ nᵉ)) →
  type-Commutative-Ringᵉ Aᵉ
binomial-sum-Commutative-Ringᵉ Aᵉ = binomial-sum-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)
```

## Properties

### Binomial sums of one and two elements

```agda
module _
  {lᵉ : Level} (Aᵉ : Commutative-Ringᵉ lᵉ)
  where

  binomial-sum-one-element-Commutative-Ringᵉ :
    (fᵉ : functional-vec-Commutative-Ringᵉ Aᵉ 1ᵉ) →
    binomial-sum-Commutative-Ringᵉ Aᵉ 0 fᵉ ＝ᵉ
    head-functional-vec-Commutative-Ringᵉ Aᵉ 0 fᵉ
  binomial-sum-one-element-Commutative-Ringᵉ =
    binomial-sum-one-element-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)

  binomial-sum-two-elements-Commutative-Ringᵉ :
    (fᵉ : functional-vec-Commutative-Ringᵉ Aᵉ 2ᵉ) →
    binomial-sum-Commutative-Ringᵉ Aᵉ 1 fᵉ ＝ᵉ
    add-Commutative-Ringᵉ Aᵉ (fᵉ (zero-Finᵉ 1ᵉ)) (fᵉ (one-Finᵉ 1ᵉ))
  binomial-sum-two-elements-Commutative-Ringᵉ =
    binomial-sum-two-elements-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)
```

### Binomial sums are homotopy invariant

```agda
module _
  {lᵉ : Level} (Aᵉ : Commutative-Ringᵉ lᵉ)
  where

  htpy-binomial-sum-Commutative-Ringᵉ :
    (nᵉ : ℕᵉ) {fᵉ gᵉ : functional-vec-Commutative-Ringᵉ Aᵉ (succ-ℕᵉ nᵉ)} →
    (fᵉ ~ᵉ gᵉ) →
    binomial-sum-Commutative-Ringᵉ Aᵉ nᵉ fᵉ ＝ᵉ binomial-sum-Commutative-Ringᵉ Aᵉ nᵉ gᵉ
  htpy-binomial-sum-Commutative-Ringᵉ =
    htpy-binomial-sum-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)
```

### Multiplication distributes over sums

```agda
module _
  {lᵉ : Level} (Aᵉ : Commutative-Ringᵉ lᵉ)
  where

  left-distributive-mul-binomial-sum-Commutative-Ringᵉ :
    (nᵉ : ℕᵉ) (xᵉ : type-Commutative-Ringᵉ Aᵉ)
    (fᵉ : functional-vec-Commutative-Ringᵉ Aᵉ (succ-ℕᵉ nᵉ)) →
    mul-Commutative-Ringᵉ Aᵉ xᵉ (binomial-sum-Commutative-Ringᵉ Aᵉ nᵉ fᵉ) ＝ᵉ
    binomial-sum-Commutative-Ringᵉ Aᵉ nᵉ (λ iᵉ → mul-Commutative-Ringᵉ Aᵉ xᵉ (fᵉ iᵉ))
  left-distributive-mul-binomial-sum-Commutative-Ringᵉ =
    left-distributive-mul-binomial-sum-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)

  right-distributive-mul-binomial-sum-Commutative-Ringᵉ :
    (nᵉ : ℕᵉ) (fᵉ : functional-vec-Commutative-Ringᵉ Aᵉ (succ-ℕᵉ nᵉ)) →
    (xᵉ : type-Commutative-Ringᵉ Aᵉ) →
    mul-Commutative-Ringᵉ Aᵉ (binomial-sum-Commutative-Ringᵉ Aᵉ nᵉ fᵉ) xᵉ ＝ᵉ
    binomial-sum-Commutative-Ringᵉ Aᵉ nᵉ (λ iᵉ → mul-Commutative-Ringᵉ Aᵉ (fᵉ iᵉ) xᵉ)
  right-distributive-mul-binomial-sum-Commutative-Ringᵉ =
    right-distributive-mul-binomial-sum-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)
```

## Theorem

### Binomial theorem for commutative rings

```agda
binomial-theorem-Commutative-Ringᵉ :
  {lᵉ : Level} (Aᵉ : Commutative-Ringᵉ lᵉ) →
  (nᵉ : ℕᵉ) (xᵉ yᵉ : type-Commutative-Ringᵉ Aᵉ) →
  power-Commutative-Ringᵉ Aᵉ nᵉ (add-Commutative-Ringᵉ Aᵉ xᵉ yᵉ) ＝ᵉ
  binomial-sum-Commutative-Ringᵉ Aᵉ nᵉ
    ( λ iᵉ →
      mul-Commutative-Ringᵉ Aᵉ
      ( power-Commutative-Ringᵉ Aᵉ (nat-Finᵉ (succ-ℕᵉ nᵉ) iᵉ) xᵉ)
      ( power-Commutative-Ringᵉ Aᵉ (dist-ℕᵉ (nat-Finᵉ (succ-ℕᵉ nᵉ) iᵉ) nᵉ) yᵉ))
binomial-theorem-Commutative-Ringᵉ Aᵉ nᵉ xᵉ yᵉ =
  binomial-theorem-Ringᵉ
    ( ring-Commutative-Ringᵉ Aᵉ)
    ( nᵉ)
    ( xᵉ)
    ( yᵉ)
    ( commutative-mul-Commutative-Ringᵉ Aᵉ xᵉ yᵉ)
```

## Corollaries

### Computing `(x+y)ⁿ⁺ᵐ` as a linear combination of `xⁿ` and `yᵐ`

```agda
is-linear-combination-power-add-Commutative-Ringᵉ :
  {lᵉ : Level} (Aᵉ : Commutative-Ringᵉ lᵉ) (nᵉ mᵉ : ℕᵉ)
  (xᵉ yᵉ : type-Commutative-Ringᵉ Aᵉ) →
  power-Commutative-Ringᵉ Aᵉ (nᵉ +ℕᵉ mᵉ) (add-Commutative-Ringᵉ Aᵉ xᵉ yᵉ) ＝ᵉ
  add-Commutative-Ringᵉ Aᵉ
    ( mul-Commutative-Ringᵉ Aᵉ
      ( power-Commutative-Ringᵉ Aᵉ mᵉ yᵉ)
      ( sum-Commutative-Ringᵉ Aᵉ nᵉ
        ( λ iᵉ →
          mul-nat-scalar-Commutative-Ringᵉ Aᵉ
            ( binomial-coefficient-ℕᵉ (nᵉ +ℕᵉ mᵉ) (nat-Finᵉ nᵉ iᵉ))
            ( mul-Commutative-Ringᵉ Aᵉ
              ( power-Commutative-Ringᵉ Aᵉ (nat-Finᵉ nᵉ iᵉ) xᵉ)
              ( power-Commutative-Ringᵉ Aᵉ (dist-ℕᵉ (nat-Finᵉ nᵉ iᵉ) nᵉ) yᵉ)))))
    ( mul-Commutative-Ringᵉ Aᵉ
      ( power-Commutative-Ringᵉ Aᵉ nᵉ xᵉ)
      ( sum-Commutative-Ringᵉ Aᵉ
        ( succ-ℕᵉ mᵉ)
        ( λ iᵉ →
          mul-nat-scalar-Commutative-Ringᵉ Aᵉ
            ( binomial-coefficient-ℕᵉ
              ( nᵉ +ℕᵉ mᵉ)
              ( nᵉ +ℕᵉ (nat-Finᵉ (succ-ℕᵉ mᵉ) iᵉ)))
            ( mul-Commutative-Ringᵉ Aᵉ
              ( power-Commutative-Ringᵉ Aᵉ (nat-Finᵉ (succ-ℕᵉ mᵉ) iᵉ) xᵉ)
              ( power-Commutative-Ringᵉ Aᵉ
                ( dist-ℕᵉ (nat-Finᵉ (succ-ℕᵉ mᵉ) iᵉ) mᵉ)
                ( yᵉ))))))
is-linear-combination-power-add-Commutative-Ringᵉ Aᵉ =
  is-linear-combination-power-add-Commutative-Semiringᵉ
    ( commutative-semiring-Commutative-Ringᵉ Aᵉ)
```