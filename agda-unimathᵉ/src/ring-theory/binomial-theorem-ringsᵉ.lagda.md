# The binomial theorem for rings

```agda
module ring-theory.binomial-theorem-ringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbersᵉ
open import elementary-number-theory.binomial-coefficientsᵉ
open import elementary-number-theory.distance-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ

open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ

open import linear-algebra.vectors-on-ringsᵉ

open import ring-theory.binomial-theorem-semiringsᵉ
open import ring-theory.powers-of-elements-ringsᵉ
open import ring-theory.ringsᵉ
open import ring-theory.sums-ringsᵉ

open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Theᵉ binomialᵉ theoremᵉ forᵉ ringsᵉ assertsᵉ thatᵉ forᵉ anyᵉ twoᵉ elementsᵉ `x`ᵉ andᵉ `y`ᵉ ofᵉ
aᵉ commutativeᵉ ringᵉ `R`ᵉ andᵉ anyᵉ naturalᵉ numberᵉ `n`,ᵉ ifᵉ `xyᵉ ＝ᵉ yx`ᵉ holdsᵉ thenᵉ weᵉ
haveᵉ

```text
  (xᵉ +ᵉ y)ⁿᵉ = ∑_{0ᵉ ≤ᵉ iᵉ <ᵉ n+1ᵉ} (nᵉ chooseᵉ iᵉ) xⁱᵉ yⁿ⁻ⁱ.ᵉ
```

## Definitions

### Binomial sums

```agda
binomial-sum-Ringᵉ :
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  (nᵉ : ℕᵉ) (fᵉ : functional-vec-Ringᵉ Rᵉ (succ-ℕᵉ nᵉ)) → type-Ringᵉ Rᵉ
binomial-sum-Ringᵉ Rᵉ = binomial-sum-Semiringᵉ (semiring-Ringᵉ Rᵉ)
```

## Properties

### Binomial sums of one and two elements

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  binomial-sum-one-element-Ringᵉ :
    (fᵉ : functional-vec-Ringᵉ Rᵉ 1ᵉ) →
    binomial-sum-Ringᵉ Rᵉ 0 fᵉ ＝ᵉ head-functional-vec-Ringᵉ Rᵉ 0 fᵉ
  binomial-sum-one-element-Ringᵉ =
    binomial-sum-one-element-Semiringᵉ (semiring-Ringᵉ Rᵉ)

  binomial-sum-two-elements-Ringᵉ :
    (fᵉ : functional-vec-Ringᵉ Rᵉ 2ᵉ) →
    binomial-sum-Ringᵉ Rᵉ 1 fᵉ ＝ᵉ add-Ringᵉ Rᵉ (fᵉ (zero-Finᵉ 1ᵉ)) (fᵉ (one-Finᵉ 1ᵉ))
  binomial-sum-two-elements-Ringᵉ =
    binomial-sum-two-elements-Semiringᵉ (semiring-Ringᵉ Rᵉ)
```

### Binomial sums are homotopy invariant

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  htpy-binomial-sum-Ringᵉ :
    (nᵉ : ℕᵉ) {fᵉ gᵉ : functional-vec-Ringᵉ Rᵉ (succ-ℕᵉ nᵉ)} →
    (fᵉ ~ᵉ gᵉ) → binomial-sum-Ringᵉ Rᵉ nᵉ fᵉ ＝ᵉ binomial-sum-Ringᵉ Rᵉ nᵉ gᵉ
  htpy-binomial-sum-Ringᵉ = htpy-binomial-sum-Semiringᵉ (semiring-Ringᵉ Rᵉ)
```

### Multiplication distributes over sums

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  left-distributive-mul-binomial-sum-Ringᵉ :
    (nᵉ : ℕᵉ) (xᵉ : type-Ringᵉ Rᵉ) (fᵉ : functional-vec-Ringᵉ Rᵉ (succ-ℕᵉ nᵉ)) →
    mul-Ringᵉ Rᵉ xᵉ (binomial-sum-Ringᵉ Rᵉ nᵉ fᵉ) ＝ᵉ
    binomial-sum-Ringᵉ Rᵉ nᵉ (λ iᵉ → mul-Ringᵉ Rᵉ xᵉ (fᵉ iᵉ))
  left-distributive-mul-binomial-sum-Ringᵉ =
    left-distributive-mul-binomial-sum-Semiringᵉ (semiring-Ringᵉ Rᵉ)

  right-distributive-mul-binomial-sum-Ringᵉ :
    (nᵉ : ℕᵉ) (fᵉ : functional-vec-Ringᵉ Rᵉ (succ-ℕᵉ nᵉ)) (xᵉ : type-Ringᵉ Rᵉ) →
    mul-Ringᵉ Rᵉ (binomial-sum-Ringᵉ Rᵉ nᵉ fᵉ) xᵉ ＝ᵉ
    binomial-sum-Ringᵉ Rᵉ nᵉ (λ iᵉ → mul-Ringᵉ Rᵉ (fᵉ iᵉ) xᵉ)
  right-distributive-mul-binomial-sum-Ringᵉ =
    right-distributive-mul-binomial-sum-Semiringᵉ (semiring-Ringᵉ Rᵉ)
```

## Theorem

### Binomial theorem for rings

```agda
binomial-theorem-Ringᵉ :
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ) (nᵉ : ℕᵉ) (xᵉ yᵉ : type-Ringᵉ Rᵉ) →
  mul-Ringᵉ Rᵉ xᵉ yᵉ ＝ᵉ mul-Ringᵉ Rᵉ yᵉ xᵉ →
  power-Ringᵉ Rᵉ nᵉ (add-Ringᵉ Rᵉ xᵉ yᵉ) ＝ᵉ
  binomial-sum-Ringᵉ Rᵉ nᵉ
    ( λ iᵉ →
      mul-Ringᵉ Rᵉ
      ( power-Ringᵉ Rᵉ (nat-Finᵉ (succ-ℕᵉ nᵉ) iᵉ) xᵉ)
      ( power-Ringᵉ Rᵉ (dist-ℕᵉ (nat-Finᵉ (succ-ℕᵉ nᵉ) iᵉ) nᵉ) yᵉ))
binomial-theorem-Ringᵉ Rᵉ = binomial-theorem-Semiringᵉ (semiring-Ringᵉ Rᵉ)
```

## Corollaries

### If `x` commutes with `y`, then we can compute `(x+y)ⁿ⁺ᵐ` as a linear combination of `xⁿ` and `yᵐ`

```agda
is-linear-combination-power-add-Ringᵉ :
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ) (nᵉ mᵉ : ℕᵉ) (xᵉ yᵉ : type-Ringᵉ Rᵉ) →
  mul-Ringᵉ Rᵉ xᵉ yᵉ ＝ᵉ mul-Ringᵉ Rᵉ yᵉ xᵉ →
  power-Ringᵉ Rᵉ (nᵉ +ℕᵉ mᵉ) (add-Ringᵉ Rᵉ xᵉ yᵉ) ＝ᵉ
  add-Ringᵉ Rᵉ
    ( mul-Ringᵉ Rᵉ
      ( power-Ringᵉ Rᵉ mᵉ yᵉ)
      ( sum-Ringᵉ Rᵉ nᵉ
        ( λ iᵉ →
          mul-nat-scalar-Ringᵉ Rᵉ
            ( binomial-coefficient-ℕᵉ (nᵉ +ℕᵉ mᵉ) (nat-Finᵉ nᵉ iᵉ))
            ( mul-Ringᵉ Rᵉ
              ( power-Ringᵉ Rᵉ (nat-Finᵉ nᵉ iᵉ) xᵉ)
              ( power-Ringᵉ Rᵉ (dist-ℕᵉ (nat-Finᵉ nᵉ iᵉ) nᵉ) yᵉ)))))
    ( mul-Ringᵉ Rᵉ
      ( power-Ringᵉ Rᵉ nᵉ xᵉ)
      ( sum-Ringᵉ Rᵉ
        ( succ-ℕᵉ mᵉ)
        ( λ iᵉ →
          mul-nat-scalar-Ringᵉ Rᵉ
            ( binomial-coefficient-ℕᵉ
              ( nᵉ +ℕᵉ mᵉ)
              ( nᵉ +ℕᵉ (nat-Finᵉ (succ-ℕᵉ mᵉ) iᵉ)))
            ( mul-Ringᵉ Rᵉ
              ( power-Ringᵉ Rᵉ (nat-Finᵉ (succ-ℕᵉ mᵉ) iᵉ) xᵉ)
              ( power-Ringᵉ Rᵉ (dist-ℕᵉ (nat-Finᵉ (succ-ℕᵉ mᵉ) iᵉ) mᵉ) yᵉ)))))
is-linear-combination-power-add-Ringᵉ Rᵉ =
  is-linear-combination-power-add-Semiringᵉ (semiring-Ringᵉ Rᵉ)
```