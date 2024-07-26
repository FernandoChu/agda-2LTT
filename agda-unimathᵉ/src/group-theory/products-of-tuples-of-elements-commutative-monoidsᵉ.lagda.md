# Products of tuples of elements in commutative monoids

```agda
module group-theory.products-of-tuples-of-elements-commutative-monoidsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.coproduct-typesᵉ
open import foundation.function-typesᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import group-theory.commutative-monoidsᵉ

open import univalent-combinatorics.countingᵉ
open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Givenᵉ anᵉ unorderedᵉ `n`-tupleᵉ ofᵉ elementsᵉ in aᵉ commutativeᵉ monoid,ᵉ weᵉ canᵉ defineᵉ
theirᵉ product.ᵉ

## Definition

### Products of ordered n-tuples of elements in commutative monoids

```agda
module _
  {lᵉ : Level} (Mᵉ : Commutative-Monoidᵉ lᵉ)
  where

  mul-fin-Commutative-Monoidᵉ :
    (nᵉ : ℕᵉ) → (Finᵉ nᵉ → type-Commutative-Monoidᵉ Mᵉ) → type-Commutative-Monoidᵉ Mᵉ
  mul-fin-Commutative-Monoidᵉ zero-ℕᵉ xᵉ = unit-Commutative-Monoidᵉ Mᵉ
  mul-fin-Commutative-Monoidᵉ (succ-ℕᵉ nᵉ) xᵉ =
    mul-Commutative-Monoidᵉ Mᵉ
      ( mul-fin-Commutative-Monoidᵉ nᵉ (xᵉ ∘ᵉ inlᵉ))
      ( xᵉ (inrᵉ starᵉ))

  mul-count-Commutative-Monoidᵉ :
    {l2ᵉ : Level} {Aᵉ : UUᵉ l2ᵉ} → countᵉ Aᵉ →
    (Aᵉ → type-Commutative-Monoidᵉ Mᵉ) → type-Commutative-Monoidᵉ Mᵉ
  mul-count-Commutative-Monoidᵉ eᵉ xᵉ =
    mul-fin-Commutative-Monoidᵉ
      ( number-of-elements-countᵉ eᵉ)
      ( xᵉ ∘ᵉ map-equiv-countᵉ eᵉ)

{-ᵉ
  compute-permutation-mul-fin-Commutative-Monoidᵉ :
    (nᵉ : ℕᵉ) (eᵉ : Finᵉ nᵉ ≃ᵉ Finᵉ nᵉ) (xᵉ : Finᵉ nᵉ → type-Commutative-Monoidᵉ Mᵉ) →
    Idᵉ ( mul-fin-Commutative-Monoidᵉ nᵉ (xᵉ ∘ᵉ map-equivᵉ eᵉ))
       ( mul-fin-Commutative-Monoidᵉ nᵉ xᵉ)
  compute-permutation-mul-fin-Commutative-Monoidᵉ zero-ℕᵉ eᵉ xᵉ = reflᵉ
  compute-permutation-mul-fin-Commutative-Monoidᵉ (succ-ℕᵉ nᵉ) eᵉ xᵉ = {!!ᵉ}

  compute-mul-double-counting-Commutative-Monoidᵉ :
    {l2ᵉ : Level} {Aᵉ : UUᵉ l2ᵉ} (e1ᵉ : countᵉ Aᵉ) (e2ᵉ : countᵉ Aᵉ) →
    (xᵉ : Aᵉ → type-Commutative-Monoidᵉ Mᵉ) →
    Idᵉ (mul-count-Commutative-Monoidᵉ e1ᵉ xᵉ) (mul-count-Commutative-Monoidᵉ e2ᵉ xᵉ)
  compute-mul-double-counting-Commutative-Monoidᵉ e1ᵉ e2ᵉ xᵉ = {!!ᵉ}
-ᵉ}
```

### Products of unordered n-tuples of elements in commutative monoids

```agda
module _
  {lᵉ : Level} (Mᵉ : Commutative-Monoidᵉ lᵉ)
  where

{-ᵉ
  mul-tuple-Commutative-Monoidᵉ :
    {nᵉ : ℕᵉ} → unordered-tuple-Commutative-Monoidᵉ nᵉ Mᵉ → type-Commutative-Monoidᵉ Mᵉ
  mul-tuple-Commutative-Monoidᵉ {nᵉ} (pairᵉ Iᵉ xᵉ) = {!!ᵉ}
-ᵉ}
```