# Products of subsets of commutative rings

```agda
module commutative-algebra.products-subsets-commutative-ringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-ringsᵉ
open import commutative-algebra.subsets-commutative-ringsᵉ

open import foundation.identity-typesᵉ
open import foundation.subtypesᵉ
open import foundation.unions-subtypesᵉ
open import foundation.universe-levelsᵉ

open import ring-theory.products-subsets-ringsᵉ
```

</details>

## Idea

Theᵉ **product**ᵉ ofᵉ twoᵉ
[subsets](commutative-algebra.subsets-commutative-rings.mdᵉ) `S`ᵉ andᵉ `T`ᵉ ofᵉ aᵉ
[commutativeᵉ ring](commutative-algebra.commutative-rings.mdᵉ) `A`ᵉ isᵉ theᵉ subsetᵉ
consistngᵉ ofᵉ productsᵉ `xy`ᵉ where `xᵉ ∈ᵉ S`ᵉ andᵉ `yᵉ ∈ᵉ T`.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Aᵉ : Commutative-Ringᵉ l1ᵉ)
  (Sᵉ : subset-Commutative-Ringᵉ l2ᵉ Aᵉ) (Tᵉ : subset-Commutative-Ringᵉ l3ᵉ Aᵉ)
  where

  product-subset-Commutative-Ringᵉ : subset-Commutative-Ringᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ) Aᵉ
  product-subset-Commutative-Ringᵉ =
    product-subset-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ) Sᵉ Tᵉ
```

## Properties

### The product of subsets of commutative rings is associative

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Aᵉ : Commutative-Ringᵉ l1ᵉ)
  (Rᵉ : subset-Commutative-Ringᵉ l2ᵉ Aᵉ)
  (Sᵉ : subset-Commutative-Ringᵉ l3ᵉ Aᵉ)
  (Tᵉ : subset-Commutative-Ringᵉ l4ᵉ Aᵉ)
  where

  forward-inclusion-associative-product-subset-Commutative-Ringᵉ :
    ( product-subset-Commutative-Ringᵉ Aᵉ
      ( product-subset-Commutative-Ringᵉ Aᵉ Rᵉ Sᵉ)
      ( Tᵉ)) ⊆ᵉ
    ( product-subset-Commutative-Ringᵉ Aᵉ
      ( Rᵉ)
      ( product-subset-Commutative-Ringᵉ Aᵉ Sᵉ Tᵉ))
  forward-inclusion-associative-product-subset-Commutative-Ringᵉ =
    forward-inclusion-associative-product-subset-Ringᵉ
      ( ring-Commutative-Ringᵉ Aᵉ)
      ( Rᵉ)
      ( Sᵉ)
      ( Tᵉ)

  backward-inclusion-associative-product-subset-Commutative-Ringᵉ :
    ( product-subset-Commutative-Ringᵉ Aᵉ
      ( Rᵉ)
      ( product-subset-Commutative-Ringᵉ Aᵉ Sᵉ Tᵉ)) ⊆ᵉ
    ( product-subset-Commutative-Ringᵉ Aᵉ
      ( product-subset-Commutative-Ringᵉ Aᵉ Rᵉ Sᵉ)
      ( Tᵉ))
  backward-inclusion-associative-product-subset-Commutative-Ringᵉ =
    backward-inclusion-associative-product-subset-Ringᵉ
      ( ring-Commutative-Ringᵉ Aᵉ)
      ( Rᵉ)
      ( Sᵉ)
      ( Tᵉ)

  associative-product-subset-Commutative-Ringᵉ :
    product-subset-Commutative-Ringᵉ Aᵉ
      ( product-subset-Commutative-Ringᵉ Aᵉ Rᵉ Sᵉ)
      ( Tᵉ) ＝ᵉ
    product-subset-Commutative-Ringᵉ Aᵉ
      ( Rᵉ)
      ( product-subset-Commutative-Ringᵉ Aᵉ Sᵉ Tᵉ)
  associative-product-subset-Commutative-Ringᵉ =
    associative-product-subset-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ) Rᵉ Sᵉ Tᵉ
```

### Products distribute over unions of families of subsets

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Aᵉ : Commutative-Ringᵉ l1ᵉ)
  (Sᵉ : subset-Commutative-Ringᵉ l2ᵉ Aᵉ)
  {Iᵉ : UUᵉ l3ᵉ} (Tᵉ : Iᵉ → subset-Commutative-Ringᵉ l4ᵉ Aᵉ)
  where

  forward-inclusion-distributive-product-union-family-of-subsets-Commutative-Ringᵉ :
    product-subset-Commutative-Ringᵉ Aᵉ Sᵉ (union-family-of-subtypesᵉ Tᵉ) ⊆ᵉ
    union-family-of-subtypesᵉ (λ iᵉ → product-subset-Commutative-Ringᵉ Aᵉ Sᵉ (Tᵉ iᵉ))
  forward-inclusion-distributive-product-union-family-of-subsets-Commutative-Ringᵉ =
    forward-inclusion-distributive-product-union-family-of-subsets-Ringᵉ
      ( ring-Commutative-Ringᵉ Aᵉ)
      ( Sᵉ)
      ( Tᵉ)

  backward-inclusion-distributive-product-union-family-of-subsets-Commutative-Ringᵉ :
    union-family-of-subtypesᵉ
      ( λ iᵉ → product-subset-Commutative-Ringᵉ Aᵉ Sᵉ (Tᵉ iᵉ)) ⊆ᵉ
    product-subset-Commutative-Ringᵉ Aᵉ Sᵉ (union-family-of-subtypesᵉ Tᵉ)
  backward-inclusion-distributive-product-union-family-of-subsets-Commutative-Ringᵉ =
    backward-inclusion-distributive-product-union-family-of-subsets-Ringᵉ
      ( ring-Commutative-Ringᵉ Aᵉ)
      ( Sᵉ)
      ( Tᵉ)

  distributive-product-union-family-of-subsets-Commutative-Ringᵉ :
    product-subset-Commutative-Ringᵉ Aᵉ Sᵉ (union-family-of-subtypesᵉ Tᵉ) ＝ᵉ
    union-family-of-subtypesᵉ (λ iᵉ → product-subset-Commutative-Ringᵉ Aᵉ Sᵉ (Tᵉ iᵉ))
  distributive-product-union-family-of-subsets-Commutative-Ringᵉ =
    distributive-product-union-family-of-subsets-Ringᵉ
      ( ring-Commutative-Ringᵉ Aᵉ)
      ( Sᵉ)
      ( Tᵉ)
```