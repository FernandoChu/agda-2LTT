# Cartesian products of monoids

```agda
module group-theory.cartesian-products-monoidsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.equality-cartesian-product-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.cartesian-products-semigroupsᵉ
open import group-theory.monoidsᵉ
open import group-theory.semigroupsᵉ
```

</details>

## Idea

Theᵉ cartesianᵉ productᵉ ofᵉ twoᵉ monoidsᵉ `M`ᵉ andᵉ `N`ᵉ consistsᵉ ofᵉ theᵉ productᵉ `Mᵉ ×ᵉ N`ᵉ
ofᵉ theᵉ underlyingᵉ setsᵉ andᵉ theᵉ componentwiseᵉ operationᵉ onᵉ it.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Mᵉ : Monoidᵉ l1ᵉ) (Nᵉ : Monoidᵉ l2ᵉ)
  where

  semigroup-product-Monoidᵉ : Semigroupᵉ (l1ᵉ ⊔ l2ᵉ)
  semigroup-product-Monoidᵉ =
    product-Semigroupᵉ (semigroup-Monoidᵉ Mᵉ) (semigroup-Monoidᵉ Nᵉ)

  set-product-Monoidᵉ : Setᵉ (l1ᵉ ⊔ l2ᵉ)
  set-product-Monoidᵉ = set-Semigroupᵉ semigroup-product-Monoidᵉ

  type-product-Monoidᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  type-product-Monoidᵉ = type-Semigroupᵉ semigroup-product-Monoidᵉ

  is-set-type-product-Monoidᵉ : is-setᵉ type-product-Monoidᵉ
  is-set-type-product-Monoidᵉ = is-set-type-Semigroupᵉ semigroup-product-Monoidᵉ

  mul-product-Monoidᵉ : (xᵉ yᵉ : type-product-Monoidᵉ) → type-product-Monoidᵉ
  mul-product-Monoidᵉ = mul-Semigroupᵉ semigroup-product-Monoidᵉ

  associative-mul-product-Monoidᵉ :
    (xᵉ yᵉ zᵉ : type-product-Monoidᵉ) →
    Idᵉ
      ( mul-product-Monoidᵉ (mul-product-Monoidᵉ xᵉ yᵉ) zᵉ)
      ( mul-product-Monoidᵉ xᵉ (mul-product-Monoidᵉ yᵉ zᵉ))
  associative-mul-product-Monoidᵉ =
    associative-mul-Semigroupᵉ semigroup-product-Monoidᵉ

  unit-product-Monoidᵉ : type-product-Monoidᵉ
  pr1ᵉ unit-product-Monoidᵉ = unit-Monoidᵉ Mᵉ
  pr2ᵉ unit-product-Monoidᵉ = unit-Monoidᵉ Nᵉ

  left-unit-law-mul-product-Monoidᵉ :
    (xᵉ : type-product-Monoidᵉ) → Idᵉ (mul-product-Monoidᵉ unit-product-Monoidᵉ xᵉ) xᵉ
  left-unit-law-mul-product-Monoidᵉ (pairᵉ xᵉ yᵉ) =
    eq-pairᵉ (left-unit-law-mul-Monoidᵉ Mᵉ xᵉ) (left-unit-law-mul-Monoidᵉ Nᵉ yᵉ)

  right-unit-law-mul-product-Monoidᵉ :
    (xᵉ : type-product-Monoidᵉ) → Idᵉ (mul-product-Monoidᵉ xᵉ unit-product-Monoidᵉ) xᵉ
  right-unit-law-mul-product-Monoidᵉ (pairᵉ xᵉ yᵉ) =
    eq-pairᵉ (right-unit-law-mul-Monoidᵉ Mᵉ xᵉ) (right-unit-law-mul-Monoidᵉ Nᵉ yᵉ)

  product-Monoidᵉ : Monoidᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ product-Monoidᵉ = semigroup-product-Monoidᵉ
  pr1ᵉ (pr2ᵉ product-Monoidᵉ) = unit-product-Monoidᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ product-Monoidᵉ)) = left-unit-law-mul-product-Monoidᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ product-Monoidᵉ)) = right-unit-law-mul-product-Monoidᵉ
```