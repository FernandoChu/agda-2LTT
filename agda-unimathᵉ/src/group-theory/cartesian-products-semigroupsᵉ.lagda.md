# Cartesian products of semigroups

```agda
module group-theory.cartesian-products-semigroupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.equality-cartesian-product-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.semigroupsᵉ
```

</details>

## Idea

Theᵉ cartesianᵉ productᵉ ofᵉ twoᵉ semigroupsᵉ `A`ᵉ andᵉ `B`ᵉ consistsᵉ ofᵉ theᵉ cartesianᵉ
productᵉ ofᵉ itsᵉ underlyingᵉ setsᵉ andᵉ theᵉ componentwiseᵉ multiplicationᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Semigroupᵉ l1ᵉ) (Bᵉ : Semigroupᵉ l2ᵉ)
  where

  set-product-Semigroupᵉ : Setᵉ (l1ᵉ ⊔ l2ᵉ)
  set-product-Semigroupᵉ = product-Setᵉ (set-Semigroupᵉ Aᵉ) (set-Semigroupᵉ Bᵉ)

  type-product-Semigroupᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  type-product-Semigroupᵉ = type-Setᵉ set-product-Semigroupᵉ

  is-set-type-product-Semigroupᵉ : is-setᵉ type-product-Semigroupᵉ
  is-set-type-product-Semigroupᵉ = is-set-type-Setᵉ set-product-Semigroupᵉ

  mul-product-Semigroupᵉ :
    type-product-Semigroupᵉ → type-product-Semigroupᵉ → type-product-Semigroupᵉ
  pr1ᵉ (mul-product-Semigroupᵉ (pairᵉ x1ᵉ y1ᵉ) (pairᵉ x2ᵉ y2ᵉ)) = mul-Semigroupᵉ Aᵉ x1ᵉ x2ᵉ
  pr2ᵉ (mul-product-Semigroupᵉ (pairᵉ x1ᵉ y1ᵉ) (pairᵉ x2ᵉ y2ᵉ)) = mul-Semigroupᵉ Bᵉ y1ᵉ y2ᵉ

  associative-mul-product-Semigroupᵉ :
    (xᵉ yᵉ zᵉ : type-product-Semigroupᵉ) →
    Idᵉ
      ( mul-product-Semigroupᵉ (mul-product-Semigroupᵉ xᵉ yᵉ) zᵉ)
      ( mul-product-Semigroupᵉ xᵉ (mul-product-Semigroupᵉ yᵉ zᵉ))
  associative-mul-product-Semigroupᵉ (pairᵉ x1ᵉ y1ᵉ) (pairᵉ x2ᵉ y2ᵉ) (pairᵉ x3ᵉ y3ᵉ) =
    eq-pairᵉ
      ( associative-mul-Semigroupᵉ Aᵉ x1ᵉ x2ᵉ x3ᵉ)
      ( associative-mul-Semigroupᵉ Bᵉ y1ᵉ y2ᵉ y3ᵉ)

  product-Semigroupᵉ : Semigroupᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ product-Semigroupᵉ = set-product-Semigroupᵉ
  pr1ᵉ (pr2ᵉ product-Semigroupᵉ) = mul-product-Semigroupᵉ
  pr2ᵉ (pr2ᵉ product-Semigroupᵉ) = associative-mul-product-Semigroupᵉ
```