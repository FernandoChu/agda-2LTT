# Cartesian products of groups

```agda
module group-theory.cartesian-products-groupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.equality-cartesian-product-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.cartesian-products-monoidsᵉ
open import group-theory.groupsᵉ
open import group-theory.monoidsᵉ
open import group-theory.semigroupsᵉ
```

</details>

## Idea

Theᵉ cartesianᵉ productᵉ ofᵉ twoᵉ groupsᵉ `G`ᵉ andᵉ `H`ᵉ hasᵉ theᵉ productᵉ ofᵉ theᵉ
underlyingᵉ setsᵉ ofᵉ `G`ᵉ andᵉ `H`ᵉ asᵉ itsᵉ underlyingᵉ type,ᵉ andᵉ isᵉ equippedᵉ with
pointwiseᵉ multiplication.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Hᵉ : Groupᵉ l2ᵉ)
  where

  monoid-product-Groupᵉ : Monoidᵉ (l1ᵉ ⊔ l2ᵉ)
  monoid-product-Groupᵉ = product-Monoidᵉ (monoid-Groupᵉ Gᵉ) (monoid-Groupᵉ Hᵉ)

  semigroup-product-Groupᵉ : Semigroupᵉ (l1ᵉ ⊔ l2ᵉ)
  semigroup-product-Groupᵉ = semigroup-Monoidᵉ monoid-product-Groupᵉ

  set-product-Groupᵉ : Setᵉ (l1ᵉ ⊔ l2ᵉ)
  set-product-Groupᵉ = set-Semigroupᵉ semigroup-product-Groupᵉ

  type-product-Groupᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  type-product-Groupᵉ = type-Semigroupᵉ semigroup-product-Groupᵉ

  is-set-type-product-Groupᵉ : is-setᵉ type-product-Groupᵉ
  is-set-type-product-Groupᵉ = is-set-type-Semigroupᵉ semigroup-product-Groupᵉ

  mul-product-Groupᵉ : (xᵉ yᵉ : type-product-Groupᵉ) → type-product-Groupᵉ
  mul-product-Groupᵉ = mul-Semigroupᵉ semigroup-product-Groupᵉ

  associative-mul-product-Groupᵉ :
    (xᵉ yᵉ zᵉ : type-product-Groupᵉ) →
    Idᵉ
      ( mul-product-Groupᵉ (mul-product-Groupᵉ xᵉ yᵉ) zᵉ)
      ( mul-product-Groupᵉ xᵉ (mul-product-Groupᵉ yᵉ zᵉ))
  associative-mul-product-Groupᵉ =
    associative-mul-Semigroupᵉ semigroup-product-Groupᵉ

  unit-product-Groupᵉ : type-product-Groupᵉ
  unit-product-Groupᵉ = unit-Monoidᵉ monoid-product-Groupᵉ

  left-unit-law-mul-product-Groupᵉ :
    (xᵉ : type-product-Groupᵉ) → Idᵉ (mul-product-Groupᵉ unit-product-Groupᵉ xᵉ) xᵉ
  left-unit-law-mul-product-Groupᵉ =
    left-unit-law-mul-Monoidᵉ monoid-product-Groupᵉ

  right-unit-law-mul-product-Groupᵉ :
    (xᵉ : type-product-Groupᵉ) → Idᵉ (mul-product-Groupᵉ xᵉ unit-product-Groupᵉ) xᵉ
  right-unit-law-mul-product-Groupᵉ =
    right-unit-law-mul-Monoidᵉ monoid-product-Groupᵉ

  inv-product-Groupᵉ : type-product-Groupᵉ → type-product-Groupᵉ
  pr1ᵉ (inv-product-Groupᵉ (pairᵉ xᵉ yᵉ)) = inv-Groupᵉ Gᵉ xᵉ
  pr2ᵉ (inv-product-Groupᵉ (pairᵉ xᵉ yᵉ)) = inv-Groupᵉ Hᵉ yᵉ

  left-inverse-law-product-Groupᵉ :
    (xᵉ : type-product-Groupᵉ) →
    Idᵉ (mul-product-Groupᵉ (inv-product-Groupᵉ xᵉ) xᵉ) unit-product-Groupᵉ
  left-inverse-law-product-Groupᵉ (pairᵉ xᵉ yᵉ) =
    eq-pairᵉ (left-inverse-law-mul-Groupᵉ Gᵉ xᵉ) (left-inverse-law-mul-Groupᵉ Hᵉ yᵉ)

  right-inverse-law-product-Groupᵉ :
    (xᵉ : type-product-Groupᵉ) →
    Idᵉ (mul-product-Groupᵉ xᵉ (inv-product-Groupᵉ xᵉ)) unit-product-Groupᵉ
  right-inverse-law-product-Groupᵉ (pairᵉ xᵉ yᵉ) =
    eq-pairᵉ (right-inverse-law-mul-Groupᵉ Gᵉ xᵉ) (right-inverse-law-mul-Groupᵉ Hᵉ yᵉ)

  product-Groupᵉ : Groupᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ product-Groupᵉ = semigroup-product-Groupᵉ
  pr1ᵉ (pr1ᵉ (pr2ᵉ product-Groupᵉ)) = unit-product-Groupᵉ
  pr1ᵉ (pr2ᵉ (pr1ᵉ (pr2ᵉ product-Groupᵉ))) = left-unit-law-mul-product-Groupᵉ
  pr2ᵉ (pr2ᵉ (pr1ᵉ (pr2ᵉ product-Groupᵉ))) = right-unit-law-mul-product-Groupᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ product-Groupᵉ)) = inv-product-Groupᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ product-Groupᵉ))) = left-inverse-law-product-Groupᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ product-Groupᵉ))) = right-inverse-law-product-Groupᵉ
```