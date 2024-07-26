# Cartesian products of abelian groups

```agda
module group-theory.cartesian-products-abelian-groupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.equality-cartesian-product-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.abelian-groupsᵉ
open import group-theory.cartesian-products-groupsᵉ
open import group-theory.groupsᵉ
open import group-theory.monoidsᵉ
open import group-theory.semigroupsᵉ
```

</details>

## Idea

Theᵉ cartesianᵉ productᵉ ofᵉ twoᵉ abelianᵉ groupsᵉ `A`ᵉ andᵉ `B`ᵉ isᵉ anᵉ abelianᵉ groupᵉ
structureᵉ onᵉ theᵉ cartesianᵉ productᵉ ofᵉ theᵉ underlyingᵉ sets.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Abᵉ l1ᵉ) (Bᵉ : Abᵉ l2ᵉ)
  where

  group-product-Abᵉ : Groupᵉ (l1ᵉ ⊔ l2ᵉ)
  group-product-Abᵉ = product-Groupᵉ (group-Abᵉ Aᵉ) (group-Abᵉ Bᵉ)

  monoid-product-Abᵉ : Monoidᵉ (l1ᵉ ⊔ l2ᵉ)
  monoid-product-Abᵉ = monoid-Groupᵉ group-product-Abᵉ

  semigroup-product-Abᵉ : Semigroupᵉ (l1ᵉ ⊔ l2ᵉ)
  semigroup-product-Abᵉ = semigroup-Groupᵉ group-product-Abᵉ

  set-product-Abᵉ : Setᵉ (l1ᵉ ⊔ l2ᵉ)
  set-product-Abᵉ = set-Groupᵉ group-product-Abᵉ

  type-product-Abᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  type-product-Abᵉ = type-Groupᵉ group-product-Abᵉ

  is-set-type-product-Abᵉ : is-setᵉ type-product-Abᵉ
  is-set-type-product-Abᵉ = is-set-type-Groupᵉ group-product-Abᵉ

  add-product-Abᵉ : (xᵉ yᵉ : type-product-Abᵉ) → type-product-Abᵉ
  add-product-Abᵉ = mul-Groupᵉ group-product-Abᵉ

  zero-product-Abᵉ : type-product-Abᵉ
  zero-product-Abᵉ = unit-Groupᵉ group-product-Abᵉ

  neg-product-Abᵉ : type-product-Abᵉ → type-product-Abᵉ
  neg-product-Abᵉ = inv-Groupᵉ group-product-Abᵉ

  associative-add-product-Abᵉ :
    (xᵉ yᵉ zᵉ : type-product-Abᵉ) →
    Idᵉ
      ( add-product-Abᵉ (add-product-Abᵉ xᵉ yᵉ) zᵉ)
      ( add-product-Abᵉ xᵉ (add-product-Abᵉ yᵉ zᵉ))
  associative-add-product-Abᵉ = associative-mul-Groupᵉ group-product-Abᵉ

  left-unit-law-add-product-Abᵉ :
    (xᵉ : type-product-Abᵉ) → Idᵉ (add-product-Abᵉ zero-product-Abᵉ xᵉ) xᵉ
  left-unit-law-add-product-Abᵉ = left-unit-law-mul-Groupᵉ group-product-Abᵉ

  right-unit-law-add-product-Abᵉ :
    (xᵉ : type-product-Abᵉ) → Idᵉ (add-product-Abᵉ xᵉ zero-product-Abᵉ) xᵉ
  right-unit-law-add-product-Abᵉ = right-unit-law-mul-Groupᵉ group-product-Abᵉ

  left-inverse-law-add-product-Abᵉ :
    (xᵉ : type-product-Abᵉ) →
    Idᵉ (add-product-Abᵉ (neg-product-Abᵉ xᵉ) xᵉ) zero-product-Abᵉ
  left-inverse-law-add-product-Abᵉ = left-inverse-law-mul-Groupᵉ group-product-Abᵉ

  right-inverse-law-add-product-Abᵉ :
    (xᵉ : type-product-Abᵉ) →
    Idᵉ (add-product-Abᵉ xᵉ (neg-product-Abᵉ xᵉ)) zero-product-Abᵉ
  right-inverse-law-add-product-Abᵉ =
    right-inverse-law-mul-Groupᵉ group-product-Abᵉ

  commutative-add-product-Abᵉ :
    (xᵉ yᵉ : type-product-Abᵉ) → Idᵉ (add-product-Abᵉ xᵉ yᵉ) (add-product-Abᵉ yᵉ xᵉ)
  commutative-add-product-Abᵉ (pairᵉ x1ᵉ y1ᵉ) (pairᵉ x2ᵉ y2ᵉ) =
    eq-pairᵉ (commutative-add-Abᵉ Aᵉ x1ᵉ x2ᵉ) (commutative-add-Abᵉ Bᵉ y1ᵉ y2ᵉ)

  product-Abᵉ : Abᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ product-Abᵉ = group-product-Abᵉ
  pr2ᵉ product-Abᵉ = commutative-add-product-Abᵉ
```