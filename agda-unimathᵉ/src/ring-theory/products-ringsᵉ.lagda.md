# Products of rings

```agda
module ring-theory.products-ringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.equality-cartesian-product-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.abelian-groupsᵉ
open import group-theory.groupsᵉ
open import group-theory.semigroupsᵉ

open import ring-theory.ringsᵉ
```

</details>

## Idea

Givenᵉ twoᵉ ringrsᵉ R1ᵉ andᵉ R2,ᵉ weᵉ defineᵉ aᵉ ringᵉ structureᵉ onᵉ theᵉ productᵉ ofᵉ R1ᵉ andᵉ
R2.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} (R1ᵉ : Ringᵉ l1ᵉ) (R2ᵉ : Ringᵉ l2ᵉ)
  where

  set-product-Ringᵉ : Setᵉ (l1ᵉ ⊔ l2ᵉ)
  set-product-Ringᵉ = product-Setᵉ (set-Ringᵉ R1ᵉ) (set-Ringᵉ R2ᵉ)

  type-product-Ringᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  type-product-Ringᵉ = type-Setᵉ set-product-Ringᵉ

  is-set-type-product-Ringᵉ : is-setᵉ type-product-Ringᵉ
  is-set-type-product-Ringᵉ = is-set-type-Setᵉ set-product-Ringᵉ

  add-product-Ringᵉ : type-product-Ringᵉ → type-product-Ringᵉ → type-product-Ringᵉ
  pr1ᵉ (add-product-Ringᵉ (x1ᵉ ,ᵉ y1ᵉ) (x2ᵉ ,ᵉ y2ᵉ)) = add-Ringᵉ R1ᵉ x1ᵉ x2ᵉ
  pr2ᵉ (add-product-Ringᵉ (x1ᵉ ,ᵉ y1ᵉ) (x2ᵉ ,ᵉ y2ᵉ)) = add-Ringᵉ R2ᵉ y1ᵉ y2ᵉ

  zero-product-Ringᵉ : type-product-Ringᵉ
  pr1ᵉ zero-product-Ringᵉ = zero-Ringᵉ R1ᵉ
  pr2ᵉ zero-product-Ringᵉ = zero-Ringᵉ R2ᵉ

  neg-product-Ringᵉ : type-product-Ringᵉ → type-product-Ringᵉ
  pr1ᵉ (neg-product-Ringᵉ (xᵉ ,ᵉ yᵉ)) = neg-Ringᵉ R1ᵉ xᵉ
  pr2ᵉ (neg-product-Ringᵉ (xᵉ ,ᵉ yᵉ)) = neg-Ringᵉ R2ᵉ yᵉ

  left-unit-law-add-product-Ringᵉ :
    (xᵉ : type-product-Ringᵉ) → Idᵉ (add-product-Ringᵉ zero-product-Ringᵉ xᵉ) xᵉ
  left-unit-law-add-product-Ringᵉ (xᵉ ,ᵉ yᵉ) =
    eq-pairᵉ (left-unit-law-add-Ringᵉ R1ᵉ xᵉ) (left-unit-law-add-Ringᵉ R2ᵉ yᵉ)

  right-unit-law-add-product-Ringᵉ :
    (xᵉ : type-product-Ringᵉ) → Idᵉ (add-product-Ringᵉ xᵉ zero-product-Ringᵉ) xᵉ
  right-unit-law-add-product-Ringᵉ (xᵉ ,ᵉ yᵉ) =
    eq-pairᵉ (right-unit-law-add-Ringᵉ R1ᵉ xᵉ) (right-unit-law-add-Ringᵉ R2ᵉ yᵉ)

  left-inverse-law-add-product-Ringᵉ :
    (xᵉ : type-product-Ringᵉ) →
    Idᵉ (add-product-Ringᵉ (neg-product-Ringᵉ xᵉ) xᵉ) zero-product-Ringᵉ
  left-inverse-law-add-product-Ringᵉ (xᵉ ,ᵉ yᵉ) =
    eq-pairᵉ (left-inverse-law-add-Ringᵉ R1ᵉ xᵉ) (left-inverse-law-add-Ringᵉ R2ᵉ yᵉ)

  right-inverse-law-add-product-Ringᵉ :
    (xᵉ : type-product-Ringᵉ) →
    Idᵉ (add-product-Ringᵉ xᵉ (neg-product-Ringᵉ xᵉ)) zero-product-Ringᵉ
  right-inverse-law-add-product-Ringᵉ (xᵉ ,ᵉ yᵉ) =
    eq-pairᵉ (right-inverse-law-add-Ringᵉ R1ᵉ xᵉ) (right-inverse-law-add-Ringᵉ R2ᵉ yᵉ)

  associative-add-product-Ringᵉ :
    (xᵉ yᵉ zᵉ : type-product-Ringᵉ) →
    Idᵉ
      ( add-product-Ringᵉ (add-product-Ringᵉ xᵉ yᵉ) zᵉ)
      ( add-product-Ringᵉ xᵉ (add-product-Ringᵉ yᵉ zᵉ))
  associative-add-product-Ringᵉ (x1ᵉ ,ᵉ y1ᵉ) (x2ᵉ ,ᵉ y2ᵉ) (x3ᵉ ,ᵉ y3ᵉ) =
    eq-pairᵉ
      ( associative-add-Ringᵉ R1ᵉ x1ᵉ x2ᵉ x3ᵉ)
      ( associative-add-Ringᵉ R2ᵉ y1ᵉ y2ᵉ y3ᵉ)

  commutative-add-product-Ringᵉ :
    (xᵉ yᵉ : type-product-Ringᵉ) → Idᵉ (add-product-Ringᵉ xᵉ yᵉ) (add-product-Ringᵉ yᵉ xᵉ)
  commutative-add-product-Ringᵉ (x1ᵉ ,ᵉ y1ᵉ) (x2ᵉ ,ᵉ y2ᵉ) =
    eq-pairᵉ
      ( commutative-add-Ringᵉ R1ᵉ x1ᵉ x2ᵉ)
      ( commutative-add-Ringᵉ R2ᵉ y1ᵉ y2ᵉ)

  mul-product-Ringᵉ : type-product-Ringᵉ → type-product-Ringᵉ → type-product-Ringᵉ
  pr1ᵉ (mul-product-Ringᵉ (x1ᵉ ,ᵉ y1ᵉ) (x2ᵉ ,ᵉ y2ᵉ)) = mul-Ringᵉ R1ᵉ x1ᵉ x2ᵉ
  pr2ᵉ (mul-product-Ringᵉ (x1ᵉ ,ᵉ y1ᵉ) (x2ᵉ ,ᵉ y2ᵉ)) = mul-Ringᵉ R2ᵉ y1ᵉ y2ᵉ

  one-product-Ringᵉ : type-product-Ringᵉ
  pr1ᵉ one-product-Ringᵉ = one-Ringᵉ R1ᵉ
  pr2ᵉ one-product-Ringᵉ = one-Ringᵉ R2ᵉ

  associative-mul-product-Ringᵉ :
    (xᵉ yᵉ zᵉ : type-product-Ringᵉ) →
    Idᵉ
      ( mul-product-Ringᵉ (mul-product-Ringᵉ xᵉ yᵉ) zᵉ)
      ( mul-product-Ringᵉ xᵉ (mul-product-Ringᵉ yᵉ zᵉ))
  associative-mul-product-Ringᵉ (x1ᵉ ,ᵉ y1ᵉ) (x2ᵉ ,ᵉ y2ᵉ) (x3ᵉ ,ᵉ y3ᵉ) =
    eq-pairᵉ
      ( associative-mul-Ringᵉ R1ᵉ x1ᵉ x2ᵉ x3ᵉ)
      ( associative-mul-Ringᵉ R2ᵉ y1ᵉ y2ᵉ y3ᵉ)

  left-unit-law-mul-product-Ringᵉ :
    (xᵉ : type-product-Ringᵉ) → Idᵉ (mul-product-Ringᵉ one-product-Ringᵉ xᵉ) xᵉ
  left-unit-law-mul-product-Ringᵉ (xᵉ ,ᵉ yᵉ) =
    eq-pairᵉ (left-unit-law-mul-Ringᵉ R1ᵉ xᵉ) (left-unit-law-mul-Ringᵉ R2ᵉ yᵉ)

  right-unit-law-mul-product-Ringᵉ :
    (xᵉ : type-product-Ringᵉ) → Idᵉ (mul-product-Ringᵉ xᵉ one-product-Ringᵉ) xᵉ
  right-unit-law-mul-product-Ringᵉ (xᵉ ,ᵉ yᵉ) =
    eq-pairᵉ (right-unit-law-mul-Ringᵉ R1ᵉ xᵉ) (right-unit-law-mul-Ringᵉ R2ᵉ yᵉ)

  left-distributive-mul-add-product-Ringᵉ :
    (xᵉ yᵉ zᵉ : type-product-Ringᵉ) →
    Idᵉ
      ( mul-product-Ringᵉ xᵉ (add-product-Ringᵉ yᵉ zᵉ))
      ( add-product-Ringᵉ (mul-product-Ringᵉ xᵉ yᵉ) (mul-product-Ringᵉ xᵉ zᵉ))
  left-distributive-mul-add-product-Ringᵉ (x1ᵉ ,ᵉ y1ᵉ) (x2ᵉ ,ᵉ y2ᵉ) (x3ᵉ ,ᵉ y3ᵉ) =
    eq-pairᵉ
      ( left-distributive-mul-add-Ringᵉ R1ᵉ x1ᵉ x2ᵉ x3ᵉ)
      ( left-distributive-mul-add-Ringᵉ R2ᵉ y1ᵉ y2ᵉ y3ᵉ)

  right-distributive-mul-add-product-Ringᵉ :
    (xᵉ yᵉ zᵉ : type-product-Ringᵉ) →
    Idᵉ
      ( mul-product-Ringᵉ (add-product-Ringᵉ xᵉ yᵉ) zᵉ)
      ( add-product-Ringᵉ (mul-product-Ringᵉ xᵉ zᵉ) (mul-product-Ringᵉ yᵉ zᵉ))
  right-distributive-mul-add-product-Ringᵉ (x1ᵉ ,ᵉ y1ᵉ) (x2ᵉ ,ᵉ y2ᵉ) (x3ᵉ ,ᵉ y3ᵉ) =
    eq-pairᵉ
      ( right-distributive-mul-add-Ringᵉ R1ᵉ x1ᵉ x2ᵉ x3ᵉ)
      ( right-distributive-mul-add-Ringᵉ R2ᵉ y1ᵉ y2ᵉ y3ᵉ)

  semigroup-product-Ringᵉ : Semigroupᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ semigroup-product-Ringᵉ = set-product-Ringᵉ
  pr1ᵉ (pr2ᵉ semigroup-product-Ringᵉ) = add-product-Ringᵉ
  pr2ᵉ (pr2ᵉ semigroup-product-Ringᵉ) = associative-add-product-Ringᵉ

  group-product-Ringᵉ : Groupᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ group-product-Ringᵉ = semigroup-product-Ringᵉ
  pr1ᵉ (pr1ᵉ (pr2ᵉ group-product-Ringᵉ)) = zero-product-Ringᵉ
  pr1ᵉ (pr2ᵉ (pr1ᵉ (pr2ᵉ group-product-Ringᵉ))) = left-unit-law-add-product-Ringᵉ
  pr2ᵉ (pr2ᵉ (pr1ᵉ (pr2ᵉ group-product-Ringᵉ))) = right-unit-law-add-product-Ringᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ group-product-Ringᵉ)) = neg-product-Ringᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ group-product-Ringᵉ))) = left-inverse-law-add-product-Ringᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ group-product-Ringᵉ))) = right-inverse-law-add-product-Ringᵉ

  ab-product-Ringᵉ : Abᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ ab-product-Ringᵉ = group-product-Ringᵉ
  pr2ᵉ ab-product-Ringᵉ = commutative-add-product-Ringᵉ

  product-Ringᵉ : Ringᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ product-Ringᵉ = ab-product-Ringᵉ
  pr1ᵉ (pr1ᵉ (pr2ᵉ product-Ringᵉ)) = mul-product-Ringᵉ
  pr2ᵉ (pr1ᵉ (pr2ᵉ product-Ringᵉ)) = associative-mul-product-Ringᵉ
  pr1ᵉ (pr1ᵉ (pr2ᵉ (pr2ᵉ product-Ringᵉ))) = one-product-Ringᵉ
  pr1ᵉ (pr2ᵉ (pr1ᵉ (pr2ᵉ (pr2ᵉ product-Ringᵉ)))) = left-unit-law-mul-product-Ringᵉ
  pr2ᵉ (pr2ᵉ (pr1ᵉ (pr2ᵉ (pr2ᵉ product-Ringᵉ)))) = right-unit-law-mul-product-Ringᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ product-Ringᵉ))) = left-distributive-mul-add-product-Ringᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ product-Ringᵉ))) = right-distributive-mul-add-product-Ringᵉ
```