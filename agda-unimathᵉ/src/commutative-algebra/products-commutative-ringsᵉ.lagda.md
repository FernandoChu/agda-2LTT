# Products of commutative rings

```agda
module commutative-algebra.products-commutative-ringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-ringsᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.equality-cartesian-product-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.abelian-groupsᵉ
open import group-theory.groupsᵉ
open import group-theory.semigroupsᵉ

open import ring-theory.products-ringsᵉ
open import ring-theory.ringsᵉ
```

</details>

## Idea

Givenᵉ twoᵉ commutativeᵉ ringsᵉ R1ᵉ andᵉ R2,ᵉ weᵉ defineᵉ aᵉ commutativeᵉ ringᵉ structureᵉ onᵉ
theᵉ productᵉ ofᵉ R1ᵉ andᵉ R2.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} (R1ᵉ : Commutative-Ringᵉ l1ᵉ) (R2ᵉ : Commutative-Ringᵉ l2ᵉ)
  where

  set-product-Commutative-Ringᵉ : Setᵉ (l1ᵉ ⊔ l2ᵉ)
  set-product-Commutative-Ringᵉ =
    set-product-Ringᵉ (ring-Commutative-Ringᵉ R1ᵉ) (ring-Commutative-Ringᵉ R2ᵉ)

  type-product-Commutative-Ringᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  type-product-Commutative-Ringᵉ =
    type-product-Ringᵉ (ring-Commutative-Ringᵉ R1ᵉ) (ring-Commutative-Ringᵉ R2ᵉ)

  is-set-type-product-Commutative-Ringᵉ : is-setᵉ type-product-Commutative-Ringᵉ
  is-set-type-product-Commutative-Ringᵉ =
    is-set-type-product-Ringᵉ
      ( ring-Commutative-Ringᵉ R1ᵉ)
      ( ring-Commutative-Ringᵉ R2ᵉ)

  add-product-Commutative-Ringᵉ :
    type-product-Commutative-Ringᵉ →
    type-product-Commutative-Ringᵉ →
    type-product-Commutative-Ringᵉ
  add-product-Commutative-Ringᵉ =
    add-product-Ringᵉ
      ( ring-Commutative-Ringᵉ R1ᵉ)
      ( ring-Commutative-Ringᵉ R2ᵉ)

  zero-product-Commutative-Ringᵉ : type-product-Commutative-Ringᵉ
  zero-product-Commutative-Ringᵉ =
    zero-product-Ringᵉ (ring-Commutative-Ringᵉ R1ᵉ) (ring-Commutative-Ringᵉ R2ᵉ)

  neg-product-Commutative-Ringᵉ :
    type-product-Commutative-Ringᵉ → type-product-Commutative-Ringᵉ
  neg-product-Commutative-Ringᵉ =
    neg-product-Ringᵉ (ring-Commutative-Ringᵉ R1ᵉ) (ring-Commutative-Ringᵉ R2ᵉ)

  left-unit-law-add-product-Commutative-Ringᵉ :
    (xᵉ : type-product-Commutative-Ringᵉ) →
    add-product-Commutative-Ringᵉ zero-product-Commutative-Ringᵉ xᵉ ＝ᵉ xᵉ
  left-unit-law-add-product-Commutative-Ringᵉ =
    left-unit-law-add-product-Ringᵉ
      ( ring-Commutative-Ringᵉ R1ᵉ)
      ( ring-Commutative-Ringᵉ R2ᵉ)

  right-unit-law-add-product-Commutative-Ringᵉ :
    (xᵉ : type-product-Commutative-Ringᵉ) →
    add-product-Commutative-Ringᵉ xᵉ zero-product-Commutative-Ringᵉ ＝ᵉ xᵉ
  right-unit-law-add-product-Commutative-Ringᵉ =
    right-unit-law-add-product-Ringᵉ
      ( ring-Commutative-Ringᵉ R1ᵉ)
      ( ring-Commutative-Ringᵉ R2ᵉ)

  left-inverse-law-add-product-Commutative-Ringᵉ :
    (xᵉ : type-product-Commutative-Ringᵉ) →
    Idᵉ
      ( add-product-Commutative-Ringᵉ (neg-product-Commutative-Ringᵉ xᵉ) xᵉ)
      zero-product-Commutative-Ringᵉ
  left-inverse-law-add-product-Commutative-Ringᵉ =
    left-inverse-law-add-product-Ringᵉ
      ( ring-Commutative-Ringᵉ R1ᵉ)
      ( ring-Commutative-Ringᵉ R2ᵉ)

  right-inverse-law-add-product-Commutative-Ringᵉ :
    (xᵉ : type-product-Commutative-Ringᵉ) →
    Idᵉ
      ( add-product-Commutative-Ringᵉ xᵉ (neg-product-Commutative-Ringᵉ xᵉ))
      ( zero-product-Commutative-Ringᵉ)
  right-inverse-law-add-product-Commutative-Ringᵉ =
    right-inverse-law-add-product-Ringᵉ
      ( ring-Commutative-Ringᵉ R1ᵉ)
      ( ring-Commutative-Ringᵉ R2ᵉ)

  associative-add-product-Commutative-Ringᵉ :
    (xᵉ yᵉ zᵉ : type-product-Commutative-Ringᵉ) →
    Idᵉ
      ( add-product-Commutative-Ringᵉ (add-product-Commutative-Ringᵉ xᵉ yᵉ) zᵉ)
      ( add-product-Commutative-Ringᵉ xᵉ (add-product-Commutative-Ringᵉ yᵉ zᵉ))
  associative-add-product-Commutative-Ringᵉ =
    associative-add-product-Ringᵉ
      ( ring-Commutative-Ringᵉ R1ᵉ)
      ( ring-Commutative-Ringᵉ R2ᵉ)

  commutative-add-product-Commutative-Ringᵉ :
    (xᵉ yᵉ : type-product-Commutative-Ringᵉ) →
    Idᵉ (add-product-Commutative-Ringᵉ xᵉ yᵉ) (add-product-Commutative-Ringᵉ yᵉ xᵉ)
  commutative-add-product-Commutative-Ringᵉ =
    commutative-add-product-Ringᵉ
      ( ring-Commutative-Ringᵉ R1ᵉ)
      ( ring-Commutative-Ringᵉ R2ᵉ)

  mul-product-Commutative-Ringᵉ :
    type-product-Commutative-Ringᵉ →
    type-product-Commutative-Ringᵉ →
    type-product-Commutative-Ringᵉ
  mul-product-Commutative-Ringᵉ =
    mul-product-Ringᵉ
      ( ring-Commutative-Ringᵉ R1ᵉ)
      ( ring-Commutative-Ringᵉ R2ᵉ)

  one-product-Commutative-Ringᵉ : type-product-Commutative-Ringᵉ
  one-product-Commutative-Ringᵉ =
    one-product-Ringᵉ
      ( ring-Commutative-Ringᵉ R1ᵉ)
      ( ring-Commutative-Ringᵉ R2ᵉ)

  associative-mul-product-Commutative-Ringᵉ :
    (xᵉ yᵉ zᵉ : type-product-Commutative-Ringᵉ) →
    Idᵉ
      ( mul-product-Commutative-Ringᵉ (mul-product-Commutative-Ringᵉ xᵉ yᵉ) zᵉ)
      ( mul-product-Commutative-Ringᵉ xᵉ (mul-product-Commutative-Ringᵉ yᵉ zᵉ))
  associative-mul-product-Commutative-Ringᵉ =
    associative-mul-product-Ringᵉ
      ( ring-Commutative-Ringᵉ R1ᵉ)
      ( ring-Commutative-Ringᵉ R2ᵉ)

  left-unit-law-mul-product-Commutative-Ringᵉ :
    (xᵉ : type-product-Commutative-Ringᵉ) →
    Idᵉ (mul-product-Commutative-Ringᵉ one-product-Commutative-Ringᵉ xᵉ) xᵉ
  left-unit-law-mul-product-Commutative-Ringᵉ =
    left-unit-law-mul-product-Ringᵉ
      ( ring-Commutative-Ringᵉ R1ᵉ)
      ( ring-Commutative-Ringᵉ R2ᵉ)

  right-unit-law-mul-product-Commutative-Ringᵉ :
    (xᵉ : type-product-Commutative-Ringᵉ) →
    Idᵉ (mul-product-Commutative-Ringᵉ xᵉ one-product-Commutative-Ringᵉ) xᵉ
  right-unit-law-mul-product-Commutative-Ringᵉ =
    right-unit-law-mul-product-Ringᵉ
      ( ring-Commutative-Ringᵉ R1ᵉ)
      ( ring-Commutative-Ringᵉ R2ᵉ)

  left-distributive-mul-add-product-Commutative-Ringᵉ :
    (xᵉ yᵉ zᵉ : type-product-Commutative-Ringᵉ) →
    Idᵉ
      ( mul-product-Commutative-Ringᵉ xᵉ (add-product-Commutative-Ringᵉ yᵉ zᵉ))
      ( add-product-Commutative-Ringᵉ
        ( mul-product-Commutative-Ringᵉ xᵉ yᵉ)
        ( mul-product-Commutative-Ringᵉ xᵉ zᵉ))
  left-distributive-mul-add-product-Commutative-Ringᵉ =
    left-distributive-mul-add-product-Ringᵉ
      ( ring-Commutative-Ringᵉ R1ᵉ)
      ( ring-Commutative-Ringᵉ R2ᵉ)

  right-distributive-mul-add-product-Commutative-Ringᵉ :
    (xᵉ yᵉ zᵉ : type-product-Commutative-Ringᵉ) →
    Idᵉ
      ( mul-product-Commutative-Ringᵉ (add-product-Commutative-Ringᵉ xᵉ yᵉ) zᵉ)
      ( add-product-Commutative-Ringᵉ
        ( mul-product-Commutative-Ringᵉ xᵉ zᵉ)
        ( mul-product-Commutative-Ringᵉ yᵉ zᵉ))
  right-distributive-mul-add-product-Commutative-Ringᵉ =
    right-distributive-mul-add-product-Ringᵉ
      ( ring-Commutative-Ringᵉ R1ᵉ)
      ( ring-Commutative-Ringᵉ R2ᵉ)

  semigroup-product-Commutative-Ringᵉ : Semigroupᵉ (l1ᵉ ⊔ l2ᵉ)
  semigroup-product-Commutative-Ringᵉ =
    semigroup-product-Ringᵉ
      ( ring-Commutative-Ringᵉ R1ᵉ)
      ( ring-Commutative-Ringᵉ R2ᵉ)

  group-product-Commutative-Ringᵉ : Groupᵉ (l1ᵉ ⊔ l2ᵉ)
  group-product-Commutative-Ringᵉ =
    group-product-Ringᵉ ( ring-Commutative-Ringᵉ R1ᵉ) ( ring-Commutative-Ringᵉ R2ᵉ)

  ab-product-Commutative-Ringᵉ : Abᵉ (l1ᵉ ⊔ l2ᵉ)
  ab-product-Commutative-Ringᵉ =
    ab-product-Ringᵉ (ring-Commutative-Ringᵉ R1ᵉ) (ring-Commutative-Ringᵉ R2ᵉ)

  ring-product-Commutative-Ringᵉ : Ringᵉ (l1ᵉ ⊔ l2ᵉ)
  ring-product-Commutative-Ringᵉ =
    product-Ringᵉ (ring-Commutative-Ringᵉ R1ᵉ) (ring-Commutative-Ringᵉ R2ᵉ)

  commutative-mul-product-Commutative-Ringᵉ :
    (xᵉ yᵉ : type-product-Commutative-Ringᵉ) →
    mul-product-Commutative-Ringᵉ xᵉ yᵉ ＝ᵉ mul-product-Commutative-Ringᵉ yᵉ xᵉ
  commutative-mul-product-Commutative-Ringᵉ (x1ᵉ ,ᵉ x2ᵉ) (y1ᵉ ,ᵉ y2ᵉ) =
    eq-pairᵉ
      ( commutative-mul-Commutative-Ringᵉ R1ᵉ x1ᵉ y1ᵉ)
      ( commutative-mul-Commutative-Ringᵉ R2ᵉ x2ᵉ y2ᵉ)

  product-Commutative-Ringᵉ : Commutative-Ringᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ product-Commutative-Ringᵉ = ring-product-Commutative-Ringᵉ
  pr2ᵉ product-Commutative-Ringᵉ = commutative-mul-product-Commutative-Ringᵉ
```