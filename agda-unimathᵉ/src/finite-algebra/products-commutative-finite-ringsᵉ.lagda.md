# Products of commutative finite rings

```agda
module finite-algebra.products-commutative-finite-ringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-ringsᵉ
open import commutative-algebra.products-commutative-ringsᵉ

open import finite-algebra.commutative-finite-ringsᵉ
open import finite-algebra.products-finite-ringsᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.abelian-groupsᵉ
open import group-theory.groupsᵉ
open import group-theory.semigroupsᵉ

open import univalent-combinatorics.finite-typesᵉ
```

</details>

## Idea

Givenᵉ twoᵉ commutativeᵉ finiteᵉ ringsᵉ R1ᵉ andᵉ R2,ᵉ weᵉ defineᵉ aᵉ commutativeᵉ finiteᵉ
ringᵉ structureᵉ onᵉ theᵉ productᵉ ofᵉ R1ᵉ andᵉ R2.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} (R1ᵉ : Commutative-Ring-𝔽ᵉ l1ᵉ) (R2ᵉ : Commutative-Ring-𝔽ᵉ l2ᵉ)
  where

  set-product-Commutative-Ring-𝔽ᵉ : Setᵉ (l1ᵉ ⊔ l2ᵉ)
  set-product-Commutative-Ring-𝔽ᵉ =
    set-product-Commutative-Ringᵉ
      ( commutative-ring-Commutative-Ring-𝔽ᵉ R1ᵉ)
      ( commutative-ring-Commutative-Ring-𝔽ᵉ R2ᵉ)

  type-product-Commutative-Ring-𝔽ᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  type-product-Commutative-Ring-𝔽ᵉ =
    type-product-Commutative-Ringᵉ
      ( commutative-ring-Commutative-Ring-𝔽ᵉ R1ᵉ)
      ( commutative-ring-Commutative-Ring-𝔽ᵉ R2ᵉ)

  is-set-type-product-Commutative-Ring-𝔽ᵉ :
    is-setᵉ type-product-Commutative-Ring-𝔽ᵉ
  is-set-type-product-Commutative-Ring-𝔽ᵉ =
    is-set-type-product-Commutative-Ringᵉ
      ( commutative-ring-Commutative-Ring-𝔽ᵉ R1ᵉ)
      ( commutative-ring-Commutative-Ring-𝔽ᵉ R2ᵉ)

  is-finite-type-product-Commutative-Ring-𝔽ᵉ :
    is-finiteᵉ type-product-Commutative-Ring-𝔽ᵉ
  is-finite-type-product-Commutative-Ring-𝔽ᵉ =
    is-finite-type-product-Ring-𝔽ᵉ
      ( finite-ring-Commutative-Ring-𝔽ᵉ R1ᵉ)
      ( finite-ring-Commutative-Ring-𝔽ᵉ R2ᵉ)

  finite-type-product-Commutative-Ring-𝔽ᵉ : 𝔽ᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ finite-type-product-Commutative-Ring-𝔽ᵉ = type-product-Commutative-Ring-𝔽ᵉ
  pr2ᵉ finite-type-product-Commutative-Ring-𝔽ᵉ =
    is-finite-type-product-Commutative-Ring-𝔽ᵉ

  add-product-Commutative-Ring-𝔽ᵉ :
    type-product-Commutative-Ring-𝔽ᵉ →
    type-product-Commutative-Ring-𝔽ᵉ →
    type-product-Commutative-Ring-𝔽ᵉ
  add-product-Commutative-Ring-𝔽ᵉ =
    add-product-Commutative-Ringᵉ
      ( commutative-ring-Commutative-Ring-𝔽ᵉ R1ᵉ)
      ( commutative-ring-Commutative-Ring-𝔽ᵉ R2ᵉ)

  zero-product-Commutative-Ring-𝔽ᵉ : type-product-Commutative-Ring-𝔽ᵉ
  zero-product-Commutative-Ring-𝔽ᵉ =
    zero-product-Commutative-Ringᵉ
      ( commutative-ring-Commutative-Ring-𝔽ᵉ R1ᵉ)
      ( commutative-ring-Commutative-Ring-𝔽ᵉ R2ᵉ)

  neg-product-Commutative-Ring-𝔽ᵉ :
    type-product-Commutative-Ring-𝔽ᵉ → type-product-Commutative-Ring-𝔽ᵉ
  neg-product-Commutative-Ring-𝔽ᵉ =
    neg-product-Commutative-Ringᵉ
      ( commutative-ring-Commutative-Ring-𝔽ᵉ R1ᵉ)
      ( commutative-ring-Commutative-Ring-𝔽ᵉ R2ᵉ)

  left-unit-law-add-product-Commutative-Ring-𝔽ᵉ :
    (xᵉ : type-product-Commutative-Ring-𝔽ᵉ) →
    Idᵉ (add-product-Commutative-Ring-𝔽ᵉ zero-product-Commutative-Ring-𝔽ᵉ xᵉ) xᵉ
  left-unit-law-add-product-Commutative-Ring-𝔽ᵉ =
    left-unit-law-add-product-Commutative-Ringᵉ
      ( commutative-ring-Commutative-Ring-𝔽ᵉ R1ᵉ)
      ( commutative-ring-Commutative-Ring-𝔽ᵉ R2ᵉ)

  right-unit-law-add-product-Commutative-Ring-𝔽ᵉ :
    (xᵉ : type-product-Commutative-Ring-𝔽ᵉ) →
    Idᵉ (add-product-Commutative-Ring-𝔽ᵉ xᵉ zero-product-Commutative-Ring-𝔽ᵉ) xᵉ
  right-unit-law-add-product-Commutative-Ring-𝔽ᵉ =
    right-unit-law-add-product-Commutative-Ringᵉ
      ( commutative-ring-Commutative-Ring-𝔽ᵉ R1ᵉ)
      ( commutative-ring-Commutative-Ring-𝔽ᵉ R2ᵉ)

  left-inverse-law-add-product-Commutative-Ring-𝔽ᵉ :
    (xᵉ : type-product-Commutative-Ring-𝔽ᵉ) →
    Idᵉ
      ( add-product-Commutative-Ring-𝔽ᵉ (neg-product-Commutative-Ring-𝔽ᵉ xᵉ) xᵉ)
      zero-product-Commutative-Ring-𝔽ᵉ
  left-inverse-law-add-product-Commutative-Ring-𝔽ᵉ =
    left-inverse-law-add-product-Commutative-Ringᵉ
      ( commutative-ring-Commutative-Ring-𝔽ᵉ R1ᵉ)
      ( commutative-ring-Commutative-Ring-𝔽ᵉ R2ᵉ)

  right-inverse-law-add-product-Commutative-Ring-𝔽ᵉ :
    (xᵉ : type-product-Commutative-Ring-𝔽ᵉ) →
    Idᵉ
      ( add-product-Commutative-Ring-𝔽ᵉ xᵉ (neg-product-Commutative-Ring-𝔽ᵉ xᵉ))
      ( zero-product-Commutative-Ring-𝔽ᵉ)
  right-inverse-law-add-product-Commutative-Ring-𝔽ᵉ =
    right-inverse-law-add-product-Commutative-Ringᵉ
      ( commutative-ring-Commutative-Ring-𝔽ᵉ R1ᵉ)
      ( commutative-ring-Commutative-Ring-𝔽ᵉ R2ᵉ)

  associative-add-product-Commutative-Ring-𝔽ᵉ :
    (xᵉ yᵉ zᵉ : type-product-Commutative-Ring-𝔽ᵉ) →
    Idᵉ
      ( add-product-Commutative-Ring-𝔽ᵉ (add-product-Commutative-Ring-𝔽ᵉ xᵉ yᵉ) zᵉ)
      ( add-product-Commutative-Ring-𝔽ᵉ xᵉ (add-product-Commutative-Ring-𝔽ᵉ yᵉ zᵉ))
  associative-add-product-Commutative-Ring-𝔽ᵉ =
    associative-add-product-Commutative-Ringᵉ
      ( commutative-ring-Commutative-Ring-𝔽ᵉ R1ᵉ)
      ( commutative-ring-Commutative-Ring-𝔽ᵉ R2ᵉ)

  commutative-add-product-Commutative-Ring-𝔽ᵉ :
    (xᵉ yᵉ : type-product-Commutative-Ring-𝔽ᵉ) →
    Idᵉ (add-product-Commutative-Ring-𝔽ᵉ xᵉ yᵉ) (add-product-Commutative-Ring-𝔽ᵉ yᵉ xᵉ)
  commutative-add-product-Commutative-Ring-𝔽ᵉ =
    commutative-add-product-Commutative-Ringᵉ
      ( commutative-ring-Commutative-Ring-𝔽ᵉ R1ᵉ)
      ( commutative-ring-Commutative-Ring-𝔽ᵉ R2ᵉ)

  mul-product-Commutative-Ring-𝔽ᵉ :
    type-product-Commutative-Ring-𝔽ᵉ →
    type-product-Commutative-Ring-𝔽ᵉ →
    type-product-Commutative-Ring-𝔽ᵉ
  mul-product-Commutative-Ring-𝔽ᵉ =
    mul-product-Commutative-Ringᵉ
      ( commutative-ring-Commutative-Ring-𝔽ᵉ R1ᵉ)
      ( commutative-ring-Commutative-Ring-𝔽ᵉ R2ᵉ)

  one-product-Commutative-Ring-𝔽ᵉ : type-product-Commutative-Ring-𝔽ᵉ
  one-product-Commutative-Ring-𝔽ᵉ =
    one-product-Commutative-Ringᵉ
      ( commutative-ring-Commutative-Ring-𝔽ᵉ R1ᵉ)
      ( commutative-ring-Commutative-Ring-𝔽ᵉ R2ᵉ)

  associative-mul-product-Commutative-Ring-𝔽ᵉ :
    (xᵉ yᵉ zᵉ : type-product-Commutative-Ring-𝔽ᵉ) →
    Idᵉ
      ( mul-product-Commutative-Ring-𝔽ᵉ (mul-product-Commutative-Ring-𝔽ᵉ xᵉ yᵉ) zᵉ)
      ( mul-product-Commutative-Ring-𝔽ᵉ xᵉ (mul-product-Commutative-Ring-𝔽ᵉ yᵉ zᵉ))
  associative-mul-product-Commutative-Ring-𝔽ᵉ =
    associative-mul-product-Commutative-Ringᵉ
      ( commutative-ring-Commutative-Ring-𝔽ᵉ R1ᵉ)
      ( commutative-ring-Commutative-Ring-𝔽ᵉ R2ᵉ)

  left-unit-law-mul-product-Commutative-Ring-𝔽ᵉ :
    (xᵉ : type-product-Commutative-Ring-𝔽ᵉ) →
    Idᵉ (mul-product-Commutative-Ring-𝔽ᵉ one-product-Commutative-Ring-𝔽ᵉ xᵉ) xᵉ
  left-unit-law-mul-product-Commutative-Ring-𝔽ᵉ =
    left-unit-law-mul-product-Commutative-Ringᵉ
      ( commutative-ring-Commutative-Ring-𝔽ᵉ R1ᵉ)
      ( commutative-ring-Commutative-Ring-𝔽ᵉ R2ᵉ)

  right-unit-law-mul-product-Commutative-Ring-𝔽ᵉ :
    (xᵉ : type-product-Commutative-Ring-𝔽ᵉ) →
    Idᵉ (mul-product-Commutative-Ring-𝔽ᵉ xᵉ one-product-Commutative-Ring-𝔽ᵉ) xᵉ
  right-unit-law-mul-product-Commutative-Ring-𝔽ᵉ =
    right-unit-law-mul-product-Commutative-Ringᵉ
      ( commutative-ring-Commutative-Ring-𝔽ᵉ R1ᵉ)
      ( commutative-ring-Commutative-Ring-𝔽ᵉ R2ᵉ)

  left-distributive-mul-add-product-Commutative-Ring-𝔽ᵉ :
    (xᵉ yᵉ zᵉ : type-product-Commutative-Ring-𝔽ᵉ) →
    Idᵉ
      ( mul-product-Commutative-Ring-𝔽ᵉ xᵉ (add-product-Commutative-Ring-𝔽ᵉ yᵉ zᵉ))
      ( add-product-Commutative-Ring-𝔽ᵉ
        ( mul-product-Commutative-Ring-𝔽ᵉ xᵉ yᵉ)
        ( mul-product-Commutative-Ring-𝔽ᵉ xᵉ zᵉ))
  left-distributive-mul-add-product-Commutative-Ring-𝔽ᵉ =
    left-distributive-mul-add-product-Commutative-Ringᵉ
      ( commutative-ring-Commutative-Ring-𝔽ᵉ R1ᵉ)
      ( commutative-ring-Commutative-Ring-𝔽ᵉ R2ᵉ)

  right-distributive-mul-add-product-Commutative-Ring-𝔽ᵉ :
    (xᵉ yᵉ zᵉ : type-product-Commutative-Ring-𝔽ᵉ) →
    Idᵉ
      ( mul-product-Commutative-Ring-𝔽ᵉ (add-product-Commutative-Ring-𝔽ᵉ xᵉ yᵉ) zᵉ)
      ( add-product-Commutative-Ring-𝔽ᵉ
        ( mul-product-Commutative-Ring-𝔽ᵉ xᵉ zᵉ)
        ( mul-product-Commutative-Ring-𝔽ᵉ yᵉ zᵉ))
  right-distributive-mul-add-product-Commutative-Ring-𝔽ᵉ =
    right-distributive-mul-add-product-Commutative-Ringᵉ
      ( commutative-ring-Commutative-Ring-𝔽ᵉ R1ᵉ)
      ( commutative-ring-Commutative-Ring-𝔽ᵉ R2ᵉ)

  semigroup-product-Commutative-Ring-𝔽ᵉ : Semigroupᵉ (l1ᵉ ⊔ l2ᵉ)
  semigroup-product-Commutative-Ring-𝔽ᵉ =
    semigroup-product-Commutative-Ringᵉ
      ( commutative-ring-Commutative-Ring-𝔽ᵉ R1ᵉ)
      ( commutative-ring-Commutative-Ring-𝔽ᵉ R2ᵉ)

  group-product-Commutative-Ring-𝔽ᵉ : Groupᵉ (l1ᵉ ⊔ l2ᵉ)
  group-product-Commutative-Ring-𝔽ᵉ =
    group-product-Commutative-Ringᵉ
      ( commutative-ring-Commutative-Ring-𝔽ᵉ R1ᵉ)
      ( commutative-ring-Commutative-Ring-𝔽ᵉ R2ᵉ)

  ab-product-Commutative-Ring-𝔽ᵉ : Abᵉ (l1ᵉ ⊔ l2ᵉ)
  ab-product-Commutative-Ring-𝔽ᵉ =
    ab-product-Commutative-Ringᵉ
      ( commutative-ring-Commutative-Ring-𝔽ᵉ R1ᵉ)
      ( commutative-ring-Commutative-Ring-𝔽ᵉ R2ᵉ)

  ring-product-Commutative-Ring-𝔽ᵉ : Commutative-Ringᵉ (l1ᵉ ⊔ l2ᵉ)
  ring-product-Commutative-Ring-𝔽ᵉ =
    product-Commutative-Ringᵉ
      ( commutative-ring-Commutative-Ring-𝔽ᵉ R1ᵉ)
      ( commutative-ring-Commutative-Ring-𝔽ᵉ R2ᵉ)

  commutative-mul-product-Commutative-Ring-𝔽ᵉ :
    (xᵉ yᵉ : type-product-Commutative-Ring-𝔽ᵉ) →
    mul-product-Commutative-Ring-𝔽ᵉ xᵉ yᵉ ＝ᵉ mul-product-Commutative-Ring-𝔽ᵉ yᵉ xᵉ
  commutative-mul-product-Commutative-Ring-𝔽ᵉ =
    commutative-mul-product-Commutative-Ringᵉ
      ( commutative-ring-Commutative-Ring-𝔽ᵉ R1ᵉ)
      ( commutative-ring-Commutative-Ring-𝔽ᵉ R2ᵉ)

  commutative-ring-product-Commutative-Ring-𝔽ᵉ : Commutative-Ringᵉ (l1ᵉ ⊔ l2ᵉ)
  commutative-ring-product-Commutative-Ring-𝔽ᵉ =
    product-Commutative-Ringᵉ
      ( commutative-ring-Commutative-Ring-𝔽ᵉ R1ᵉ)
      ( commutative-ring-Commutative-Ring-𝔽ᵉ R2ᵉ)

  product-Commutative-Ring-𝔽ᵉ : Commutative-Ring-𝔽ᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ product-Commutative-Ring-𝔽ᵉ =
    product-Ring-𝔽ᵉ
      ( finite-ring-Commutative-Ring-𝔽ᵉ R1ᵉ)
      ( finite-ring-Commutative-Ring-𝔽ᵉ R2ᵉ)
  pr2ᵉ product-Commutative-Ring-𝔽ᵉ = commutative-mul-product-Commutative-Ring-𝔽ᵉ
```