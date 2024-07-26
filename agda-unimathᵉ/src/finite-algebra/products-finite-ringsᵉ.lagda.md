# Products of finite rings

```agda
module finite-algebra.products-finite-ringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import finite-algebra.finite-ringsᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.abelian-groupsᵉ
open import group-theory.groupsᵉ
open import group-theory.semigroupsᵉ

open import ring-theory.products-ringsᵉ
open import ring-theory.ringsᵉ

open import univalent-combinatorics.cartesian-product-typesᵉ
open import univalent-combinatorics.finite-typesᵉ
```

</details>

## Idea

Givenᵉ twoᵉ finiteᵉ ringsᵉ R1ᵉ andᵉ R2,ᵉ weᵉ defineᵉ aᵉ ringᵉ structureᵉ onᵉ theᵉ productᵉ ofᵉ
R1ᵉ andᵉ R2.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} (R1ᵉ : Ring-𝔽ᵉ l1ᵉ) (R2ᵉ : Ring-𝔽ᵉ l2ᵉ)
  where

  set-product-Ring-𝔽ᵉ : Setᵉ (l1ᵉ ⊔ l2ᵉ)
  set-product-Ring-𝔽ᵉ = set-product-Ringᵉ (ring-Ring-𝔽ᵉ R1ᵉ) (ring-Ring-𝔽ᵉ R2ᵉ)

  type-product-Ring-𝔽ᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  type-product-Ring-𝔽ᵉ = type-product-Ringᵉ (ring-Ring-𝔽ᵉ R1ᵉ) (ring-Ring-𝔽ᵉ R2ᵉ)

  is-set-type-product-Ring-𝔽ᵉ : is-setᵉ type-product-Ring-𝔽ᵉ
  is-set-type-product-Ring-𝔽ᵉ =
    is-set-type-product-Ringᵉ (ring-Ring-𝔽ᵉ R1ᵉ) (ring-Ring-𝔽ᵉ R2ᵉ)

  is-finite-type-product-Ring-𝔽ᵉ : is-finiteᵉ type-product-Ring-𝔽ᵉ
  is-finite-type-product-Ring-𝔽ᵉ =
    is-finite-productᵉ (is-finite-type-Ring-𝔽ᵉ R1ᵉ) (is-finite-type-Ring-𝔽ᵉ R2ᵉ)

  finite-type-product-Ring-𝔽ᵉ : 𝔽ᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ finite-type-product-Ring-𝔽ᵉ = type-product-Ring-𝔽ᵉ
  pr2ᵉ finite-type-product-Ring-𝔽ᵉ = is-finite-type-product-Ring-𝔽ᵉ

  add-product-Ring-𝔽ᵉ :
    type-product-Ring-𝔽ᵉ → type-product-Ring-𝔽ᵉ → type-product-Ring-𝔽ᵉ
  add-product-Ring-𝔽ᵉ = add-product-Ringᵉ (ring-Ring-𝔽ᵉ R1ᵉ) (ring-Ring-𝔽ᵉ R2ᵉ)

  zero-product-Ring-𝔽ᵉ : type-product-Ring-𝔽ᵉ
  zero-product-Ring-𝔽ᵉ = zero-product-Ringᵉ (ring-Ring-𝔽ᵉ R1ᵉ) (ring-Ring-𝔽ᵉ R2ᵉ)

  neg-product-Ring-𝔽ᵉ : type-product-Ring-𝔽ᵉ → type-product-Ring-𝔽ᵉ
  neg-product-Ring-𝔽ᵉ = neg-product-Ringᵉ (ring-Ring-𝔽ᵉ R1ᵉ) (ring-Ring-𝔽ᵉ R2ᵉ)

  left-unit-law-add-product-Ring-𝔽ᵉ :
    (xᵉ : type-product-Ring-𝔽ᵉ) → Idᵉ (add-product-Ring-𝔽ᵉ zero-product-Ring-𝔽ᵉ xᵉ) xᵉ
  left-unit-law-add-product-Ring-𝔽ᵉ =
    left-unit-law-add-product-Ringᵉ (ring-Ring-𝔽ᵉ R1ᵉ) (ring-Ring-𝔽ᵉ R2ᵉ)

  right-unit-law-add-product-Ring-𝔽ᵉ :
    (xᵉ : type-product-Ring-𝔽ᵉ) → Idᵉ (add-product-Ring-𝔽ᵉ xᵉ zero-product-Ring-𝔽ᵉ) xᵉ
  right-unit-law-add-product-Ring-𝔽ᵉ =
    right-unit-law-add-product-Ringᵉ (ring-Ring-𝔽ᵉ R1ᵉ) (ring-Ring-𝔽ᵉ R2ᵉ)

  left-inverse-law-add-product-Ring-𝔽ᵉ :
    (xᵉ : type-product-Ring-𝔽ᵉ) →
    Idᵉ (add-product-Ring-𝔽ᵉ (neg-product-Ring-𝔽ᵉ xᵉ) xᵉ) zero-product-Ring-𝔽ᵉ
  left-inverse-law-add-product-Ring-𝔽ᵉ =
    left-inverse-law-add-product-Ringᵉ (ring-Ring-𝔽ᵉ R1ᵉ) (ring-Ring-𝔽ᵉ R2ᵉ)

  right-inverse-law-add-product-Ring-𝔽ᵉ :
    (xᵉ : type-product-Ring-𝔽ᵉ) →
    Idᵉ (add-product-Ring-𝔽ᵉ xᵉ (neg-product-Ring-𝔽ᵉ xᵉ)) zero-product-Ring-𝔽ᵉ
  right-inverse-law-add-product-Ring-𝔽ᵉ =
    right-inverse-law-add-product-Ringᵉ (ring-Ring-𝔽ᵉ R1ᵉ) (ring-Ring-𝔽ᵉ R2ᵉ)

  associative-add-product-Ring-𝔽ᵉ :
    (xᵉ yᵉ zᵉ : type-product-Ring-𝔽ᵉ) →
    Idᵉ
      ( add-product-Ring-𝔽ᵉ (add-product-Ring-𝔽ᵉ xᵉ yᵉ) zᵉ)
      ( add-product-Ring-𝔽ᵉ xᵉ (add-product-Ring-𝔽ᵉ yᵉ zᵉ))
  associative-add-product-Ring-𝔽ᵉ =
    associative-add-product-Ringᵉ (ring-Ring-𝔽ᵉ R1ᵉ) (ring-Ring-𝔽ᵉ R2ᵉ)

  commutative-add-product-Ring-𝔽ᵉ :
    (xᵉ yᵉ : type-product-Ring-𝔽ᵉ) →
    Idᵉ (add-product-Ring-𝔽ᵉ xᵉ yᵉ) (add-product-Ring-𝔽ᵉ yᵉ xᵉ)
  commutative-add-product-Ring-𝔽ᵉ =
    commutative-add-product-Ringᵉ (ring-Ring-𝔽ᵉ R1ᵉ) (ring-Ring-𝔽ᵉ R2ᵉ)

  mul-product-Ring-𝔽ᵉ :
    type-product-Ring-𝔽ᵉ → type-product-Ring-𝔽ᵉ → type-product-Ring-𝔽ᵉ
  mul-product-Ring-𝔽ᵉ = mul-product-Ringᵉ (ring-Ring-𝔽ᵉ R1ᵉ) (ring-Ring-𝔽ᵉ R2ᵉ)

  one-product-Ring-𝔽ᵉ : type-product-Ring-𝔽ᵉ
  one-product-Ring-𝔽ᵉ = one-product-Ringᵉ (ring-Ring-𝔽ᵉ R1ᵉ) (ring-Ring-𝔽ᵉ R2ᵉ)

  associative-mul-product-Ring-𝔽ᵉ :
    (xᵉ yᵉ zᵉ : type-product-Ring-𝔽ᵉ) →
    Idᵉ
      ( mul-product-Ring-𝔽ᵉ (mul-product-Ring-𝔽ᵉ xᵉ yᵉ) zᵉ)
      ( mul-product-Ring-𝔽ᵉ xᵉ (mul-product-Ring-𝔽ᵉ yᵉ zᵉ))
  associative-mul-product-Ring-𝔽ᵉ =
    associative-mul-product-Ringᵉ (ring-Ring-𝔽ᵉ R1ᵉ) (ring-Ring-𝔽ᵉ R2ᵉ)

  left-unit-law-mul-product-Ring-𝔽ᵉ :
    (xᵉ : type-product-Ring-𝔽ᵉ) → Idᵉ (mul-product-Ring-𝔽ᵉ one-product-Ring-𝔽ᵉ xᵉ) xᵉ
  left-unit-law-mul-product-Ring-𝔽ᵉ =
    left-unit-law-mul-product-Ringᵉ (ring-Ring-𝔽ᵉ R1ᵉ) (ring-Ring-𝔽ᵉ R2ᵉ)

  right-unit-law-mul-product-Ring-𝔽ᵉ :
    (xᵉ : type-product-Ring-𝔽ᵉ) → Idᵉ (mul-product-Ring-𝔽ᵉ xᵉ one-product-Ring-𝔽ᵉ) xᵉ
  right-unit-law-mul-product-Ring-𝔽ᵉ =
    right-unit-law-mul-product-Ringᵉ (ring-Ring-𝔽ᵉ R1ᵉ) (ring-Ring-𝔽ᵉ R2ᵉ)

  left-distributive-mul-add-product-Ring-𝔽ᵉ :
    (xᵉ yᵉ zᵉ : type-product-Ring-𝔽ᵉ) →
    Idᵉ
      ( mul-product-Ring-𝔽ᵉ xᵉ (add-product-Ring-𝔽ᵉ yᵉ zᵉ))
      ( add-product-Ring-𝔽ᵉ (mul-product-Ring-𝔽ᵉ xᵉ yᵉ) (mul-product-Ring-𝔽ᵉ xᵉ zᵉ))
  left-distributive-mul-add-product-Ring-𝔽ᵉ =
    left-distributive-mul-add-product-Ringᵉ (ring-Ring-𝔽ᵉ R1ᵉ) (ring-Ring-𝔽ᵉ R2ᵉ)

  right-distributive-mul-add-product-Ring-𝔽ᵉ :
    (xᵉ yᵉ zᵉ : type-product-Ring-𝔽ᵉ) →
    Idᵉ
      ( mul-product-Ring-𝔽ᵉ (add-product-Ring-𝔽ᵉ xᵉ yᵉ) zᵉ)
      ( add-product-Ring-𝔽ᵉ (mul-product-Ring-𝔽ᵉ xᵉ zᵉ) (mul-product-Ring-𝔽ᵉ yᵉ zᵉ))
  right-distributive-mul-add-product-Ring-𝔽ᵉ =
    right-distributive-mul-add-product-Ringᵉ (ring-Ring-𝔽ᵉ R1ᵉ) (ring-Ring-𝔽ᵉ R2ᵉ)

  semigroup-product-Ring-𝔽ᵉ : Semigroupᵉ (l1ᵉ ⊔ l2ᵉ)
  semigroup-product-Ring-𝔽ᵉ =
    semigroup-product-Ringᵉ (ring-Ring-𝔽ᵉ R1ᵉ) (ring-Ring-𝔽ᵉ R2ᵉ)

  group-product-Ring-𝔽ᵉ : Groupᵉ (l1ᵉ ⊔ l2ᵉ)
  group-product-Ring-𝔽ᵉ = group-product-Ringᵉ (ring-Ring-𝔽ᵉ R1ᵉ) (ring-Ring-𝔽ᵉ R2ᵉ)

  ab-product-Ring-𝔽ᵉ : Abᵉ (l1ᵉ ⊔ l2ᵉ)
  ab-product-Ring-𝔽ᵉ = ab-product-Ringᵉ (ring-Ring-𝔽ᵉ R1ᵉ) (ring-Ring-𝔽ᵉ R2ᵉ)

  ring-product-Ring-𝔽ᵉ : Ringᵉ (l1ᵉ ⊔ l2ᵉ)
  ring-product-Ring-𝔽ᵉ = product-Ringᵉ (ring-Ring-𝔽ᵉ R1ᵉ) (ring-Ring-𝔽ᵉ R2ᵉ)

  product-Ring-𝔽ᵉ : Ring-𝔽ᵉ (l1ᵉ ⊔ l2ᵉ)
  product-Ring-𝔽ᵉ =
    finite-ring-is-finite-Ringᵉ ring-product-Ring-𝔽ᵉ is-finite-type-product-Ring-𝔽ᵉ
```