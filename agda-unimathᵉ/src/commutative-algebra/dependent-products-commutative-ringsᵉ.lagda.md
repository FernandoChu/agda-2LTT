# Dependent products of commutative rings

```agda
module commutative-algebra.dependent-products-commutative-ringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-ringsᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.abelian-groupsᵉ
open import group-theory.commutative-monoidsᵉ
open import group-theory.dependent-products-commutative-monoidsᵉ

open import ring-theory.dependent-products-ringsᵉ
open import ring-theory.ringsᵉ
```

</details>

## Idea

Givenᵉ aᵉ familyᵉ ofᵉ commutativeᵉ ringsᵉ `Aᵉ i`ᵉ indexedᵉ byᵉ `iᵉ : I`,ᵉ theirᵉ **dependentᵉ
product**ᵉ `Π(i:I),ᵉ Aᵉ i`ᵉ isᵉ againᵉ aᵉ commutativeᵉ ring.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Iᵉ : UUᵉ l1ᵉ) (Aᵉ : Iᵉ → Commutative-Ringᵉ l2ᵉ)
  where

  ring-Π-Commutative-Ringᵉ : Ringᵉ (l1ᵉ ⊔ l2ᵉ)
  ring-Π-Commutative-Ringᵉ = Π-Ringᵉ Iᵉ (λ iᵉ → ring-Commutative-Ringᵉ (Aᵉ iᵉ))

  ab-Π-Commutative-Ringᵉ : Abᵉ (l1ᵉ ⊔ l2ᵉ)
  ab-Π-Commutative-Ringᵉ = ab-Ringᵉ ring-Π-Commutative-Ringᵉ

  multiplicative-commutative-monoid-Π-Commutative-Ringᵉ :
    Commutative-Monoidᵉ (l1ᵉ ⊔ l2ᵉ)
  multiplicative-commutative-monoid-Π-Commutative-Ringᵉ =
    Π-Commutative-Monoidᵉ Iᵉ
      ( λ iᵉ → multiplicative-commutative-monoid-Commutative-Ringᵉ (Aᵉ iᵉ))

  set-Π-Commutative-Ringᵉ : Setᵉ (l1ᵉ ⊔ l2ᵉ)
  set-Π-Commutative-Ringᵉ = set-Ringᵉ ring-Π-Commutative-Ringᵉ

  type-Π-Commutative-Ringᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  type-Π-Commutative-Ringᵉ = type-Ringᵉ ring-Π-Commutative-Ringᵉ

  is-set-type-Π-Commutative-Ringᵉ : is-setᵉ type-Π-Commutative-Ringᵉ
  is-set-type-Π-Commutative-Ringᵉ =
    is-set-type-Ringᵉ ring-Π-Commutative-Ringᵉ

  add-Π-Commutative-Ringᵉ :
    type-Π-Commutative-Ringᵉ → type-Π-Commutative-Ringᵉ →
    type-Π-Commutative-Ringᵉ
  add-Π-Commutative-Ringᵉ = add-Ringᵉ ring-Π-Commutative-Ringᵉ

  zero-Π-Commutative-Ringᵉ : type-Π-Commutative-Ringᵉ
  zero-Π-Commutative-Ringᵉ = zero-Ringᵉ ring-Π-Commutative-Ringᵉ

  associative-add-Π-Commutative-Ringᵉ :
    (xᵉ yᵉ zᵉ : type-Π-Commutative-Ringᵉ) →
    add-Π-Commutative-Ringᵉ (add-Π-Commutative-Ringᵉ xᵉ yᵉ) zᵉ ＝ᵉ
    add-Π-Commutative-Ringᵉ xᵉ (add-Π-Commutative-Ringᵉ yᵉ zᵉ)
  associative-add-Π-Commutative-Ringᵉ =
    associative-add-Ringᵉ ring-Π-Commutative-Ringᵉ

  left-unit-law-add-Π-Commutative-Ringᵉ :
    (xᵉ : type-Π-Commutative-Ringᵉ) →
    add-Π-Commutative-Ringᵉ zero-Π-Commutative-Ringᵉ xᵉ ＝ᵉ xᵉ
  left-unit-law-add-Π-Commutative-Ringᵉ =
    left-unit-law-add-Ringᵉ ring-Π-Commutative-Ringᵉ

  right-unit-law-add-Π-Commutative-Ringᵉ :
    (xᵉ : type-Π-Commutative-Ringᵉ) →
    add-Π-Commutative-Ringᵉ xᵉ zero-Π-Commutative-Ringᵉ ＝ᵉ xᵉ
  right-unit-law-add-Π-Commutative-Ringᵉ =
    right-unit-law-add-Ringᵉ ring-Π-Commutative-Ringᵉ

  commutative-add-Π-Commutative-Ringᵉ :
    (xᵉ yᵉ : type-Π-Commutative-Ringᵉ) →
    add-Π-Commutative-Ringᵉ xᵉ yᵉ ＝ᵉ add-Π-Commutative-Ringᵉ yᵉ xᵉ
  commutative-add-Π-Commutative-Ringᵉ =
    commutative-add-Ringᵉ ring-Π-Commutative-Ringᵉ

  mul-Π-Commutative-Ringᵉ :
    type-Π-Commutative-Ringᵉ → type-Π-Commutative-Ringᵉ →
    type-Π-Commutative-Ringᵉ
  mul-Π-Commutative-Ringᵉ =
    mul-Ringᵉ ring-Π-Commutative-Ringᵉ

  one-Π-Commutative-Ringᵉ : type-Π-Commutative-Ringᵉ
  one-Π-Commutative-Ringᵉ =
    one-Ringᵉ ring-Π-Commutative-Ringᵉ

  associative-mul-Π-Commutative-Ringᵉ :
    (xᵉ yᵉ zᵉ : type-Π-Commutative-Ringᵉ) →
    mul-Π-Commutative-Ringᵉ (mul-Π-Commutative-Ringᵉ xᵉ yᵉ) zᵉ ＝ᵉ
    mul-Π-Commutative-Ringᵉ xᵉ (mul-Π-Commutative-Ringᵉ yᵉ zᵉ)
  associative-mul-Π-Commutative-Ringᵉ =
    associative-mul-Ringᵉ ring-Π-Commutative-Ringᵉ

  left-unit-law-mul-Π-Commutative-Ringᵉ :
    (xᵉ : type-Π-Commutative-Ringᵉ) →
    mul-Π-Commutative-Ringᵉ one-Π-Commutative-Ringᵉ xᵉ ＝ᵉ xᵉ
  left-unit-law-mul-Π-Commutative-Ringᵉ =
    left-unit-law-mul-Ringᵉ ring-Π-Commutative-Ringᵉ

  right-unit-law-mul-Π-Commutative-Ringᵉ :
    (xᵉ : type-Π-Commutative-Ringᵉ) →
    mul-Π-Commutative-Ringᵉ xᵉ one-Π-Commutative-Ringᵉ ＝ᵉ xᵉ
  right-unit-law-mul-Π-Commutative-Ringᵉ =
    right-unit-law-mul-Ringᵉ ring-Π-Commutative-Ringᵉ

  left-distributive-mul-add-Π-Commutative-Ringᵉ :
    (fᵉ gᵉ hᵉ : type-Π-Commutative-Ringᵉ) →
    mul-Π-Commutative-Ringᵉ fᵉ (add-Π-Commutative-Ringᵉ gᵉ hᵉ) ＝ᵉ
    add-Π-Commutative-Ringᵉ
      ( mul-Π-Commutative-Ringᵉ fᵉ gᵉ)
      ( mul-Π-Commutative-Ringᵉ fᵉ hᵉ)
  left-distributive-mul-add-Π-Commutative-Ringᵉ =
    left-distributive-mul-add-Ringᵉ ring-Π-Commutative-Ringᵉ

  right-distributive-mul-add-Π-Commutative-Ringᵉ :
    (fᵉ gᵉ hᵉ : type-Π-Commutative-Ringᵉ) →
    mul-Π-Commutative-Ringᵉ (add-Π-Commutative-Ringᵉ fᵉ gᵉ) hᵉ ＝ᵉ
    add-Π-Commutative-Ringᵉ
      ( mul-Π-Commutative-Ringᵉ fᵉ hᵉ)
      ( mul-Π-Commutative-Ringᵉ gᵉ hᵉ)
  right-distributive-mul-add-Π-Commutative-Ringᵉ =
    right-distributive-mul-add-Ringᵉ ring-Π-Commutative-Ringᵉ

  left-zero-law-mul-Π-Commutative-Ringᵉ :
    (fᵉ : type-Π-Commutative-Ringᵉ) →
    mul-Π-Commutative-Ringᵉ zero-Π-Commutative-Ringᵉ fᵉ ＝ᵉ
    zero-Π-Commutative-Ringᵉ
  left-zero-law-mul-Π-Commutative-Ringᵉ =
    left-zero-law-mul-Ringᵉ ring-Π-Commutative-Ringᵉ

  right-zero-law-mul-Π-Commutative-Ringᵉ :
    (fᵉ : type-Π-Commutative-Ringᵉ) →
    mul-Π-Commutative-Ringᵉ fᵉ zero-Π-Commutative-Ringᵉ ＝ᵉ
    zero-Π-Commutative-Ringᵉ
  right-zero-law-mul-Π-Commutative-Ringᵉ =
    right-zero-law-mul-Ringᵉ ring-Π-Commutative-Ringᵉ

  commutative-mul-Π-Commutative-Ringᵉ :
    (fᵉ gᵉ : type-Π-Commutative-Ringᵉ) →
    mul-Π-Commutative-Ringᵉ fᵉ gᵉ ＝ᵉ mul-Π-Commutative-Ringᵉ gᵉ fᵉ
  commutative-mul-Π-Commutative-Ringᵉ =
    commutative-mul-Commutative-Monoidᵉ
      multiplicative-commutative-monoid-Π-Commutative-Ringᵉ

  Π-Commutative-Ringᵉ : Commutative-Ringᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ Π-Commutative-Ringᵉ = ring-Π-Commutative-Ringᵉ
  pr2ᵉ Π-Commutative-Ringᵉ = commutative-mul-Π-Commutative-Ringᵉ
```