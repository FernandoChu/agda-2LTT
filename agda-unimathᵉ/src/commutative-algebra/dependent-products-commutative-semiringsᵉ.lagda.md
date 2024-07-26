# Dependent products of commutative semirings

```agda
module commutative-algebra.dependent-products-commutative-semiringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-semiringsᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.commutative-monoidsᵉ
open import group-theory.dependent-products-commutative-monoidsᵉ

open import ring-theory.dependent-products-semiringsᵉ
open import ring-theory.semiringsᵉ
```

</details>

## Idea

Givenᵉ aᵉ familyᵉ ofᵉ commutativeᵉ semiringsᵉ `Aᵉ i`ᵉ indexedᵉ byᵉ `iᵉ : I`,ᵉ theirᵉ
**dependentᵉ product**ᵉ `Πᵉ (i:I),ᵉ Aᵉ i`ᵉ isᵉ againᵉ aᵉ commutativeᵉ semiring.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Iᵉ : UUᵉ l1ᵉ) (Aᵉ : Iᵉ → Commutative-Semiringᵉ l2ᵉ)
  where

  semiring-Π-Commutative-Semiringᵉ : Semiringᵉ (l1ᵉ ⊔ l2ᵉ)
  semiring-Π-Commutative-Semiringᵉ =
    Π-Semiringᵉ Iᵉ (λ iᵉ → semiring-Commutative-Semiringᵉ (Aᵉ iᵉ))

  additive-commutative-monoid-Π-Commutative-Semiringᵉ :
    Commutative-Monoidᵉ (l1ᵉ ⊔ l2ᵉ)
  additive-commutative-monoid-Π-Commutative-Semiringᵉ =
    Π-Commutative-Monoidᵉ Iᵉ
      ( λ iᵉ → additive-commutative-monoid-Commutative-Semiringᵉ (Aᵉ iᵉ))

  multiplicative-commutative-monoid-Π-Commutative-Semiringᵉ :
    Commutative-Monoidᵉ (l1ᵉ ⊔ l2ᵉ)
  multiplicative-commutative-monoid-Π-Commutative-Semiringᵉ =
    Π-Commutative-Monoidᵉ Iᵉ
      ( λ iᵉ → multiplicative-commutative-monoid-Commutative-Semiringᵉ (Aᵉ iᵉ))

  set-Π-Commutative-Semiringᵉ : Setᵉ (l1ᵉ ⊔ l2ᵉ)
  set-Π-Commutative-Semiringᵉ =
    set-Π-Semiringᵉ Iᵉ (λ iᵉ → semiring-Commutative-Semiringᵉ (Aᵉ iᵉ))

  type-Π-Commutative-Semiringᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  type-Π-Commutative-Semiringᵉ =
    type-Π-Semiringᵉ Iᵉ (λ iᵉ → semiring-Commutative-Semiringᵉ (Aᵉ iᵉ))

  is-set-type-Π-Commutative-Semiringᵉ : is-setᵉ type-Π-Commutative-Semiringᵉ
  is-set-type-Π-Commutative-Semiringᵉ =
    is-set-type-Π-Semiringᵉ Iᵉ (λ iᵉ → semiring-Commutative-Semiringᵉ (Aᵉ iᵉ))

  add-Π-Commutative-Semiringᵉ :
    type-Π-Commutative-Semiringᵉ → type-Π-Commutative-Semiringᵉ →
    type-Π-Commutative-Semiringᵉ
  add-Π-Commutative-Semiringᵉ =
    add-Π-Semiringᵉ Iᵉ (λ iᵉ → semiring-Commutative-Semiringᵉ (Aᵉ iᵉ))

  zero-Π-Commutative-Semiringᵉ : type-Π-Commutative-Semiringᵉ
  zero-Π-Commutative-Semiringᵉ =
    zero-Π-Semiringᵉ Iᵉ (λ iᵉ → semiring-Commutative-Semiringᵉ (Aᵉ iᵉ))

  associative-add-Π-Commutative-Semiringᵉ :
    (xᵉ yᵉ zᵉ : type-Π-Commutative-Semiringᵉ) →
    add-Π-Commutative-Semiringᵉ (add-Π-Commutative-Semiringᵉ xᵉ yᵉ) zᵉ ＝ᵉ
    add-Π-Commutative-Semiringᵉ xᵉ (add-Π-Commutative-Semiringᵉ yᵉ zᵉ)
  associative-add-Π-Commutative-Semiringᵉ =
    associative-add-Π-Semiringᵉ Iᵉ (λ iᵉ → semiring-Commutative-Semiringᵉ (Aᵉ iᵉ))

  left-unit-law-add-Π-Commutative-Semiringᵉ :
    (xᵉ : type-Π-Commutative-Semiringᵉ) →
    add-Π-Commutative-Semiringᵉ zero-Π-Commutative-Semiringᵉ xᵉ ＝ᵉ xᵉ
  left-unit-law-add-Π-Commutative-Semiringᵉ =
    left-unit-law-add-Π-Semiringᵉ Iᵉ (λ iᵉ → semiring-Commutative-Semiringᵉ (Aᵉ iᵉ))

  right-unit-law-add-Π-Commutative-Semiringᵉ :
    (xᵉ : type-Π-Commutative-Semiringᵉ) →
    add-Π-Commutative-Semiringᵉ xᵉ zero-Π-Commutative-Semiringᵉ ＝ᵉ xᵉ
  right-unit-law-add-Π-Commutative-Semiringᵉ =
    right-unit-law-add-Π-Semiringᵉ Iᵉ (λ iᵉ → semiring-Commutative-Semiringᵉ (Aᵉ iᵉ))

  commutative-add-Π-Commutative-Semiringᵉ :
    (xᵉ yᵉ : type-Π-Commutative-Semiringᵉ) →
    add-Π-Commutative-Semiringᵉ xᵉ yᵉ ＝ᵉ add-Π-Commutative-Semiringᵉ yᵉ xᵉ
  commutative-add-Π-Commutative-Semiringᵉ =
    commutative-add-Π-Semiringᵉ Iᵉ (λ iᵉ → semiring-Commutative-Semiringᵉ (Aᵉ iᵉ))

  mul-Π-Commutative-Semiringᵉ :
    type-Π-Commutative-Semiringᵉ → type-Π-Commutative-Semiringᵉ →
    type-Π-Commutative-Semiringᵉ
  mul-Π-Commutative-Semiringᵉ =
    mul-Π-Semiringᵉ Iᵉ (λ iᵉ → semiring-Commutative-Semiringᵉ (Aᵉ iᵉ))

  one-Π-Commutative-Semiringᵉ : type-Π-Commutative-Semiringᵉ
  one-Π-Commutative-Semiringᵉ =
    one-Π-Semiringᵉ Iᵉ (λ iᵉ → semiring-Commutative-Semiringᵉ (Aᵉ iᵉ))

  associative-mul-Π-Commutative-Semiringᵉ :
    (xᵉ yᵉ zᵉ : type-Π-Commutative-Semiringᵉ) →
    mul-Π-Commutative-Semiringᵉ (mul-Π-Commutative-Semiringᵉ xᵉ yᵉ) zᵉ ＝ᵉ
    mul-Π-Commutative-Semiringᵉ xᵉ (mul-Π-Commutative-Semiringᵉ yᵉ zᵉ)
  associative-mul-Π-Commutative-Semiringᵉ =
    associative-mul-Π-Semiringᵉ Iᵉ (λ iᵉ → semiring-Commutative-Semiringᵉ (Aᵉ iᵉ))

  left-unit-law-mul-Π-Commutative-Semiringᵉ :
    (xᵉ : type-Π-Commutative-Semiringᵉ) →
    mul-Π-Commutative-Semiringᵉ one-Π-Commutative-Semiringᵉ xᵉ ＝ᵉ xᵉ
  left-unit-law-mul-Π-Commutative-Semiringᵉ =
    left-unit-law-mul-Π-Semiringᵉ Iᵉ (λ iᵉ → semiring-Commutative-Semiringᵉ (Aᵉ iᵉ))

  right-unit-law-mul-Π-Commutative-Semiringᵉ :
    (xᵉ : type-Π-Commutative-Semiringᵉ) →
    mul-Π-Commutative-Semiringᵉ xᵉ one-Π-Commutative-Semiringᵉ ＝ᵉ xᵉ
  right-unit-law-mul-Π-Commutative-Semiringᵉ =
    right-unit-law-mul-Π-Semiringᵉ Iᵉ (λ iᵉ → semiring-Commutative-Semiringᵉ (Aᵉ iᵉ))

  left-distributive-mul-add-Π-Commutative-Semiringᵉ :
    (fᵉ gᵉ hᵉ : type-Π-Commutative-Semiringᵉ) →
    mul-Π-Commutative-Semiringᵉ fᵉ (add-Π-Commutative-Semiringᵉ gᵉ hᵉ) ＝ᵉ
    add-Π-Commutative-Semiringᵉ
      ( mul-Π-Commutative-Semiringᵉ fᵉ gᵉ)
      ( mul-Π-Commutative-Semiringᵉ fᵉ hᵉ)
  left-distributive-mul-add-Π-Commutative-Semiringᵉ =
    left-distributive-mul-add-Π-Semiringᵉ Iᵉ
      ( λ iᵉ → semiring-Commutative-Semiringᵉ (Aᵉ iᵉ))

  right-distributive-mul-add-Π-Commutative-Semiringᵉ :
    (fᵉ gᵉ hᵉ : type-Π-Commutative-Semiringᵉ) →
    mul-Π-Commutative-Semiringᵉ (add-Π-Commutative-Semiringᵉ fᵉ gᵉ) hᵉ ＝ᵉ
    add-Π-Commutative-Semiringᵉ
      ( mul-Π-Commutative-Semiringᵉ fᵉ hᵉ)
      ( mul-Π-Commutative-Semiringᵉ gᵉ hᵉ)
  right-distributive-mul-add-Π-Commutative-Semiringᵉ =
    right-distributive-mul-add-Π-Semiringᵉ Iᵉ
      ( λ iᵉ → semiring-Commutative-Semiringᵉ (Aᵉ iᵉ))

  left-zero-law-mul-Π-Commutative-Semiringᵉ :
    (fᵉ : type-Π-Commutative-Semiringᵉ) →
    mul-Π-Commutative-Semiringᵉ zero-Π-Commutative-Semiringᵉ fᵉ ＝ᵉ
    zero-Π-Commutative-Semiringᵉ
  left-zero-law-mul-Π-Commutative-Semiringᵉ =
    left-zero-law-mul-Π-Semiringᵉ Iᵉ (λ iᵉ → semiring-Commutative-Semiringᵉ (Aᵉ iᵉ))

  right-zero-law-mul-Π-Commutative-Semiringᵉ :
    (fᵉ : type-Π-Commutative-Semiringᵉ) →
    mul-Π-Commutative-Semiringᵉ fᵉ zero-Π-Commutative-Semiringᵉ ＝ᵉ
    zero-Π-Commutative-Semiringᵉ
  right-zero-law-mul-Π-Commutative-Semiringᵉ =
    right-zero-law-mul-Π-Semiringᵉ Iᵉ (λ iᵉ → semiring-Commutative-Semiringᵉ (Aᵉ iᵉ))

  commutative-mul-Π-Commutative-Semiringᵉ :
    (fᵉ gᵉ : type-Π-Commutative-Semiringᵉ) →
    mul-Π-Commutative-Semiringᵉ fᵉ gᵉ ＝ᵉ mul-Π-Commutative-Semiringᵉ gᵉ fᵉ
  commutative-mul-Π-Commutative-Semiringᵉ =
    commutative-mul-Commutative-Monoidᵉ
      multiplicative-commutative-monoid-Π-Commutative-Semiringᵉ

  Π-Commutative-Semiringᵉ : Commutative-Semiringᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ Π-Commutative-Semiringᵉ = semiring-Π-Commutative-Semiringᵉ
  pr2ᵉ Π-Commutative-Semiringᵉ = commutative-mul-Π-Commutative-Semiringᵉ
```