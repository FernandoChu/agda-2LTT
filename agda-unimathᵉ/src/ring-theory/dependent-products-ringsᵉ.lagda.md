# Dependent products of rings

```agda
module ring-theory.dependent-products-ringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.abelian-groupsᵉ
open import group-theory.dependent-products-abelian-groupsᵉ
open import group-theory.groupsᵉ
open import group-theory.monoidsᵉ
open import group-theory.semigroupsᵉ

open import ring-theory.dependent-products-semiringsᵉ
open import ring-theory.ringsᵉ
open import ring-theory.semiringsᵉ
```

</details>

## Idea

Givenᵉ aᵉ familyᵉ ofᵉ ringsᵉ `Rᵉ i`ᵉ indexedᵉ byᵉ `iᵉ : I`,ᵉ theirᵉ dependentᵉ productᵉ
`Π(i:I),ᵉ Rᵉ i`ᵉ isᵉ againᵉ aᵉ ring.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Iᵉ : UUᵉ l1ᵉ) (Rᵉ : Iᵉ → Ringᵉ l2ᵉ)
  where

  semiring-Π-Ringᵉ : Semiringᵉ (l1ᵉ ⊔ l2ᵉ)
  semiring-Π-Ringᵉ = Π-Semiringᵉ Iᵉ (λ iᵉ → semiring-Ringᵉ (Rᵉ iᵉ))

  ab-Π-Ringᵉ : Abᵉ (l1ᵉ ⊔ l2ᵉ)
  ab-Π-Ringᵉ = Π-Abᵉ Iᵉ (λ iᵉ → ab-Ringᵉ (Rᵉ iᵉ))

  group-Π-Ringᵉ : Groupᵉ (l1ᵉ ⊔ l2ᵉ)
  group-Π-Ringᵉ = group-Abᵉ ab-Π-Ringᵉ

  semigroup-Π-Ringᵉ : Semigroupᵉ (l1ᵉ ⊔ l2ᵉ)
  semigroup-Π-Ringᵉ = semigroup-Abᵉ ab-Π-Ringᵉ

  multiplicative-monoid-Π-Ringᵉ : Monoidᵉ (l1ᵉ ⊔ l2ᵉ)
  multiplicative-monoid-Π-Ringᵉ =
    multiplicative-monoid-Semiringᵉ semiring-Π-Ringᵉ

  set-Π-Ringᵉ : Setᵉ (l1ᵉ ⊔ l2ᵉ)
  set-Π-Ringᵉ = set-Semiringᵉ semiring-Π-Ringᵉ

  type-Π-Ringᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  type-Π-Ringᵉ = type-Semiringᵉ semiring-Π-Ringᵉ

  is-set-type-Π-Ringᵉ : is-setᵉ type-Π-Ringᵉ
  is-set-type-Π-Ringᵉ = is-set-type-Semiringᵉ semiring-Π-Ringᵉ

  add-Π-Ringᵉ : type-Π-Ringᵉ → type-Π-Ringᵉ → type-Π-Ringᵉ
  add-Π-Ringᵉ = add-Semiringᵉ semiring-Π-Ringᵉ

  zero-Π-Ringᵉ : type-Π-Ringᵉ
  zero-Π-Ringᵉ = zero-Semiringᵉ semiring-Π-Ringᵉ

  neg-Π-Ringᵉ : type-Π-Ringᵉ → type-Π-Ringᵉ
  neg-Π-Ringᵉ = neg-Abᵉ ab-Π-Ringᵉ

  associative-add-Π-Ringᵉ :
    (xᵉ yᵉ zᵉ : type-Π-Ringᵉ) →
    Idᵉ (add-Π-Ringᵉ (add-Π-Ringᵉ xᵉ yᵉ) zᵉ) (add-Π-Ringᵉ xᵉ (add-Π-Ringᵉ yᵉ zᵉ))
  associative-add-Π-Ringᵉ = associative-add-Semiringᵉ semiring-Π-Ringᵉ

  left-unit-law-add-Π-Ringᵉ :
    (xᵉ : type-Π-Ringᵉ) → Idᵉ (add-Π-Ringᵉ zero-Π-Ringᵉ xᵉ) xᵉ
  left-unit-law-add-Π-Ringᵉ = left-unit-law-add-Semiringᵉ semiring-Π-Ringᵉ

  right-unit-law-add-Π-Ringᵉ :
    (xᵉ : type-Π-Ringᵉ) → Idᵉ (add-Π-Ringᵉ xᵉ zero-Π-Ringᵉ) xᵉ
  right-unit-law-add-Π-Ringᵉ = right-unit-law-add-Semiringᵉ semiring-Π-Ringᵉ

  left-inverse-law-add-Π-Ringᵉ :
    (xᵉ : type-Π-Ringᵉ) → Idᵉ (add-Π-Ringᵉ (neg-Π-Ringᵉ xᵉ) xᵉ) zero-Π-Ringᵉ
  left-inverse-law-add-Π-Ringᵉ = left-inverse-law-add-Abᵉ ab-Π-Ringᵉ

  right-inverse-law-add-Π-Ringᵉ :
    (xᵉ : type-Π-Ringᵉ) → Idᵉ (add-Π-Ringᵉ xᵉ (neg-Π-Ringᵉ xᵉ)) zero-Π-Ringᵉ
  right-inverse-law-add-Π-Ringᵉ = right-inverse-law-add-Abᵉ ab-Π-Ringᵉ

  commutative-add-Π-Ringᵉ :
    (xᵉ yᵉ : type-Π-Ringᵉ) → Idᵉ (add-Π-Ringᵉ xᵉ yᵉ) (add-Π-Ringᵉ yᵉ xᵉ)
  commutative-add-Π-Ringᵉ = commutative-add-Semiringᵉ semiring-Π-Ringᵉ

  mul-Π-Ringᵉ : type-Π-Ringᵉ → type-Π-Ringᵉ → type-Π-Ringᵉ
  mul-Π-Ringᵉ = mul-Semiringᵉ semiring-Π-Ringᵉ

  one-Π-Ringᵉ : type-Π-Ringᵉ
  one-Π-Ringᵉ = one-Semiringᵉ semiring-Π-Ringᵉ

  associative-mul-Π-Ringᵉ :
    (xᵉ yᵉ zᵉ : type-Π-Ringᵉ) →
    Idᵉ (mul-Π-Ringᵉ (mul-Π-Ringᵉ xᵉ yᵉ) zᵉ) (mul-Π-Ringᵉ xᵉ (mul-Π-Ringᵉ yᵉ zᵉ))
  associative-mul-Π-Ringᵉ =
    associative-mul-Semiringᵉ semiring-Π-Ringᵉ

  left-unit-law-mul-Π-Ringᵉ :
    (xᵉ : type-Π-Ringᵉ) → Idᵉ (mul-Π-Ringᵉ one-Π-Ringᵉ xᵉ) xᵉ
  left-unit-law-mul-Π-Ringᵉ =
    left-unit-law-mul-Semiringᵉ semiring-Π-Ringᵉ

  right-unit-law-mul-Π-Ringᵉ :
    (xᵉ : type-Π-Ringᵉ) → Idᵉ (mul-Π-Ringᵉ xᵉ one-Π-Ringᵉ) xᵉ
  right-unit-law-mul-Π-Ringᵉ =
    right-unit-law-mul-Semiringᵉ semiring-Π-Ringᵉ

  left-distributive-mul-add-Π-Ringᵉ :
    (fᵉ gᵉ hᵉ : type-Π-Ringᵉ) →
    mul-Π-Ringᵉ fᵉ (add-Π-Ringᵉ gᵉ hᵉ) ＝ᵉ
    add-Π-Ringᵉ (mul-Π-Ringᵉ fᵉ gᵉ) (mul-Π-Ringᵉ fᵉ hᵉ)
  left-distributive-mul-add-Π-Ringᵉ =
    left-distributive-mul-add-Semiringᵉ semiring-Π-Ringᵉ

  right-distributive-mul-add-Π-Ringᵉ :
    (fᵉ gᵉ hᵉ : type-Π-Ringᵉ) →
    Idᵉ
      ( mul-Π-Ringᵉ (add-Π-Ringᵉ fᵉ gᵉ) hᵉ)
      ( add-Π-Ringᵉ (mul-Π-Ringᵉ fᵉ hᵉ) (mul-Π-Ringᵉ gᵉ hᵉ))
  right-distributive-mul-add-Π-Ringᵉ =
    right-distributive-mul-add-Semiringᵉ semiring-Π-Ringᵉ

  Π-Ringᵉ : Ringᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ Π-Ringᵉ = ab-Π-Ringᵉ
  pr1ᵉ (pr1ᵉ (pr2ᵉ Π-Ringᵉ)) = mul-Π-Ringᵉ
  pr2ᵉ (pr1ᵉ (pr2ᵉ Π-Ringᵉ)) = associative-mul-Π-Ringᵉ
  pr1ᵉ (pr1ᵉ (pr2ᵉ (pr2ᵉ Π-Ringᵉ))) = one-Π-Ringᵉ
  pr1ᵉ (pr2ᵉ (pr1ᵉ (pr2ᵉ (pr2ᵉ Π-Ringᵉ)))) = left-unit-law-mul-Π-Ringᵉ
  pr2ᵉ (pr2ᵉ (pr1ᵉ (pr2ᵉ (pr2ᵉ Π-Ringᵉ)))) = right-unit-law-mul-Π-Ringᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ Π-Ringᵉ))) = left-distributive-mul-add-Π-Ringᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ Π-Ringᵉ))) = right-distributive-mul-add-Π-Ringᵉ
```