# Dependent products of groups

```agda
module group-theory.dependent-products-groupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.identity-typesᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.dependent-products-semigroupsᵉ
open import group-theory.groupsᵉ
open import group-theory.monoidsᵉ
open import group-theory.semigroupsᵉ
```

</details>

## Idea

Givenᵉ aᵉ familyᵉ ofᵉ groupsᵉ `Gᵢ`ᵉ indexedᵉ byᵉ `iᵉ : I`,ᵉ theᵉ dependentᵉ productᵉ
`Π(iᵉ : I),ᵉ Gᵢ`ᵉ isᵉ aᵉ groupᵉ consistingᵉ ofᵉ dependentᵉ functionsᵉ takingᵉ `iᵉ : I`ᵉ to anᵉ
elementᵉ ofᵉ theᵉ underlyingᵉ typeᵉ ofᵉ `Gᵢ`.ᵉ Theᵉ multiplicativeᵉ operationᵉ andᵉ theᵉ
unitᵉ areᵉ givenᵉ pointwise.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Iᵉ : UUᵉ l1ᵉ) (Gᵉ : Iᵉ → Groupᵉ l2ᵉ)
  where

  semigroup-Π-Groupᵉ : Semigroupᵉ (l1ᵉ ⊔ l2ᵉ)
  semigroup-Π-Groupᵉ = Π-Semigroupᵉ Iᵉ (λ iᵉ → semigroup-Groupᵉ (Gᵉ iᵉ))

  set-Π-Groupᵉ : Setᵉ (l1ᵉ ⊔ l2ᵉ)
  set-Π-Groupᵉ = set-Semigroupᵉ semigroup-Π-Groupᵉ

  type-Π-Groupᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  type-Π-Groupᵉ = type-Semigroupᵉ semigroup-Π-Groupᵉ

  mul-Π-Groupᵉ : (fᵉ gᵉ : type-Π-Groupᵉ) → type-Π-Groupᵉ
  mul-Π-Groupᵉ = mul-Semigroupᵉ semigroup-Π-Groupᵉ

  associative-mul-Π-Groupᵉ :
    (fᵉ gᵉ hᵉ : type-Π-Groupᵉ) →
    mul-Π-Groupᵉ (mul-Π-Groupᵉ fᵉ gᵉ) hᵉ ＝ᵉ
    mul-Π-Groupᵉ fᵉ (mul-Π-Groupᵉ gᵉ hᵉ)
  associative-mul-Π-Groupᵉ =
    associative-mul-Semigroupᵉ semigroup-Π-Groupᵉ

  unit-Π-Groupᵉ : type-Π-Groupᵉ
  unit-Π-Groupᵉ iᵉ = unit-Groupᵉ (Gᵉ iᵉ)

  left-unit-law-mul-Π-Groupᵉ :
    (fᵉ : type-Π-Groupᵉ) → mul-Π-Groupᵉ unit-Π-Groupᵉ fᵉ ＝ᵉ fᵉ
  left-unit-law-mul-Π-Groupᵉ fᵉ =
    eq-htpyᵉ (λ iᵉ → left-unit-law-mul-Groupᵉ (Gᵉ iᵉ) (fᵉ iᵉ))

  right-unit-law-mul-Π-Groupᵉ :
    (fᵉ : type-Π-Groupᵉ) → mul-Π-Groupᵉ fᵉ unit-Π-Groupᵉ ＝ᵉ fᵉ
  right-unit-law-mul-Π-Groupᵉ fᵉ =
    eq-htpyᵉ (λ iᵉ → right-unit-law-mul-Groupᵉ (Gᵉ iᵉ) (fᵉ iᵉ))

  is-unital-Π-Groupᵉ : is-unital-Semigroupᵉ semigroup-Π-Groupᵉ
  pr1ᵉ is-unital-Π-Groupᵉ = unit-Π-Groupᵉ
  pr1ᵉ (pr2ᵉ is-unital-Π-Groupᵉ) = left-unit-law-mul-Π-Groupᵉ
  pr2ᵉ (pr2ᵉ is-unital-Π-Groupᵉ) = right-unit-law-mul-Π-Groupᵉ

  monoid-Π-Groupᵉ : Monoidᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ monoid-Π-Groupᵉ = semigroup-Π-Groupᵉ
  pr2ᵉ monoid-Π-Groupᵉ = is-unital-Π-Groupᵉ

  inv-Π-Groupᵉ : type-Π-Groupᵉ → type-Π-Groupᵉ
  inv-Π-Groupᵉ fᵉ xᵉ = inv-Groupᵉ (Gᵉ xᵉ) (fᵉ xᵉ)

  left-inverse-law-mul-Π-Groupᵉ :
    (fᵉ : type-Π-Groupᵉ) →
    mul-Π-Groupᵉ (inv-Π-Groupᵉ fᵉ) fᵉ ＝ᵉ unit-Π-Groupᵉ
  left-inverse-law-mul-Π-Groupᵉ fᵉ =
    eq-htpyᵉ (λ xᵉ → left-inverse-law-mul-Groupᵉ (Gᵉ xᵉ) (fᵉ xᵉ))

  right-inverse-law-mul-Π-Groupᵉ :
    (fᵉ : type-Π-Groupᵉ) →
    mul-Π-Groupᵉ fᵉ (inv-Π-Groupᵉ fᵉ) ＝ᵉ unit-Π-Groupᵉ
  right-inverse-law-mul-Π-Groupᵉ fᵉ =
    eq-htpyᵉ (λ xᵉ → right-inverse-law-mul-Groupᵉ (Gᵉ xᵉ) (fᵉ xᵉ))

  is-group-Π-Groupᵉ : is-group-Semigroupᵉ semigroup-Π-Groupᵉ
  pr1ᵉ is-group-Π-Groupᵉ = is-unital-Π-Groupᵉ
  pr1ᵉ (pr2ᵉ is-group-Π-Groupᵉ) = inv-Π-Groupᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ is-group-Π-Groupᵉ)) = left-inverse-law-mul-Π-Groupᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ is-group-Π-Groupᵉ)) = right-inverse-law-mul-Π-Groupᵉ

  Π-Groupᵉ : Groupᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ Π-Groupᵉ = semigroup-Π-Groupᵉ
  pr2ᵉ Π-Groupᵉ = is-group-Π-Groupᵉ
```