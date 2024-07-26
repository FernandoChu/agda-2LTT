# Dependent products of abelian groups

```agda
module group-theory.dependent-products-abelian-groupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.identity-typesᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.abelian-groupsᵉ
open import group-theory.dependent-products-groupsᵉ
open import group-theory.groupsᵉ
open import group-theory.monoidsᵉ
open import group-theory.semigroupsᵉ
```

</details>

## Idea

Givenᵉ aᵉ familyᵉ ofᵉ abelianᵉ groupsᵉ `Aᵢ`ᵉ indexedᵉ byᵉ `iᵉ : I`,ᵉ theᵉ dependentᵉ productᵉ
`Π(iᵉ : I),ᵉ Aᵢ`ᵉ isᵉ anᵉ abelianᵉ groupᵉ consistingᵉ ofᵉ dependentᵉ functionsᵉ takingᵉ
`iᵉ : I`ᵉ to anᵉ elementᵉ ofᵉ theᵉ underlyingᵉ typeᵉ ofᵉ `Aᵢ`.ᵉ Theᵉ multiplicativeᵉ
operationᵉ andᵉ theᵉ unitᵉ areᵉ givenᵉ pointwise.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Iᵉ : UUᵉ l1ᵉ) (Aᵉ : Iᵉ → Abᵉ l2ᵉ)
  where

  group-Π-Abᵉ : Groupᵉ (l1ᵉ ⊔ l2ᵉ)
  group-Π-Abᵉ = Π-Groupᵉ Iᵉ (λ iᵉ → group-Abᵉ (Aᵉ iᵉ))

  semigroup-Π-Abᵉ : Semigroupᵉ (l1ᵉ ⊔ l2ᵉ)
  semigroup-Π-Abᵉ = semigroup-Groupᵉ group-Π-Abᵉ

  set-Π-Abᵉ : Setᵉ (l1ᵉ ⊔ l2ᵉ)
  set-Π-Abᵉ = set-Groupᵉ group-Π-Abᵉ

  type-Π-Abᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  type-Π-Abᵉ = type-Groupᵉ group-Π-Abᵉ

  add-Π-Abᵉ : (fᵉ gᵉ : type-Π-Abᵉ) → type-Π-Abᵉ
  add-Π-Abᵉ = mul-Semigroupᵉ semigroup-Π-Abᵉ

  associative-add-Π-Abᵉ :
    (fᵉ gᵉ hᵉ : type-Π-Abᵉ) →
    add-Π-Abᵉ (add-Π-Abᵉ fᵉ gᵉ) hᵉ ＝ᵉ add-Π-Abᵉ fᵉ (add-Π-Abᵉ gᵉ hᵉ)
  associative-add-Π-Abᵉ = associative-mul-Groupᵉ group-Π-Abᵉ

  zero-Π-Abᵉ : type-Π-Abᵉ
  zero-Π-Abᵉ = unit-Groupᵉ group-Π-Abᵉ

  left-unit-law-add-Π-Abᵉ : (fᵉ : type-Π-Abᵉ) → add-Π-Abᵉ zero-Π-Abᵉ fᵉ ＝ᵉ fᵉ
  left-unit-law-add-Π-Abᵉ = left-unit-law-mul-Groupᵉ group-Π-Abᵉ

  right-unit-law-add-Π-Abᵉ : (fᵉ : type-Π-Abᵉ) → add-Π-Abᵉ fᵉ zero-Π-Abᵉ ＝ᵉ fᵉ
  right-unit-law-add-Π-Abᵉ = right-unit-law-mul-Groupᵉ group-Π-Abᵉ

  is-unital-Π-Abᵉ : is-unital-Semigroupᵉ semigroup-Π-Abᵉ
  is-unital-Π-Abᵉ = is-unital-Groupᵉ group-Π-Abᵉ

  monoid-Π-Abᵉ : Monoidᵉ (l1ᵉ ⊔ l2ᵉ)
  monoid-Π-Abᵉ = monoid-Groupᵉ group-Π-Abᵉ

  neg-Π-Abᵉ : type-Π-Abᵉ → type-Π-Abᵉ
  neg-Π-Abᵉ = inv-Groupᵉ group-Π-Abᵉ

  left-inverse-law-add-Π-Abᵉ :
    (fᵉ : type-Π-Abᵉ) → add-Π-Abᵉ (neg-Π-Abᵉ fᵉ) fᵉ ＝ᵉ zero-Π-Abᵉ
  left-inverse-law-add-Π-Abᵉ = left-inverse-law-mul-Groupᵉ group-Π-Abᵉ

  right-inverse-law-add-Π-Abᵉ :
    (fᵉ : type-Π-Abᵉ) → add-Π-Abᵉ fᵉ (neg-Π-Abᵉ fᵉ) ＝ᵉ zero-Π-Abᵉ
  right-inverse-law-add-Π-Abᵉ = right-inverse-law-mul-Groupᵉ group-Π-Abᵉ

  is-group-Π-Abᵉ : is-group-Semigroupᵉ semigroup-Π-Abᵉ
  is-group-Π-Abᵉ = is-group-Groupᵉ group-Π-Abᵉ

  commutative-add-Π-Abᵉ :
    (fᵉ gᵉ : type-Π-Abᵉ) → add-Π-Abᵉ fᵉ gᵉ ＝ᵉ add-Π-Abᵉ gᵉ fᵉ
  commutative-add-Π-Abᵉ fᵉ gᵉ =
    eq-htpyᵉ (λ iᵉ → commutative-add-Abᵉ (Aᵉ iᵉ) (fᵉ iᵉ) (gᵉ iᵉ))

  Π-Abᵉ : Abᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ Π-Abᵉ = group-Π-Abᵉ
  pr2ᵉ Π-Abᵉ = commutative-add-Π-Abᵉ
```