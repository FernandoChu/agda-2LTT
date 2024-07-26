# Dependent products of commutative monoids

```agda
module group-theory.dependent-products-commutative-monoidsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.identity-typesᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.commutative-monoidsᵉ
open import group-theory.dependent-products-monoidsᵉ
open import group-theory.monoidsᵉ
```

</details>

## Idea

Givenᵉ aᵉ familyᵉ ofᵉ commutativeᵉ monoidsᵉ `Mᵢ`ᵉ indexedᵉ byᵉ `iᵉ : I`,ᵉ theᵉ dependentᵉ
productᵉ `Π(iᵉ : I),ᵉ Mᵢ`ᵉ isᵉ aᵉ commutativeᵉ monoidᵉ consistingᵉ ofᵉ dependentᵉ functionsᵉ
takingᵉ `iᵉ : I`ᵉ to anᵉ elementᵉ ofᵉ theᵉ underlyingᵉ typeᵉ ofᵉ `Mᵢ`.ᵉ Theᵉ multiplicativeᵉ
operationᵉ andᵉ theᵉ unitᵉ areᵉ givenᵉ pointwise.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Iᵉ : UUᵉ l1ᵉ) (Mᵉ : Iᵉ → Commutative-Monoidᵉ l2ᵉ)
  where

  monoid-Π-Commutative-Monoidᵉ : Monoidᵉ (l1ᵉ ⊔ l2ᵉ)
  monoid-Π-Commutative-Monoidᵉ =
    Π-Monoidᵉ Iᵉ (λ iᵉ → monoid-Commutative-Monoidᵉ (Mᵉ iᵉ))

  set-Π-Commutative-Monoidᵉ : Setᵉ (l1ᵉ ⊔ l2ᵉ)
  set-Π-Commutative-Monoidᵉ =
    set-Π-Monoidᵉ Iᵉ (λ iᵉ → monoid-Commutative-Monoidᵉ (Mᵉ iᵉ))

  type-Π-Commutative-Monoidᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  type-Π-Commutative-Monoidᵉ =
    type-Π-Monoidᵉ Iᵉ (λ iᵉ → monoid-Commutative-Monoidᵉ (Mᵉ iᵉ))

  unit-Π-Commutative-Monoidᵉ : type-Π-Commutative-Monoidᵉ
  unit-Π-Commutative-Monoidᵉ =
    unit-Π-Monoidᵉ Iᵉ (λ iᵉ → monoid-Commutative-Monoidᵉ (Mᵉ iᵉ))

  mul-Π-Commutative-Monoidᵉ :
    (fᵉ gᵉ : type-Π-Commutative-Monoidᵉ) → type-Π-Commutative-Monoidᵉ
  mul-Π-Commutative-Monoidᵉ =
    mul-Π-Monoidᵉ Iᵉ (λ iᵉ → monoid-Commutative-Monoidᵉ (Mᵉ iᵉ))

  associative-mul-Π-Commutative-Monoidᵉ :
    (fᵉ gᵉ hᵉ : type-Π-Commutative-Monoidᵉ) →
    mul-Π-Commutative-Monoidᵉ (mul-Π-Commutative-Monoidᵉ fᵉ gᵉ) hᵉ ＝ᵉ
    mul-Π-Commutative-Monoidᵉ fᵉ (mul-Π-Commutative-Monoidᵉ gᵉ hᵉ)
  associative-mul-Π-Commutative-Monoidᵉ =
    associative-mul-Π-Monoidᵉ Iᵉ (λ iᵉ → monoid-Commutative-Monoidᵉ (Mᵉ iᵉ))

  left-unit-law-mul-Π-Commutative-Monoidᵉ :
    (fᵉ : type-Π-Commutative-Monoidᵉ) →
    mul-Π-Commutative-Monoidᵉ unit-Π-Commutative-Monoidᵉ fᵉ ＝ᵉ fᵉ
  left-unit-law-mul-Π-Commutative-Monoidᵉ =
    left-unit-law-mul-Π-Monoidᵉ Iᵉ (λ iᵉ → monoid-Commutative-Monoidᵉ (Mᵉ iᵉ))

  right-unit-law-mul-Π-Commutative-Monoidᵉ :
    (fᵉ : type-Π-Commutative-Monoidᵉ) →
    mul-Π-Commutative-Monoidᵉ fᵉ unit-Π-Commutative-Monoidᵉ ＝ᵉ fᵉ
  right-unit-law-mul-Π-Commutative-Monoidᵉ =
    right-unit-law-mul-Π-Monoidᵉ Iᵉ (λ iᵉ → monoid-Commutative-Monoidᵉ (Mᵉ iᵉ))

  commutative-mul-Π-Commutative-Monoidᵉ :
    (fᵉ gᵉ : type-Π-Commutative-Monoidᵉ) →
    mul-Π-Commutative-Monoidᵉ fᵉ gᵉ ＝ᵉ mul-Π-Commutative-Monoidᵉ gᵉ fᵉ
  commutative-mul-Π-Commutative-Monoidᵉ fᵉ gᵉ =
    eq-htpyᵉ (λ iᵉ → commutative-mul-Commutative-Monoidᵉ (Mᵉ iᵉ) (fᵉ iᵉ) (gᵉ iᵉ))

  Π-Commutative-Monoidᵉ : Commutative-Monoidᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ Π-Commutative-Monoidᵉ = monoid-Π-Commutative-Monoidᵉ
  pr2ᵉ Π-Commutative-Monoidᵉ = commutative-mul-Π-Commutative-Monoidᵉ
```