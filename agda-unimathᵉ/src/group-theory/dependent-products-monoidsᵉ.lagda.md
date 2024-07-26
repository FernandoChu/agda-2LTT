# Dependent products of monoids

```agda
module group-theory.dependent-products-monoidsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.identity-typesᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.dependent-products-semigroupsᵉ
open import group-theory.monoidsᵉ
open import group-theory.semigroupsᵉ
```

</details>

## Idea

Givenᵉ aᵉ familyᵉ ofᵉ monoidsᵉ `Mᵢ`ᵉ indexedᵉ byᵉ `iᵉ : I`,ᵉ theᵉ dependentᵉ productᵉ
`Π(iᵉ : I),ᵉ Mᵢ`ᵉ isᵉ aᵉ monoidᵉ consistingᵉ ofᵉ dependentᵉ functionsᵉ takingᵉ `iᵉ : I`ᵉ to
anᵉ elementᵉ ofᵉ theᵉ underlyingᵉ typeᵉ ofᵉ `Mᵢ`.ᵉ Theᵉ multiplicativeᵉ operationᵉ andᵉ theᵉ
unitᵉ areᵉ givenᵉ pointwise.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Iᵉ : UUᵉ l1ᵉ) (Mᵉ : Iᵉ → Monoidᵉ l2ᵉ)
  where

  semigroup-Π-Monoidᵉ : Semigroupᵉ (l1ᵉ ⊔ l2ᵉ)
  semigroup-Π-Monoidᵉ = Π-Semigroupᵉ Iᵉ (λ iᵉ → semigroup-Monoidᵉ (Mᵉ iᵉ))

  set-Π-Monoidᵉ : Setᵉ (l1ᵉ ⊔ l2ᵉ)
  set-Π-Monoidᵉ = set-Semigroupᵉ semigroup-Π-Monoidᵉ

  type-Π-Monoidᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  type-Π-Monoidᵉ = type-Semigroupᵉ semigroup-Π-Monoidᵉ

  mul-Π-Monoidᵉ : (fᵉ gᵉ : type-Π-Monoidᵉ) → type-Π-Monoidᵉ
  mul-Π-Monoidᵉ = mul-Semigroupᵉ semigroup-Π-Monoidᵉ

  associative-mul-Π-Monoidᵉ :
    (fᵉ gᵉ hᵉ : type-Π-Monoidᵉ) →
    mul-Π-Monoidᵉ (mul-Π-Monoidᵉ fᵉ gᵉ) hᵉ ＝ᵉ
    mul-Π-Monoidᵉ fᵉ (mul-Π-Monoidᵉ gᵉ hᵉ)
  associative-mul-Π-Monoidᵉ =
    associative-mul-Semigroupᵉ semigroup-Π-Monoidᵉ

  unit-Π-Monoidᵉ : type-Π-Monoidᵉ
  unit-Π-Monoidᵉ iᵉ = unit-Monoidᵉ (Mᵉ iᵉ)

  left-unit-law-mul-Π-Monoidᵉ :
    (fᵉ : type-Π-Monoidᵉ) → mul-Π-Monoidᵉ unit-Π-Monoidᵉ fᵉ ＝ᵉ fᵉ
  left-unit-law-mul-Π-Monoidᵉ fᵉ =
    eq-htpyᵉ (λ iᵉ → left-unit-law-mul-Monoidᵉ (Mᵉ iᵉ) (fᵉ iᵉ))

  right-unit-law-mul-Π-Monoidᵉ :
    (fᵉ : type-Π-Monoidᵉ) → mul-Π-Monoidᵉ fᵉ unit-Π-Monoidᵉ ＝ᵉ fᵉ
  right-unit-law-mul-Π-Monoidᵉ fᵉ =
    eq-htpyᵉ (λ iᵉ → right-unit-law-mul-Monoidᵉ (Mᵉ iᵉ) (fᵉ iᵉ))

  is-unital-Π-Monoidᵉ : is-unital-Semigroupᵉ semigroup-Π-Monoidᵉ
  pr1ᵉ is-unital-Π-Monoidᵉ = unit-Π-Monoidᵉ
  pr1ᵉ (pr2ᵉ is-unital-Π-Monoidᵉ) = left-unit-law-mul-Π-Monoidᵉ
  pr2ᵉ (pr2ᵉ is-unital-Π-Monoidᵉ) = right-unit-law-mul-Π-Monoidᵉ

  Π-Monoidᵉ : Monoidᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ Π-Monoidᵉ = semigroup-Π-Monoidᵉ
  pr2ᵉ Π-Monoidᵉ = is-unital-Π-Monoidᵉ
```