# Dependent products of semirings

```agda
module ring-theory.dependent-products-semiringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.identity-typesᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.commutative-monoidsᵉ
open import group-theory.dependent-products-commutative-monoidsᵉ
open import group-theory.dependent-products-monoidsᵉ
open import group-theory.monoidsᵉ
open import group-theory.semigroupsᵉ

open import ring-theory.semiringsᵉ
```

</details>

## Idea

Givenᵉ aᵉ familyᵉ ofᵉ semiringsᵉ `Rᵉ i`ᵉ indexedᵉ byᵉ `iᵉ : I`,ᵉ theirᵉ dependentᵉ productᵉ
`Π(i:I),ᵉ Rᵉ i`ᵉ isᵉ againᵉ aᵉ semiring.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Iᵉ : UUᵉ l1ᵉ) (Rᵉ : Iᵉ → Semiringᵉ l2ᵉ)
  where

  additive-commutative-monoid-Π-Semiringᵉ : Commutative-Monoidᵉ (l1ᵉ ⊔ l2ᵉ)
  additive-commutative-monoid-Π-Semiringᵉ =
    Π-Commutative-Monoidᵉ Iᵉ
      ( λ iᵉ → additive-commutative-monoid-Semiringᵉ (Rᵉ iᵉ))

  semigroup-Π-Semiringᵉ : Semigroupᵉ (l1ᵉ ⊔ l2ᵉ)
  semigroup-Π-Semiringᵉ =
    semigroup-Commutative-Monoidᵉ additive-commutative-monoid-Π-Semiringᵉ

  multiplicative-monoid-Π-Semiringᵉ : Monoidᵉ (l1ᵉ ⊔ l2ᵉ)
  multiplicative-monoid-Π-Semiringᵉ =
    Π-Monoidᵉ Iᵉ (λ iᵉ → multiplicative-monoid-Semiringᵉ (Rᵉ iᵉ))

  set-Π-Semiringᵉ : Setᵉ (l1ᵉ ⊔ l2ᵉ)
  set-Π-Semiringᵉ =
    set-Commutative-Monoidᵉ additive-commutative-monoid-Π-Semiringᵉ

  type-Π-Semiringᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  type-Π-Semiringᵉ =
    type-Commutative-Monoidᵉ additive-commutative-monoid-Π-Semiringᵉ

  is-set-type-Π-Semiringᵉ : is-setᵉ type-Π-Semiringᵉ
  is-set-type-Π-Semiringᵉ =
    is-set-type-Commutative-Monoidᵉ additive-commutative-monoid-Π-Semiringᵉ

  add-Π-Semiringᵉ : type-Π-Semiringᵉ → type-Π-Semiringᵉ → type-Π-Semiringᵉ
  add-Π-Semiringᵉ =
    mul-Commutative-Monoidᵉ additive-commutative-monoid-Π-Semiringᵉ

  zero-Π-Semiringᵉ : type-Π-Semiringᵉ
  zero-Π-Semiringᵉ =
    unit-Commutative-Monoidᵉ additive-commutative-monoid-Π-Semiringᵉ

  associative-add-Π-Semiringᵉ :
    (xᵉ yᵉ zᵉ : type-Π-Semiringᵉ) →
    add-Π-Semiringᵉ (add-Π-Semiringᵉ xᵉ yᵉ) zᵉ ＝ᵉ
    add-Π-Semiringᵉ xᵉ (add-Π-Semiringᵉ yᵉ zᵉ)
  associative-add-Π-Semiringᵉ =
    associative-mul-Commutative-Monoidᵉ additive-commutative-monoid-Π-Semiringᵉ

  left-unit-law-add-Π-Semiringᵉ :
    (xᵉ : type-Π-Semiringᵉ) → add-Π-Semiringᵉ zero-Π-Semiringᵉ xᵉ ＝ᵉ xᵉ
  left-unit-law-add-Π-Semiringᵉ =
    left-unit-law-mul-Commutative-Monoidᵉ additive-commutative-monoid-Π-Semiringᵉ

  right-unit-law-add-Π-Semiringᵉ :
    (xᵉ : type-Π-Semiringᵉ) → add-Π-Semiringᵉ xᵉ zero-Π-Semiringᵉ ＝ᵉ xᵉ
  right-unit-law-add-Π-Semiringᵉ =
    right-unit-law-mul-Commutative-Monoidᵉ additive-commutative-monoid-Π-Semiringᵉ

  commutative-add-Π-Semiringᵉ :
    (xᵉ yᵉ : type-Π-Semiringᵉ) → add-Π-Semiringᵉ xᵉ yᵉ ＝ᵉ add-Π-Semiringᵉ yᵉ xᵉ
  commutative-add-Π-Semiringᵉ =
    commutative-mul-Commutative-Monoidᵉ additive-commutative-monoid-Π-Semiringᵉ

  mul-Π-Semiringᵉ : type-Π-Semiringᵉ → type-Π-Semiringᵉ → type-Π-Semiringᵉ
  mul-Π-Semiringᵉ = mul-Monoidᵉ multiplicative-monoid-Π-Semiringᵉ

  one-Π-Semiringᵉ : type-Π-Semiringᵉ
  one-Π-Semiringᵉ = unit-Monoidᵉ multiplicative-monoid-Π-Semiringᵉ

  associative-mul-Π-Semiringᵉ :
    (xᵉ yᵉ zᵉ : type-Π-Semiringᵉ) →
    mul-Π-Semiringᵉ (mul-Π-Semiringᵉ xᵉ yᵉ) zᵉ ＝ᵉ
    mul-Π-Semiringᵉ xᵉ (mul-Π-Semiringᵉ yᵉ zᵉ)
  associative-mul-Π-Semiringᵉ =
    associative-mul-Monoidᵉ multiplicative-monoid-Π-Semiringᵉ

  left-unit-law-mul-Π-Semiringᵉ :
    (xᵉ : type-Π-Semiringᵉ) → mul-Π-Semiringᵉ one-Π-Semiringᵉ xᵉ ＝ᵉ xᵉ
  left-unit-law-mul-Π-Semiringᵉ =
    left-unit-law-mul-Monoidᵉ multiplicative-monoid-Π-Semiringᵉ

  right-unit-law-mul-Π-Semiringᵉ :
    (xᵉ : type-Π-Semiringᵉ) → mul-Π-Semiringᵉ xᵉ one-Π-Semiringᵉ ＝ᵉ xᵉ
  right-unit-law-mul-Π-Semiringᵉ =
    right-unit-law-mul-Monoidᵉ multiplicative-monoid-Π-Semiringᵉ

  left-distributive-mul-add-Π-Semiringᵉ :
    (fᵉ gᵉ hᵉ : type-Π-Semiringᵉ) →
    mul-Π-Semiringᵉ fᵉ (add-Π-Semiringᵉ gᵉ hᵉ) ＝ᵉ
    add-Π-Semiringᵉ (mul-Π-Semiringᵉ fᵉ gᵉ) (mul-Π-Semiringᵉ fᵉ hᵉ)
  left-distributive-mul-add-Π-Semiringᵉ fᵉ gᵉ hᵉ =
    eq-htpyᵉ (λ iᵉ → left-distributive-mul-add-Semiringᵉ (Rᵉ iᵉ) (fᵉ iᵉ) (gᵉ iᵉ) (hᵉ iᵉ))

  right-distributive-mul-add-Π-Semiringᵉ :
    (fᵉ gᵉ hᵉ : type-Π-Semiringᵉ) →
    mul-Π-Semiringᵉ (add-Π-Semiringᵉ fᵉ gᵉ) hᵉ ＝ᵉ
    add-Π-Semiringᵉ (mul-Π-Semiringᵉ fᵉ hᵉ) (mul-Π-Semiringᵉ gᵉ hᵉ)
  right-distributive-mul-add-Π-Semiringᵉ fᵉ gᵉ hᵉ =
    eq-htpyᵉ (λ iᵉ → right-distributive-mul-add-Semiringᵉ (Rᵉ iᵉ) (fᵉ iᵉ) (gᵉ iᵉ) (hᵉ iᵉ))

  left-zero-law-mul-Π-Semiringᵉ :
    (fᵉ : type-Π-Semiringᵉ) →
    mul-Π-Semiringᵉ zero-Π-Semiringᵉ fᵉ ＝ᵉ zero-Π-Semiringᵉ
  left-zero-law-mul-Π-Semiringᵉ fᵉ =
    eq-htpyᵉ (λ iᵉ → left-zero-law-mul-Semiringᵉ (Rᵉ iᵉ) (fᵉ iᵉ))

  right-zero-law-mul-Π-Semiringᵉ :
    (fᵉ : type-Π-Semiringᵉ) →
    mul-Π-Semiringᵉ fᵉ zero-Π-Semiringᵉ ＝ᵉ zero-Π-Semiringᵉ
  right-zero-law-mul-Π-Semiringᵉ fᵉ =
    eq-htpyᵉ (λ iᵉ → right-zero-law-mul-Semiringᵉ (Rᵉ iᵉ) (fᵉ iᵉ))

  Π-Semiringᵉ : Semiringᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ Π-Semiringᵉ = additive-commutative-monoid-Π-Semiringᵉ
  pr1ᵉ (pr1ᵉ (pr1ᵉ (pr2ᵉ Π-Semiringᵉ))) = mul-Π-Semiringᵉ
  pr2ᵉ (pr1ᵉ (pr1ᵉ (pr2ᵉ Π-Semiringᵉ))) = associative-mul-Π-Semiringᵉ
  pr1ᵉ (pr1ᵉ (pr2ᵉ (pr1ᵉ (pr2ᵉ Π-Semiringᵉ)))) = one-Π-Semiringᵉ
  pr1ᵉ (pr2ᵉ (pr1ᵉ (pr2ᵉ (pr1ᵉ (pr2ᵉ Π-Semiringᵉ))))) = left-unit-law-mul-Π-Semiringᵉ
  pr2ᵉ (pr2ᵉ (pr1ᵉ (pr2ᵉ (pr1ᵉ (pr2ᵉ Π-Semiringᵉ))))) = right-unit-law-mul-Π-Semiringᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ (pr1ᵉ (pr2ᵉ Π-Semiringᵉ)))) = left-distributive-mul-add-Π-Semiringᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ (pr1ᵉ (pr2ᵉ Π-Semiringᵉ)))) = right-distributive-mul-add-Π-Semiringᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ Π-Semiringᵉ)) = left-zero-law-mul-Π-Semiringᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ Π-Semiringᵉ)) = right-zero-law-mul-Π-Semiringᵉ
```