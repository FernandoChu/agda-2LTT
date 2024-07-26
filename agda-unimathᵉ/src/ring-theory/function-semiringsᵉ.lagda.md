# Function semirings

```agda
module ring-theory.function-semiringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.commutative-monoidsᵉ
open import group-theory.monoidsᵉ

open import ring-theory.dependent-products-semiringsᵉ
open import ring-theory.semiringsᵉ
```

</details>

## Idea

Givenᵉ aᵉ semiringᵉ `R`ᵉ andᵉ aᵉ typeᵉ `X`,ᵉ theᵉ functionᵉ semiringᵉ `R^X`ᵉ consistsᵉ ofᵉ
functionsᵉ fromᵉ `X`ᵉ intoᵉ theᵉ underlyingᵉ typeᵉ ofᵉ `R`.ᵉ Theᵉ semiringᵉ operationsᵉ areᵉ
definedᵉ pointwiseᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Rᵉ : Semiringᵉ l1ᵉ) (Xᵉ : UUᵉ l2ᵉ)
  where

  additive-commutative-monoid-function-Semiringᵉ : Commutative-Monoidᵉ (l1ᵉ ⊔ l2ᵉ)
  additive-commutative-monoid-function-Semiringᵉ =
    additive-commutative-monoid-Π-Semiringᵉ Xᵉ (λ _ → Rᵉ)

  multiplicative-monoid-function-Semiringᵉ : Monoidᵉ (l1ᵉ ⊔ l2ᵉ)
  multiplicative-monoid-function-Semiringᵉ =
    multiplicative-monoid-Π-Semiringᵉ Xᵉ (λ _ → Rᵉ)

  set-function-Semiringᵉ : Setᵉ (l1ᵉ ⊔ l2ᵉ)
  set-function-Semiringᵉ = set-Π-Semiringᵉ Xᵉ (λ _ → Rᵉ)

  type-function-Semiringᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  type-function-Semiringᵉ = type-Π-Semiringᵉ Xᵉ (λ _ → Rᵉ)

  is-set-type-function-Semiringᵉ : is-setᵉ type-function-Semiringᵉ
  is-set-type-function-Semiringᵉ =
    is-set-type-Π-Semiringᵉ Xᵉ (λ _ → Rᵉ)

  add-function-Semiringᵉ :
    type-function-Semiringᵉ → type-function-Semiringᵉ → type-function-Semiringᵉ
  add-function-Semiringᵉ = add-Π-Semiringᵉ Xᵉ (λ _ → Rᵉ)

  zero-function-Semiringᵉ : type-function-Semiringᵉ
  zero-function-Semiringᵉ = zero-Π-Semiringᵉ Xᵉ (λ _ → Rᵉ)

  associative-add-function-Semiringᵉ :
    (xᵉ yᵉ zᵉ : type-function-Semiringᵉ) →
    add-function-Semiringᵉ (add-function-Semiringᵉ xᵉ yᵉ) zᵉ ＝ᵉ
    add-function-Semiringᵉ xᵉ (add-function-Semiringᵉ yᵉ zᵉ)
  associative-add-function-Semiringᵉ =
    associative-add-Π-Semiringᵉ Xᵉ (λ _ → Rᵉ)

  left-unit-law-add-function-Semiringᵉ :
    (xᵉ : type-function-Semiringᵉ) →
    add-function-Semiringᵉ zero-function-Semiringᵉ xᵉ ＝ᵉ xᵉ
  left-unit-law-add-function-Semiringᵉ =
    left-unit-law-add-Π-Semiringᵉ Xᵉ (λ _ → Rᵉ)

  right-unit-law-add-function-Semiringᵉ :
    (xᵉ : type-function-Semiringᵉ) →
    add-function-Semiringᵉ xᵉ zero-function-Semiringᵉ ＝ᵉ xᵉ
  right-unit-law-add-function-Semiringᵉ =
    right-unit-law-add-Π-Semiringᵉ Xᵉ (λ _ → Rᵉ)

  commutative-add-function-Semiringᵉ :
    (xᵉ yᵉ : type-function-Semiringᵉ) →
    add-function-Semiringᵉ xᵉ yᵉ ＝ᵉ add-function-Semiringᵉ yᵉ xᵉ
  commutative-add-function-Semiringᵉ =
    commutative-add-Π-Semiringᵉ Xᵉ (λ _ → Rᵉ)

  mul-function-Semiringᵉ :
    type-function-Semiringᵉ → type-function-Semiringᵉ → type-function-Semiringᵉ
  mul-function-Semiringᵉ =
    mul-Π-Semiringᵉ Xᵉ (λ _ → Rᵉ)

  one-function-Semiringᵉ : type-function-Semiringᵉ
  one-function-Semiringᵉ = one-Π-Semiringᵉ Xᵉ (λ _ → Rᵉ)

  associative-mul-function-Semiringᵉ :
    (xᵉ yᵉ zᵉ : type-function-Semiringᵉ) →
    mul-function-Semiringᵉ (mul-function-Semiringᵉ xᵉ yᵉ) zᵉ ＝ᵉ
    mul-function-Semiringᵉ xᵉ (mul-function-Semiringᵉ yᵉ zᵉ)
  associative-mul-function-Semiringᵉ =
    associative-mul-Π-Semiringᵉ Xᵉ (λ _ → Rᵉ)

  left-unit-law-mul-function-Semiringᵉ :
    (xᵉ : type-function-Semiringᵉ) →
    mul-function-Semiringᵉ one-function-Semiringᵉ xᵉ ＝ᵉ xᵉ
  left-unit-law-mul-function-Semiringᵉ =
    left-unit-law-mul-Π-Semiringᵉ Xᵉ (λ _ → Rᵉ)

  right-unit-law-mul-function-Semiringᵉ :
    (xᵉ : type-function-Semiringᵉ) →
    mul-function-Semiringᵉ xᵉ one-function-Semiringᵉ ＝ᵉ xᵉ
  right-unit-law-mul-function-Semiringᵉ =
    right-unit-law-mul-Π-Semiringᵉ Xᵉ (λ _ → Rᵉ)

  left-distributive-mul-add-function-Semiringᵉ :
    (fᵉ gᵉ hᵉ : type-function-Semiringᵉ) →
    mul-function-Semiringᵉ fᵉ (add-function-Semiringᵉ gᵉ hᵉ) ＝ᵉ
    add-function-Semiringᵉ
      ( mul-function-Semiringᵉ fᵉ gᵉ)
      ( mul-function-Semiringᵉ fᵉ hᵉ)
  left-distributive-mul-add-function-Semiringᵉ =
    left-distributive-mul-add-Π-Semiringᵉ Xᵉ (λ _ → Rᵉ)

  right-distributive-mul-add-function-Semiringᵉ :
    (fᵉ gᵉ hᵉ : type-function-Semiringᵉ) →
    mul-function-Semiringᵉ (add-function-Semiringᵉ fᵉ gᵉ) hᵉ ＝ᵉ
    add-function-Semiringᵉ
      ( mul-function-Semiringᵉ fᵉ hᵉ)
      ( mul-function-Semiringᵉ gᵉ hᵉ)
  right-distributive-mul-add-function-Semiringᵉ =
    right-distributive-mul-add-Π-Semiringᵉ Xᵉ (λ _ → Rᵉ)

  left-zero-law-mul-function-Semiringᵉ :
    (fᵉ : type-function-Semiringᵉ) →
    mul-function-Semiringᵉ zero-function-Semiringᵉ fᵉ ＝ᵉ zero-function-Semiringᵉ
  left-zero-law-mul-function-Semiringᵉ =
    left-zero-law-mul-Π-Semiringᵉ Xᵉ (λ _ → Rᵉ)

  right-zero-law-mul-function-Semiringᵉ :
    (fᵉ : type-function-Semiringᵉ) →
    mul-function-Semiringᵉ fᵉ zero-function-Semiringᵉ ＝ᵉ zero-function-Semiringᵉ
  right-zero-law-mul-function-Semiringᵉ =
    right-zero-law-mul-Π-Semiringᵉ Xᵉ (λ _ → Rᵉ)

  function-Semiringᵉ : Semiringᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ function-Semiringᵉ = additive-commutative-monoid-function-Semiringᵉ
  pr1ᵉ (pr1ᵉ (pr1ᵉ (pr2ᵉ function-Semiringᵉ))) = mul-function-Semiringᵉ
  pr2ᵉ (pr1ᵉ (pr1ᵉ (pr2ᵉ function-Semiringᵉ))) = associative-mul-function-Semiringᵉ
  pr1ᵉ (pr1ᵉ (pr2ᵉ (pr1ᵉ (pr2ᵉ function-Semiringᵉ)))) = one-function-Semiringᵉ
  pr1ᵉ (pr2ᵉ (pr1ᵉ (pr2ᵉ (pr1ᵉ (pr2ᵉ function-Semiringᵉ))))) =
    left-unit-law-mul-function-Semiringᵉ
  pr2ᵉ (pr2ᵉ (pr1ᵉ (pr2ᵉ (pr1ᵉ (pr2ᵉ function-Semiringᵉ))))) =
    right-unit-law-mul-function-Semiringᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ (pr1ᵉ (pr2ᵉ function-Semiringᵉ)))) =
    left-distributive-mul-add-function-Semiringᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ (pr1ᵉ (pr2ᵉ function-Semiringᵉ)))) =
    right-distributive-mul-add-function-Semiringᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ function-Semiringᵉ)) = left-zero-law-mul-function-Semiringᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ function-Semiringᵉ)) = right-zero-law-mul-function-Semiringᵉ
```