# Function rings

```agda
module ring-theory.function-ringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.identity-typesᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.abelian-groupsᵉ
open import group-theory.monoidsᵉ

open import ring-theory.dependent-products-ringsᵉ
open import ring-theory.ringsᵉ
```

</details>

## Idea

Givenᵉ aᵉ ringᵉ `R`ᵉ andᵉ aᵉ typeᵉ `X`,ᵉ theᵉ exponentᵉ ringᵉ `R^X`ᵉ consistsᵉ ofᵉ functionsᵉ
fromᵉ `X`ᵉ intoᵉ theᵉ underlyingᵉ typeᵉ ofᵉ `R`.ᵉ Theᵉ operationsᵉ onᵉ `R^X`ᵉ areᵉ definedᵉ
pointwise.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ) (Xᵉ : UUᵉ l2ᵉ)
  where

  function-Ringᵉ : Ringᵉ (l1ᵉ ⊔ l2ᵉ)
  function-Ringᵉ = Π-Ringᵉ Xᵉ (λ _ → Rᵉ)

  ab-function-Ringᵉ : Abᵉ (l1ᵉ ⊔ l2ᵉ)
  ab-function-Ringᵉ = ab-Π-Ringᵉ Xᵉ (λ _ → Rᵉ)

  multiplicative-monoid-function-Ringᵉ : Monoidᵉ (l1ᵉ ⊔ l2ᵉ)
  multiplicative-monoid-function-Ringᵉ =
    multiplicative-monoid-Π-Ringᵉ Xᵉ (λ _ → Rᵉ)

  set-function-Ringᵉ : Setᵉ (l1ᵉ ⊔ l2ᵉ)
  set-function-Ringᵉ = set-Π-Ringᵉ Xᵉ (λ _ → Rᵉ)

  type-function-Ringᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  type-function-Ringᵉ = type-Π-Ringᵉ Xᵉ (λ _ → Rᵉ)

  zero-function-Ringᵉ : type-function-Ringᵉ
  zero-function-Ringᵉ = zero-Π-Ringᵉ Xᵉ (λ _ → Rᵉ)

  one-function-Ringᵉ : type-function-Ringᵉ
  one-function-Ringᵉ = one-Π-Ringᵉ Xᵉ (λ _ → Rᵉ)

  add-function-Ringᵉ : (fᵉ gᵉ : type-function-Ringᵉ) → type-function-Ringᵉ
  add-function-Ringᵉ = add-Π-Ringᵉ Xᵉ (λ _ → Rᵉ)

  neg-function-Ringᵉ : type-function-Ringᵉ → type-function-Ringᵉ
  neg-function-Ringᵉ = neg-Π-Ringᵉ Xᵉ (λ _ → Rᵉ)

  mul-function-Ringᵉ : (fᵉ gᵉ : type-function-Ringᵉ) → type-function-Ringᵉ
  mul-function-Ringᵉ = mul-Π-Ringᵉ Xᵉ (λ _ → Rᵉ)

  associative-add-function-Ringᵉ :
    (fᵉ gᵉ hᵉ : type-function-Ringᵉ) →
    add-function-Ringᵉ (add-function-Ringᵉ fᵉ gᵉ) hᵉ ＝ᵉ
    add-function-Ringᵉ fᵉ (add-function-Ringᵉ gᵉ hᵉ)
  associative-add-function-Ringᵉ = associative-add-Π-Ringᵉ Xᵉ (λ _ → Rᵉ)

  commutative-add-function-Ringᵉ :
    (fᵉ gᵉ : type-function-Ringᵉ) →
    add-function-Ringᵉ fᵉ gᵉ ＝ᵉ add-function-Ringᵉ gᵉ fᵉ
  commutative-add-function-Ringᵉ = commutative-add-Π-Ringᵉ Xᵉ (λ _ → Rᵉ)

  left-unit-law-add-function-Ringᵉ :
    (fᵉ : type-function-Ringᵉ) →
    add-function-Ringᵉ zero-function-Ringᵉ fᵉ ＝ᵉ fᵉ
  left-unit-law-add-function-Ringᵉ =
    left-unit-law-add-Π-Ringᵉ Xᵉ (λ _ → Rᵉ)

  right-unit-law-add-function-Ringᵉ :
    (fᵉ : type-function-Ringᵉ) →
    add-function-Ringᵉ fᵉ zero-function-Ringᵉ ＝ᵉ fᵉ
  right-unit-law-add-function-Ringᵉ =
    right-unit-law-add-Π-Ringᵉ Xᵉ (λ _ → Rᵉ)

  left-inverse-law-add-function-Ringᵉ :
    (fᵉ : type-function-Ringᵉ) →
    add-function-Ringᵉ (neg-function-Ringᵉ fᵉ) fᵉ ＝ᵉ zero-function-Ringᵉ
  left-inverse-law-add-function-Ringᵉ =
    left-inverse-law-add-Π-Ringᵉ Xᵉ (λ _ → Rᵉ)

  right-inverse-law-add-function-Ringᵉ :
    (fᵉ : type-function-Ringᵉ) →
    add-function-Ringᵉ fᵉ (neg-function-Ringᵉ fᵉ) ＝ᵉ zero-function-Ringᵉ
  right-inverse-law-add-function-Ringᵉ =
    right-inverse-law-add-Π-Ringᵉ Xᵉ (λ _ → Rᵉ)

  associative-mul-function-Ringᵉ :
    (fᵉ gᵉ hᵉ : type-function-Ringᵉ) →
    mul-function-Ringᵉ (mul-function-Ringᵉ fᵉ gᵉ) hᵉ ＝ᵉ
    mul-function-Ringᵉ fᵉ (mul-function-Ringᵉ gᵉ hᵉ)
  associative-mul-function-Ringᵉ =
    associative-mul-Π-Ringᵉ Xᵉ (λ _ → Rᵉ)

  left-unit-law-mul-function-Ringᵉ :
    (fᵉ : type-function-Ringᵉ) →
    mul-function-Ringᵉ one-function-Ringᵉ fᵉ ＝ᵉ fᵉ
  left-unit-law-mul-function-Ringᵉ =
    left-unit-law-mul-Π-Ringᵉ Xᵉ (λ _ → Rᵉ)

  right-unit-law-mul-function-Ringᵉ :
    (fᵉ : type-function-Ringᵉ) →
    mul-function-Ringᵉ fᵉ one-function-Ringᵉ ＝ᵉ fᵉ
  right-unit-law-mul-function-Ringᵉ =
    right-unit-law-mul-Π-Ringᵉ Xᵉ (λ _ → Rᵉ)

  left-distributive-mul-add-function-Ringᵉ :
    (fᵉ gᵉ hᵉ : type-function-Ringᵉ) →
    mul-function-Ringᵉ fᵉ (add-function-Ringᵉ gᵉ hᵉ) ＝ᵉ
    add-function-Ringᵉ (mul-function-Ringᵉ fᵉ gᵉ) (mul-function-Ringᵉ fᵉ hᵉ)
  left-distributive-mul-add-function-Ringᵉ =
    left-distributive-mul-add-Π-Ringᵉ Xᵉ (λ _ → Rᵉ)

  right-distributive-mul-add-function-Ringᵉ :
    (fᵉ gᵉ hᵉ : type-function-Ringᵉ) →
    mul-function-Ringᵉ (add-function-Ringᵉ fᵉ gᵉ) hᵉ ＝ᵉ
    add-function-Ringᵉ (mul-function-Ringᵉ fᵉ hᵉ) (mul-function-Ringᵉ gᵉ hᵉ)
  right-distributive-mul-add-function-Ringᵉ =
    right-distributive-mul-add-Π-Ringᵉ Xᵉ (λ _ → Rᵉ)
```