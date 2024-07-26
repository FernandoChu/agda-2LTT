# Function groups

```agda
module group-theory.function-groupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.dependent-products-groupsᵉ
open import group-theory.groupsᵉ
open import group-theory.monoidsᵉ
open import group-theory.semigroupsᵉ
```

</details>

## Idea

Givenᵉ aᵉ groupᵉ `G`ᵉ andᵉ aᵉ typeᵉ `X`,ᵉ theᵉ functionᵉ groupᵉ `G^X`ᵉ consistsᵉ ofᵉ functionsᵉ
fromᵉ `X`ᵉ to theᵉ underlyingᵉ typeᵉ ofᵉ `G`.ᵉ Theᵉ groupᵉ operationsᵉ areᵉ givenᵉ
pointwise.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Xᵉ : UUᵉ l2ᵉ)
  where

  function-Groupᵉ : Groupᵉ (l1ᵉ ⊔ l2ᵉ)
  function-Groupᵉ = Π-Groupᵉ Xᵉ (λ _ → Gᵉ)

  semigroup-function-Groupᵉ : Semigroupᵉ (l1ᵉ ⊔ l2ᵉ)
  semigroup-function-Groupᵉ = semigroup-Π-Groupᵉ Xᵉ (λ _ → Gᵉ)

  set-function-Groupᵉ : Setᵉ (l1ᵉ ⊔ l2ᵉ)
  set-function-Groupᵉ = set-Π-Groupᵉ Xᵉ (λ _ → Gᵉ)

  type-function-Groupᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  type-function-Groupᵉ = type-Π-Groupᵉ Xᵉ (λ _ → Gᵉ)

  mul-function-Groupᵉ :
    (fᵉ gᵉ : type-function-Groupᵉ) → type-function-Groupᵉ
  mul-function-Groupᵉ = mul-Π-Groupᵉ Xᵉ (λ _ → Gᵉ)

  associative-mul-function-Groupᵉ :
    (fᵉ gᵉ hᵉ : type-function-Groupᵉ) →
    mul-function-Groupᵉ (mul-function-Groupᵉ fᵉ gᵉ) hᵉ ＝ᵉ
    mul-function-Groupᵉ fᵉ (mul-function-Groupᵉ gᵉ hᵉ)
  associative-mul-function-Groupᵉ =
    associative-mul-Π-Groupᵉ Xᵉ (λ _ → Gᵉ)

  unit-function-Groupᵉ : type-function-Groupᵉ
  unit-function-Groupᵉ = unit-Π-Groupᵉ Xᵉ (λ _ → Gᵉ)

  left-unit-law-mul-function-Groupᵉ :
    (fᵉ : type-function-Groupᵉ) →
    mul-function-Groupᵉ unit-function-Groupᵉ fᵉ ＝ᵉ fᵉ
  left-unit-law-mul-function-Groupᵉ =
    left-unit-law-mul-Π-Groupᵉ Xᵉ (λ _ → Gᵉ)

  right-unit-law-mul-function-Groupᵉ :
    (fᵉ : type-function-Groupᵉ) →
    mul-function-Groupᵉ fᵉ unit-function-Groupᵉ ＝ᵉ fᵉ
  right-unit-law-mul-function-Groupᵉ =
    right-unit-law-mul-Π-Groupᵉ Xᵉ (λ _ → Gᵉ)

  is-unital-function-Groupᵉ :
    is-unital-Semigroupᵉ semigroup-function-Groupᵉ
  is-unital-function-Groupᵉ = is-unital-Π-Groupᵉ Xᵉ (λ _ → Gᵉ)

  monoid-function-Groupᵉ : Monoidᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ monoid-function-Groupᵉ = semigroup-function-Groupᵉ
  pr2ᵉ monoid-function-Groupᵉ = is-unital-function-Groupᵉ

  inv-function-Groupᵉ : type-function-Groupᵉ → type-function-Groupᵉ
  inv-function-Groupᵉ = inv-Π-Groupᵉ Xᵉ (λ _ → Gᵉ)

  left-inverse-law-mul-function-Groupᵉ :
    (fᵉ : type-function-Groupᵉ) →
    mul-function-Groupᵉ (inv-function-Groupᵉ fᵉ) fᵉ ＝ᵉ unit-function-Groupᵉ
  left-inverse-law-mul-function-Groupᵉ =
    left-inverse-law-mul-Π-Groupᵉ Xᵉ (λ _ → Gᵉ)

  right-inverse-law-mul-function-Groupᵉ :
    (fᵉ : type-function-Groupᵉ) →
    mul-function-Groupᵉ fᵉ (inv-function-Groupᵉ fᵉ) ＝ᵉ unit-function-Groupᵉ
  right-inverse-law-mul-function-Groupᵉ =
    right-inverse-law-mul-Π-Groupᵉ Xᵉ (λ _ → Gᵉ)

  is-group-function-Groupᵉ : is-group-Semigroupᵉ semigroup-function-Groupᵉ
  is-group-function-Groupᵉ = is-group-Π-Groupᵉ Xᵉ (λ _ → Gᵉ)
```