# Function semigroups

```agda
module group-theory.function-semigroupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.identity-typesᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.dependent-products-semigroupsᵉ
open import group-theory.semigroupsᵉ
```

</details>

## Idea

Givenᵉ aᵉ semigroupᵉ `G`ᵉ andᵉ aᵉ typeᵉ `X`,ᵉ theᵉ functionᵉ semigroupᵉ `G^X`ᵉ consistsᵉ ofᵉ
functionsᵉ fromᵉ `X`ᵉ to theᵉ underlyingᵉ typeᵉ ofᵉ `G`.ᵉ Theᵉ semigroupᵉ operationᵉ isᵉ
givenᵉ pointwise.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Semigroupᵉ l1ᵉ) (Xᵉ : UUᵉ l2ᵉ)
  where

  function-Semigroupᵉ : Semigroupᵉ (l1ᵉ ⊔ l2ᵉ)
  function-Semigroupᵉ = Π-Semigroupᵉ Xᵉ (λ _ → Gᵉ)

  set-function-Semigroupᵉ : Setᵉ (l1ᵉ ⊔ l2ᵉ)
  set-function-Semigroupᵉ = set-Π-Semigroupᵉ Xᵉ (λ _ → Gᵉ)

  type-function-Semigroupᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  type-function-Semigroupᵉ = type-Π-Semigroupᵉ Xᵉ (λ _ → Gᵉ)

  mul-function-Semigroupᵉ :
    (fᵉ gᵉ : type-function-Semigroupᵉ) → type-function-Semigroupᵉ
  mul-function-Semigroupᵉ = mul-Π-Semigroupᵉ Xᵉ (λ _ → Gᵉ)

  associative-mul-function-Semigroupᵉ :
    (fᵉ gᵉ hᵉ : type-function-Semigroupᵉ) →
    mul-function-Semigroupᵉ (mul-function-Semigroupᵉ fᵉ gᵉ) hᵉ ＝ᵉ
    mul-function-Semigroupᵉ fᵉ (mul-function-Semigroupᵉ gᵉ hᵉ)
  associative-mul-function-Semigroupᵉ =
    associative-mul-Π-Semigroupᵉ Xᵉ (λ _ → Gᵉ)

  has-associative-mul-function-Semigroupᵉ :
    has-associative-mul-Setᵉ set-function-Semigroupᵉ
  has-associative-mul-function-Semigroupᵉ =
    has-associative-mul-Π-Semigroupᵉ Xᵉ (λ _ → Gᵉ)
```