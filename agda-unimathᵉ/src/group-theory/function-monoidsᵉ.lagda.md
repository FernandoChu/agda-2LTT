# Function monoids

```agda
module group-theory.function-monoidsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.identity-typesᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.dependent-products-monoidsᵉ
open import group-theory.monoidsᵉ
open import group-theory.semigroupsᵉ
```

</details>

## Idea

Givenᵉ aᵉ [monoid](group-theory.monoids.mdᵉ) `M`ᵉ andᵉ aᵉ typeᵉ `X`,ᵉ theᵉ **functionᵉ
monoid**ᵉ `M^X`ᵉ consistsᵉ ofᵉ functionsᵉ fromᵉ `X`ᵉ to theᵉ underlyingᵉ typeᵉ ofᵉ `M`.ᵉ Theᵉ
multiplicativeᵉ operationᵉ andᵉ theᵉ unitᵉ areᵉ givenᵉ pointwise.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Mᵉ : Monoidᵉ l1ᵉ) (Xᵉ : UUᵉ l2ᵉ)
  where

  function-Monoidᵉ : Monoidᵉ (l1ᵉ ⊔ l2ᵉ)
  function-Monoidᵉ = Π-Monoidᵉ Xᵉ (λ _ → Mᵉ)

  semigroup-function-Monoidᵉ : Semigroupᵉ (l1ᵉ ⊔ l2ᵉ)
  semigroup-function-Monoidᵉ = semigroup-Π-Monoidᵉ Xᵉ (λ _ → Mᵉ)

  set-function-Monoidᵉ : Setᵉ (l1ᵉ ⊔ l2ᵉ)
  set-function-Monoidᵉ = set-Π-Monoidᵉ Xᵉ (λ _ → Mᵉ)

  type-function-Monoidᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  type-function-Monoidᵉ = type-Π-Monoidᵉ Xᵉ (λ _ → Mᵉ)

  mul-function-Monoidᵉ :
    (fᵉ gᵉ : type-function-Monoidᵉ) → type-function-Monoidᵉ
  mul-function-Monoidᵉ = mul-Π-Monoidᵉ Xᵉ (λ _ → Mᵉ)

  associative-mul-function-Monoidᵉ :
    (fᵉ gᵉ hᵉ : type-function-Monoidᵉ) →
    mul-function-Monoidᵉ (mul-function-Monoidᵉ fᵉ gᵉ) hᵉ ＝ᵉ
    mul-function-Monoidᵉ fᵉ (mul-function-Monoidᵉ gᵉ hᵉ)
  associative-mul-function-Monoidᵉ =
    associative-mul-Π-Monoidᵉ Xᵉ (λ _ → Mᵉ)

  unit-function-Monoidᵉ : type-function-Monoidᵉ
  unit-function-Monoidᵉ = unit-Π-Monoidᵉ Xᵉ (λ _ → Mᵉ)

  left-unit-law-mul-function-Monoidᵉ :
    (fᵉ : type-function-Monoidᵉ) →
    mul-function-Monoidᵉ unit-function-Monoidᵉ fᵉ ＝ᵉ fᵉ
  left-unit-law-mul-function-Monoidᵉ =
    left-unit-law-mul-Π-Monoidᵉ Xᵉ (λ _ → Mᵉ)

  right-unit-law-mul-function-Monoidᵉ :
    (fᵉ : type-function-Monoidᵉ) →
    mul-function-Monoidᵉ fᵉ unit-function-Monoidᵉ ＝ᵉ fᵉ
  right-unit-law-mul-function-Monoidᵉ =
    right-unit-law-mul-Π-Monoidᵉ Xᵉ (λ _ → Mᵉ)

  is-unital-function-Monoidᵉ :
    is-unital-Semigroupᵉ semigroup-function-Monoidᵉ
  is-unital-function-Monoidᵉ = is-unital-Π-Monoidᵉ Xᵉ (λ _ → Mᵉ)
```