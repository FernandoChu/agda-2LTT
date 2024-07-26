# Function commutative monoids

```agda
module group-theory.function-commutative-monoidsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.identity-typesᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.commutative-monoidsᵉ
open import group-theory.dependent-products-commutative-monoidsᵉ
open import group-theory.monoidsᵉ
```

</details>

## Idea

Givenᵉ aᵉ commutativeᵉ monoidᵉ `M`ᵉ andᵉ aᵉ typeᵉ `X`,ᵉ theᵉ functionᵉ commuativeᵉ monoidᵉ
`M^X`ᵉ consistsᵉ ofᵉ functionsᵉ fromᵉ `X`ᵉ to theᵉ underlyingᵉ typeᵉ ofᵉ `M`.ᵉ Theᵉ
multiplicativeᵉ operationᵉ andᵉ theᵉ unitᵉ areᵉ givenᵉ pointwise.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Mᵉ : Commutative-Monoidᵉ l1ᵉ) (Xᵉ : UUᵉ l2ᵉ)
  where

  function-Commutative-Monoidᵉ : Commutative-Monoidᵉ (l1ᵉ ⊔ l2ᵉ)
  function-Commutative-Monoidᵉ = Π-Commutative-Monoidᵉ Xᵉ (λ _ → Mᵉ)

  monoid-function-Commutative-Monoidᵉ : Monoidᵉ (l1ᵉ ⊔ l2ᵉ)
  monoid-function-Commutative-Monoidᵉ =
    monoid-Π-Commutative-Monoidᵉ Xᵉ (λ _ → Mᵉ)

  set-function-Commutative-Monoidᵉ : Setᵉ (l1ᵉ ⊔ l2ᵉ)
  set-function-Commutative-Monoidᵉ =
    set-Π-Commutative-Monoidᵉ Xᵉ (λ _ → Mᵉ)

  type-function-Commutative-Monoidᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  type-function-Commutative-Monoidᵉ =
    type-Π-Commutative-Monoidᵉ Xᵉ (λ _ → Mᵉ)

  unit-function-Commutative-Monoidᵉ : type-function-Commutative-Monoidᵉ
  unit-function-Commutative-Monoidᵉ =
    unit-Π-Commutative-Monoidᵉ Xᵉ (λ _ → Mᵉ)

  mul-function-Commutative-Monoidᵉ :
    (fᵉ gᵉ : type-function-Commutative-Monoidᵉ) →
    type-function-Commutative-Monoidᵉ
  mul-function-Commutative-Monoidᵉ =
    mul-Π-Commutative-Monoidᵉ Xᵉ (λ _ → Mᵉ)

  associative-mul-function-Commutative-Monoidᵉ :
    (fᵉ gᵉ hᵉ : type-function-Commutative-Monoidᵉ) →
    mul-function-Commutative-Monoidᵉ (mul-function-Commutative-Monoidᵉ fᵉ gᵉ) hᵉ ＝ᵉ
    mul-function-Commutative-Monoidᵉ fᵉ (mul-function-Commutative-Monoidᵉ gᵉ hᵉ)
  associative-mul-function-Commutative-Monoidᵉ =
    associative-mul-Π-Commutative-Monoidᵉ Xᵉ (λ _ → Mᵉ)

  left-unit-law-mul-function-Commutative-Monoidᵉ :
    (fᵉ : type-function-Commutative-Monoidᵉ) →
    mul-function-Commutative-Monoidᵉ unit-function-Commutative-Monoidᵉ fᵉ ＝ᵉ fᵉ
  left-unit-law-mul-function-Commutative-Monoidᵉ =
    left-unit-law-mul-Π-Commutative-Monoidᵉ Xᵉ (λ _ → Mᵉ)

  right-unit-law-mul-function-Commutative-Monoidᵉ :
    (fᵉ : type-function-Commutative-Monoidᵉ) →
    mul-function-Commutative-Monoidᵉ fᵉ unit-function-Commutative-Monoidᵉ ＝ᵉ fᵉ
  right-unit-law-mul-function-Commutative-Monoidᵉ =
    right-unit-law-mul-Π-Commutative-Monoidᵉ Xᵉ (λ _ → Mᵉ)

  commutative-mul-function-Commutative-Monoidᵉ :
    (fᵉ gᵉ : type-function-Commutative-Monoidᵉ) →
    mul-function-Commutative-Monoidᵉ fᵉ gᵉ ＝ᵉ mul-function-Commutative-Monoidᵉ gᵉ fᵉ
  commutative-mul-function-Commutative-Monoidᵉ =
    commutative-mul-Π-Commutative-Monoidᵉ Xᵉ (λ _ → Mᵉ)
```