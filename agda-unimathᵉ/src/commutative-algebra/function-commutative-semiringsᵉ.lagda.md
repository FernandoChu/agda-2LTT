# Function commutative semirings

```agda
module commutative-algebra.function-commutative-semiringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-semiringsᵉ
open import commutative-algebra.dependent-products-commutative-semiringsᵉ

open import foundation.identity-typesᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.commutative-monoidsᵉ

open import ring-theory.semiringsᵉ
```

</details>

## Idea

Givenᵉ aᵉ commutativeᵉ semiringᵉ `A`ᵉ andᵉ aᵉ typeᵉ `X`,ᵉ theᵉ typeᵉ `A^X`ᵉ ofᵉ functionsᵉ
fromᵉ `X`ᵉ to theᵉ underlyingᵉ typeᵉ ofᵉ `A`ᵉ isᵉ againᵉ aᵉ commutativeᵉ semiring.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Commutative-Semiringᵉ l1ᵉ) (Xᵉ : UUᵉ l2ᵉ)
  where

  function-Commutative-Semiringᵉ : Commutative-Semiringᵉ (l1ᵉ ⊔ l2ᵉ)
  function-Commutative-Semiringᵉ =
    Π-Commutative-Semiringᵉ Xᵉ (λ _ → Aᵉ)

  semiring-function-Commutative-Semiringᵉ : Semiringᵉ (l1ᵉ ⊔ l2ᵉ)
  semiring-function-Commutative-Semiringᵉ =
    semiring-Π-Commutative-Semiringᵉ Xᵉ (λ _ → Aᵉ)

  additive-commutative-monoid-function-Commutative-Semiringᵉ :
    Commutative-Monoidᵉ (l1ᵉ ⊔ l2ᵉ)
  additive-commutative-monoid-function-Commutative-Semiringᵉ =
    additive-commutative-monoid-Π-Commutative-Semiringᵉ Xᵉ (λ _ → Aᵉ)

  multiplicative-commutative-monoid-function-Commutative-Semiringᵉ :
    Commutative-Monoidᵉ (l1ᵉ ⊔ l2ᵉ)
  multiplicative-commutative-monoid-function-Commutative-Semiringᵉ =
    multiplicative-commutative-monoid-Π-Commutative-Semiringᵉ Xᵉ (λ _ → Aᵉ)

  set-function-Commutative-Semiringᵉ : Setᵉ (l1ᵉ ⊔ l2ᵉ)
  set-function-Commutative-Semiringᵉ =
    set-Π-Commutative-Semiringᵉ Xᵉ (λ _ → Aᵉ)

  type-function-Commutative-Semiringᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  type-function-Commutative-Semiringᵉ =
    type-Π-Commutative-Semiringᵉ Xᵉ (λ _ → Aᵉ)

  is-set-type-function-Commutative-Semiringᵉ :
    is-setᵉ type-function-Commutative-Semiringᵉ
  is-set-type-function-Commutative-Semiringᵉ =
    is-set-type-Π-Commutative-Semiringᵉ Xᵉ (λ _ → Aᵉ)

  add-function-Commutative-Semiringᵉ :
    type-function-Commutative-Semiringᵉ → type-function-Commutative-Semiringᵉ →
    type-function-Commutative-Semiringᵉ
  add-function-Commutative-Semiringᵉ =
    add-Π-Commutative-Semiringᵉ Xᵉ (λ _ → Aᵉ)

  zero-function-Commutative-Semiringᵉ : type-function-Commutative-Semiringᵉ
  zero-function-Commutative-Semiringᵉ =
    zero-Π-Commutative-Semiringᵉ Xᵉ (λ _ → Aᵉ)

  associative-add-function-Commutative-Semiringᵉ :
    (xᵉ yᵉ zᵉ : type-function-Commutative-Semiringᵉ) →
    add-function-Commutative-Semiringᵉ
      ( add-function-Commutative-Semiringᵉ xᵉ yᵉ)
      ( zᵉ) ＝ᵉ
    add-function-Commutative-Semiringᵉ
      ( xᵉ)
      ( add-function-Commutative-Semiringᵉ yᵉ zᵉ)
  associative-add-function-Commutative-Semiringᵉ =
    associative-add-Π-Commutative-Semiringᵉ Xᵉ (λ _ → Aᵉ)

  left-unit-law-add-function-Commutative-Semiringᵉ :
    (xᵉ : type-function-Commutative-Semiringᵉ) →
    add-function-Commutative-Semiringᵉ zero-function-Commutative-Semiringᵉ xᵉ ＝ᵉ xᵉ
  left-unit-law-add-function-Commutative-Semiringᵉ =
    left-unit-law-add-Π-Commutative-Semiringᵉ Xᵉ (λ _ → Aᵉ)

  right-unit-law-add-function-Commutative-Semiringᵉ :
    (xᵉ : type-function-Commutative-Semiringᵉ) →
    add-function-Commutative-Semiringᵉ xᵉ zero-function-Commutative-Semiringᵉ ＝ᵉ xᵉ
  right-unit-law-add-function-Commutative-Semiringᵉ =
    right-unit-law-add-Π-Commutative-Semiringᵉ Xᵉ (λ _ → Aᵉ)

  commutative-add-function-Commutative-Semiringᵉ :
    (xᵉ yᵉ : type-function-Commutative-Semiringᵉ) →
    add-function-Commutative-Semiringᵉ xᵉ yᵉ ＝ᵉ
    add-function-Commutative-Semiringᵉ yᵉ xᵉ
  commutative-add-function-Commutative-Semiringᵉ =
    commutative-add-Π-Commutative-Semiringᵉ Xᵉ (λ _ → Aᵉ)

  mul-function-Commutative-Semiringᵉ :
    type-function-Commutative-Semiringᵉ → type-function-Commutative-Semiringᵉ →
    type-function-Commutative-Semiringᵉ
  mul-function-Commutative-Semiringᵉ =
    mul-Π-Commutative-Semiringᵉ Xᵉ (λ _ → Aᵉ)

  one-function-Commutative-Semiringᵉ : type-function-Commutative-Semiringᵉ
  one-function-Commutative-Semiringᵉ =
    one-Π-Commutative-Semiringᵉ Xᵉ (λ _ → Aᵉ)

  associative-mul-function-Commutative-Semiringᵉ :
    (xᵉ yᵉ zᵉ : type-function-Commutative-Semiringᵉ) →
    mul-function-Commutative-Semiringᵉ
      ( mul-function-Commutative-Semiringᵉ xᵉ yᵉ)
      ( zᵉ) ＝ᵉ
    mul-function-Commutative-Semiringᵉ
      ( xᵉ)
      ( mul-function-Commutative-Semiringᵉ yᵉ zᵉ)
  associative-mul-function-Commutative-Semiringᵉ =
    associative-mul-Π-Commutative-Semiringᵉ Xᵉ (λ _ → Aᵉ)

  left-unit-law-mul-function-Commutative-Semiringᵉ :
    (xᵉ : type-function-Commutative-Semiringᵉ) →
    mul-function-Commutative-Semiringᵉ one-function-Commutative-Semiringᵉ xᵉ ＝ᵉ xᵉ
  left-unit-law-mul-function-Commutative-Semiringᵉ =
    left-unit-law-mul-Π-Commutative-Semiringᵉ Xᵉ (λ _ → Aᵉ)

  right-unit-law-mul-function-Commutative-Semiringᵉ :
    (xᵉ : type-function-Commutative-Semiringᵉ) →
    mul-function-Commutative-Semiringᵉ xᵉ one-function-Commutative-Semiringᵉ ＝ᵉ xᵉ
  right-unit-law-mul-function-Commutative-Semiringᵉ =
    right-unit-law-mul-Π-Commutative-Semiringᵉ Xᵉ (λ _ → Aᵉ)

  left-distributive-mul-add-function-Commutative-Semiringᵉ :
    (fᵉ gᵉ hᵉ : type-function-Commutative-Semiringᵉ) →
    mul-function-Commutative-Semiringᵉ fᵉ
      ( add-function-Commutative-Semiringᵉ gᵉ hᵉ) ＝ᵉ
    add-function-Commutative-Semiringᵉ
      ( mul-function-Commutative-Semiringᵉ fᵉ gᵉ)
      ( mul-function-Commutative-Semiringᵉ fᵉ hᵉ)
  left-distributive-mul-add-function-Commutative-Semiringᵉ =
    left-distributive-mul-add-Π-Commutative-Semiringᵉ Xᵉ (λ _ → Aᵉ)

  right-distributive-mul-add-function-Commutative-Semiringᵉ :
    (fᵉ gᵉ hᵉ : type-function-Commutative-Semiringᵉ) →
    mul-function-Commutative-Semiringᵉ
      ( add-function-Commutative-Semiringᵉ fᵉ gᵉ) hᵉ ＝ᵉ
    add-function-Commutative-Semiringᵉ
      ( mul-function-Commutative-Semiringᵉ fᵉ hᵉ)
      ( mul-function-Commutative-Semiringᵉ gᵉ hᵉ)
  right-distributive-mul-add-function-Commutative-Semiringᵉ =
    right-distributive-mul-add-Π-Commutative-Semiringᵉ Xᵉ (λ _ → Aᵉ)

  left-zero-law-mul-function-Commutative-Semiringᵉ :
    (fᵉ : type-function-Commutative-Semiringᵉ) →
    mul-function-Commutative-Semiringᵉ zero-function-Commutative-Semiringᵉ fᵉ ＝ᵉ
    zero-function-Commutative-Semiringᵉ
  left-zero-law-mul-function-Commutative-Semiringᵉ =
    left-zero-law-mul-Π-Commutative-Semiringᵉ Xᵉ (λ _ → Aᵉ)

  right-zero-law-mul-function-Commutative-Semiringᵉ :
    (fᵉ : type-function-Commutative-Semiringᵉ) →
    mul-function-Commutative-Semiringᵉ fᵉ zero-function-Commutative-Semiringᵉ ＝ᵉ
    zero-function-Commutative-Semiringᵉ
  right-zero-law-mul-function-Commutative-Semiringᵉ =
    right-zero-law-mul-Π-Commutative-Semiringᵉ Xᵉ (λ _ → Aᵉ)

  commutative-mul-function-Commutative-Semiringᵉ :
    (fᵉ gᵉ : type-function-Commutative-Semiringᵉ) →
    mul-function-Commutative-Semiringᵉ fᵉ gᵉ ＝ᵉ
    mul-function-Commutative-Semiringᵉ gᵉ fᵉ
  commutative-mul-function-Commutative-Semiringᵉ =
    commutative-mul-Commutative-Monoidᵉ
      multiplicative-commutative-monoid-function-Commutative-Semiringᵉ
```