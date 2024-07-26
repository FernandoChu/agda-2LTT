# Function commutative rings

```agda
module commutative-algebra.function-commutative-ringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-ringsᵉ
open import commutative-algebra.dependent-products-commutative-ringsᵉ

open import foundation.identity-typesᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.abelian-groupsᵉ
open import group-theory.commutative-monoidsᵉ

open import ring-theory.ringsᵉ
```

</details>

## Idea

Givenᵉ aᵉ commutativeᵉ ringᵉ `A`ᵉ andᵉ aᵉ typeᵉ `X`,ᵉ theᵉ typeᵉ `A^X`ᵉ ofᵉ functionsᵉ fromᵉ
`X`ᵉ intoᵉ theᵉ underlyingᵉ typeᵉ ofᵉ `A`ᵉ isᵉ againᵉ aᵉ commutativeᵉ ring.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Commutative-Ringᵉ l1ᵉ) (Xᵉ : UUᵉ l2ᵉ)
  where

  function-Commutative-Ringᵉ : Commutative-Ringᵉ (l1ᵉ ⊔ l2ᵉ)
  function-Commutative-Ringᵉ = Π-Commutative-Ringᵉ Xᵉ (λ _ → Aᵉ)

  ring-function-Commutative-Ringᵉ : Ringᵉ (l1ᵉ ⊔ l2ᵉ)
  ring-function-Commutative-Ringᵉ =
    ring-Commutative-Ringᵉ function-Commutative-Ringᵉ

  ab-function-Commutative-Ringᵉ : Abᵉ (l1ᵉ ⊔ l2ᵉ)
  ab-function-Commutative-Ringᵉ =
    ab-Commutative-Ringᵉ function-Commutative-Ringᵉ

  multiplicative-commutative-monoid-function-Commutative-Ringᵉ :
    Commutative-Monoidᵉ (l1ᵉ ⊔ l2ᵉ)
  multiplicative-commutative-monoid-function-Commutative-Ringᵉ =
    multiplicative-commutative-monoid-Commutative-Ringᵉ function-Commutative-Ringᵉ

  set-function-Commutative-Ringᵉ : Setᵉ (l1ᵉ ⊔ l2ᵉ)
  set-function-Commutative-Ringᵉ = set-Ringᵉ ring-function-Commutative-Ringᵉ

  type-function-Commutative-Ringᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  type-function-Commutative-Ringᵉ = type-Ringᵉ ring-function-Commutative-Ringᵉ

  is-set-type-function-Commutative-Ringᵉ : is-setᵉ type-function-Commutative-Ringᵉ
  is-set-type-function-Commutative-Ringᵉ =
    is-set-type-Commutative-Ringᵉ function-Commutative-Ringᵉ

  add-function-Commutative-Ringᵉ :
    type-function-Commutative-Ringᵉ → type-function-Commutative-Ringᵉ →
    type-function-Commutative-Ringᵉ
  add-function-Commutative-Ringᵉ =
    add-Commutative-Ringᵉ function-Commutative-Ringᵉ

  zero-function-Commutative-Ringᵉ : type-function-Commutative-Ringᵉ
  zero-function-Commutative-Ringᵉ =
    zero-Commutative-Ringᵉ function-Commutative-Ringᵉ

  associative-add-function-Commutative-Ringᵉ :
    (xᵉ yᵉ zᵉ : type-function-Commutative-Ringᵉ) →
    add-function-Commutative-Ringᵉ (add-function-Commutative-Ringᵉ xᵉ yᵉ) zᵉ ＝ᵉ
    add-function-Commutative-Ringᵉ xᵉ (add-function-Commutative-Ringᵉ yᵉ zᵉ)
  associative-add-function-Commutative-Ringᵉ =
    associative-add-Commutative-Ringᵉ function-Commutative-Ringᵉ

  left-unit-law-add-function-Commutative-Ringᵉ :
    (xᵉ : type-function-Commutative-Ringᵉ) →
    add-function-Commutative-Ringᵉ zero-function-Commutative-Ringᵉ xᵉ ＝ᵉ xᵉ
  left-unit-law-add-function-Commutative-Ringᵉ =
    left-unit-law-add-Commutative-Ringᵉ function-Commutative-Ringᵉ

  right-unit-law-add-function-Commutative-Ringᵉ :
    (xᵉ : type-function-Commutative-Ringᵉ) →
    add-function-Commutative-Ringᵉ xᵉ zero-function-Commutative-Ringᵉ ＝ᵉ xᵉ
  right-unit-law-add-function-Commutative-Ringᵉ =
    right-unit-law-add-Commutative-Ringᵉ function-Commutative-Ringᵉ

  commutative-add-function-Commutative-Ringᵉ :
    (xᵉ yᵉ : type-function-Commutative-Ringᵉ) →
    add-function-Commutative-Ringᵉ xᵉ yᵉ ＝ᵉ add-function-Commutative-Ringᵉ yᵉ xᵉ
  commutative-add-function-Commutative-Ringᵉ =
    commutative-add-Commutative-Ringᵉ function-Commutative-Ringᵉ

  mul-function-Commutative-Ringᵉ :
    type-function-Commutative-Ringᵉ → type-function-Commutative-Ringᵉ →
    type-function-Commutative-Ringᵉ
  mul-function-Commutative-Ringᵉ =
    mul-Commutative-Ringᵉ function-Commutative-Ringᵉ

  one-function-Commutative-Ringᵉ : type-function-Commutative-Ringᵉ
  one-function-Commutative-Ringᵉ =
    one-Commutative-Ringᵉ function-Commutative-Ringᵉ

  associative-mul-function-Commutative-Ringᵉ :
    (xᵉ yᵉ zᵉ : type-function-Commutative-Ringᵉ) →
    mul-function-Commutative-Ringᵉ (mul-function-Commutative-Ringᵉ xᵉ yᵉ) zᵉ ＝ᵉ
    mul-function-Commutative-Ringᵉ xᵉ (mul-function-Commutative-Ringᵉ yᵉ zᵉ)
  associative-mul-function-Commutative-Ringᵉ =
    associative-mul-Commutative-Ringᵉ function-Commutative-Ringᵉ

  left-unit-law-mul-function-Commutative-Ringᵉ :
    (xᵉ : type-function-Commutative-Ringᵉ) →
    mul-function-Commutative-Ringᵉ one-function-Commutative-Ringᵉ xᵉ ＝ᵉ xᵉ
  left-unit-law-mul-function-Commutative-Ringᵉ =
    left-unit-law-mul-Commutative-Ringᵉ function-Commutative-Ringᵉ

  right-unit-law-mul-function-Commutative-Ringᵉ :
    (xᵉ : type-function-Commutative-Ringᵉ) →
    mul-function-Commutative-Ringᵉ xᵉ one-function-Commutative-Ringᵉ ＝ᵉ xᵉ
  right-unit-law-mul-function-Commutative-Ringᵉ =
    right-unit-law-mul-Commutative-Ringᵉ function-Commutative-Ringᵉ

  left-distributive-mul-add-function-Commutative-Ringᵉ :
    (fᵉ gᵉ hᵉ : type-function-Commutative-Ringᵉ) →
    mul-function-Commutative-Ringᵉ fᵉ (add-function-Commutative-Ringᵉ gᵉ hᵉ) ＝ᵉ
    add-function-Commutative-Ringᵉ
      ( mul-function-Commutative-Ringᵉ fᵉ gᵉ)
      ( mul-function-Commutative-Ringᵉ fᵉ hᵉ)
  left-distributive-mul-add-function-Commutative-Ringᵉ =
    left-distributive-mul-add-Commutative-Ringᵉ function-Commutative-Ringᵉ

  right-distributive-mul-add-function-Commutative-Ringᵉ :
    (fᵉ gᵉ hᵉ : type-function-Commutative-Ringᵉ) →
    mul-function-Commutative-Ringᵉ (add-function-Commutative-Ringᵉ fᵉ gᵉ) hᵉ ＝ᵉ
    add-function-Commutative-Ringᵉ
      ( mul-function-Commutative-Ringᵉ fᵉ hᵉ)
      ( mul-function-Commutative-Ringᵉ gᵉ hᵉ)
  right-distributive-mul-add-function-Commutative-Ringᵉ =
    right-distributive-mul-add-Commutative-Ringᵉ function-Commutative-Ringᵉ

  left-zero-law-mul-function-Commutative-Ringᵉ :
    (fᵉ : type-function-Commutative-Ringᵉ) →
    mul-function-Commutative-Ringᵉ zero-function-Commutative-Ringᵉ fᵉ ＝ᵉ
    zero-function-Commutative-Ringᵉ
  left-zero-law-mul-function-Commutative-Ringᵉ =
    left-zero-law-mul-Commutative-Ringᵉ function-Commutative-Ringᵉ

  right-zero-law-mul-function-Commutative-Ringᵉ :
    (fᵉ : type-function-Commutative-Ringᵉ) →
    mul-function-Commutative-Ringᵉ fᵉ zero-function-Commutative-Ringᵉ ＝ᵉ
    zero-function-Commutative-Ringᵉ
  right-zero-law-mul-function-Commutative-Ringᵉ =
    right-zero-law-mul-Commutative-Ringᵉ function-Commutative-Ringᵉ

  commutative-mul-function-Commutative-Ringᵉ :
    (fᵉ gᵉ : type-function-Commutative-Ringᵉ) →
    mul-function-Commutative-Ringᵉ fᵉ gᵉ ＝ᵉ mul-function-Commutative-Ringᵉ gᵉ fᵉ
  commutative-mul-function-Commutative-Ringᵉ =
    commutative-mul-Commutative-Ringᵉ function-Commutative-Ringᵉ
```