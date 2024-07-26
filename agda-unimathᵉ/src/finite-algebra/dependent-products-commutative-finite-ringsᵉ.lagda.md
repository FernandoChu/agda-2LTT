# Dependent products of commutative finit rings

```agda
module finite-algebra.dependent-products-commutative-finite-ringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-ringsᵉ
open import commutative-algebra.dependent-products-commutative-ringsᵉ

open import finite-algebra.commutative-finite-ringsᵉ
open import finite-algebra.dependent-products-finite-ringsᵉ
open import finite-algebra.finite-ringsᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.function-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.abelian-groupsᵉ
open import group-theory.commutative-monoidsᵉ

open import ring-theory.dependent-products-ringsᵉ
open import ring-theory.ringsᵉ

open import univalent-combinatorics.finite-typesᵉ
```

</details>

## Idea

Givenᵉ aᵉ familyᵉ ofᵉ commutativeᵉ finiteᵉ ringsᵉ `Aᵉ i`ᵉ indexedᵉ byᵉ aᵉ finiteᵉ typeᵉ
`iᵉ : I`,ᵉ theirᵉ **dependentᵉ product**ᵉ `Π(i:I),ᵉ Aᵉ i`ᵉ isᵉ againᵉ aᵉ finiteᵉ commutativeᵉ
ring.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Iᵉ : 𝔽ᵉ l1ᵉ) (Aᵉ : type-𝔽ᵉ Iᵉ → Commutative-Ring-𝔽ᵉ l2ᵉ)
  where

  finite-ring-Π-Commutative-Ring-𝔽ᵉ : Ring-𝔽ᵉ (l1ᵉ ⊔ l2ᵉ)
  finite-ring-Π-Commutative-Ring-𝔽ᵉ =
    Π-Ring-𝔽ᵉ Iᵉ (λ iᵉ → finite-ring-Commutative-Ring-𝔽ᵉ (Aᵉ iᵉ))

  ring-Π-Commutative-Ring-𝔽ᵉ : Ringᵉ (l1ᵉ ⊔ l2ᵉ)
  ring-Π-Commutative-Ring-𝔽ᵉ =
    Π-Ringᵉ (type-𝔽ᵉ Iᵉ) (ring-Commutative-Ring-𝔽ᵉ ∘ᵉ Aᵉ)

  ab-Π-Commutative-Ring-𝔽ᵉ : Abᵉ (l1ᵉ ⊔ l2ᵉ)
  ab-Π-Commutative-Ring-𝔽ᵉ =
    ab-Π-Commutative-Ringᵉ (type-𝔽ᵉ Iᵉ) (commutative-ring-Commutative-Ring-𝔽ᵉ ∘ᵉ Aᵉ)

  multiplicative-commutative-monoid-Π-Commutative-Ring-𝔽ᵉ :
    Commutative-Monoidᵉ (l1ᵉ ⊔ l2ᵉ)
  multiplicative-commutative-monoid-Π-Commutative-Ring-𝔽ᵉ =
    multiplicative-commutative-monoid-Π-Commutative-Ringᵉ
      ( type-𝔽ᵉ Iᵉ)
      ( commutative-ring-Commutative-Ring-𝔽ᵉ ∘ᵉ Aᵉ)

  set-Π-Commutative-Ring-𝔽ᵉ : Setᵉ (l1ᵉ ⊔ l2ᵉ)
  set-Π-Commutative-Ring-𝔽ᵉ =
    set-Π-Commutative-Ringᵉ
      ( type-𝔽ᵉ Iᵉ)
      ( commutative-ring-Commutative-Ring-𝔽ᵉ ∘ᵉ Aᵉ)

  type-Π-Commutative-Ring-𝔽ᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  type-Π-Commutative-Ring-𝔽ᵉ =
    type-Π-Commutative-Ringᵉ (type-𝔽ᵉ Iᵉ) (commutative-ring-Commutative-Ring-𝔽ᵉ ∘ᵉ Aᵉ)

  finite-type-Π-Commutative-Ring-𝔽ᵉ : 𝔽ᵉ (l1ᵉ ⊔ l2ᵉ)
  finite-type-Π-Commutative-Ring-𝔽ᵉ =
    finite-type-Π-Ring-𝔽ᵉ Iᵉ (finite-ring-Commutative-Ring-𝔽ᵉ ∘ᵉ Aᵉ)

  is-finite-type-Π-Commutative-Ring-𝔽ᵉ : is-finiteᵉ type-Π-Commutative-Ring-𝔽ᵉ
  is-finite-type-Π-Commutative-Ring-𝔽ᵉ =
    is-finite-type-Π-Ring-𝔽ᵉ Iᵉ (finite-ring-Commutative-Ring-𝔽ᵉ ∘ᵉ Aᵉ)

  is-set-type-Π-Commutative-Ring-𝔽ᵉ : is-setᵉ type-Π-Commutative-Ring-𝔽ᵉ
  is-set-type-Π-Commutative-Ring-𝔽ᵉ =
    is-set-type-Π-Commutative-Ringᵉ
      ( type-𝔽ᵉ Iᵉ)
      ( commutative-ring-Commutative-Ring-𝔽ᵉ ∘ᵉ Aᵉ)

  add-Π-Commutative-Ring-𝔽ᵉ :
    type-Π-Commutative-Ring-𝔽ᵉ → type-Π-Commutative-Ring-𝔽ᵉ →
    type-Π-Commutative-Ring-𝔽ᵉ
  add-Π-Commutative-Ring-𝔽ᵉ =
    add-Π-Commutative-Ringᵉ (type-𝔽ᵉ Iᵉ) (commutative-ring-Commutative-Ring-𝔽ᵉ ∘ᵉ Aᵉ)

  zero-Π-Commutative-Ring-𝔽ᵉ : type-Π-Commutative-Ring-𝔽ᵉ
  zero-Π-Commutative-Ring-𝔽ᵉ =
    zero-Π-Commutative-Ringᵉ (type-𝔽ᵉ Iᵉ) (commutative-ring-Commutative-Ring-𝔽ᵉ ∘ᵉ Aᵉ)

  associative-add-Π-Commutative-Ring-𝔽ᵉ :
    (xᵉ yᵉ zᵉ : type-Π-Commutative-Ring-𝔽ᵉ) →
    add-Π-Commutative-Ring-𝔽ᵉ (add-Π-Commutative-Ring-𝔽ᵉ xᵉ yᵉ) zᵉ ＝ᵉ
    add-Π-Commutative-Ring-𝔽ᵉ xᵉ (add-Π-Commutative-Ring-𝔽ᵉ yᵉ zᵉ)
  associative-add-Π-Commutative-Ring-𝔽ᵉ =
    associative-add-Π-Commutative-Ringᵉ
      ( type-𝔽ᵉ Iᵉ)
      ( commutative-ring-Commutative-Ring-𝔽ᵉ ∘ᵉ Aᵉ)

  left-unit-law-add-Π-Commutative-Ring-𝔽ᵉ :
    (xᵉ : type-Π-Commutative-Ring-𝔽ᵉ) →
    add-Π-Commutative-Ring-𝔽ᵉ zero-Π-Commutative-Ring-𝔽ᵉ xᵉ ＝ᵉ xᵉ
  left-unit-law-add-Π-Commutative-Ring-𝔽ᵉ =
    left-unit-law-add-Π-Commutative-Ringᵉ
      ( type-𝔽ᵉ Iᵉ)
      ( commutative-ring-Commutative-Ring-𝔽ᵉ ∘ᵉ Aᵉ)

  right-unit-law-add-Π-Commutative-Ring-𝔽ᵉ :
    (xᵉ : type-Π-Commutative-Ring-𝔽ᵉ) →
    add-Π-Commutative-Ring-𝔽ᵉ xᵉ zero-Π-Commutative-Ring-𝔽ᵉ ＝ᵉ xᵉ
  right-unit-law-add-Π-Commutative-Ring-𝔽ᵉ =
    right-unit-law-add-Π-Commutative-Ringᵉ
      ( type-𝔽ᵉ Iᵉ)
      ( commutative-ring-Commutative-Ring-𝔽ᵉ ∘ᵉ Aᵉ)

  commutative-add-Π-Commutative-Ring-𝔽ᵉ :
    (xᵉ yᵉ : type-Π-Commutative-Ring-𝔽ᵉ) →
    add-Π-Commutative-Ring-𝔽ᵉ xᵉ yᵉ ＝ᵉ add-Π-Commutative-Ring-𝔽ᵉ yᵉ xᵉ
  commutative-add-Π-Commutative-Ring-𝔽ᵉ =
    commutative-add-Π-Commutative-Ringᵉ
      ( type-𝔽ᵉ Iᵉ)
      ( commutative-ring-Commutative-Ring-𝔽ᵉ ∘ᵉ Aᵉ)

  mul-Π-Commutative-Ring-𝔽ᵉ :
    type-Π-Commutative-Ring-𝔽ᵉ → type-Π-Commutative-Ring-𝔽ᵉ →
    type-Π-Commutative-Ring-𝔽ᵉ
  mul-Π-Commutative-Ring-𝔽ᵉ =
    mul-Π-Commutative-Ringᵉ (type-𝔽ᵉ Iᵉ) (commutative-ring-Commutative-Ring-𝔽ᵉ ∘ᵉ Aᵉ)

  one-Π-Commutative-Ring-𝔽ᵉ : type-Π-Commutative-Ring-𝔽ᵉ
  one-Π-Commutative-Ring-𝔽ᵉ =
    one-Π-Commutative-Ringᵉ (type-𝔽ᵉ Iᵉ) (commutative-ring-Commutative-Ring-𝔽ᵉ ∘ᵉ Aᵉ)

  associative-mul-Π-Commutative-Ring-𝔽ᵉ :
    (xᵉ yᵉ zᵉ : type-Π-Commutative-Ring-𝔽ᵉ) →
    mul-Π-Commutative-Ring-𝔽ᵉ (mul-Π-Commutative-Ring-𝔽ᵉ xᵉ yᵉ) zᵉ ＝ᵉ
    mul-Π-Commutative-Ring-𝔽ᵉ xᵉ (mul-Π-Commutative-Ring-𝔽ᵉ yᵉ zᵉ)
  associative-mul-Π-Commutative-Ring-𝔽ᵉ =
    associative-mul-Π-Commutative-Ringᵉ
      ( type-𝔽ᵉ Iᵉ)
      ( commutative-ring-Commutative-Ring-𝔽ᵉ ∘ᵉ Aᵉ)

  left-unit-law-mul-Π-Commutative-Ring-𝔽ᵉ :
    (xᵉ : type-Π-Commutative-Ring-𝔽ᵉ) →
    mul-Π-Commutative-Ring-𝔽ᵉ one-Π-Commutative-Ring-𝔽ᵉ xᵉ ＝ᵉ xᵉ
  left-unit-law-mul-Π-Commutative-Ring-𝔽ᵉ =
    left-unit-law-mul-Π-Commutative-Ringᵉ
      ( type-𝔽ᵉ Iᵉ)
      ( commutative-ring-Commutative-Ring-𝔽ᵉ ∘ᵉ Aᵉ)

  right-unit-law-mul-Π-Commutative-Ring-𝔽ᵉ :
    (xᵉ : type-Π-Commutative-Ring-𝔽ᵉ) →
    mul-Π-Commutative-Ring-𝔽ᵉ xᵉ one-Π-Commutative-Ring-𝔽ᵉ ＝ᵉ xᵉ
  right-unit-law-mul-Π-Commutative-Ring-𝔽ᵉ =
    right-unit-law-mul-Π-Commutative-Ringᵉ
      ( type-𝔽ᵉ Iᵉ)
      ( commutative-ring-Commutative-Ring-𝔽ᵉ ∘ᵉ Aᵉ)

  left-distributive-mul-add-Π-Commutative-Ring-𝔽ᵉ :
    (fᵉ gᵉ hᵉ : type-Π-Commutative-Ring-𝔽ᵉ) →
    mul-Π-Commutative-Ring-𝔽ᵉ fᵉ (add-Π-Commutative-Ring-𝔽ᵉ gᵉ hᵉ) ＝ᵉ
    add-Π-Commutative-Ring-𝔽ᵉ
      ( mul-Π-Commutative-Ring-𝔽ᵉ fᵉ gᵉ)
      ( mul-Π-Commutative-Ring-𝔽ᵉ fᵉ hᵉ)
  left-distributive-mul-add-Π-Commutative-Ring-𝔽ᵉ =
    left-distributive-mul-add-Π-Commutative-Ringᵉ
      ( type-𝔽ᵉ Iᵉ)
      ( commutative-ring-Commutative-Ring-𝔽ᵉ ∘ᵉ Aᵉ)

  right-distributive-mul-add-Π-Commutative-Ring-𝔽ᵉ :
    (fᵉ gᵉ hᵉ : type-Π-Commutative-Ring-𝔽ᵉ) →
    mul-Π-Commutative-Ring-𝔽ᵉ (add-Π-Commutative-Ring-𝔽ᵉ fᵉ gᵉ) hᵉ ＝ᵉ
    add-Π-Commutative-Ring-𝔽ᵉ
      ( mul-Π-Commutative-Ring-𝔽ᵉ fᵉ hᵉ)
      ( mul-Π-Commutative-Ring-𝔽ᵉ gᵉ hᵉ)
  right-distributive-mul-add-Π-Commutative-Ring-𝔽ᵉ =
    right-distributive-mul-add-Π-Commutative-Ringᵉ
      ( type-𝔽ᵉ Iᵉ)
      ( commutative-ring-Commutative-Ring-𝔽ᵉ ∘ᵉ Aᵉ)

  left-zero-law-mul-Π-Commutative-Ring-𝔽ᵉ :
    (fᵉ : type-Π-Commutative-Ring-𝔽ᵉ) →
    mul-Π-Commutative-Ring-𝔽ᵉ zero-Π-Commutative-Ring-𝔽ᵉ fᵉ ＝ᵉ
    zero-Π-Commutative-Ring-𝔽ᵉ
  left-zero-law-mul-Π-Commutative-Ring-𝔽ᵉ =
    left-zero-law-mul-Π-Commutative-Ringᵉ
      ( type-𝔽ᵉ Iᵉ)
      ( commutative-ring-Commutative-Ring-𝔽ᵉ ∘ᵉ Aᵉ)

  right-zero-law-mul-Π-Commutative-Ring-𝔽ᵉ :
    (fᵉ : type-Π-Commutative-Ring-𝔽ᵉ) →
    mul-Π-Commutative-Ring-𝔽ᵉ fᵉ zero-Π-Commutative-Ring-𝔽ᵉ ＝ᵉ
    zero-Π-Commutative-Ring-𝔽ᵉ
  right-zero-law-mul-Π-Commutative-Ring-𝔽ᵉ =
    right-zero-law-mul-Π-Commutative-Ringᵉ
      ( type-𝔽ᵉ Iᵉ)
      ( commutative-ring-Commutative-Ring-𝔽ᵉ ∘ᵉ Aᵉ)

  commutative-mul-Π-Commutative-Ring-𝔽ᵉ :
    (fᵉ gᵉ : type-Π-Commutative-Ring-𝔽ᵉ) →
    mul-Π-Commutative-Ring-𝔽ᵉ fᵉ gᵉ ＝ᵉ mul-Π-Commutative-Ring-𝔽ᵉ gᵉ fᵉ
  commutative-mul-Π-Commutative-Ring-𝔽ᵉ =
    commutative-mul-Π-Commutative-Ringᵉ
      ( type-𝔽ᵉ Iᵉ)
      ( commutative-ring-Commutative-Ring-𝔽ᵉ ∘ᵉ Aᵉ)

  commutative-ring-Π-Commutative-Ring-𝔽ᵉ : Commutative-Ringᵉ (l1ᵉ ⊔ l2ᵉ)
  commutative-ring-Π-Commutative-Ring-𝔽ᵉ =
    Π-Commutative-Ringᵉ (type-𝔽ᵉ Iᵉ) (commutative-ring-Commutative-Ring-𝔽ᵉ ∘ᵉ Aᵉ)

  Π-Commutative-Ring-𝔽ᵉ : Commutative-Ring-𝔽ᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ Π-Commutative-Ring-𝔽ᵉ = finite-ring-Π-Commutative-Ring-𝔽ᵉ
  pr2ᵉ Π-Commutative-Ring-𝔽ᵉ = commutative-mul-Π-Commutative-Ring-𝔽ᵉ
```