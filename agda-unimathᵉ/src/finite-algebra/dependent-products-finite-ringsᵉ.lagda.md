# Dependent products of finite rings

```agda
module finite-algebra.dependent-products-finite-ringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import finite-algebra.finite-ringsᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.function-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.abelian-groupsᵉ
open import group-theory.groupsᵉ
open import group-theory.monoidsᵉ
open import group-theory.semigroupsᵉ

open import ring-theory.dependent-products-ringsᵉ
open import ring-theory.ringsᵉ
open import ring-theory.semiringsᵉ

open import univalent-combinatorics.dependent-function-typesᵉ
open import univalent-combinatorics.finite-typesᵉ
```

</details>

## Idea

Givenᵉ aᵉ familyᵉ ofᵉ finiteᵉ ringsᵉ `Aᵉ i`ᵉ indexedᵉ byᵉ aᵉ finiteᵉ typeᵉ `iᵉ : I`,ᵉ theirᵉ
**dependentᵉ product**ᵉ `Π(i:I),ᵉ Aᵉ i`ᵉ isᵉ againᵉ aᵉ finiteᵉ ring.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Iᵉ : 𝔽ᵉ l1ᵉ) (Aᵉ : type-𝔽ᵉ Iᵉ → Ring-𝔽ᵉ l2ᵉ)
  where

  semiring-Π-Ring-𝔽ᵉ : Semiringᵉ (l1ᵉ ⊔ l2ᵉ)
  semiring-Π-Ring-𝔽ᵉ = semiring-Π-Ringᵉ (type-𝔽ᵉ Iᵉ) (ring-Ring-𝔽ᵉ ∘ᵉ Aᵉ)

  ab-Π-Ring-𝔽ᵉ : Abᵉ (l1ᵉ ⊔ l2ᵉ)
  ab-Π-Ring-𝔽ᵉ = ab-Π-Ringᵉ (type-𝔽ᵉ Iᵉ) (ring-Ring-𝔽ᵉ ∘ᵉ Aᵉ)

  group-Π-Ring-𝔽ᵉ : Groupᵉ (l1ᵉ ⊔ l2ᵉ)
  group-Π-Ring-𝔽ᵉ = group-Π-Ringᵉ (type-𝔽ᵉ Iᵉ) (ring-Ring-𝔽ᵉ ∘ᵉ Aᵉ)

  semigroup-Π-Ring-𝔽ᵉ : Semigroupᵉ (l1ᵉ ⊔ l2ᵉ)
  semigroup-Π-Ring-𝔽ᵉ = semigroup-Π-Ringᵉ (type-𝔽ᵉ Iᵉ) (ring-Ring-𝔽ᵉ ∘ᵉ Aᵉ)

  multiplicative-monoid-Π-Ring-𝔽ᵉ : Monoidᵉ (l1ᵉ ⊔ l2ᵉ)
  multiplicative-monoid-Π-Ring-𝔽ᵉ =
    multiplicative-monoid-Π-Ringᵉ (type-𝔽ᵉ Iᵉ) (ring-Ring-𝔽ᵉ ∘ᵉ Aᵉ)

  set-Π-Ring-𝔽ᵉ : Setᵉ (l1ᵉ ⊔ l2ᵉ)
  set-Π-Ring-𝔽ᵉ = set-Π-Ringᵉ (type-𝔽ᵉ Iᵉ) (ring-Ring-𝔽ᵉ ∘ᵉ Aᵉ)

  type-Π-Ring-𝔽ᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  type-Π-Ring-𝔽ᵉ = type-Π-Ringᵉ (type-𝔽ᵉ Iᵉ) (ring-Ring-𝔽ᵉ ∘ᵉ Aᵉ)

  is-finite-type-Π-Ring-𝔽ᵉ : is-finiteᵉ (type-Π-Ring-𝔽ᵉ)
  is-finite-type-Π-Ring-𝔽ᵉ =
    is-finite-Πᵉ (is-finite-type-𝔽ᵉ Iᵉ) (λ iᵉ → is-finite-type-Ring-𝔽ᵉ (Aᵉ iᵉ))

  finite-type-Π-Ring-𝔽ᵉ : 𝔽ᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ finite-type-Π-Ring-𝔽ᵉ = type-Π-Ring-𝔽ᵉ
  pr2ᵉ finite-type-Π-Ring-𝔽ᵉ = is-finite-type-Π-Ring-𝔽ᵉ

  is-set-type-Π-Ring-𝔽ᵉ : is-setᵉ type-Π-Ring-𝔽ᵉ
  is-set-type-Π-Ring-𝔽ᵉ = is-set-type-Π-Ringᵉ (type-𝔽ᵉ Iᵉ) (ring-Ring-𝔽ᵉ ∘ᵉ Aᵉ)

  add-Π-Ring-𝔽ᵉ : type-Π-Ring-𝔽ᵉ → type-Π-Ring-𝔽ᵉ → type-Π-Ring-𝔽ᵉ
  add-Π-Ring-𝔽ᵉ = add-Π-Ringᵉ (type-𝔽ᵉ Iᵉ) (ring-Ring-𝔽ᵉ ∘ᵉ Aᵉ)

  zero-Π-Ring-𝔽ᵉ : type-Π-Ring-𝔽ᵉ
  zero-Π-Ring-𝔽ᵉ = zero-Π-Ringᵉ (type-𝔽ᵉ Iᵉ) (ring-Ring-𝔽ᵉ ∘ᵉ Aᵉ)

  neg-Π-Ring-𝔽ᵉ : type-Π-Ring-𝔽ᵉ → type-Π-Ring-𝔽ᵉ
  neg-Π-Ring-𝔽ᵉ = neg-Π-Ringᵉ (type-𝔽ᵉ Iᵉ) (ring-Ring-𝔽ᵉ ∘ᵉ Aᵉ)

  associative-add-Π-Ring-𝔽ᵉ :
    (xᵉ yᵉ zᵉ : type-Π-Ring-𝔽ᵉ) →
    Idᵉ (add-Π-Ring-𝔽ᵉ (add-Π-Ring-𝔽ᵉ xᵉ yᵉ) zᵉ) (add-Π-Ring-𝔽ᵉ xᵉ (add-Π-Ring-𝔽ᵉ yᵉ zᵉ))
  associative-add-Π-Ring-𝔽ᵉ =
    associative-add-Π-Ringᵉ (type-𝔽ᵉ Iᵉ) (ring-Ring-𝔽ᵉ ∘ᵉ Aᵉ)

  left-unit-law-add-Π-Ring-𝔽ᵉ :
    (xᵉ : type-Π-Ring-𝔽ᵉ) → Idᵉ (add-Π-Ring-𝔽ᵉ zero-Π-Ring-𝔽ᵉ xᵉ) xᵉ
  left-unit-law-add-Π-Ring-𝔽ᵉ =
    left-unit-law-add-Π-Ringᵉ (type-𝔽ᵉ Iᵉ) (ring-Ring-𝔽ᵉ ∘ᵉ Aᵉ)

  right-unit-law-add-Π-Ring-𝔽ᵉ :
    (xᵉ : type-Π-Ring-𝔽ᵉ) → Idᵉ (add-Π-Ring-𝔽ᵉ xᵉ zero-Π-Ring-𝔽ᵉ) xᵉ
  right-unit-law-add-Π-Ring-𝔽ᵉ =
    right-unit-law-add-Π-Ringᵉ (type-𝔽ᵉ Iᵉ) (ring-Ring-𝔽ᵉ ∘ᵉ Aᵉ)

  left-inverse-law-add-Π-Ring-𝔽ᵉ :
    (xᵉ : type-Π-Ring-𝔽ᵉ) → Idᵉ (add-Π-Ring-𝔽ᵉ (neg-Π-Ring-𝔽ᵉ xᵉ) xᵉ) zero-Π-Ring-𝔽ᵉ
  left-inverse-law-add-Π-Ring-𝔽ᵉ =
    left-inverse-law-add-Π-Ringᵉ (type-𝔽ᵉ Iᵉ) (ring-Ring-𝔽ᵉ ∘ᵉ Aᵉ)

  right-inverse-law-add-Π-Ring-𝔽ᵉ :
    (xᵉ : type-Π-Ring-𝔽ᵉ) → Idᵉ (add-Π-Ring-𝔽ᵉ xᵉ (neg-Π-Ring-𝔽ᵉ xᵉ)) zero-Π-Ring-𝔽ᵉ
  right-inverse-law-add-Π-Ring-𝔽ᵉ =
    right-inverse-law-add-Π-Ringᵉ (type-𝔽ᵉ Iᵉ) (ring-Ring-𝔽ᵉ ∘ᵉ Aᵉ)

  commutative-add-Π-Ring-𝔽ᵉ :
    (xᵉ yᵉ : type-Π-Ring-𝔽ᵉ) → Idᵉ (add-Π-Ring-𝔽ᵉ xᵉ yᵉ) (add-Π-Ring-𝔽ᵉ yᵉ xᵉ)
  commutative-add-Π-Ring-𝔽ᵉ =
    commutative-add-Π-Ringᵉ (type-𝔽ᵉ Iᵉ) (ring-Ring-𝔽ᵉ ∘ᵉ Aᵉ)

  mul-Π-Ring-𝔽ᵉ : type-Π-Ring-𝔽ᵉ → type-Π-Ring-𝔽ᵉ → type-Π-Ring-𝔽ᵉ
  mul-Π-Ring-𝔽ᵉ = mul-Π-Ringᵉ (type-𝔽ᵉ Iᵉ) (ring-Ring-𝔽ᵉ ∘ᵉ Aᵉ)

  one-Π-Ring-𝔽ᵉ : type-Π-Ring-𝔽ᵉ
  one-Π-Ring-𝔽ᵉ = one-Π-Ringᵉ (type-𝔽ᵉ Iᵉ) (ring-Ring-𝔽ᵉ ∘ᵉ Aᵉ)

  associative-mul-Π-Ring-𝔽ᵉ :
    (xᵉ yᵉ zᵉ : type-Π-Ring-𝔽ᵉ) →
    Idᵉ (mul-Π-Ring-𝔽ᵉ (mul-Π-Ring-𝔽ᵉ xᵉ yᵉ) zᵉ) (mul-Π-Ring-𝔽ᵉ xᵉ (mul-Π-Ring-𝔽ᵉ yᵉ zᵉ))
  associative-mul-Π-Ring-𝔽ᵉ =
    associative-mul-Π-Ringᵉ (type-𝔽ᵉ Iᵉ) (ring-Ring-𝔽ᵉ ∘ᵉ Aᵉ)

  left-unit-law-mul-Π-Ring-𝔽ᵉ :
    (xᵉ : type-Π-Ring-𝔽ᵉ) → Idᵉ (mul-Π-Ring-𝔽ᵉ one-Π-Ring-𝔽ᵉ xᵉ) xᵉ
  left-unit-law-mul-Π-Ring-𝔽ᵉ =
    left-unit-law-mul-Π-Ringᵉ (type-𝔽ᵉ Iᵉ) (ring-Ring-𝔽ᵉ ∘ᵉ Aᵉ)

  right-unit-law-mul-Π-Ring-𝔽ᵉ :
    (xᵉ : type-Π-Ring-𝔽ᵉ) → Idᵉ (mul-Π-Ring-𝔽ᵉ xᵉ one-Π-Ring-𝔽ᵉ) xᵉ
  right-unit-law-mul-Π-Ring-𝔽ᵉ =
    right-unit-law-mul-Π-Ringᵉ (type-𝔽ᵉ Iᵉ) (ring-Ring-𝔽ᵉ ∘ᵉ Aᵉ)

  left-distributive-mul-add-Π-Ring-𝔽ᵉ :
    (fᵉ gᵉ hᵉ : type-Π-Ring-𝔽ᵉ) →
    mul-Π-Ring-𝔽ᵉ fᵉ (add-Π-Ring-𝔽ᵉ gᵉ hᵉ) ＝ᵉ
    add-Π-Ring-𝔽ᵉ (mul-Π-Ring-𝔽ᵉ fᵉ gᵉ) (mul-Π-Ring-𝔽ᵉ fᵉ hᵉ)
  left-distributive-mul-add-Π-Ring-𝔽ᵉ =
    left-distributive-mul-add-Π-Ringᵉ (type-𝔽ᵉ Iᵉ) (ring-Ring-𝔽ᵉ ∘ᵉ Aᵉ)

  right-distributive-mul-add-Π-Ring-𝔽ᵉ :
    (fᵉ gᵉ hᵉ : type-Π-Ring-𝔽ᵉ) →
    Idᵉ
      ( mul-Π-Ring-𝔽ᵉ (add-Π-Ring-𝔽ᵉ fᵉ gᵉ) hᵉ)
      ( add-Π-Ring-𝔽ᵉ (mul-Π-Ring-𝔽ᵉ fᵉ hᵉ) (mul-Π-Ring-𝔽ᵉ gᵉ hᵉ))
  right-distributive-mul-add-Π-Ring-𝔽ᵉ =
    right-distributive-mul-add-Π-Ringᵉ (type-𝔽ᵉ Iᵉ) (ring-Ring-𝔽ᵉ ∘ᵉ Aᵉ)

  ring-Π-Ring-𝔽ᵉ : Ringᵉ (l1ᵉ ⊔ l2ᵉ)
  ring-Π-Ring-𝔽ᵉ = Π-Ringᵉ (type-𝔽ᵉ Iᵉ) (ring-Ring-𝔽ᵉ ∘ᵉ Aᵉ)

  Π-Ring-𝔽ᵉ : Ring-𝔽ᵉ (l1ᵉ ⊔ l2ᵉ)
  Π-Ring-𝔽ᵉ = finite-ring-is-finite-Ringᵉ ring-Π-Ring-𝔽ᵉ is-finite-type-Π-Ring-𝔽ᵉ
```