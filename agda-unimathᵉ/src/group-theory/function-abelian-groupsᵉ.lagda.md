# Function groups of abelian groups

```agda
module group-theory.function-abelian-groupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.identity-typesᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.abelian-groupsᵉ
open import group-theory.dependent-products-abelian-groupsᵉ
open import group-theory.groupsᵉ
open import group-theory.monoidsᵉ
open import group-theory.semigroupsᵉ
```

</details>

## Idea

Givenᵉ anᵉ abelianᵉ groupᵉ `G`ᵉ andᵉ aᵉ typeᵉ `X`,ᵉ theᵉ functionᵉ groupᵉ `G^X`ᵉ consistsᵉ ofᵉ
functionsᵉ fromᵉ `X`ᵉ to theᵉ underlyingᵉ typeᵉ ofᵉ `G`.ᵉ Theᵉ groupᵉ operationsᵉ areᵉ givenᵉ
pointwise.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Abᵉ l1ᵉ) (Xᵉ : UUᵉ l2ᵉ)
  where

  function-Abᵉ : Abᵉ (l1ᵉ ⊔ l2ᵉ)
  function-Abᵉ = Π-Abᵉ Xᵉ (λ _ → Aᵉ)

  group-function-Abᵉ : Groupᵉ (l1ᵉ ⊔ l2ᵉ)
  group-function-Abᵉ = group-Π-Abᵉ Xᵉ (λ _ → Aᵉ)

  semigroup-function-Abᵉ : Semigroupᵉ (l1ᵉ ⊔ l2ᵉ)
  semigroup-function-Abᵉ = semigroup-Π-Abᵉ Xᵉ (λ _ → Aᵉ)

  set-function-Abᵉ : Setᵉ (l1ᵉ ⊔ l2ᵉ)
  set-function-Abᵉ = set-Π-Abᵉ Xᵉ (λ _ → Aᵉ)

  type-function-Abᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  type-function-Abᵉ = type-Π-Abᵉ Xᵉ (λ _ → Aᵉ)

  add-function-Abᵉ :
    (fᵉ gᵉ : type-function-Abᵉ) → type-function-Abᵉ
  add-function-Abᵉ = add-Π-Abᵉ Xᵉ (λ _ → Aᵉ)

  associative-add-function-Abᵉ :
    (fᵉ gᵉ hᵉ : type-function-Abᵉ) →
    add-function-Abᵉ (add-function-Abᵉ fᵉ gᵉ) hᵉ ＝ᵉ
    add-function-Abᵉ fᵉ (add-function-Abᵉ gᵉ hᵉ)
  associative-add-function-Abᵉ = associative-add-Π-Abᵉ Xᵉ (λ _ → Aᵉ)

  zero-function-Abᵉ : type-function-Abᵉ
  zero-function-Abᵉ = zero-Π-Abᵉ Xᵉ (λ _ → Aᵉ)

  left-unit-law-add-function-Abᵉ :
    (fᵉ : type-function-Abᵉ) → add-function-Abᵉ zero-function-Abᵉ fᵉ ＝ᵉ fᵉ
  left-unit-law-add-function-Abᵉ = left-unit-law-add-Π-Abᵉ Xᵉ (λ _ → Aᵉ)

  right-unit-law-add-function-Abᵉ :
    (fᵉ : type-function-Abᵉ) → add-function-Abᵉ fᵉ zero-function-Abᵉ ＝ᵉ fᵉ
  right-unit-law-add-function-Abᵉ = right-unit-law-add-Π-Abᵉ Xᵉ (λ _ → Aᵉ)

  monoid-function-Abᵉ : Monoidᵉ (l1ᵉ ⊔ l2ᵉ)
  monoid-function-Abᵉ = monoid-Π-Abᵉ Xᵉ (λ _ → Aᵉ)

  neg-function-Abᵉ : type-function-Abᵉ → type-function-Abᵉ
  neg-function-Abᵉ = neg-Π-Abᵉ Xᵉ (λ _ → Aᵉ)

  left-inverse-law-add-function-Abᵉ :
    (fᵉ : type-function-Abᵉ) →
    add-function-Abᵉ (neg-function-Abᵉ fᵉ) fᵉ ＝ᵉ zero-function-Abᵉ
  left-inverse-law-add-function-Abᵉ =
    left-inverse-law-add-Π-Abᵉ Xᵉ (λ _ → Aᵉ)

  right-inverse-law-add-function-Abᵉ :
    (fᵉ : type-function-Abᵉ) →
    add-function-Abᵉ fᵉ (neg-function-Abᵉ fᵉ) ＝ᵉ zero-function-Abᵉ
  right-inverse-law-add-function-Abᵉ =
    right-inverse-law-add-Π-Abᵉ Xᵉ (λ _ → Aᵉ)

  commutative-add-function-Abᵉ :
    (fᵉ gᵉ : type-function-Abᵉ) →
    add-function-Abᵉ fᵉ gᵉ ＝ᵉ add-function-Abᵉ gᵉ fᵉ
  commutative-add-function-Abᵉ = commutative-add-Π-Abᵉ Xᵉ (λ _ → Aᵉ)
```