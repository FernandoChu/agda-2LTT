# Finite posets

```agda
module order-theory.finite-posetsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.decidable-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.function-typesᵉ
open import foundation.propositionsᵉ
open import foundation.universe-levelsᵉ

open import order-theory.finite-preordersᵉ
open import order-theory.posetsᵉ
open import order-theory.preordersᵉ

open import univalent-combinatorics.finite-typesᵉ
```

</details>

## Definitions

Aᵉ **finiteᵉ poset**ᵉ isᵉ aᵉ [poset](order-theory.posets.mdᵉ) ofᵉ whichᵉ theᵉ underlyingᵉ
typeᵉ isᵉ [finite](univalent-combinatorics.finite-types.md),ᵉ andᵉ ofᵉ whichᵉ theᵉ
orderingᵉ relationᵉ isᵉ [decidable](foundation.decidable-relations.md).ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Pᵉ : Posetᵉ l1ᵉ l2ᵉ)
  where

  is-finite-Poset-Propᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  is-finite-Poset-Propᵉ = is-finite-Preorder-Propᵉ (preorder-Posetᵉ Pᵉ)

  is-finite-Posetᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-finite-Posetᵉ = is-finite-Preorderᵉ (preorder-Posetᵉ Pᵉ)

  is-prop-is-finite-Posetᵉ : is-propᵉ is-finite-Posetᵉ
  is-prop-is-finite-Posetᵉ = is-prop-is-finite-Preorderᵉ (preorder-Posetᵉ Pᵉ)

  is-finite-type-is-finite-Posetᵉ :
    is-finite-Posetᵉ → is-finiteᵉ (type-Posetᵉ Pᵉ)
  is-finite-type-is-finite-Posetᵉ =
    is-finite-type-is-finite-Preorderᵉ (preorder-Posetᵉ Pᵉ)

  is-decidable-leq-is-finite-Posetᵉ :
    is-finite-Posetᵉ → (xᵉ yᵉ : type-Posetᵉ Pᵉ) → is-decidableᵉ (leq-Posetᵉ Pᵉ xᵉ yᵉ)
  is-decidable-leq-is-finite-Posetᵉ =
    is-decidable-leq-is-finite-Preorderᵉ (preorder-Posetᵉ Pᵉ)

Poset-𝔽ᵉ : (l1ᵉ l2ᵉ : Level) → UUᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ)
Poset-𝔽ᵉ l1ᵉ l2ᵉ =
  Σᵉ ( Preorder-𝔽ᵉ l1ᵉ l2ᵉ)
    ( λ Pᵉ → is-antisymmetric-leq-Preorderᵉ (preorder-Preorder-𝔽ᵉ Pᵉ))

preorder-𝔽-Poset-𝔽ᵉ : {l1ᵉ l2ᵉ : Level} → Poset-𝔽ᵉ l1ᵉ l2ᵉ → Preorder-𝔽ᵉ l1ᵉ l2ᵉ
preorder-𝔽-Poset-𝔽ᵉ = pr1ᵉ

preorder-Poset-𝔽ᵉ : {l1ᵉ l2ᵉ : Level} → Poset-𝔽ᵉ l1ᵉ l2ᵉ → Preorderᵉ l1ᵉ l2ᵉ
preorder-Poset-𝔽ᵉ = preorder-Preorder-𝔽ᵉ ∘ᵉ pr1ᵉ

is-antisymmetric-leq-Poset-𝔽ᵉ :
  {l1ᵉ l2ᵉ : Level} (Pᵉ : Poset-𝔽ᵉ l1ᵉ l2ᵉ) →
  is-antisymmetric-leq-Preorderᵉ (preorder-Poset-𝔽ᵉ Pᵉ)
is-antisymmetric-leq-Poset-𝔽ᵉ = pr2ᵉ

poset-Poset-𝔽ᵉ : {l1ᵉ l2ᵉ : Level} → Poset-𝔽ᵉ l1ᵉ l2ᵉ → Posetᵉ l1ᵉ l2ᵉ
pr1ᵉ (poset-Poset-𝔽ᵉ Pᵉ) = preorder-Poset-𝔽ᵉ Pᵉ
pr2ᵉ (poset-Poset-𝔽ᵉ Pᵉ) = is-antisymmetric-leq-Poset-𝔽ᵉ Pᵉ
```