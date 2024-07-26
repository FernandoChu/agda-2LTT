# Decidable total orders

```agda
module order-theory.decidable-total-ordersᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relationsᵉ
open import foundation.coproduct-typesᵉ
open import foundation.decidable-propositionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ

open import order-theory.decidable-posetsᵉ
open import order-theory.decidable-total-preordersᵉ
open import order-theory.posetsᵉ
open import order-theory.preordersᵉ
open import order-theory.total-ordersᵉ
```

</details>

## Idea

Aᵉ **decidableᵉ totalᵉ order**ᵉ isᵉ aᵉ [totalᵉ order](order-theory.total-orders.mdᵉ) ofᵉ
whichᵉ theᵉ inequalityᵉ [relation](foundation.binary-relations.mdᵉ) isᵉ
[decidable](foundation.decidable-relations.md).ᵉ

## Definitions

### The predicate on posets of being decidable total orders

```agda
is-decidable-total-prop-Posetᵉ : {l1ᵉ l2ᵉ : Level} → Posetᵉ l1ᵉ l2ᵉ → Propᵉ (l1ᵉ ⊔ l2ᵉ)
is-decidable-total-prop-Posetᵉ Pᵉ =
  product-Propᵉ (is-total-Poset-Propᵉ Pᵉ) (is-decidable-leq-Poset-Propᵉ Pᵉ)

is-decidable-total-Posetᵉ : {l1ᵉ l2ᵉ : Level} → Posetᵉ l1ᵉ l2ᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
is-decidable-total-Posetᵉ Pᵉ = type-Propᵉ (is-decidable-total-prop-Posetᵉ Pᵉ)

is-prop-is-decidable-total-Posetᵉ :
  {l1ᵉ l2ᵉ : Level} (Pᵉ : Posetᵉ l1ᵉ l2ᵉ) → is-propᵉ (is-decidable-total-Posetᵉ Pᵉ)
is-prop-is-decidable-total-Posetᵉ Pᵉ =
  is-prop-type-Propᵉ (is-decidable-total-prop-Posetᵉ Pᵉ)
```

### The type of decidable total orders

```agda
Decidable-Total-Orderᵉ : (l1ᵉ l2ᵉ : Level) → UUᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ)
Decidable-Total-Orderᵉ l1ᵉ l2ᵉ = Σᵉ (Posetᵉ l1ᵉ l2ᵉ) (is-decidable-total-Posetᵉ)

module _
  {l1ᵉ l2ᵉ : Level} (Pᵉ : Decidable-Total-Orderᵉ l1ᵉ l2ᵉ)
  where

  poset-Decidable-Total-Orderᵉ : Posetᵉ l1ᵉ l2ᵉ
  poset-Decidable-Total-Orderᵉ = pr1ᵉ Pᵉ

  is-total-poset-Decidable-Total-Orderᵉ :
    is-total-Posetᵉ (poset-Decidable-Total-Orderᵉ)
  is-total-poset-Decidable-Total-Orderᵉ = pr1ᵉ (pr2ᵉ Pᵉ)

  is-decidable-poset-Decidable-Total-Orderᵉ :
    is-decidable-leq-Posetᵉ (poset-Decidable-Total-Orderᵉ)
  is-decidable-poset-Decidable-Total-Orderᵉ = pr2ᵉ (pr2ᵉ Pᵉ)

  type-Decidable-Total-Orderᵉ : UUᵉ l1ᵉ
  type-Decidable-Total-Orderᵉ = type-Posetᵉ poset-Decidable-Total-Orderᵉ

  leq-Decidable-Total-Order-Propᵉ :
    (xᵉ yᵉ : type-Decidable-Total-Orderᵉ) → Propᵉ l2ᵉ
  leq-Decidable-Total-Order-Propᵉ = leq-Poset-Propᵉ poset-Decidable-Total-Orderᵉ

  leq-Decidable-Total-Orderᵉ :
    (xᵉ yᵉ : type-Decidable-Total-Orderᵉ) → UUᵉ l2ᵉ
  leq-Decidable-Total-Orderᵉ = leq-Posetᵉ poset-Decidable-Total-Orderᵉ

  is-prop-leq-Decidable-Total-Orderᵉ :
    (xᵉ yᵉ : type-Decidable-Total-Orderᵉ) →
    is-propᵉ (leq-Decidable-Total-Orderᵉ xᵉ yᵉ)
  is-prop-leq-Decidable-Total-Orderᵉ =
    is-prop-leq-Posetᵉ poset-Decidable-Total-Orderᵉ

  le-Decidable-Total-Order-Propᵉ :
    (xᵉ yᵉ : type-Decidable-Total-Orderᵉ) → Propᵉ (l1ᵉ ⊔ l2ᵉ)
  le-Decidable-Total-Order-Propᵉ =
    le-Poset-Propᵉ poset-Decidable-Total-Orderᵉ

  le-Decidable-Total-Orderᵉ :
    (xᵉ yᵉ : type-Decidable-Total-Orderᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  le-Decidable-Total-Orderᵉ =
    le-Posetᵉ poset-Decidable-Total-Orderᵉ

  is-prop-le-Decidable-Total-Orderᵉ :
    (xᵉ yᵉ : type-Decidable-Total-Orderᵉ) →
    is-propᵉ (le-Decidable-Total-Orderᵉ xᵉ yᵉ)
  is-prop-le-Decidable-Total-Orderᵉ =
    is-prop-le-Posetᵉ poset-Decidable-Total-Orderᵉ

  decidable-poset-Decidable-Total-Orderᵉ : Decidable-Posetᵉ l1ᵉ l2ᵉ
  pr1ᵉ decidable-poset-Decidable-Total-Orderᵉ = poset-Decidable-Total-Orderᵉ
  pr2ᵉ decidable-poset-Decidable-Total-Orderᵉ =
    is-decidable-poset-Decidable-Total-Orderᵉ

  leq-total-decidable-poset-decidable-Propᵉ :
    (xᵉ yᵉ : type-Decidable-Total-Orderᵉ) → Decidable-Propᵉ l2ᵉ
  leq-total-decidable-poset-decidable-Propᵉ =
    leq-decidable-poset-decidable-Propᵉ decidable-poset-Decidable-Total-Orderᵉ

  concatenate-eq-leq-Decidable-Total-Orderᵉ :
    {xᵉ yᵉ zᵉ : type-Decidable-Total-Orderᵉ} → xᵉ ＝ᵉ yᵉ →
    leq-Decidable-Total-Orderᵉ yᵉ zᵉ → leq-Decidable-Total-Orderᵉ xᵉ zᵉ
  concatenate-eq-leq-Decidable-Total-Orderᵉ =
    concatenate-eq-leq-Posetᵉ poset-Decidable-Total-Orderᵉ

  concatenate-leq-eq-Decidable-Total-Orderᵉ :
    {xᵉ yᵉ zᵉ : type-Decidable-Total-Orderᵉ} →
    leq-Decidable-Total-Orderᵉ xᵉ yᵉ → yᵉ ＝ᵉ zᵉ → leq-Decidable-Total-Orderᵉ xᵉ zᵉ
  concatenate-leq-eq-Decidable-Total-Orderᵉ =
    concatenate-leq-eq-Posetᵉ poset-Decidable-Total-Orderᵉ

  refl-leq-Decidable-Total-Orderᵉ : is-reflexiveᵉ leq-Decidable-Total-Orderᵉ
  refl-leq-Decidable-Total-Orderᵉ =
    refl-leq-Posetᵉ poset-Decidable-Total-Orderᵉ

  transitive-leq-Decidable-Total-Orderᵉ : is-transitiveᵉ leq-Decidable-Total-Orderᵉ
  transitive-leq-Decidable-Total-Orderᵉ =
    transitive-leq-Posetᵉ poset-Decidable-Total-Orderᵉ

  preorder-Decidable-Total-Orderᵉ : Preorderᵉ l1ᵉ l2ᵉ
  preorder-Decidable-Total-Orderᵉ = preorder-Posetᵉ poset-Decidable-Total-Orderᵉ

  decidable-total-preorder-Decidable-Total-Orderᵉ :
    Decidable-Total-Preorderᵉ l1ᵉ l2ᵉ
  pr1ᵉ decidable-total-preorder-Decidable-Total-Orderᵉ =
    preorder-Decidable-Total-Orderᵉ
  pr1ᵉ (pr2ᵉ decidable-total-preorder-Decidable-Total-Orderᵉ) =
    is-total-poset-Decidable-Total-Orderᵉ
  pr2ᵉ (pr2ᵉ decidable-total-preorder-Decidable-Total-Orderᵉ) =
    is-decidable-poset-Decidable-Total-Orderᵉ

  leq-or-strict-greater-Decidable-Posetᵉ :
    (xᵉ yᵉ : type-Decidable-Total-Orderᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  leq-or-strict-greater-Decidable-Posetᵉ =
    leq-or-strict-greater-Decidable-Preorderᵉ
      decidable-total-preorder-Decidable-Total-Orderᵉ

  is-leq-or-strict-greater-Decidable-Total-Orderᵉ :
    (xᵉ yᵉ : type-Decidable-Total-Orderᵉ) →
    leq-or-strict-greater-Decidable-Posetᵉ xᵉ yᵉ
  is-leq-or-strict-greater-Decidable-Total-Orderᵉ =
    is-leq-or-strict-greater-Decidable-Total-Preorderᵉ
      decidable-total-preorder-Decidable-Total-Orderᵉ

  antisymmetric-leq-Decidable-Total-Orderᵉ :
    (xᵉ yᵉ : type-Decidable-Total-Orderᵉ) →
    leq-Decidable-Total-Orderᵉ xᵉ yᵉ → leq-Decidable-Total-Orderᵉ yᵉ xᵉ → Idᵉ xᵉ yᵉ
  antisymmetric-leq-Decidable-Total-Orderᵉ =
    antisymmetric-leq-Posetᵉ poset-Decidable-Total-Orderᵉ

  is-prop-leq-or-strict-greater-Decidable-Total-Orderᵉ :
    (xᵉ yᵉ : type-Decidable-Total-Orderᵉ) →
    is-propᵉ (leq-or-strict-greater-Decidable-Posetᵉ xᵉ yᵉ)
  is-prop-leq-or-strict-greater-Decidable-Total-Orderᵉ xᵉ yᵉ =
    is-prop-coproductᵉ
      ( λ pᵉ qᵉ →
        pr1ᵉ qᵉ (invᵉ (antisymmetric-leq-Decidable-Total-Orderᵉ xᵉ yᵉ pᵉ (pr2ᵉ qᵉ))))
      ( is-prop-leq-Decidable-Total-Orderᵉ xᵉ yᵉ)
      ( is-prop-le-Decidable-Total-Orderᵉ yᵉ xᵉ)

  is-set-type-Decidable-Total-Orderᵉ : is-setᵉ type-Decidable-Total-Orderᵉ
  is-set-type-Decidable-Total-Orderᵉ =
    is-set-type-Posetᵉ poset-Decidable-Total-Orderᵉ

  set-Decidable-Total-Orderᵉ : Setᵉ l1ᵉ
  set-Decidable-Total-Orderᵉ = set-Posetᵉ poset-Decidable-Total-Orderᵉ
```