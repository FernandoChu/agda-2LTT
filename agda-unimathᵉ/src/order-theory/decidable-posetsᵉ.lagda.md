# Decidable posets

```agda
module order-theory.decidable-posetsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relationsᵉ
open import foundation.decidable-propositionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ

open import order-theory.decidable-preordersᵉ
open import order-theory.posetsᵉ
open import order-theory.preordersᵉ
```

</details>

## Idea

Aᵉ **decidableᵉ poset**ᵉ isᵉ aᵉ posetᵉ ofᵉ whichᵉ theᵉ orderingᵉ relationᵉ isᵉ decidable.ᵉ Itᵉ
followsᵉ thatᵉ decidableᵉ posetsᵉ haveᵉ decidableᵉ equality.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Xᵉ : Posetᵉ l1ᵉ l2ᵉ)
  where

  is-decidable-leq-Poset-Propᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  is-decidable-leq-Poset-Propᵉ =
    is-decidable-leq-Preorder-Propᵉ (preorder-Posetᵉ Xᵉ)

  is-decidable-leq-Posetᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-decidable-leq-Posetᵉ = type-Propᵉ is-decidable-leq-Poset-Propᵉ

  is-prop-is-decidable-leq-Posetᵉ : is-propᵉ is-decidable-leq-Posetᵉ
  is-prop-is-decidable-leq-Posetᵉ = is-prop-type-Propᵉ is-decidable-leq-Poset-Propᵉ

Decidable-Posetᵉ : (l1ᵉ l2ᵉ : Level) → UUᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ)
Decidable-Posetᵉ l1ᵉ l2ᵉ = Σᵉ (Posetᵉ l1ᵉ l2ᵉ) is-decidable-leq-Posetᵉ

module _
  {l1ᵉ l2ᵉ : Level} (Xᵉ : Decidable-Posetᵉ l1ᵉ l2ᵉ)
  where

  poset-Decidable-Posetᵉ : Posetᵉ l1ᵉ l2ᵉ
  poset-Decidable-Posetᵉ = pr1ᵉ Xᵉ

  preorder-Decidable-Posetᵉ : Preorderᵉ l1ᵉ l2ᵉ
  preorder-Decidable-Posetᵉ = preorder-Posetᵉ poset-Decidable-Posetᵉ

  is-decidable-leq-Decidable-Posetᵉ :
    is-decidable-leq-Posetᵉ (poset-Decidable-Posetᵉ)
  is-decidable-leq-Decidable-Posetᵉ = pr2ᵉ Xᵉ

  type-Decidable-Posetᵉ : UUᵉ l1ᵉ
  type-Decidable-Posetᵉ = type-Posetᵉ poset-Decidable-Posetᵉ

  leq-Decidable-Poset-Propᵉ : (xᵉ yᵉ : type-Decidable-Posetᵉ) → Propᵉ l2ᵉ
  leq-Decidable-Poset-Propᵉ = leq-Poset-Propᵉ poset-Decidable-Posetᵉ

  leq-Decidable-Posetᵉ : (xᵉ yᵉ : type-Decidable-Posetᵉ) → UUᵉ l2ᵉ
  leq-Decidable-Posetᵉ = leq-Posetᵉ poset-Decidable-Posetᵉ

  is-prop-leq-Decidable-Posetᵉ :
    (xᵉ yᵉ : type-Decidable-Posetᵉ) → is-propᵉ (leq-Decidable-Posetᵉ xᵉ yᵉ)
  is-prop-leq-Decidable-Posetᵉ = is-prop-leq-Posetᵉ poset-Decidable-Posetᵉ

  decidable-preorder-Decidable-Posetᵉ : Decidable-Preorderᵉ l1ᵉ l2ᵉ
  pr1ᵉ decidable-preorder-Decidable-Posetᵉ = preorder-Decidable-Posetᵉ
  pr2ᵉ decidable-preorder-Decidable-Posetᵉ = is-decidable-leq-Decidable-Posetᵉ

  leq-decidable-poset-decidable-Propᵉ :
    (xᵉ yᵉ : type-Decidable-Posetᵉ) → Decidable-Propᵉ l2ᵉ
  leq-decidable-poset-decidable-Propᵉ =
    leq-Decidable-Preorder-Decidable-Propᵉ decidable-preorder-Decidable-Posetᵉ

  concatenate-eq-leq-Decidable-Posetᵉ :
    {xᵉ yᵉ zᵉ : type-Decidable-Posetᵉ} → xᵉ ＝ᵉ yᵉ →
    leq-Decidable-Posetᵉ yᵉ zᵉ → leq-Decidable-Posetᵉ xᵉ zᵉ
  concatenate-eq-leq-Decidable-Posetᵉ =
    concatenate-eq-leq-Posetᵉ poset-Decidable-Posetᵉ

  concatenate-leq-eq-Decidable-Posetᵉ :
    {xᵉ yᵉ zᵉ : type-Decidable-Posetᵉ} →
    leq-Decidable-Posetᵉ xᵉ yᵉ → yᵉ ＝ᵉ zᵉ → leq-Decidable-Posetᵉ xᵉ zᵉ
  concatenate-leq-eq-Decidable-Posetᵉ =
    concatenate-leq-eq-Posetᵉ poset-Decidable-Posetᵉ

  refl-leq-Decidable-Posetᵉ : is-reflexiveᵉ leq-Decidable-Posetᵉ
  refl-leq-Decidable-Posetᵉ = refl-leq-Posetᵉ poset-Decidable-Posetᵉ

  transitive-leq-Decidable-Posetᵉ : is-transitiveᵉ leq-Decidable-Posetᵉ
  transitive-leq-Decidable-Posetᵉ = transitive-leq-Posetᵉ poset-Decidable-Posetᵉ

  antisymmetric-leq-Decidable-Posetᵉ : is-antisymmetricᵉ leq-Decidable-Posetᵉ
  antisymmetric-leq-Decidable-Posetᵉ =
    antisymmetric-leq-Posetᵉ poset-Decidable-Posetᵉ

  is-set-type-Decidable-Posetᵉ : is-setᵉ type-Decidable-Posetᵉ
  is-set-type-Decidable-Posetᵉ = is-set-type-Posetᵉ poset-Decidable-Posetᵉ

  set-Decidable-Posetᵉ : Setᵉ l1ᵉ
  set-Decidable-Posetᵉ = set-Posetᵉ poset-Decidable-Posetᵉ
```