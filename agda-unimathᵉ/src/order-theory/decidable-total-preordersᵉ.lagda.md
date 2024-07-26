# Decidable total preorders

```agda
module order-theory.decidable-total-preordersᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relationsᵉ
open import foundation.cartesian-product-typesᵉ
open import foundation.coproduct-typesᵉ
open import foundation.decidable-propositionsᵉ
open import foundation.decidable-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.empty-typesᵉ
open import foundation.function-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.propositionsᵉ
open import foundation.universe-levelsᵉ

open import order-theory.decidable-preordersᵉ
open import order-theory.preordersᵉ
open import order-theory.total-preordersᵉ
```

</details>

## Idea

Aᵉ **decidableᵉ totalᵉ preorder**ᵉ isᵉ aᵉ totalᵉ preorderᵉ ofᵉ whichᵉ theᵉ inequalityᵉ
relationᵉ isᵉ decidable.ᵉ

## Definitions

```agda
Decidable-Total-Preorderᵉ : (l1ᵉ l2ᵉ : Level) → UUᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ)
Decidable-Total-Preorderᵉ l1ᵉ l2ᵉ =
  Σᵉ (Preorderᵉ l1ᵉ l2ᵉ) (λ Xᵉ → is-total-Preorderᵉ Xᵉ ×ᵉ is-decidable-leq-Preorderᵉ Xᵉ)

module _
  {l1ᵉ l2ᵉ : Level} (Xᵉ : Decidable-Total-Preorderᵉ l1ᵉ l2ᵉ)
  where

  preorder-Decidable-Total-Preorderᵉ : Preorderᵉ l1ᵉ l2ᵉ
  preorder-Decidable-Total-Preorderᵉ = pr1ᵉ Xᵉ

  is-total-Decidable-Total-Preorderᵉ :
    is-total-Preorderᵉ preorder-Decidable-Total-Preorderᵉ
  is-total-Decidable-Total-Preorderᵉ = pr1ᵉ (pr2ᵉ Xᵉ)

  is-decidable-leq-Decidable-Total-Preorderᵉ :
    is-decidable-leq-Preorderᵉ preorder-Decidable-Total-Preorderᵉ
  is-decidable-leq-Decidable-Total-Preorderᵉ = pr2ᵉ (pr2ᵉ Xᵉ)

  decidable-preorder-Decidable-Total-Preorderᵉ : Decidable-Preorderᵉ l1ᵉ l2ᵉ
  pr1ᵉ decidable-preorder-Decidable-Total-Preorderᵉ =
    preorder-Decidable-Total-Preorderᵉ
  pr2ᵉ decidable-preorder-Decidable-Total-Preorderᵉ =
    is-decidable-leq-Decidable-Total-Preorderᵉ

  type-Decidable-Total-Preorderᵉ : UUᵉ l1ᵉ
  type-Decidable-Total-Preorderᵉ =
    type-Preorderᵉ preorder-Decidable-Total-Preorderᵉ

  leq-Decidable-Total-Preorder-Propᵉ :
    (xᵉ yᵉ : type-Decidable-Total-Preorderᵉ) → Propᵉ l2ᵉ
  leq-Decidable-Total-Preorder-Propᵉ =
    leq-Preorder-Propᵉ preorder-Decidable-Total-Preorderᵉ

  leq-Decidable-Total-Preorderᵉ :
    (xᵉ yᵉ : type-Decidable-Total-Preorderᵉ) → UUᵉ l2ᵉ
  leq-Decidable-Total-Preorderᵉ =
    leq-Preorderᵉ preorder-Decidable-Total-Preorderᵉ

  is-prop-leq-Decidable-Total-Preorderᵉ :
    (xᵉ yᵉ : type-Decidable-Total-Preorderᵉ) →
    is-propᵉ (leq-Decidable-Total-Preorderᵉ xᵉ yᵉ)
  is-prop-leq-Decidable-Total-Preorderᵉ =
    is-prop-leq-Preorderᵉ preorder-Decidable-Total-Preorderᵉ

  le-Decidable-Total-Preorder-Propᵉ :
    (xᵉ yᵉ : type-Decidable-Total-Preorderᵉ) → Propᵉ (l1ᵉ ⊔ l2ᵉ)
  le-Decidable-Total-Preorder-Propᵉ =
    le-Preorder-Propᵉ preorder-Decidable-Total-Preorderᵉ

  le-Decidable-Total-Preorderᵉ :
    (xᵉ yᵉ : type-Decidable-Total-Preorderᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  le-Decidable-Total-Preorderᵉ =
    le-Preorderᵉ preorder-Decidable-Total-Preorderᵉ

  is-prop-le-Decidable-Total-Preorderᵉ :
    (xᵉ yᵉ : type-Decidable-Total-Preorderᵉ) →
    is-propᵉ (le-Decidable-Total-Preorderᵉ xᵉ yᵉ)
  is-prop-le-Decidable-Total-Preorderᵉ =
    is-prop-le-Preorderᵉ preorder-Decidable-Total-Preorderᵉ

  leq-Total-Decidable-Preorder-Decidable-Propᵉ :
    (xᵉ yᵉ : type-Decidable-Total-Preorderᵉ) → Decidable-Propᵉ l2ᵉ
  leq-Total-Decidable-Preorder-Decidable-Propᵉ =
    leq-Decidable-Preorder-Decidable-Propᵉ
      decidable-preorder-Decidable-Total-Preorderᵉ

  refl-leq-Decidable-Total-Preorderᵉ :
    is-reflexiveᵉ leq-Decidable-Total-Preorderᵉ
  refl-leq-Decidable-Total-Preorderᵉ =
    refl-leq-Preorderᵉ preorder-Decidable-Total-Preorderᵉ

  transitive-leq-Decidable-Total-Preorderᵉ :
    is-transitiveᵉ leq-Decidable-Total-Preorderᵉ
  transitive-leq-Decidable-Total-Preorderᵉ =
    transitive-leq-Preorderᵉ preorder-Decidable-Total-Preorderᵉ

  leq-or-strict-greater-Decidable-Preorderᵉ :
    (xᵉ yᵉ : type-Decidable-Total-Preorderᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  leq-or-strict-greater-Decidable-Preorderᵉ xᵉ yᵉ =
    leq-Decidable-Total-Preorderᵉ xᵉ yᵉ +ᵉ le-Decidable-Total-Preorderᵉ yᵉ xᵉ

  abstract
    helper-is-leq-or-strict-greater-Decidable-Total-Preorderᵉ :
      (xᵉ yᵉ : type-Decidable-Total-Preorderᵉ) →
      is-decidableᵉ (leq-Decidable-Total-Preorderᵉ xᵉ yᵉ) →
      leq-or-strict-greater-Decidable-Preorderᵉ xᵉ yᵉ
    helper-is-leq-or-strict-greater-Decidable-Total-Preorderᵉ xᵉ yᵉ (inlᵉ pᵉ) =
      inlᵉ pᵉ
    helper-is-leq-or-strict-greater-Decidable-Total-Preorderᵉ xᵉ yᵉ (inrᵉ pᵉ) =
      inrᵉ
        ( ( λ where reflᵉ → pᵉ (refl-leq-Decidable-Total-Preorderᵉ xᵉ)) ,ᵉ
          ( apply-universal-property-trunc-Propᵉ
            ( is-total-Decidable-Total-Preorderᵉ yᵉ xᵉ)
            ( leq-Decidable-Total-Preorder-Propᵉ yᵉ xᵉ)
            ( ind-coproductᵉ
                ( λ _ → leq-Decidable-Total-Preorderᵉ yᵉ xᵉ)
                ( idᵉ)
                ( ex-falsoᵉ ∘ᵉ pᵉ))))

  is-leq-or-strict-greater-Decidable-Total-Preorderᵉ :
    (xᵉ yᵉ : type-Decidable-Total-Preorderᵉ) →
    leq-or-strict-greater-Decidable-Preorderᵉ xᵉ yᵉ
  is-leq-or-strict-greater-Decidable-Total-Preorderᵉ xᵉ yᵉ =
    helper-is-leq-or-strict-greater-Decidable-Total-Preorderᵉ
      ( xᵉ)
      ( yᵉ)
      ( is-decidable-leq-Decidable-Total-Preorderᵉ xᵉ yᵉ)
```