# Decidable preorders

```agda
module order-theory.decidable-preordersᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relationsᵉ
open import foundation.decidable-propositionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.propositionsᵉ
open import foundation.universe-levelsᵉ

open import order-theory.preordersᵉ
```

</details>

## Idea

Aᵉ **decidableᵉ preorder**ᵉ isᵉ aᵉ preorderᵉ ofᵉ whichᵉ theᵉ orderingᵉ relationᵉ isᵉ
decidable.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Xᵉ : Preorderᵉ l1ᵉ l2ᵉ)
  where

  is-decidable-leq-Preorder-Propᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  is-decidable-leq-Preorder-Propᵉ =
    Π-Propᵉ
      ( type-Preorderᵉ Xᵉ)
      ( λ xᵉ →
        Π-Propᵉ
          ( type-Preorderᵉ Xᵉ)
          ( λ yᵉ → is-decidable-Propᵉ (leq-Preorder-Propᵉ Xᵉ xᵉ yᵉ)))

  is-decidable-leq-Preorderᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-decidable-leq-Preorderᵉ = type-Propᵉ is-decidable-leq-Preorder-Propᵉ

  is-prop-is-decidable-leq-Preorderᵉ : is-propᵉ is-decidable-leq-Preorderᵉ
  is-prop-is-decidable-leq-Preorderᵉ =
    is-prop-type-Propᵉ is-decidable-leq-Preorder-Propᵉ

Decidable-Preorderᵉ : (l1ᵉ l2ᵉ : Level) → UUᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ)
Decidable-Preorderᵉ l1ᵉ l2ᵉ = Σᵉ (Preorderᵉ l1ᵉ l2ᵉ) is-decidable-leq-Preorderᵉ

module _
  {l1ᵉ l2ᵉ : Level} (Xᵉ : Decidable-Preorderᵉ l1ᵉ l2ᵉ)
  where

  preorder-Decidable-Preorderᵉ : Preorderᵉ l1ᵉ l2ᵉ
  preorder-Decidable-Preorderᵉ = pr1ᵉ Xᵉ

  is-decidable-leq-Decidable-Preorderᵉ :
    is-decidable-leq-Preorderᵉ preorder-Decidable-Preorderᵉ
  is-decidable-leq-Decidable-Preorderᵉ = pr2ᵉ Xᵉ

  type-Decidable-Preorderᵉ : UUᵉ l1ᵉ
  type-Decidable-Preorderᵉ = type-Preorderᵉ preorder-Decidable-Preorderᵉ

  leq-Decidable-Preorder-Propᵉ :
    (xᵉ yᵉ : type-Decidable-Preorderᵉ) → Propᵉ l2ᵉ
  leq-Decidable-Preorder-Propᵉ =
    leq-Preorder-Propᵉ preorder-Decidable-Preorderᵉ

  leq-Decidable-Preorderᵉ :
    (xᵉ yᵉ : type-Decidable-Preorderᵉ) → UUᵉ l2ᵉ
  leq-Decidable-Preorderᵉ = leq-Preorderᵉ preorder-Decidable-Preorderᵉ

  is-prop-leq-Decidable-Preorderᵉ :
    (xᵉ yᵉ : type-Decidable-Preorderᵉ) →
    is-propᵉ (leq-Decidable-Preorderᵉ xᵉ yᵉ)
  is-prop-leq-Decidable-Preorderᵉ =
    is-prop-leq-Preorderᵉ preorder-Decidable-Preorderᵉ

  leq-Decidable-Preorder-Decidable-Propᵉ :
    (xᵉ yᵉ : type-Decidable-Preorderᵉ) → Decidable-Propᵉ l2ᵉ
  pr1ᵉ (leq-Decidable-Preorder-Decidable-Propᵉ xᵉ yᵉ) =
    leq-Decidable-Preorderᵉ xᵉ yᵉ
  pr1ᵉ (pr2ᵉ (leq-Decidable-Preorder-Decidable-Propᵉ xᵉ yᵉ)) =
    is-prop-leq-Decidable-Preorderᵉ xᵉ yᵉ
  pr2ᵉ (pr2ᵉ (leq-Decidable-Preorder-Decidable-Propᵉ xᵉ yᵉ)) =
    is-decidable-leq-Decidable-Preorderᵉ xᵉ yᵉ

  refl-leq-Decidable-Preorderᵉ : is-reflexiveᵉ leq-Decidable-Preorderᵉ
  refl-leq-Decidable-Preorderᵉ = refl-leq-Preorderᵉ preorder-Decidable-Preorderᵉ

  transitive-leq-Decidable-Preorderᵉ : is-transitiveᵉ leq-Decidable-Preorderᵉ
  transitive-leq-Decidable-Preorderᵉ =
    transitive-leq-Preorderᵉ preorder-Decidable-Preorderᵉ
```