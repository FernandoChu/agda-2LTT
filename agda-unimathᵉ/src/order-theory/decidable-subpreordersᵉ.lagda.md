# Decidable subpreorders

```agda
module order-theory.decidable-subpreordersᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relationsᵉ
open import foundation.decidable-subtypesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.universe-levelsᵉ

open import order-theory.preordersᵉ
open import order-theory.subpreordersᵉ
```

</details>

## Idea

Aᵉ **decidableᵉ subpreorder**ᵉ ofᵉ `P`ᵉ isᵉ aᵉ decidableᵉ subtypeᵉ ofᵉ `P`ᵉ equippedᵉ with
theᵉ restrictedᵉ orderingᵉ ofᵉ `P`.ᵉ

## Definition

```agda
Decidable-Subpreorderᵉ :
  {l1ᵉ l2ᵉ : Level} (l3ᵉ : Level) → Preorderᵉ l1ᵉ l2ᵉ → UUᵉ (l1ᵉ ⊔ lsuc l3ᵉ)
Decidable-Subpreorderᵉ l3ᵉ Pᵉ = decidable-subtypeᵉ l3ᵉ (type-Preorderᵉ Pᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Pᵉ : Preorderᵉ l1ᵉ l2ᵉ) (Sᵉ : Decidable-Subpreorderᵉ l3ᵉ Pᵉ)
  where

  type-Decidable-Subpreorderᵉ : UUᵉ (l1ᵉ ⊔ l3ᵉ)
  type-Decidable-Subpreorderᵉ =
    type-Subpreorderᵉ Pᵉ (subtype-decidable-subtypeᵉ Sᵉ)

  eq-type-Decidable-Subpreorderᵉ :
    (xᵉ yᵉ : type-Decidable-Subpreorderᵉ) → Idᵉ (pr1ᵉ xᵉ) (pr1ᵉ yᵉ) → Idᵉ xᵉ yᵉ
  eq-type-Decidable-Subpreorderᵉ =
    eq-type-Subpreorderᵉ Pᵉ (subtype-decidable-subtypeᵉ Sᵉ)

  leq-Decidable-Subpreorder-Propᵉ :
    (xᵉ yᵉ : type-Decidable-Subpreorderᵉ) → Propᵉ l2ᵉ
  leq-Decidable-Subpreorder-Propᵉ =
    leq-Subpreorder-Propᵉ Pᵉ (subtype-decidable-subtypeᵉ Sᵉ)

  leq-Decidable-Subpreorderᵉ : (xᵉ yᵉ : type-Decidable-Subpreorderᵉ) → UUᵉ l2ᵉ
  leq-Decidable-Subpreorderᵉ =
    leq-Subpreorderᵉ Pᵉ (subtype-decidable-subtypeᵉ Sᵉ)

  is-prop-leq-Decidable-Subpreorderᵉ :
    (xᵉ yᵉ : type-Decidable-Subpreorderᵉ) →
    is-propᵉ (leq-Decidable-Subpreorderᵉ xᵉ yᵉ)
  is-prop-leq-Decidable-Subpreorderᵉ =
    is-prop-leq-Subpreorderᵉ Pᵉ (subtype-decidable-subtypeᵉ Sᵉ)

  refl-leq-Decidable-Subpreorderᵉ : is-reflexiveᵉ leq-Decidable-Subpreorderᵉ
  refl-leq-Decidable-Subpreorderᵉ =
    refl-leq-Subpreorderᵉ Pᵉ (subtype-decidable-subtypeᵉ Sᵉ)

  transitive-leq-Decidable-Subpreorderᵉ : is-transitiveᵉ leq-Decidable-Subpreorderᵉ
  transitive-leq-Decidable-Subpreorderᵉ =
    transitive-leq-Subpreorderᵉ Pᵉ (subtype-decidable-subtypeᵉ Sᵉ)

  preorder-Decidable-Subpreorderᵉ : Preorderᵉ (l1ᵉ ⊔ l3ᵉ) l2ᵉ
  preorder-Decidable-Subpreorderᵉ =
    preorder-Subpreorderᵉ Pᵉ (subtype-decidable-subtypeᵉ Sᵉ)
```