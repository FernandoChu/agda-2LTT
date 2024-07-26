# Decidable subposets

```agda
module order-theory.decidable-subposetsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relationsᵉ
open import foundation.decidable-subtypesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.universe-levelsᵉ

open import order-theory.posetsᵉ
open import order-theory.subposetsᵉ
```

</details>

## Idea

Aᵉ **decidableᵉ subposet**ᵉ ofᵉ aᵉ posetᵉ `P`ᵉ isᵉ aᵉ decidableᵉ subtypeᵉ ofᵉ `P`,ᵉ equippedᵉ
with theᵉ restrictedᵉ orderingᵉ ofᵉ `P`.ᵉ

## Definition

```agda
Decidable-Subposetᵉ :
  {l1ᵉ l2ᵉ : Level} (l3ᵉ : Level) → Posetᵉ l1ᵉ l2ᵉ → UUᵉ (l1ᵉ ⊔ lsuc l3ᵉ)
Decidable-Subposetᵉ l3ᵉ Pᵉ = decidable-subtypeᵉ l3ᵉ (type-Posetᵉ Pᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Pᵉ : Posetᵉ l1ᵉ l2ᵉ) (Sᵉ : Decidable-Subposetᵉ l3ᵉ Pᵉ)
  where

  type-Decidable-Subposetᵉ : UUᵉ (l1ᵉ ⊔ l3ᵉ)
  type-Decidable-Subposetᵉ =
    type-Subposetᵉ Pᵉ (subtype-decidable-subtypeᵉ Sᵉ)

  eq-type-Decidable-Subposetᵉ :
    (xᵉ yᵉ : type-Decidable-Subposetᵉ) → Idᵉ (pr1ᵉ xᵉ) (pr1ᵉ yᵉ) → Idᵉ xᵉ yᵉ
  eq-type-Decidable-Subposetᵉ =
    eq-type-Subposetᵉ Pᵉ (subtype-decidable-subtypeᵉ Sᵉ)

  leq-Decidable-Subposet-Propᵉ :
    (xᵉ yᵉ : type-Decidable-Subposetᵉ) → Propᵉ l2ᵉ
  leq-Decidable-Subposet-Propᵉ =
    leq-Subposet-Propᵉ Pᵉ (subtype-decidable-subtypeᵉ Sᵉ)

  leq-Decidable-Subposetᵉ : (xᵉ yᵉ : type-Decidable-Subposetᵉ) → UUᵉ l2ᵉ
  leq-Decidable-Subposetᵉ =
    leq-Subposetᵉ Pᵉ (subtype-decidable-subtypeᵉ Sᵉ)

  is-prop-leq-Decidable-Subposetᵉ :
    (xᵉ yᵉ : type-Decidable-Subposetᵉ) →
    is-propᵉ (leq-Decidable-Subposetᵉ xᵉ yᵉ)
  is-prop-leq-Decidable-Subposetᵉ =
    is-prop-leq-Subposetᵉ Pᵉ (subtype-decidable-subtypeᵉ Sᵉ)

  refl-leq-Decidable-Subposetᵉ : is-reflexiveᵉ leq-Decidable-Subposetᵉ
  refl-leq-Decidable-Subposetᵉ =
    refl-leq-Subposetᵉ Pᵉ (subtype-decidable-subtypeᵉ Sᵉ)

  transitive-leq-Decidable-Subposetᵉ : is-transitiveᵉ leq-Decidable-Subposetᵉ
  transitive-leq-Decidable-Subposetᵉ =
    transitive-leq-Subposetᵉ Pᵉ (subtype-decidable-subtypeᵉ Sᵉ)

  poset-Decidable-Subposetᵉ : Posetᵉ (l1ᵉ ⊔ l3ᵉ) l2ᵉ
  poset-Decidable-Subposetᵉ = poset-Subposetᵉ Pᵉ (subtype-decidable-subtypeᵉ Sᵉ)
```