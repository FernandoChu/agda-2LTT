# Subposets

```agda
module order-theory.subposetsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relationsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.universe-levelsᵉ

open import order-theory.posetsᵉ
open import order-theory.preordersᵉ
open import order-theory.subpreordersᵉ
```

</details>

## Idea

Aᵉ **subposet**ᵉ ofᵉ aᵉ posetᵉ `P`ᵉ isᵉ aᵉ subtypeᵉ ofᵉ `P`.ᵉ Byᵉ restrictionᵉ ofᵉ theᵉ
orderingᵉ onᵉ `P`,ᵉ subposetsᵉ haveᵉ againᵉ theᵉ structureᵉ ofᵉ aᵉ poset.ᵉ

## Definitions

### Subposets

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Xᵉ : Posetᵉ l1ᵉ l2ᵉ) (Sᵉ : type-Posetᵉ Xᵉ → Propᵉ l3ᵉ)
  where

  type-Subposetᵉ : UUᵉ (l1ᵉ ⊔ l3ᵉ)
  type-Subposetᵉ = type-Subpreorderᵉ (preorder-Posetᵉ Xᵉ) Sᵉ

  eq-type-Subposetᵉ :
    (xᵉ yᵉ : type-Subposetᵉ) → Idᵉ (pr1ᵉ xᵉ) (pr1ᵉ yᵉ) → Idᵉ xᵉ yᵉ
  eq-type-Subposetᵉ = eq-type-Subpreorderᵉ (preorder-Posetᵉ Xᵉ) Sᵉ

  leq-Subposet-Propᵉ : (xᵉ yᵉ : type-Subposetᵉ) → Propᵉ l2ᵉ
  leq-Subposet-Propᵉ = leq-Subpreorder-Propᵉ (preorder-Posetᵉ Xᵉ) Sᵉ

  leq-Subposetᵉ : (xᵉ yᵉ : type-Subposetᵉ) → UUᵉ l2ᵉ
  leq-Subposetᵉ = leq-Subpreorderᵉ (preorder-Posetᵉ Xᵉ) Sᵉ

  is-prop-leq-Subposetᵉ :
    (xᵉ yᵉ : type-Subposetᵉ) → is-propᵉ (leq-Subposetᵉ xᵉ yᵉ)
  is-prop-leq-Subposetᵉ = is-prop-leq-Subpreorderᵉ (preorder-Posetᵉ Xᵉ) Sᵉ

  refl-leq-Subposetᵉ : is-reflexiveᵉ leq-Subposetᵉ
  refl-leq-Subposetᵉ = refl-leq-Subpreorderᵉ (preorder-Posetᵉ Xᵉ) Sᵉ

  transitive-leq-Subposetᵉ : is-transitiveᵉ leq-Subposetᵉ
  transitive-leq-Subposetᵉ = transitive-leq-Subpreorderᵉ (preorder-Posetᵉ Xᵉ) Sᵉ

  antisymmetric-leq-Subposetᵉ : is-antisymmetricᵉ leq-Subposetᵉ
  antisymmetric-leq-Subposetᵉ xᵉ yᵉ Hᵉ Kᵉ =
    eq-type-Subposetᵉ xᵉ yᵉ (antisymmetric-leq-Posetᵉ Xᵉ (pr1ᵉ xᵉ) (pr1ᵉ yᵉ) Hᵉ Kᵉ)

  preorder-Subposetᵉ : Preorderᵉ (l1ᵉ ⊔ l3ᵉ) l2ᵉ
  pr1ᵉ preorder-Subposetᵉ = type-Subposetᵉ
  pr1ᵉ (pr2ᵉ preorder-Subposetᵉ) = leq-Subposet-Propᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ preorder-Subposetᵉ)) = refl-leq-Subposetᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ preorder-Subposetᵉ)) = transitive-leq-Subposetᵉ

  poset-Subposetᵉ : Posetᵉ (l1ᵉ ⊔ l3ᵉ) l2ᵉ
  pr1ᵉ poset-Subposetᵉ = preorder-Subposetᵉ
  pr2ᵉ poset-Subposetᵉ = antisymmetric-leq-Subposetᵉ
```

### Inclusion of sub-posets

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Xᵉ : Posetᵉ l1ᵉ l2ᵉ)
  where

  module _
    {l3ᵉ l4ᵉ : Level} (Sᵉ : type-Posetᵉ Xᵉ → Propᵉ l3ᵉ)
    (Tᵉ : type-Posetᵉ Xᵉ → Propᵉ l4ᵉ)
    where

    inclusion-Subposet-Propᵉ : Propᵉ (l1ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
    inclusion-Subposet-Propᵉ =
      inclusion-Subpreorder-Propᵉ (preorder-Posetᵉ Xᵉ) Sᵉ Tᵉ

    inclusion-Subposetᵉ : UUᵉ (l1ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
    inclusion-Subposetᵉ = inclusion-Subpreorderᵉ (preorder-Posetᵉ Xᵉ) Sᵉ Tᵉ

    is-prop-inclusion-Subposetᵉ : is-propᵉ inclusion-Subposetᵉ
    is-prop-inclusion-Subposetᵉ =
      is-prop-inclusion-Subpreorderᵉ (preorder-Posetᵉ Xᵉ) Sᵉ Tᵉ

  refl-inclusion-Subposetᵉ :
    {l3ᵉ : Level} (Sᵉ : type-Posetᵉ Xᵉ → Propᵉ l3ᵉ) →
    inclusion-Subposetᵉ Sᵉ Sᵉ
  refl-inclusion-Subposetᵉ = refl-inclusion-Subpreorderᵉ (preorder-Posetᵉ Xᵉ)

  transitive-inclusion-Subposetᵉ :
    {l3ᵉ l4ᵉ l5ᵉ : Level} (Sᵉ : type-Posetᵉ Xᵉ → Propᵉ l3ᵉ)
    (Tᵉ : type-Posetᵉ Xᵉ → Propᵉ l4ᵉ)
    (Uᵉ : type-Posetᵉ Xᵉ → Propᵉ l5ᵉ) →
    inclusion-Subposetᵉ Tᵉ Uᵉ →
    inclusion-Subposetᵉ Sᵉ Tᵉ →
    inclusion-Subposetᵉ Sᵉ Uᵉ
  transitive-inclusion-Subposetᵉ =
    transitive-inclusion-Subpreorderᵉ (preorder-Posetᵉ Xᵉ)

  sub-poset-Preorderᵉ : (lᵉ : Level) → Preorderᵉ (l1ᵉ ⊔ lsuc lᵉ) (l1ᵉ ⊔ lᵉ)
  pr1ᵉ (sub-poset-Preorderᵉ lᵉ) = type-Posetᵉ Xᵉ → Propᵉ lᵉ
  pr1ᵉ (pr2ᵉ (sub-poset-Preorderᵉ lᵉ)) = inclusion-Subposet-Propᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ (sub-poset-Preorderᵉ lᵉ))) = refl-inclusion-Subposetᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ (sub-poset-Preorderᵉ lᵉ))) = transitive-inclusion-Subposetᵉ
```