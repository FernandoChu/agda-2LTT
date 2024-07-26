# Finite preorders

```agda
module order-theory.finite-preordersᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.binary-relationsᵉ
open import foundation.cartesian-product-typesᵉ
open import foundation.decidable-equalityᵉ
open import foundation.decidable-propositionsᵉ
open import foundation.decidable-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.mere-equivalencesᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ

open import order-theory.decidable-preordersᵉ
open import order-theory.decidable-subpreordersᵉ
open import order-theory.preordersᵉ

open import univalent-combinatorics.decidable-subtypesᵉ
open import univalent-combinatorics.equality-finite-typesᵉ
open import univalent-combinatorics.finite-typesᵉ
open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Weᵉ sayᵉ thatᵉ aᵉ [preorder](order-theory.preorders.mdᵉ) `P`ᵉ isᵉ **finite**ᵉ ifᵉ `P`ᵉ hasᵉ
[finitelyᵉ manyᵉ elements](univalent-combinatorics.finite-types.mdᵉ) andᵉ theᵉ
orderingᵉ relationᵉ onᵉ `P`ᵉ isᵉ [decidable](foundation.decidable-relations.md).ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Pᵉ : Preorderᵉ l1ᵉ l2ᵉ)
  where

  is-finite-Preorder-Propᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  is-finite-Preorder-Propᵉ =
    product-Propᵉ
      ( is-finite-Propᵉ (type-Preorderᵉ Pᵉ))
      ( is-decidable-leq-Preorder-Propᵉ Pᵉ)

  is-finite-Preorderᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-finite-Preorderᵉ = type-Propᵉ is-finite-Preorder-Propᵉ

  is-prop-is-finite-Preorderᵉ : is-propᵉ is-finite-Preorderᵉ
  is-prop-is-finite-Preorderᵉ = is-prop-type-Propᵉ is-finite-Preorder-Propᵉ

  is-finite-type-is-finite-Preorderᵉ :
    is-finite-Preorderᵉ → is-finiteᵉ (type-Preorderᵉ Pᵉ)
  is-finite-type-is-finite-Preorderᵉ = pr1ᵉ

  is-decidable-leq-is-finite-Preorderᵉ :
    is-finite-Preorderᵉ →
    (xᵉ yᵉ : type-Preorderᵉ Pᵉ) → is-decidableᵉ (leq-Preorderᵉ Pᵉ xᵉ yᵉ)
  is-decidable-leq-is-finite-Preorderᵉ Hᵉ = pr2ᵉ Hᵉ

Preorder-𝔽ᵉ : (l1ᵉ l2ᵉ : Level) → UUᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ)
Preorder-𝔽ᵉ l1ᵉ l2ᵉ =
  Σᵉ ( 𝔽ᵉ l1ᵉ)
    ( λ Pᵉ →
      Σᵉ ( (xᵉ yᵉ : type-𝔽ᵉ Pᵉ) → Decidable-Propᵉ l2ᵉ)
        ( λ Rᵉ →
          ( (xᵉ : type-𝔽ᵉ Pᵉ) → type-Decidable-Propᵉ (Rᵉ xᵉ xᵉ)) ×ᵉ
          ( (xᵉ yᵉ zᵉ : type-𝔽ᵉ Pᵉ) →
            type-Decidable-Propᵉ (Rᵉ yᵉ zᵉ) → type-Decidable-Propᵉ (Rᵉ xᵉ yᵉ) →
            type-Decidable-Propᵉ (Rᵉ xᵉ zᵉ))))

finite-preorder-is-finite-Preorderᵉ :
  {l1ᵉ l2ᵉ : Level} (Pᵉ : Preorderᵉ l1ᵉ l2ᵉ) → is-finite-Preorderᵉ Pᵉ →
  Preorder-𝔽ᵉ l1ᵉ l2ᵉ
pr1ᵉ (pr1ᵉ (finite-preorder-is-finite-Preorderᵉ Pᵉ Hᵉ)) = type-Preorderᵉ Pᵉ
pr2ᵉ (pr1ᵉ (finite-preorder-is-finite-Preorderᵉ Pᵉ Hᵉ)) = pr1ᵉ Hᵉ
pr1ᵉ (pr1ᵉ (pr2ᵉ (finite-preorder-is-finite-Preorderᵉ Pᵉ Hᵉ)) xᵉ yᵉ) =
  leq-Preorderᵉ Pᵉ xᵉ yᵉ
pr1ᵉ (pr2ᵉ (pr1ᵉ (pr2ᵉ (finite-preorder-is-finite-Preorderᵉ Pᵉ Hᵉ)) xᵉ yᵉ)) =
  is-prop-leq-Preorderᵉ Pᵉ xᵉ yᵉ
pr2ᵉ (pr2ᵉ (pr1ᵉ (pr2ᵉ (finite-preorder-is-finite-Preorderᵉ Pᵉ Hᵉ)) xᵉ yᵉ)) =
  pr2ᵉ Hᵉ xᵉ yᵉ
pr1ᵉ (pr2ᵉ (pr2ᵉ (finite-preorder-is-finite-Preorderᵉ Pᵉ Hᵉ))) =
  refl-leq-Preorderᵉ Pᵉ
pr2ᵉ (pr2ᵉ (pr2ᵉ (finite-preorder-is-finite-Preorderᵉ Pᵉ Hᵉ))) =
  transitive-leq-Preorderᵉ Pᵉ

module _
  {l1ᵉ l2ᵉ : Level} (Pᵉ : Preorder-𝔽ᵉ l1ᵉ l2ᵉ)
  where

  finite-type-Preorder-𝔽ᵉ : 𝔽ᵉ l1ᵉ
  finite-type-Preorder-𝔽ᵉ = pr1ᵉ Pᵉ

  type-Preorder-𝔽ᵉ : UUᵉ l1ᵉ
  type-Preorder-𝔽ᵉ = type-𝔽ᵉ finite-type-Preorder-𝔽ᵉ

  is-finite-type-Preorder-𝔽ᵉ : is-finiteᵉ type-Preorder-𝔽ᵉ
  is-finite-type-Preorder-𝔽ᵉ =
    is-finite-type-𝔽ᵉ finite-type-Preorder-𝔽ᵉ

  number-of-types-Preorder-𝔽ᵉ : ℕᵉ
  number-of-types-Preorder-𝔽ᵉ =
    number-of-elements-is-finiteᵉ is-finite-type-Preorder-𝔽ᵉ

  mere-equiv-type-Preorder-𝔽ᵉ :
    mere-equivᵉ (Finᵉ number-of-types-Preorder-𝔽ᵉ) type-Preorder-𝔽ᵉ
  mere-equiv-type-Preorder-𝔽ᵉ =
    mere-equiv-is-finiteᵉ is-finite-type-Preorder-𝔽ᵉ

  is-set-type-Preorder-𝔽ᵉ : is-setᵉ type-Preorder-𝔽ᵉ
  is-set-type-Preorder-𝔽ᵉ =
    is-set-is-finiteᵉ is-finite-type-Preorder-𝔽ᵉ

  has-decidable-equality-type-Preorder-𝔽ᵉ :
    has-decidable-equalityᵉ type-Preorder-𝔽ᵉ
  has-decidable-equality-type-Preorder-𝔽ᵉ =
    has-decidable-equality-is-finiteᵉ is-finite-type-Preorder-𝔽ᵉ

  leq-finite-preorder-Decidable-Propᵉ :
    (xᵉ yᵉ : type-Preorder-𝔽ᵉ) → Decidable-Propᵉ l2ᵉ
  leq-finite-preorder-Decidable-Propᵉ = pr1ᵉ (pr2ᵉ Pᵉ)

  leq-Preorder-𝔽ᵉ : (xᵉ yᵉ : type-Preorder-𝔽ᵉ) → UUᵉ l2ᵉ
  leq-Preorder-𝔽ᵉ xᵉ yᵉ =
    type-Decidable-Propᵉ (leq-finite-preorder-Decidable-Propᵉ xᵉ yᵉ)

  is-decidable-prop-leq-Preorder-𝔽ᵉ :
    (xᵉ yᵉ : type-Preorder-𝔽ᵉ) →
    is-decidable-propᵉ (leq-Preorder-𝔽ᵉ xᵉ yᵉ)
  is-decidable-prop-leq-Preorder-𝔽ᵉ xᵉ yᵉ =
    is-decidable-prop-type-Decidable-Propᵉ
      ( leq-finite-preorder-Decidable-Propᵉ xᵉ yᵉ)

  is-decidable-leq-Preorder-𝔽ᵉ :
    (xᵉ yᵉ : type-Preorder-𝔽ᵉ) → is-decidableᵉ (leq-Preorder-𝔽ᵉ xᵉ yᵉ)
  is-decidable-leq-Preorder-𝔽ᵉ xᵉ yᵉ =
    is-decidable-Decidable-Propᵉ (leq-finite-preorder-Decidable-Propᵉ xᵉ yᵉ)

  is-prop-leq-Preorder-𝔽ᵉ :
    (xᵉ yᵉ : type-Preorder-𝔽ᵉ) → is-propᵉ (leq-Preorder-𝔽ᵉ xᵉ yᵉ)
  is-prop-leq-Preorder-𝔽ᵉ xᵉ yᵉ =
    is-prop-type-Decidable-Propᵉ (leq-finite-preorder-Decidable-Propᵉ xᵉ yᵉ)

  leq-Preorder-𝔽-Propᵉ :
    (xᵉ yᵉ : type-Preorder-𝔽ᵉ) → Propᵉ l2ᵉ
  pr1ᵉ (leq-Preorder-𝔽-Propᵉ xᵉ yᵉ) = leq-Preorder-𝔽ᵉ xᵉ yᵉ
  pr2ᵉ (leq-Preorder-𝔽-Propᵉ xᵉ yᵉ) = is-prop-leq-Preorder-𝔽ᵉ xᵉ yᵉ

  refl-leq-Preorder-𝔽ᵉ :
    (xᵉ : type-Preorder-𝔽ᵉ) → leq-Preorder-𝔽ᵉ xᵉ xᵉ
  refl-leq-Preorder-𝔽ᵉ = pr1ᵉ (pr2ᵉ (pr2ᵉ Pᵉ))

  transitive-leq-Preorder-𝔽ᵉ : is-transitiveᵉ leq-Preorder-𝔽ᵉ
  transitive-leq-Preorder-𝔽ᵉ = pr2ᵉ (pr2ᵉ (pr2ᵉ Pᵉ))

  preorder-Preorder-𝔽ᵉ : Preorderᵉ l1ᵉ l2ᵉ
  pr1ᵉ preorder-Preorder-𝔽ᵉ = type-Preorder-𝔽ᵉ
  pr1ᵉ (pr2ᵉ preorder-Preorder-𝔽ᵉ) = leq-Preorder-𝔽-Propᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ preorder-Preorder-𝔽ᵉ)) = refl-leq-Preorder-𝔽ᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ preorder-Preorder-𝔽ᵉ)) = transitive-leq-Preorder-𝔽ᵉ

  is-finite-preorder-Preorder-𝔽ᵉ :
    is-finite-Preorderᵉ preorder-Preorder-𝔽ᵉ
  pr1ᵉ is-finite-preorder-Preorder-𝔽ᵉ = is-finite-type-Preorder-𝔽ᵉ
  pr2ᵉ is-finite-preorder-Preorder-𝔽ᵉ = is-decidable-leq-Preorder-𝔽ᵉ
```

### Decidable sub-preorders of finite preorders

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Pᵉ : Preorder-𝔽ᵉ l1ᵉ l2ᵉ)
  (Sᵉ : type-Preorder-𝔽ᵉ Pᵉ → Decidable-Propᵉ l3ᵉ)
  where

  type-finite-Subpreorderᵉ : UUᵉ (l1ᵉ ⊔ l3ᵉ)
  type-finite-Subpreorderᵉ =
    type-Decidable-Subpreorderᵉ (preorder-Preorder-𝔽ᵉ Pᵉ) Sᵉ

  is-finite-type-finite-Subpreorderᵉ : is-finiteᵉ type-finite-Subpreorderᵉ
  is-finite-type-finite-Subpreorderᵉ =
    is-finite-type-decidable-subtypeᵉ Sᵉ (is-finite-type-Preorder-𝔽ᵉ Pᵉ)

  eq-type-finite-Subpreorderᵉ :
    (xᵉ yᵉ : type-finite-Subpreorderᵉ) → Idᵉ (pr1ᵉ xᵉ) (pr1ᵉ yᵉ) → Idᵉ xᵉ yᵉ
  eq-type-finite-Subpreorderᵉ =
    eq-type-Decidable-Subpreorderᵉ (preorder-Preorder-𝔽ᵉ Pᵉ) Sᵉ

  leq-finite-Subpreorder-Decidable-Propᵉ :
    (xᵉ yᵉ : type-finite-Subpreorderᵉ) → Decidable-Propᵉ l2ᵉ
  leq-finite-Subpreorder-Decidable-Propᵉ xᵉ yᵉ =
    leq-finite-preorder-Decidable-Propᵉ Pᵉ (pr1ᵉ xᵉ) (pr1ᵉ yᵉ)

  leq-finite-Subpreorder-Propᵉ :
    (xᵉ yᵉ : type-finite-Subpreorderᵉ) → Propᵉ l2ᵉ
  leq-finite-Subpreorder-Propᵉ =
    leq-Decidable-Subpreorder-Propᵉ (preorder-Preorder-𝔽ᵉ Pᵉ) Sᵉ

  leq-finite-Subpreorderᵉ : (xᵉ yᵉ : type-finite-Subpreorderᵉ) → UUᵉ l2ᵉ
  leq-finite-Subpreorderᵉ =
    leq-Decidable-Subpreorderᵉ (preorder-Preorder-𝔽ᵉ Pᵉ) Sᵉ

  is-prop-leq-finite-Subpreorderᵉ :
    (xᵉ yᵉ : type-finite-Subpreorderᵉ) →
    is-propᵉ (leq-finite-Subpreorderᵉ xᵉ yᵉ)
  is-prop-leq-finite-Subpreorderᵉ =
    is-prop-leq-Decidable-Subpreorderᵉ (preorder-Preorder-𝔽ᵉ Pᵉ) Sᵉ

  refl-leq-finite-Subpreorderᵉ :
    (xᵉ : type-finite-Subpreorderᵉ) → leq-finite-Subpreorderᵉ xᵉ xᵉ
  refl-leq-finite-Subpreorderᵉ =
    refl-leq-Decidable-Subpreorderᵉ (preorder-Preorder-𝔽ᵉ Pᵉ) Sᵉ

  transitive-leq-finite-Subpreorderᵉ : is-transitiveᵉ leq-finite-Subpreorderᵉ
  transitive-leq-finite-Subpreorderᵉ =
    transitive-leq-Decidable-Subpreorderᵉ (preorder-Preorder-𝔽ᵉ Pᵉ) Sᵉ

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Pᵉ : Preorder-𝔽ᵉ l1ᵉ l2ᵉ)
  (Sᵉ : type-Preorder-𝔽ᵉ Pᵉ → Decidable-Propᵉ l3ᵉ)
  where

  type-finite-Subpreorder-𝔽ᵉ : 𝔽ᵉ (l1ᵉ ⊔ l3ᵉ)
  pr1ᵉ type-finite-Subpreorder-𝔽ᵉ = type-finite-Subpreorderᵉ Pᵉ Sᵉ
  pr2ᵉ type-finite-Subpreorder-𝔽ᵉ = is-finite-type-finite-Subpreorderᵉ Pᵉ Sᵉ

  finite-Subpreorderᵉ : Preorder-𝔽ᵉ (l1ᵉ ⊔ l3ᵉ) l2ᵉ
  pr1ᵉ finite-Subpreorderᵉ = type-finite-Subpreorder-𝔽ᵉ
  pr1ᵉ (pr2ᵉ finite-Subpreorderᵉ) = leq-finite-Subpreorder-Decidable-Propᵉ Pᵉ Sᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ finite-Subpreorderᵉ)) = refl-leq-finite-Subpreorderᵉ Pᵉ Sᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ finite-Subpreorderᵉ)) = transitive-leq-finite-Subpreorderᵉ Pᵉ Sᵉ
```