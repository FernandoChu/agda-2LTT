# Subpreorders

```agda
module order-theory.subpreordersᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relationsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.function-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.subtypesᵉ
open import foundation.universe-levelsᵉ

open import order-theory.preordersᵉ
```

</details>

## Idea

Aᵉ **subpreorder**ᵉ ofᵉ aᵉ preorderᵉ `P`ᵉ isᵉ aᵉ subtypeᵉ ofᵉ `P`.ᵉ Byᵉ restrictionᵉ ofᵉ theᵉ
orderingᵉ onᵉ `P`,ᵉ theᵉ subpreorderᵉ inheritsᵉ theᵉ structureᵉ ofᵉ aᵉ preorder.ᵉ

## Definition

### Subpreorders

```agda
Subpreorderᵉ :
  {l1ᵉ l2ᵉ : Level} (l3ᵉ : Level) → Preorderᵉ l1ᵉ l2ᵉ → UUᵉ (l1ᵉ ⊔ lsuc l3ᵉ)
Subpreorderᵉ l3ᵉ Pᵉ = subtypeᵉ l3ᵉ (type-Preorderᵉ Pᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Pᵉ : Preorderᵉ l1ᵉ l2ᵉ) (Sᵉ : Subpreorderᵉ l3ᵉ Pᵉ)
  where

  type-Subpreorderᵉ : UUᵉ (l1ᵉ ⊔ l3ᵉ)
  type-Subpreorderᵉ = type-subtypeᵉ Sᵉ

  eq-type-Subpreorderᵉ :
    (xᵉ yᵉ : type-Subpreorderᵉ) → Idᵉ (pr1ᵉ xᵉ) (pr1ᵉ yᵉ) → Idᵉ xᵉ yᵉ
  eq-type-Subpreorderᵉ xᵉ yᵉ = eq-type-subtypeᵉ Sᵉ

  leq-Subpreorder-Propᵉ : (xᵉ yᵉ : type-Subpreorderᵉ) → Propᵉ l2ᵉ
  leq-Subpreorder-Propᵉ xᵉ yᵉ = leq-Preorder-Propᵉ Pᵉ (pr1ᵉ xᵉ) (pr1ᵉ yᵉ)

  leq-Subpreorderᵉ : (xᵉ yᵉ : type-Subpreorderᵉ) → UUᵉ l2ᵉ
  leq-Subpreorderᵉ xᵉ yᵉ = type-Propᵉ (leq-Subpreorder-Propᵉ xᵉ yᵉ)

  is-prop-leq-Subpreorderᵉ :
    (xᵉ yᵉ : type-Subpreorderᵉ) → is-propᵉ (leq-Subpreorderᵉ xᵉ yᵉ)
  is-prop-leq-Subpreorderᵉ xᵉ yᵉ =
    is-prop-type-Propᵉ (leq-Subpreorder-Propᵉ xᵉ yᵉ)

  refl-leq-Subpreorderᵉ : is-reflexiveᵉ leq-Subpreorderᵉ
  refl-leq-Subpreorderᵉ xᵉ = refl-leq-Preorderᵉ Pᵉ (pr1ᵉ xᵉ)

  transitive-leq-Subpreorderᵉ : is-transitiveᵉ leq-Subpreorderᵉ
  transitive-leq-Subpreorderᵉ xᵉ yᵉ zᵉ =
    transitive-leq-Preorderᵉ Pᵉ (pr1ᵉ xᵉ) (pr1ᵉ yᵉ) (pr1ᵉ zᵉ)

  preorder-Subpreorderᵉ : Preorderᵉ (l1ᵉ ⊔ l3ᵉ) l2ᵉ
  pr1ᵉ preorder-Subpreorderᵉ = type-Subpreorderᵉ
  pr1ᵉ (pr2ᵉ preorder-Subpreorderᵉ) = leq-Subpreorder-Propᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ preorder-Subpreorderᵉ)) = refl-leq-Subpreorderᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ preorder-Subpreorderᵉ)) = transitive-leq-Subpreorderᵉ
```

### Inclusions of subpreorders

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Pᵉ : Preorderᵉ l1ᵉ l2ᵉ)
  where

  module _
    {l3ᵉ l4ᵉ : Level} (Sᵉ : type-Preorderᵉ Pᵉ → Propᵉ l3ᵉ)
    (Tᵉ : type-Preorderᵉ Pᵉ → Propᵉ l4ᵉ)
    where

    inclusion-Subpreorder-Propᵉ : Propᵉ (l1ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
    inclusion-Subpreorder-Propᵉ =
      Π-Propᵉ (type-Preorderᵉ Pᵉ) (λ xᵉ → hom-Propᵉ (Sᵉ xᵉ) (Tᵉ xᵉ))

    inclusion-Subpreorderᵉ : UUᵉ (l1ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
    inclusion-Subpreorderᵉ = type-Propᵉ inclusion-Subpreorder-Propᵉ

    is-prop-inclusion-Subpreorderᵉ : is-propᵉ inclusion-Subpreorderᵉ
    is-prop-inclusion-Subpreorderᵉ =
      is-prop-type-Propᵉ inclusion-Subpreorder-Propᵉ

  refl-inclusion-Subpreorderᵉ :
    {l3ᵉ : Level} → is-reflexiveᵉ (inclusion-Subpreorderᵉ {l3ᵉ})
  refl-inclusion-Subpreorderᵉ Sᵉ xᵉ = idᵉ

  transitive-inclusion-Subpreorderᵉ :
    {l3ᵉ l4ᵉ l5ᵉ : Level} (Sᵉ : type-Preorderᵉ Pᵉ → Propᵉ l3ᵉ)
    (Tᵉ : type-Preorderᵉ Pᵉ → Propᵉ l4ᵉ)
    (Uᵉ : type-Preorderᵉ Pᵉ → Propᵉ l5ᵉ) →
    inclusion-Subpreorderᵉ Tᵉ Uᵉ →
    inclusion-Subpreorderᵉ Sᵉ Tᵉ →
    inclusion-Subpreorderᵉ Sᵉ Uᵉ
  transitive-inclusion-Subpreorderᵉ Sᵉ Tᵉ Uᵉ gᵉ fᵉ xᵉ = (gᵉ xᵉ) ∘ᵉ (fᵉ xᵉ)

  Sub-Preorderᵉ : (lᵉ : Level) → Preorderᵉ (l1ᵉ ⊔ lsuc lᵉ) (l1ᵉ ⊔ lᵉ)
  pr1ᵉ (Sub-Preorderᵉ lᵉ) = type-Preorderᵉ Pᵉ → Propᵉ lᵉ
  pr1ᵉ (pr2ᵉ (Sub-Preorderᵉ lᵉ)) = inclusion-Subpreorder-Propᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ (Sub-Preorderᵉ lᵉ))) = refl-inclusion-Subpreorderᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ (Sub-Preorderᵉ lᵉ))) = transitive-inclusion-Subpreorderᵉ
```