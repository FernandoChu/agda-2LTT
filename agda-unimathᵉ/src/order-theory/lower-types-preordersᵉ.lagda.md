# Lower types in preorders

```agda
module order-theory.lower-types-preordersᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.subtypesᵉ
open import foundation.universe-levelsᵉ

open import order-theory.preordersᵉ
```

</details>

## Idea

Aᵉ **lowerᵉ type**ᵉ in aᵉ preorderᵉ `P`ᵉ isᵉ aᵉ downwardsᵉ closedᵉ subtypeᵉ ofᵉ `P`.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Pᵉ : Preorderᵉ l1ᵉ l2ᵉ)
  where

  is-downwards-closed-subtype-Preorderᵉ :
    {l3ᵉ : Level} (Sᵉ : subtypeᵉ l3ᵉ (type-Preorderᵉ Pᵉ)) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  is-downwards-closed-subtype-Preorderᵉ Sᵉ =
    (xᵉ yᵉ : type-Preorderᵉ Pᵉ) →
    leq-Preorderᵉ Pᵉ yᵉ xᵉ → is-in-subtypeᵉ Sᵉ xᵉ → is-in-subtypeᵉ Sᵉ yᵉ

lower-type-Preorderᵉ :
  {l1ᵉ l2ᵉ : Level} (l3ᵉ : Level) → Preorderᵉ l1ᵉ l2ᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ lsuc l3ᵉ)
lower-type-Preorderᵉ l3ᵉ Pᵉ =
  Σᵉ (subtypeᵉ l3ᵉ (type-Preorderᵉ Pᵉ)) (is-downwards-closed-subtype-Preorderᵉ Pᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Pᵉ : Preorderᵉ l1ᵉ l2ᵉ) (Lᵉ : lower-type-Preorderᵉ l3ᵉ Pᵉ)
  where

  subtype-lower-type-Preorderᵉ : subtypeᵉ l3ᵉ (type-Preorderᵉ Pᵉ)
  subtype-lower-type-Preorderᵉ = pr1ᵉ Lᵉ

  type-lower-type-Preorderᵉ : UUᵉ (l1ᵉ ⊔ l3ᵉ)
  type-lower-type-Preorderᵉ = type-subtypeᵉ subtype-lower-type-Preorderᵉ

  inclusion-lower-type-Preorderᵉ :
    type-lower-type-Preorderᵉ → type-Preorderᵉ Pᵉ
  inclusion-lower-type-Preorderᵉ = pr1ᵉ

  leq-lower-type-Preorderᵉ : (xᵉ yᵉ : type-lower-type-Preorderᵉ) → UUᵉ l2ᵉ
  leq-lower-type-Preorderᵉ xᵉ yᵉ =
    leq-Preorderᵉ Pᵉ
      ( inclusion-lower-type-Preorderᵉ xᵉ)
      ( inclusion-lower-type-Preorderᵉ yᵉ)
```