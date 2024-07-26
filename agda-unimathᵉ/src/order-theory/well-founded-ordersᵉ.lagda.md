# Well-founded orders

```agda
module order-theory.well-founded-ordersᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relationsᵉ
open import foundation.cartesian-product-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import order-theory.well-founded-relationsᵉ
```

</details>

## Idea

Aᵉ **well-foundedᵉ order**ᵉ isᵉ aᵉ [transitive](foundation.binary-relations.mdᵉ)
[well-foundedᵉ relation](order-theory.well-founded-relations.md).ᵉ

## Definitions

### The predicate of being a well-founded order

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} (Rᵉ : Relationᵉ l2ᵉ Xᵉ)
  where

  is-well-founded-order-Relationᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-well-founded-order-Relationᵉ = is-transitiveᵉ Rᵉ ×ᵉ is-well-founded-Relationᵉ Rᵉ
```

### Well-founded orders

```agda
Well-Founded-Orderᵉ : {l1ᵉ : Level} (l2ᵉ : Level) → UUᵉ l1ᵉ → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
Well-Founded-Orderᵉ l2ᵉ Xᵉ = Σᵉ (Relationᵉ l2ᵉ Xᵉ) is-well-founded-order-Relationᵉ

module _
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} (Rᵉ : Well-Founded-Orderᵉ l2ᵉ Xᵉ)
  where

  rel-Well-Founded-Orderᵉ : Relationᵉ l2ᵉ Xᵉ
  rel-Well-Founded-Orderᵉ = pr1ᵉ Rᵉ

  is-well-founded-order-Well-Founded-Orderᵉ :
    is-well-founded-order-Relationᵉ rel-Well-Founded-Orderᵉ
  is-well-founded-order-Well-Founded-Orderᵉ = pr2ᵉ Rᵉ

  is-transitive-Well-Founded-Orderᵉ : is-transitiveᵉ rel-Well-Founded-Orderᵉ
  is-transitive-Well-Founded-Orderᵉ =
    pr1ᵉ is-well-founded-order-Well-Founded-Orderᵉ

  is-well-founded-relation-Well-Founded-Orderᵉ :
    is-well-founded-Relationᵉ rel-Well-Founded-Orderᵉ
  is-well-founded-relation-Well-Founded-Orderᵉ =
    pr2ᵉ is-well-founded-order-Well-Founded-Orderᵉ

  well-founded-relation-Well-Founded-Orderᵉ : Well-Founded-Relationᵉ l2ᵉ Xᵉ
  pr1ᵉ well-founded-relation-Well-Founded-Orderᵉ =
    rel-Well-Founded-Orderᵉ
  pr2ᵉ well-founded-relation-Well-Founded-Orderᵉ =
    is-well-founded-relation-Well-Founded-Orderᵉ

  is-asymmetric-Well-Founded-Orderᵉ :
    is-asymmetricᵉ rel-Well-Founded-Orderᵉ
  is-asymmetric-Well-Founded-Orderᵉ =
    is-asymmetric-Well-Founded-Relationᵉ well-founded-relation-Well-Founded-Orderᵉ

  is-irreflexive-Well-Founded-Orderᵉ :
    is-irreflexiveᵉ rel-Well-Founded-Orderᵉ
  is-irreflexive-Well-Founded-Orderᵉ =
    is-irreflexive-Well-Founded-Relationᵉ
      ( well-founded-relation-Well-Founded-Orderᵉ)
```