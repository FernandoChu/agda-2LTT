# Ideals in preorders

```agda
module order-theory.ideals-preordersᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.inhabited-typesᵉ
open import foundation.universe-levelsᵉ

open import order-theory.lower-types-preordersᵉ
open import order-theory.preordersᵉ
```

</details>

## Idea

**Ideals**ᵉ in preordersᵉ areᵉ inhabitedᵉ lowerᵉ typesᵉ `L`ᵉ thatᵉ containᵉ anᵉ upperᵉ
boundᵉ forᵉ everyᵉ pairᵉ ofᵉ elementsᵉ in `L`.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Pᵉ : Preorderᵉ l1ᵉ l2ᵉ)
  where

  is-ideal-lower-type-Preorderᵉ :
    {l3ᵉ : Level} (Lᵉ : lower-type-Preorderᵉ l3ᵉ Pᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  is-ideal-lower-type-Preorderᵉ Lᵉ =
    ( is-inhabitedᵉ (type-lower-type-Preorderᵉ Pᵉ Lᵉ)) ×ᵉ
    ( (xᵉ yᵉ : type-lower-type-Preorderᵉ Pᵉ Lᵉ) →
      is-inhabitedᵉ
        ( Σᵉ ( type-lower-type-Preorderᵉ Pᵉ Lᵉ)
            ( λ zᵉ →
              ( leq-lower-type-Preorderᵉ Pᵉ Lᵉ xᵉ zᵉ) ×ᵉ
              ( leq-lower-type-Preorderᵉ Pᵉ Lᵉ yᵉ zᵉ))))
```