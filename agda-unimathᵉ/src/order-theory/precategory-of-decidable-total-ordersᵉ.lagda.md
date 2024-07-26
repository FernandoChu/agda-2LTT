# The precategory of decidable total orders

```agda
module order-theory.precategory-of-decidable-total-ordersᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.full-large-subprecategoriesᵉ
open import category-theory.large-precategoriesᵉ
open import category-theory.precategoriesᵉ

open import foundation.universe-levelsᵉ

open import order-theory.decidable-total-ordersᵉ
open import order-theory.precategory-of-posetsᵉ
```

</details>

## Idea

Theᵉ **(largeᵉ) precategoryᵉ ofᵉ decidableᵉ totalᵉ orders**ᵉ consistsᵉ ofᵉ
[decidableᵉ totalᵉ orders](order-theory.decidable-total-orders.mdᵉ) andᵉ
[orderᵉ preservingᵉ maps](order-theory.order-preserving-maps-posets.mdᵉ) andᵉ isᵉ
exhibitedᵉ asᵉ aᵉ
[fullᵉ subprecategory](category-theory.full-large-subprecategories.mdᵉ) ofᵉ theᵉ
[precategoryᵉ ofᵉ posets](order-theory.precategory-of-posets.md).ᵉ

## Definitions

### The large precategory of decidable total orders

```agda
parametric-Decidable-Total-Order-Full-Large-Subprecategoryᵉ :
  (αᵉ βᵉ : Level → Level) →
  Full-Large-Subprecategoryᵉ
    ( λ lᵉ → αᵉ lᵉ ⊔ βᵉ lᵉ)
    ( parametric-Poset-Large-Precategoryᵉ αᵉ βᵉ)
parametric-Decidable-Total-Order-Full-Large-Subprecategoryᵉ αᵉ βᵉ =
  is-decidable-total-prop-Posetᵉ

Decidable-Total-Order-Large-Precategoryᵉ :
  Large-Precategoryᵉ lsuc (_⊔ᵉ_)
Decidable-Total-Order-Large-Precategoryᵉ =
  large-precategory-Full-Large-Subprecategoryᵉ
    ( Poset-Large-Precategoryᵉ)
    ( parametric-Decidable-Total-Order-Full-Large-Subprecategoryᵉ
      ( λ lᵉ → lᵉ)
      ( λ lᵉ → lᵉ))
```

### The precategory or total orders of universe level `l`

```agda
Decidable-Total-Order-Precategoryᵉ : (lᵉ : Level) → Precategoryᵉ (lsuc lᵉ) lᵉ
Decidable-Total-Order-Precategoryᵉ =
  precategory-Large-Precategoryᵉ Decidable-Total-Order-Large-Precategoryᵉ
```