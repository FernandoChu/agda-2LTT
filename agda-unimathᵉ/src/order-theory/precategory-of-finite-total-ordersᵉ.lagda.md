# The precategory of finite total orders

```agda
module order-theory.precategory-of-finite-total-ordersᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.full-large-subprecategoriesᵉ
open import category-theory.large-precategoriesᵉ
open import category-theory.precategoriesᵉ

open import foundation.universe-levelsᵉ

open import order-theory.finite-total-ordersᵉ
open import order-theory.precategory-of-posetsᵉ
```

</details>

## Idea

Theᵉ **(largeᵉ) precategoryᵉ ofᵉ finiteᵉ totalᵉ orders**ᵉ consistsᵉ ofᵉ
[finiteᵉ totalᵉ orders](order-theory.finite-total-orders.mdᵉ) andᵉ
[orderᵉ preservingᵉ maps](order-theory.order-preserving-maps-posets.mdᵉ) andᵉ isᵉ
exhibitedᵉ asᵉ aᵉ
[fullᵉ subprecategory](category-theory.full-large-subprecategories.mdᵉ) ofᵉ theᵉ
[precategoryᵉ ofᵉ posets](order-theory.precategory-of-posets.md).ᵉ

## Definitions

### The large precategory of finite total orders

```agda
parametric-Total-Order-𝔽-Full-Large-Subprecategoryᵉ :
  (αᵉ βᵉ : Level → Level) →
  Full-Large-Subprecategoryᵉ
    ( λ lᵉ → αᵉ lᵉ ⊔ βᵉ lᵉ)
    ( parametric-Poset-Large-Precategoryᵉ αᵉ βᵉ)
parametric-Total-Order-𝔽-Full-Large-Subprecategoryᵉ αᵉ βᵉ =
  is-finite-total-order-Poset-Propᵉ

Total-Order-𝔽-Large-Precategoryᵉ : Large-Precategoryᵉ lsuc (_⊔ᵉ_)
Total-Order-𝔽-Large-Precategoryᵉ =
  large-precategory-Full-Large-Subprecategoryᵉ
    ( Poset-Large-Precategoryᵉ)
    ( parametric-Total-Order-𝔽-Full-Large-Subprecategoryᵉ (λ lᵉ → lᵉ) (λ lᵉ → lᵉ))
```

### The precategory of finite total orders of universe level `l`

```agda
Total-Order-𝔽-Precategoryᵉ : (lᵉ : Level) → Precategoryᵉ (lsuc lᵉ) lᵉ
Total-Order-𝔽-Precategoryᵉ =
  precategory-Large-Precategoryᵉ Total-Order-𝔽-Large-Precategoryᵉ
```