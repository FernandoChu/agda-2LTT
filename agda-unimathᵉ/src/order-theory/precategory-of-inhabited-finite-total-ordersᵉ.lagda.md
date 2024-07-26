# The precategory of inhabited finite total orders

```agda
module order-theory.precategory-of-inhabited-finite-total-ordersᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.full-large-subprecategoriesᵉ
open import category-theory.large-precategoriesᵉ
open import category-theory.precategoriesᵉ

open import foundation.universe-levelsᵉ

open import order-theory.inhabited-finite-total-ordersᵉ
open import order-theory.precategory-of-posetsᵉ
```

</details>

## Idea

Theᵉ **(largeᵉ) precategoryᵉ ofᵉ inhabitedᵉ finiteᵉ totalᵉ orders**ᵉ consistsᵉ ofᵉ
[inhabitedᵉ finiteᵉ totalᵉ orders](order-theory.inhabited-finite-total-orders.mdᵉ)
andᵉ [orderᵉ preservingᵉ maps](order-theory.order-preserving-maps-posets.mdᵉ) andᵉ isᵉ
exhibitedᵉ asᵉ aᵉ
[fullᵉ subprecategory](category-theory.full-large-subprecategories.mdᵉ) ofᵉ theᵉ
[precategoryᵉ ofᵉ posets](order-theory.precategory-of-posets.md).ᵉ

## Definitions

### The large precategory of inhabited finite total orders

```agda
parametric-Inhabited-Total-Order-𝔽-Full-Large-Subprecategoryᵉ :
  (αᵉ βᵉ : Level → Level) →
  Full-Large-Subprecategoryᵉ
    ( λ lᵉ → αᵉ lᵉ ⊔ βᵉ lᵉ)
    ( parametric-Poset-Large-Precategoryᵉ αᵉ βᵉ)
parametric-Inhabited-Total-Order-𝔽-Full-Large-Subprecategoryᵉ αᵉ βᵉ =
  is-inhabited-finite-total-order-Poset-Propᵉ

Inhabited-Total-Order-𝔽-Large-Precategoryᵉ : Large-Precategoryᵉ lsuc (_⊔ᵉ_)
Inhabited-Total-Order-𝔽-Large-Precategoryᵉ =
  large-precategory-Full-Large-Subprecategoryᵉ
    ( Poset-Large-Precategoryᵉ)
    ( parametric-Inhabited-Total-Order-𝔽-Full-Large-Subprecategoryᵉ
      ( λ lᵉ → lᵉ)
      ( λ lᵉ → lᵉ))
```

### The precategory of finite total orders of universe level `l`

```agda
Inhabited-Total-Order-𝔽-Precategoryᵉ : (lᵉ : Level) → Precategoryᵉ (lsuc lᵉ) lᵉ
Inhabited-Total-Order-𝔽-Precategoryᵉ =
  precategory-Large-Precategoryᵉ Inhabited-Total-Order-𝔽-Large-Precategoryᵉ
```