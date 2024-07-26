# The precategory of finite posets

```agda
module order-theory.precategory-of-finite-posetsᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.full-large-subprecategoriesᵉ
open import category-theory.large-precategoriesᵉ
open import category-theory.precategoriesᵉ

open import foundation.universe-levelsᵉ

open import order-theory.finite-posetsᵉ
open import order-theory.precategory-of-posetsᵉ
```

</details>

## Idea

Theᵉ **(largeᵉ) precategoryᵉ ofᵉ finiteᵉ posets**ᵉ consistsᵉ ofᵉ
[finiteᵉ posets](order-theory.finite-posets.mdᵉ) andᵉ
[orderᵉ preservingᵉ maps](order-theory.order-preserving-maps-posets.mdᵉ) andᵉ isᵉ
exhibitedᵉ asᵉ aᵉ
[fullᵉ subprecategory](category-theory.full-large-subprecategories.mdᵉ) ofᵉ theᵉ
[precategoryᵉ ofᵉ posets](order-theory.precategory-of-posets.md).ᵉ

## Definitions

### The large precategory of finite posets

```agda
parametric-Poset-𝔽-Full-Large-Subprecategoryᵉ :
  (αᵉ βᵉ : Level → Level) →
  Full-Large-Subprecategoryᵉ
    ( λ lᵉ → αᵉ lᵉ ⊔ βᵉ lᵉ)
    ( parametric-Poset-Large-Precategoryᵉ αᵉ βᵉ)
parametric-Poset-𝔽-Full-Large-Subprecategoryᵉ αᵉ βᵉ = is-finite-Poset-Propᵉ

Poset-𝔽-Large-Precategoryᵉ :
  Large-Precategoryᵉ lsuc (_⊔ᵉ_)
Poset-𝔽-Large-Precategoryᵉ =
  large-precategory-Full-Large-Subprecategoryᵉ
    ( Poset-Large-Precategoryᵉ)
    ( parametric-Poset-𝔽-Full-Large-Subprecategoryᵉ (λ lᵉ → lᵉ) (λ lᵉ → lᵉ))
```

### The precategory of finite posets of universe level `l`

```agda
Poset-𝔽-Precategoryᵉ : (lᵉ : Level) → Precategoryᵉ (lsuc lᵉ) lᵉ
Poset-𝔽-Precategoryᵉ = precategory-Large-Precategoryᵉ Poset-𝔽-Large-Precategoryᵉ
```