# The precategory of groups

```agda
module group-theory.precategory-of-groupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.full-large-subprecategoriesᵉ
open import category-theory.large-precategoriesᵉ
open import category-theory.precategoriesᵉ

open import foundation.universe-levelsᵉ

open import group-theory.groupsᵉ
open import group-theory.precategory-of-semigroupsᵉ
```

</details>

## Definition

### The precategory of groups as a full subprecategory of the precategory of semigroups

```agda
Group-Full-Large-Subprecategoryᵉ :
  Full-Large-Subprecategoryᵉ (λ lᵉ → lᵉ) Semigroup-Large-Precategoryᵉ
Group-Full-Large-Subprecategoryᵉ = is-group-prop-Semigroupᵉ
```

### The large precategory of groups

```agda
Group-Large-Precategoryᵉ : Large-Precategoryᵉ lsuc (_⊔ᵉ_)
Group-Large-Precategoryᵉ =
  large-precategory-Full-Large-Subprecategoryᵉ
    ( Semigroup-Large-Precategoryᵉ)
    ( Group-Full-Large-Subprecategoryᵉ)
```

### The small precategories of groups

```agda
Group-Precategoryᵉ : (lᵉ : Level) → Precategoryᵉ (lsuc lᵉ) lᵉ
Group-Precategoryᵉ = precategory-Large-Precategoryᵉ Group-Large-Precategoryᵉ
```