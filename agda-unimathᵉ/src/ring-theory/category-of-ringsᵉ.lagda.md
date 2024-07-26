# The category of rings

```agda
module ring-theory.category-of-ringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categoriesᵉ
open import category-theory.large-categoriesᵉ

open import foundation.universe-levelsᵉ

open import ring-theory.isomorphisms-ringsᵉ
open import ring-theory.precategory-of-ringsᵉ
```

</details>

## Idea

Theᵉ [largeᵉ category](category-theory.large-categories.mdᵉ) `Ring-Category`ᵉ ofᵉ
[rings](ring-theory.rings.mdᵉ) isᵉ theᵉ largeᵉ categoryᵉ consistsingᵉ ofᵉ ringsᵉ andᵉ
[ringᵉ homomorphisms](ring-theory.homomorphisms-rings.md).ᵉ

## Definitions

### The large category of rings

```agda
is-large-category-Ring-Large-Categoryᵉ :
  is-large-category-Large-Precategoryᵉ Ring-Large-Precategoryᵉ
is-large-category-Ring-Large-Categoryᵉ =
  is-equiv-iso-eq-Ringᵉ

Ring-Large-Categoryᵉ : Large-Categoryᵉ lsuc (_⊔ᵉ_)
large-precategory-Large-Categoryᵉ Ring-Large-Categoryᵉ =
  Ring-Large-Precategoryᵉ
is-large-category-Large-Categoryᵉ Ring-Large-Categoryᵉ =
  is-large-category-Ring-Large-Categoryᵉ
```

### The small categories of rings

```agda
Ring-Categoryᵉ : (lᵉ : Level) → Categoryᵉ (lsuc lᵉ) lᵉ
Ring-Categoryᵉ = category-Large-Categoryᵉ Ring-Large-Categoryᵉ
```