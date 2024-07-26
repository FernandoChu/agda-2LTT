# The category of commutative rings

```agda
module commutative-algebra.category-of-commutative-ringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categoriesᵉ
open import category-theory.large-categoriesᵉ

open import commutative-algebra.isomorphisms-commutative-ringsᵉ
open import commutative-algebra.precategory-of-commutative-ringsᵉ

open import foundation.universe-levelsᵉ
```

</details>

## Idea

Theᵉ [largeᵉ category](category-theory.large-categories.mdᵉ)
`Commutative-Ring-Category`ᵉ ofᵉ
[commutativeᵉ rings](commutative-algebra.commutative-rings.mdᵉ) isᵉ theᵉ largeᵉ
categoryᵉ consistsingᵉ ofᵉ commutativeᵉ ringsᵉ andᵉ
[ringᵉ homomorphisms](commutative-algebra.homomorphisms-commutative-rings.md).ᵉ

## Definitions

### The large category of commutative rings

```agda
is-large-category-Commutative-Ring-Large-Categoryᵉ :
  is-large-category-Large-Precategoryᵉ Commutative-Ring-Large-Precategoryᵉ
is-large-category-Commutative-Ring-Large-Categoryᵉ =
  is-equiv-iso-eq-Commutative-Ringᵉ

Commutative-Ring-Large-Categoryᵉ : Large-Categoryᵉ lsuc (_⊔ᵉ_)
large-precategory-Large-Categoryᵉ Commutative-Ring-Large-Categoryᵉ =
  Commutative-Ring-Large-Precategoryᵉ
is-large-category-Large-Categoryᵉ Commutative-Ring-Large-Categoryᵉ =
  is-large-category-Commutative-Ring-Large-Categoryᵉ
```

### The small categories of commutative rings

```agda
Commutative-Ring-Categoryᵉ : (lᵉ : Level) → Categoryᵉ (lsuc lᵉ) lᵉ
Commutative-Ring-Categoryᵉ =
  category-Large-Categoryᵉ Commutative-Ring-Large-Categoryᵉ
```