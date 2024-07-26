# The precategory of commutative monoids

```agda
module group-theory.precategory-of-commutative-monoidsᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.full-large-subprecategoriesᵉ
open import category-theory.large-precategoriesᵉ
open import category-theory.precategoriesᵉ

open import foundation.universe-levelsᵉ

open import group-theory.commutative-monoidsᵉ
open import group-theory.precategory-of-monoidsᵉ
```

</details>

## Idea

Theᵉ **precategoryᵉ ofᵉ commutativeᵉ monoids**ᵉ consistsᵉ ofᵉ commutativeᵉ monoidsᵉ andᵉ
homomorphismsᵉ ofᵉ monoids.ᵉ

## Definitions

### The precategory of commutative monoids as a full subprecategory of monoids

```agda
Commutative-Monoid-Full-Large-Subprecategoryᵉ :
  Full-Large-Subprecategoryᵉ (λ lᵉ → lᵉ) Monoid-Large-Precategoryᵉ
Commutative-Monoid-Full-Large-Subprecategoryᵉ = is-commutative-prop-Monoidᵉ
```

### The large precategory of commutative monoids

```agda
Commutative-Monoid-Large-Precategoryᵉ : Large-Precategoryᵉ lsuc (_⊔ᵉ_)
Commutative-Monoid-Large-Precategoryᵉ =
  large-precategory-Full-Large-Subprecategoryᵉ
    ( Monoid-Large-Precategoryᵉ)
    ( Commutative-Monoid-Full-Large-Subprecategoryᵉ)
```

### The precategory of small commutative monoids

```agda
Commutative-Monoid-Precategoryᵉ : (lᵉ : Level) → Precategoryᵉ (lsuc lᵉ) lᵉ
Commutative-Monoid-Precategoryᵉ =
  precategory-Large-Precategoryᵉ Commutative-Monoid-Large-Precategoryᵉ
```