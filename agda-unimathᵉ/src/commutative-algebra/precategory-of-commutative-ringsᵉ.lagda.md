# The precategory of commutative rings

```agda
module commutative-algebra.precategory-of-commutative-ringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.full-large-subprecategoriesᵉ
open import category-theory.large-precategoriesᵉ
open import category-theory.precategoriesᵉ

open import commutative-algebra.commutative-ringsᵉ

open import foundation.universe-levelsᵉ

open import ring-theory.precategory-of-ringsᵉ
```

</details>

## Idea

Theᵉ
{{#conceptᵉ "precategoryᵉ ofᵉ commutativeᵉ rings"ᵉ Agda=Commutative-Ring-Large-Precategoryᵉ}}
consistsᵉ ofᵉ [commutativeᵉ rings](commutative-algebra.commutative-rings.mdᵉ) andᵉ
[homomorphismsᵉ ofᵉ commutativeᵉ rings](commutative-algebra.homomorphisms-commutative-rings.md).ᵉ

## Definitions

### The precategory of commutative rings as a full subprecategory of rings

```agda
Commutative-Ring-Full-Large-Subprecategoryᵉ :
  Full-Large-Subprecategoryᵉ (λ lᵉ → lᵉ) Ring-Large-Precategoryᵉ
Commutative-Ring-Full-Large-Subprecategoryᵉ = is-commutative-prop-Ringᵉ
```

### The large precategory of commutative rings

```agda
Commutative-Ring-Large-Precategoryᵉ : Large-Precategoryᵉ lsuc (_⊔ᵉ_)
Commutative-Ring-Large-Precategoryᵉ =
  large-precategory-Full-Large-Subprecategoryᵉ
    ( Ring-Large-Precategoryᵉ)
    ( Commutative-Ring-Full-Large-Subprecategoryᵉ)
```

### The precategory of commutative rings of universe level `l`

```agda
Commutative-Ring-Precategoryᵉ : (lᵉ : Level) → Precategoryᵉ (lsuc lᵉ) lᵉ
Commutative-Ring-Precategoryᵉ =
  precategory-Large-Precategoryᵉ Commutative-Ring-Large-Precategoryᵉ
```