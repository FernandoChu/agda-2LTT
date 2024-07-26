# The precategory of commutative semirings

```agda
module commutative-algebra.precategory-of-commutative-semiringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.full-large-subprecategoriesᵉ
open import category-theory.large-precategoriesᵉ
open import category-theory.precategoriesᵉ

open import commutative-algebra.commutative-semiringsᵉ

open import foundation.universe-levelsᵉ

open import ring-theory.precategory-of-semiringsᵉ
```

</details>

## Idea

Theᵉ
{{#conceptᵉ "precategoryᵉ ofᵉ commutativeᵉ semirings"ᵉ Agda=Commutative-Semiring-Large-Precategoryᵉ}}
consistsᵉ ofᵉ
[commutativeᵉ semirings](commutative-algebra.commutative-semirings.mdᵉ) andᵉ
[homomorphismsᵉ ofᵉ semirings](commutative-algebra.homomorphisms-commutative-semirings.md).ᵉ

## Definitions

### The precategory of commutative semirings as a full subprecategory of semirings

```agda
Commutative-Semiring-Full-Large-Precategoryᵉ :
  Full-Large-Subprecategoryᵉ (λ lᵉ → lᵉ) Semiring-Large-Precategoryᵉ
Commutative-Semiring-Full-Large-Precategoryᵉ = is-commutative-prop-Semiringᵉ
```

### The large precategory of commutative semirings

```agda
Commutative-Semiring-Large-Precategoryᵉ : Large-Precategoryᵉ lsuc (_⊔ᵉ_)
Commutative-Semiring-Large-Precategoryᵉ =
  large-precategory-Full-Large-Subprecategoryᵉ
    ( Semiring-Large-Precategoryᵉ)
    ( Commutative-Semiring-Full-Large-Precategoryᵉ)
```

### The precategory of commutative semirings of universe level `l`

```agda
Commutative-Semiring-Precategoryᵉ : (lᵉ : Level) → Precategoryᵉ (lsuc lᵉ) lᵉ
Commutative-Semiring-Precategoryᵉ =
  precategory-Large-Precategoryᵉ Commutative-Semiring-Large-Precategoryᵉ
```