# The precategory of monoids

```agda
module group-theory.precategory-of-monoidsᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.large-precategoriesᵉ
open import category-theory.large-subprecategoriesᵉ
open import category-theory.precategoriesᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import group-theory.homomorphisms-monoidsᵉ
open import group-theory.monoidsᵉ
open import group-theory.precategory-of-semigroupsᵉ
```

</details>

## Idea

Theᵉ {{#conceptᵉ "precategoryᵉ ofᵉ monoids"ᵉ Agda=Monoid-Large-Precategoryᵉ}} consistsᵉ
ofᵉ [monoids](group-theory.monoids.mdᵉ) andᵉ
[homomorphismsᵉ ofᵉ monoids](group-theory.homomorphisms-monoids.md).ᵉ

## Definitions

### The precategory of monoids as a subprecategory of the precategory of semigroups

```agda
Monoid-Large-Subprecategoryᵉ :
  Large-Subprecategoryᵉ (λ lᵉ → lᵉ) (λ l1ᵉ l2ᵉ → l2ᵉ) Semigroup-Large-Precategoryᵉ
Monoid-Large-Subprecategoryᵉ =
  λ where
    .subtype-obj-Large-Subprecategoryᵉ lᵉ →
      is-unital-prop-Semigroupᵉ {lᵉ}
    .subtype-hom-Large-Subprecategoryᵉ Gᵉ Hᵉ is-unital-Gᵉ is-unital-Hᵉ →
      preserves-unit-hom-prop-Semigroupᵉ (Gᵉ ,ᵉ is-unital-Gᵉ) (Hᵉ ,ᵉ is-unital-Hᵉ)
    .contains-id-Large-Subprecategoryᵉ Gᵉ is-unital-Gᵉ →
      preserves-unit-id-hom-Monoidᵉ (Gᵉ ,ᵉ is-unital-Gᵉ)
    .is-closed-under-composition-Large-Subprecategoryᵉ
      Gᵉ Hᵉ Kᵉ gᵉ fᵉ is-unital-Gᵉ is-unital-Hᵉ is-unital-Kᵉ unit-gᵉ unit-fᵉ →
      preserves-unit-comp-hom-Monoidᵉ
        ( Gᵉ ,ᵉ is-unital-Gᵉ)
        ( Hᵉ ,ᵉ is-unital-Hᵉ)
        ( Kᵉ ,ᵉ is-unital-Kᵉ)
        ( gᵉ ,ᵉ unit-gᵉ)
        ( fᵉ ,ᵉ unit-fᵉ)
```

### The large precategory of monoids

```agda
Monoid-Large-Precategoryᵉ : Large-Precategoryᵉ lsuc (_⊔ᵉ_)
Monoid-Large-Precategoryᵉ =
  large-precategory-Large-Subprecategoryᵉ Monoid-Large-Subprecategoryᵉ
```

### The precategory of small monoids

```agda
Monoid-Precategoryᵉ : (lᵉ : Level) → Precategoryᵉ (lsuc lᵉ) lᵉ
Monoid-Precategoryᵉ = precategory-Large-Precategoryᵉ Monoid-Large-Precategoryᵉ
```