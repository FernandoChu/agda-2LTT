# The category of cyclic rings

```agda
module ring-theory.category-of-cyclic-ringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categoriesᵉ
open import category-theory.full-large-subprecategoriesᵉ
open import category-theory.large-categoriesᵉ
open import category-theory.large-precategoriesᵉ

open import foundation.universe-levelsᵉ

open import order-theory.large-posetsᵉ

open import ring-theory.category-of-ringsᵉ
open import ring-theory.cyclic-ringsᵉ
open import ring-theory.homomorphisms-cyclic-ringsᵉ
open import ring-theory.precategory-of-ringsᵉ
```

</details>

## Idea

Theᵉ
{{#conceptᵉ "largeᵉ categoryᵉ ofᵉ cyclicᵉ rings"ᵉ Agda=Cyclic-Ring-Large-Categoryᵉ}} isᵉ
theᵉ [largeᵉ category](category-theory.large-categories.mdᵉ) consistingᵉ ofᵉ
[cyclicᵉ rings](ring-theory.cyclic-rings.mdᵉ) andᵉ
[ringᵉ homomorphisms](ring-theory.homomorphisms-cyclic-rings.md).ᵉ

Noteᵉ thatᵉ weᵉ alreadyᵉ showedᵉ thatᵉ thereᵉ isᵉ atᵉ mostᵉ oneᵉ ringᵉ homomorphismᵉ betweenᵉ
anyᵉ twoᵉ cyclicᵉ rings,ᵉ soᵉ itᵉ followsᵉ thatᵉ theᵉ largeᵉ categoryᵉ ofᵉ cyclicᵉ ringsᵉ isᵉ
in factᵉ aᵉ [largeᵉ poset](order-theory.large-posets.md).ᵉ Theᵉ largeᵉ posetᵉ ofᵉ cyclicᵉ
ringsᵉ isᵉ constructedᵉ in theᵉ fileᵉ
[`ring-theory.poset-of-cyclic-rings`](ring-theory.poset-of-cyclic-rings.md).ᵉ

## Definition

### The precategory of cyclic rings as a full subprecategory of the precategory of rings

```agda
Cyclic-Ring-Full-Large-Subprecategoryᵉ :
  Full-Large-Subprecategoryᵉ (λ lᵉ → lᵉ) Ring-Large-Precategoryᵉ
Cyclic-Ring-Full-Large-Subprecategoryᵉ = is-cyclic-prop-Ringᵉ
```

### The large precategory of cyclic rings

```agda
Cyclic-Ring-Large-Precategoryᵉ : Large-Precategoryᵉ lsuc (_⊔ᵉ_)
Cyclic-Ring-Large-Precategoryᵉ =
  large-precategory-Full-Large-Subprecategoryᵉ
    ( Ring-Large-Precategoryᵉ)
    ( Cyclic-Ring-Full-Large-Subprecategoryᵉ)
```

### The large category of cyclic rings

```agda
abstract
  is-large-category-Cyclic-Ring-Large-Categoryᵉ :
    is-large-category-Large-Precategoryᵉ Cyclic-Ring-Large-Precategoryᵉ
  is-large-category-Cyclic-Ring-Large-Categoryᵉ =
    is-large-category-large-precategory-is-large-category-Full-Large-Subprecategoryᵉ
      ( Ring-Large-Precategoryᵉ)
      ( Cyclic-Ring-Full-Large-Subprecategoryᵉ)
      ( is-large-category-Ring-Large-Categoryᵉ)

Cyclic-Ring-Large-Categoryᵉ : Large-Categoryᵉ lsuc (_⊔ᵉ_)
large-precategory-Large-Categoryᵉ
  Cyclic-Ring-Large-Categoryᵉ =
  Cyclic-Ring-Large-Precategoryᵉ
is-large-category-Large-Categoryᵉ
  Cyclic-Ring-Large-Categoryᵉ =
  is-large-category-Cyclic-Ring-Large-Categoryᵉ
```

### The small categories of cyclic rings

```agda
Cyclic-Ring-Categoryᵉ : (lᵉ : Level) → Categoryᵉ (lsuc lᵉ) lᵉ
Cyclic-Ring-Categoryᵉ = category-Large-Categoryᵉ Cyclic-Ring-Large-Categoryᵉ
```

## Properties

### The large category of cyclic rings is a large poset

```agda
is-large-poset-Cyclic-Ring-Large-Categoryᵉ :
  is-large-poset-Large-Categoryᵉ Cyclic-Ring-Large-Categoryᵉ
is-large-poset-Cyclic-Ring-Large-Categoryᵉ =
  is-prop-hom-Cyclic-Ringᵉ
```

## See also

### Table of files related to cyclic types, groups, and rings

{{#includeᵉ tables/cyclic-types.mdᵉ}}