# The category of semigroups

```agda
module group-theory.category-of-semigroupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categoriesᵉ
open import category-theory.large-categoriesᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ

open import group-theory.isomorphisms-semigroupsᵉ
open import group-theory.precategory-of-semigroupsᵉ
open import group-theory.semigroupsᵉ
```

</details>

## Idea

Sinceᵉ isomorphicᵉ semigroupsᵉ areᵉ equal,ᵉ theᵉ precategoryᵉ ofᵉ semigroupsᵉ isᵉ aᵉ
category.ᵉ

## Definition

### The large category of semigroups

```agda
is-large-category-Semigroupᵉ :
  is-large-category-Large-Precategoryᵉ Semigroup-Large-Precategoryᵉ
is-large-category-Semigroupᵉ Gᵉ =
  fundamental-theorem-idᵉ (is-torsorial-iso-Semigroupᵉ Gᵉ) (iso-eq-Semigroupᵉ Gᵉ)

extensionality-Semigroupᵉ :
  {lᵉ : Level} (Gᵉ Hᵉ : Semigroupᵉ lᵉ) → Idᵉ Gᵉ Hᵉ ≃ᵉ iso-Semigroupᵉ Gᵉ Hᵉ
pr1ᵉ (extensionality-Semigroupᵉ Gᵉ Hᵉ) = iso-eq-Semigroupᵉ Gᵉ Hᵉ
pr2ᵉ (extensionality-Semigroupᵉ Gᵉ Hᵉ) = is-large-category-Semigroupᵉ Gᵉ Hᵉ

eq-iso-Semigroupᵉ :
  {lᵉ : Level} (Gᵉ Hᵉ : Semigroupᵉ lᵉ) → iso-Semigroupᵉ Gᵉ Hᵉ → Idᵉ Gᵉ Hᵉ
eq-iso-Semigroupᵉ Gᵉ Hᵉ = map-inv-is-equivᵉ (is-large-category-Semigroupᵉ Gᵉ Hᵉ)

Semigroup-Large-Categoryᵉ : Large-Categoryᵉ lsuc (_⊔ᵉ_)
large-precategory-Large-Categoryᵉ Semigroup-Large-Categoryᵉ =
  Semigroup-Large-Precategoryᵉ
is-large-category-Large-Categoryᵉ Semigroup-Large-Categoryᵉ =
  is-large-category-Semigroupᵉ
```

### The category of small semigroups

```agda
Semigroup-Categoryᵉ : (lᵉ : Level) → Categoryᵉ (lsuc lᵉ) lᵉ
Semigroup-Categoryᵉ = category-Large-Categoryᵉ Semigroup-Large-Categoryᵉ
```