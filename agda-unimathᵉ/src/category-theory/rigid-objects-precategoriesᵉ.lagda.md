# Rigid objects in a precategory

```agda
module category-theory.rigid-objects-precategoriesᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.isomorphisms-in-precategoriesᵉ
open import category-theory.precategoriesᵉ

open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.propositionsᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Aᵉ **rigidᵉ object**ᵉ in aᵉ [precategory](category-theory.precategories.mdᵉ) isᵉ anᵉ
objectᵉ whoseᵉ [automorphismᵉ group](group-theory.automorphism-groups.mdᵉ) isᵉ
[trivial](group-theory.trivial-groups.md).ᵉ

## Definitions

### The predicate of being rigid

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ) (xᵉ : obj-Precategoryᵉ Cᵉ)
  where

  is-rigid-obj-prop-Precategoryᵉ : Propᵉ l2ᵉ
  is-rigid-obj-prop-Precategoryᵉ = is-contr-Propᵉ (iso-Precategoryᵉ Cᵉ xᵉ xᵉ)

  is-rigid-obj-Precategoryᵉ : UUᵉ l2ᵉ
  is-rigid-obj-Precategoryᵉ = type-Propᵉ is-rigid-obj-prop-Precategoryᵉ

  is-prop-is-rigid-obj-Precategoryᵉ : is-propᵉ is-rigid-obj-Precategoryᵉ
  is-prop-is-rigid-obj-Precategoryᵉ =
    is-prop-type-Propᵉ is-rigid-obj-prop-Precategoryᵉ
```

### The type of rigid objects in a precategory

```agda
rigid-obj-Precategoryᵉ : {l1ᵉ l2ᵉ : Level} (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
rigid-obj-Precategoryᵉ Cᵉ = Σᵉ (obj-Precategoryᵉ Cᵉ) (is-rigid-obj-Precategoryᵉ Cᵉ)

module _
  {l1ᵉ l2ᵉ : Level} (Cᵉ : Precategoryᵉ l1ᵉ l2ᵉ)
  where

  obj-rigid-obj-Precategoryᵉ : rigid-obj-Precategoryᵉ Cᵉ → obj-Precategoryᵉ Cᵉ
  obj-rigid-obj-Precategoryᵉ = pr1ᵉ

  is-rigid-rigid-obj-Precategoryᵉ :
    (xᵉ : rigid-obj-Precategoryᵉ Cᵉ) →
    is-rigid-obj-Precategoryᵉ Cᵉ (obj-rigid-obj-Precategoryᵉ xᵉ)
  is-rigid-rigid-obj-Precategoryᵉ = pr2ᵉ
```

## External links

-ᵉ [rigidᵉ object](https://ncatlab.org/nlab/show/rigid+objectᵉ) atᵉ $n$Labᵉ