# Isomorphisms of concrete groups

```agda
module group-theory.isomorphisms-concrete-groupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.isomorphisms-in-large-precategoriesᵉ

open import foundation.universe-levelsᵉ

open import group-theory.concrete-groupsᵉ
open import group-theory.precategory-of-concrete-groupsᵉ
```

</details>

## Idea

**Isomorphisms**ᵉ ofᵉ [concreteᵉ groups](group-theory.concrete-groups.mdᵉ) areᵉ
[isomorphisms](category-theory.isomorphisms-in-large-precategories.mdᵉ) in theᵉ
[largeᵉ precategoryᵉ ofᵉ concreteᵉ groups](group-theory.precategory-of-concrete-groups.md).ᵉ

## Definition

```agda
iso-Concrete-Groupᵉ :
  {l1ᵉ l2ᵉ : Level} → Concrete-Groupᵉ l1ᵉ → Concrete-Groupᵉ l2ᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
iso-Concrete-Groupᵉ = iso-Large-Precategoryᵉ Concrete-Group-Large-Precategoryᵉ
```

## Properties

### Equivalences of concrete groups are isomorphisms of concrete groups

Thisᵉ remainsᵉ to beᵉ shown.ᵉ
[#736](https://github.com/UniMath/agda-unimath/issues/736ᵉ)