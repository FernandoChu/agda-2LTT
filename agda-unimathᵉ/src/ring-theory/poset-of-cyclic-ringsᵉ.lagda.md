# The poset of cyclic rings

```agda
module ring-theory.poset-of-cyclic-ringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levelsᵉ

open import order-theory.large-posetsᵉ

open import ring-theory.category-of-cyclic-ringsᵉ
```

</details>

## Idea

Theᵉ **largeᵉ poset**ᵉ ofᵉ [cyclicᵉ rings](ring-theory.cyclic-rings.mdᵉ) isᵉ justᵉ theᵉ
[largeᵉ categoryᵉ ofᵉ cyclicᵉ rings](ring-theory.category-of-cyclic-rings.md),ᵉ whichᵉ
happensᵉ to beᵉ aᵉ [largeᵉ poset](order-theory.large-posets.md).ᵉ

Theᵉ largeᵉ posetᵉ ofᵉ cyclicᵉ ringsᵉ isᵉ dualᵉ to theᵉ largeᵉ posetᵉ ofᵉ
[subgroups](group-theory.subgroups.mdᵉ) ofᵉ theᵉ
[groupᵉ ofᵉ integers](elementary-number-theory.group-of-integers.md).ᵉ

## Definition

### The large poset of cyclic rings

```agda
Cyclic-Ring-Large-Posetᵉ : Large-Posetᵉ lsuc (_⊔ᵉ_)
Cyclic-Ring-Large-Posetᵉ =
  large-poset-Large-Categoryᵉ
    ( Cyclic-Ring-Large-Categoryᵉ)
    ( is-large-poset-Cyclic-Ring-Large-Categoryᵉ)
```

## See also

### Table of files related to cyclic types, groups, and rings

{{#includeᵉ tables/cyclic-types.mdᵉ}}