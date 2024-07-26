# Subsets of groups

```agda
module group-theory.subsets-groupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.large-locale-of-subtypesᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.groupsᵉ

open import order-theory.large-localesᵉ
open import order-theory.large-posetsᵉ
```

</details>

## Idea

Aᵉ **subset**ᵉ ofᵉ aᵉ [group](group-theory.groups.mdᵉ) `G`ᵉ isᵉ aᵉ
[subtype](foundation.subtypes.mdᵉ) ofᵉ theᵉ underlyingᵉ typeᵉ ofᵉ `G`.ᵉ Theᵉ
[largeᵉ poset](order-theory.large-posets.mdᵉ) ofᵉ allᵉ subsetsᵉ ofᵉ `G`ᵉ isᵉ calledᵉ theᵉ
**powerset**ᵉ ofᵉ `G`.ᵉ

## Definitions

### The large locale of subsets of a group

```agda
module _
  {l1ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ)
  where

  powerset-large-locale-Groupᵉ :
    Large-Localeᵉ (λ l2ᵉ → l1ᵉ ⊔ lsuc l2ᵉ) (λ l2ᵉ l3ᵉ → l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ) lzero
  powerset-large-locale-Groupᵉ = powerset-Large-Localeᵉ (type-Groupᵉ Gᵉ)
```

### The large poset of subsets of a group

```agda
module _
  {l1ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ)
  where

  powerset-large-poset-Groupᵉ :
    Large-Posetᵉ (λ l2ᵉ → l1ᵉ ⊔ lsuc l2ᵉ) (λ l2ᵉ l3ᵉ → l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  powerset-large-poset-Groupᵉ =
    large-poset-Large-Localeᵉ (powerset-large-locale-Groupᵉ Gᵉ)
```

### Subsets of groups

```agda
subset-Groupᵉ :
  (lᵉ : Level) {l1ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) → UUᵉ (lsuc lᵉ ⊔ l1ᵉ)
subset-Groupᵉ lᵉ Gᵉ = type-Large-Localeᵉ (powerset-large-locale-Groupᵉ Gᵉ) lᵉ

is-set-subset-Groupᵉ :
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) → is-setᵉ (subset-Groupᵉ l2ᵉ Gᵉ)
is-set-subset-Groupᵉ Gᵉ =
  is-set-type-Large-Localeᵉ (powerset-large-locale-Groupᵉ Gᵉ)
```