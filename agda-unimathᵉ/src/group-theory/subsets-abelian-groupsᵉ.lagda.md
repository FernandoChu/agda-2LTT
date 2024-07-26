# Subsets of abelian groups

```agda
module group-theory.subsets-abelian-groupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.large-locale-of-subtypesᵉ
open import foundation.powersetsᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.abelian-groupsᵉ
open import group-theory.subsets-groupsᵉ

open import order-theory.large-localesᵉ
open import order-theory.large-posetsᵉ
```

</details>

## Idea

Aᵉ **subset**ᵉ ofᵉ anᵉ [abelianᵉ group](group-theory.abelian-groups.mdᵉ) `A`ᵉ isᵉ aᵉ
[subtype](foundation.subtypes.mdᵉ) ofᵉ theᵉ underlyingᵉ typeᵉ ofᵉ `A`.ᵉ Theᵉ
[largeᵉ poset](order-theory.large-posets.mdᵉ) ofᵉ allᵉ subsetsᵉ ofᵉ `A`ᵉ isᵉ calledᵉ theᵉ
**powerset**ᵉ ofᵉ `A`.ᵉ

## Definitions

### The large locale of subsets of an abelian group

```agda
module _
  {l1ᵉ : Level} (Gᵉ : Abᵉ l1ᵉ)
  where

  powerset-large-locale-Abᵉ :
    Large-Localeᵉ (λ l2ᵉ → l1ᵉ ⊔ lsuc l2ᵉ) (λ l2ᵉ l3ᵉ → l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ) lzero
  powerset-large-locale-Abᵉ = powerset-Large-Localeᵉ (type-Abᵉ Gᵉ)
```

### The large poset of subsets of an abelian group

```agda
module _
  {l1ᵉ : Level} (Gᵉ : Abᵉ l1ᵉ)
  where

  powerset-large-poset-Abᵉ :
    Large-Posetᵉ (λ l2ᵉ → l1ᵉ ⊔ lsuc l2ᵉ) (λ l2ᵉ l3ᵉ → l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  powerset-large-poset-Abᵉ =
    large-poset-Large-Localeᵉ (powerset-large-locale-Abᵉ Gᵉ)
```

### Subsets of abelian groups

```agda
subset-Abᵉ :
  (lᵉ : Level) {l1ᵉ : Level} (Aᵉ : Abᵉ l1ᵉ) → UUᵉ (lsuc lᵉ ⊔ l1ᵉ)
subset-Abᵉ lᵉ Aᵉ = subset-Groupᵉ lᵉ (group-Abᵉ Aᵉ)

is-set-subset-Abᵉ :
  (lᵉ : Level) {l1ᵉ : Level} (Aᵉ : Abᵉ l1ᵉ) → is-setᵉ (subset-Abᵉ lᵉ Aᵉ)
is-set-subset-Abᵉ lᵉ Aᵉ = is-set-subset-Groupᵉ (group-Abᵉ Aᵉ)
```