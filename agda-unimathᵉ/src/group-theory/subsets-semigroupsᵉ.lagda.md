# Subsets of semigroups

```agda
module group-theory.subsets-semigroupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.identity-typesᵉ
open import foundation.large-locale-of-subtypesᵉ
open import foundation.powersetsᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.subtypesᵉ
open import foundation.universe-levelsᵉ

open import group-theory.semigroupsᵉ

open import order-theory.large-localesᵉ
open import order-theory.large-posetsᵉ
```

</details>

## Idea

Aᵉ **subsetᵉ ofᵉ aᵉ semigroup**ᵉ `G`ᵉ isᵉ aᵉ [subtype](foundation.subtypes.mdᵉ) ofᵉ theᵉ
underlyingᵉ typeᵉ ofᵉ theᵉ [semigroup](group-theory.semigroups.mdᵉ) `G`.ᵉ Theᵉ
**powerset**ᵉ ofᵉ aᵉ semigroupᵉ isᵉ theᵉ [largeᵉ poset](order-theory.large-posets.mdᵉ)
ofᵉ allᵉ subsetsᵉ ofᵉ `G`,ᵉ i.e.,ᵉ itᵉ isᵉ theᵉ [powerset](foundation.powersets.mdᵉ) ofᵉ
theᵉ underlyingᵉ [set](foundation.sets.mdᵉ) ofᵉ `G`.ᵉ

## Definitions

### The large locale of subsets of a semigroup

```agda
module _
  {l1ᵉ : Level} (Gᵉ : Semigroupᵉ l1ᵉ)
  where

  powerset-large-locale-Semigroupᵉ :
    Large-Localeᵉ (λ l2ᵉ → l1ᵉ ⊔ lsuc l2ᵉ) (λ l2ᵉ l3ᵉ → l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ) lzero
  powerset-large-locale-Semigroupᵉ =
    powerset-Large-Localeᵉ (type-Semigroupᵉ Gᵉ)
```

### The large poset of subsets of a semigroup

```agda
module _
  {l1ᵉ : Level} (Gᵉ : Semigroupᵉ l1ᵉ)
  where

  powerset-large-poset-Semigroupᵉ :
    Large-Posetᵉ (λ lᵉ → l1ᵉ ⊔ lsuc lᵉ) (λ l2ᵉ l3ᵉ → l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  powerset-large-poset-Semigroupᵉ = powerset-Large-Posetᵉ (type-Semigroupᵉ Gᵉ)
```

### Subsets of semigroups

```agda
subset-Semigroupᵉ :
  {l1ᵉ : Level} (l2ᵉ : Level) (Gᵉ : Semigroupᵉ l1ᵉ) → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
subset-Semigroupᵉ l2ᵉ Gᵉ = subtypeᵉ l2ᵉ (type-Semigroupᵉ Gᵉ)

module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Semigroupᵉ l1ᵉ) (Pᵉ : subset-Semigroupᵉ l2ᵉ Gᵉ)
  where

  is-in-subset-Semigroupᵉ : type-Semigroupᵉ Gᵉ → UUᵉ l2ᵉ
  is-in-subset-Semigroupᵉ = is-in-subtypeᵉ Pᵉ

  is-closed-under-eq-subset-Semigroupᵉ :
    {xᵉ yᵉ : type-Semigroupᵉ Gᵉ} →
    is-in-subset-Semigroupᵉ xᵉ → (xᵉ ＝ᵉ yᵉ) → is-in-subset-Semigroupᵉ yᵉ
  is-closed-under-eq-subset-Semigroupᵉ =
    is-closed-under-eq-subtypeᵉ Pᵉ

  is-closed-under-eq-subset-Semigroup'ᵉ :
    {xᵉ yᵉ : type-Semigroupᵉ Gᵉ} →
    is-in-subset-Semigroupᵉ yᵉ → (xᵉ ＝ᵉ yᵉ) → is-in-subset-Semigroupᵉ xᵉ
  is-closed-under-eq-subset-Semigroup'ᵉ =
    is-closed-under-eq-subtype'ᵉ Pᵉ

  is-prop-is-in-subset-Semigroupᵉ :
    (xᵉ : type-Semigroupᵉ Gᵉ) → is-propᵉ (is-in-subset-Semigroupᵉ xᵉ)
  is-prop-is-in-subset-Semigroupᵉ = is-prop-is-in-subtypeᵉ Pᵉ

  type-subset-Semigroupᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  type-subset-Semigroupᵉ = type-subtypeᵉ Pᵉ

  is-set-type-subset-Semigroupᵉ : is-setᵉ type-subset-Semigroupᵉ
  is-set-type-subset-Semigroupᵉ =
    is-set-type-subtypeᵉ Pᵉ (is-set-type-Semigroupᵉ Gᵉ)

  set-subset-Semigroupᵉ : Setᵉ (l1ᵉ ⊔ l2ᵉ)
  set-subset-Semigroupᵉ = set-subsetᵉ (set-Semigroupᵉ Gᵉ) Pᵉ

  inclusion-subset-Semigroupᵉ : type-subset-Semigroupᵉ → type-Semigroupᵉ Gᵉ
  inclusion-subset-Semigroupᵉ = inclusion-subtypeᵉ Pᵉ

  ap-inclusion-subset-Semigroupᵉ :
    (xᵉ yᵉ : type-subset-Semigroupᵉ) →
    xᵉ ＝ᵉ yᵉ → (inclusion-subset-Semigroupᵉ xᵉ ＝ᵉ inclusion-subset-Semigroupᵉ yᵉ)
  ap-inclusion-subset-Semigroupᵉ = ap-inclusion-subtypeᵉ Pᵉ

  is-in-subset-inclusion-subset-Semigroupᵉ :
    (xᵉ : type-subset-Semigroupᵉ) →
    is-in-subset-Semigroupᵉ (inclusion-subset-Semigroupᵉ xᵉ)
  is-in-subset-inclusion-subset-Semigroupᵉ =
    is-in-subtype-inclusion-subtypeᵉ Pᵉ
```