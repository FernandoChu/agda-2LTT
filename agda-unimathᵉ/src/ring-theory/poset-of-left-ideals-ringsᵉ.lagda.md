# The poset of left ideals of a ring

```agda
module ring-theory.poset-of-left-ideals-ringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relationsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.powersetsᵉ
open import foundation.propositionsᵉ
open import foundation.subtypesᵉ
open import foundation.universe-levelsᵉ

open import order-theory.large-posetsᵉ
open import order-theory.large-preordersᵉ
open import order-theory.order-preserving-maps-large-posetsᵉ
open import order-theory.order-preserving-maps-large-preordersᵉ
open import order-theory.similarity-of-elements-large-posetsᵉ

open import ring-theory.left-ideals-ringsᵉ
open import ring-theory.ringsᵉ
```

</details>

## Idea

Theᵉ [leftᵉ ideals](ring-theory.left-ideals-rings.mdᵉ) ofᵉ aᵉ
[ring](ring-theory.rings.mdᵉ) formᵉ aᵉ [largeᵉ poset](order-theory.large-posets.mdᵉ)
orderedᵉ byᵉ inclusion.ᵉ

## Definition

### The inclusion relation on left ideals

```agda
module _
  {l1ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ)
  where

  leq-prop-left-ideal-Ringᵉ :
    {l2ᵉ l3ᵉ : Level} →
    left-ideal-Ringᵉ l2ᵉ Rᵉ → left-ideal-Ringᵉ l3ᵉ Rᵉ → Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  leq-prop-left-ideal-Ringᵉ Iᵉ Jᵉ =
    leq-prop-subtypeᵉ
      ( subset-left-ideal-Ringᵉ Rᵉ Iᵉ)
      ( subset-left-ideal-Ringᵉ Rᵉ Jᵉ)

  leq-left-ideal-Ringᵉ :
    {l2ᵉ l3ᵉ : Level} →
    left-ideal-Ringᵉ l2ᵉ Rᵉ → left-ideal-Ringᵉ l3ᵉ Rᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  leq-left-ideal-Ringᵉ Iᵉ Jᵉ =
    subset-left-ideal-Ringᵉ Rᵉ Iᵉ ⊆ᵉ subset-left-ideal-Ringᵉ Rᵉ Jᵉ

  is-prop-leq-left-ideal-Ringᵉ :
    {l2ᵉ l3ᵉ : Level} (Iᵉ : left-ideal-Ringᵉ l2ᵉ Rᵉ) (Jᵉ : left-ideal-Ringᵉ l3ᵉ Rᵉ) →
    is-propᵉ (leq-left-ideal-Ringᵉ Iᵉ Jᵉ)
  is-prop-leq-left-ideal-Ringᵉ Iᵉ Jᵉ =
    is-prop-leq-subtypeᵉ
      ( subset-left-ideal-Ringᵉ Rᵉ Iᵉ)
      ( subset-left-ideal-Ringᵉ Rᵉ Jᵉ)

  refl-leq-left-ideal-Ringᵉ :
    {l2ᵉ : Level} → is-reflexiveᵉ (leq-left-ideal-Ringᵉ {l2ᵉ})
  refl-leq-left-ideal-Ringᵉ Iᵉ =
    refl-leq-subtypeᵉ (subset-left-ideal-Ringᵉ Rᵉ Iᵉ)

  transitive-leq-left-ideal-Ringᵉ :
    {l2ᵉ l3ᵉ l4ᵉ : Level}
    (Iᵉ : left-ideal-Ringᵉ l2ᵉ Rᵉ)
    (Jᵉ : left-ideal-Ringᵉ l3ᵉ Rᵉ)
    (Kᵉ : left-ideal-Ringᵉ l4ᵉ Rᵉ) →
    leq-left-ideal-Ringᵉ Jᵉ Kᵉ →
    leq-left-ideal-Ringᵉ Iᵉ Jᵉ →
    leq-left-ideal-Ringᵉ Iᵉ Kᵉ
  transitive-leq-left-ideal-Ringᵉ Iᵉ Jᵉ Kᵉ =
    transitive-leq-subtypeᵉ
      ( subset-left-ideal-Ringᵉ Rᵉ Iᵉ)
      ( subset-left-ideal-Ringᵉ Rᵉ Jᵉ)
      ( subset-left-ideal-Ringᵉ Rᵉ Kᵉ)

  antisymmetric-leq-left-ideal-Ringᵉ :
    {l2ᵉ : Level} → is-antisymmetricᵉ (leq-left-ideal-Ringᵉ {l2ᵉ})
  antisymmetric-leq-left-ideal-Ringᵉ Iᵉ Jᵉ Uᵉ Vᵉ =
    eq-has-same-elements-left-ideal-Ringᵉ Rᵉ Iᵉ Jᵉ (λ xᵉ → Uᵉ xᵉ ,ᵉ Vᵉ xᵉ)
```

### The large poset of left ideals

```agda
module _
  {l1ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ)
  where

  left-ideal-Ring-Large-Preorderᵉ :
    Large-Preorderᵉ (λ l2ᵉ → l1ᵉ ⊔ lsuc l2ᵉ) (λ l2ᵉ l3ᵉ → l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  type-Large-Preorderᵉ left-ideal-Ring-Large-Preorderᵉ lᵉ =
    left-ideal-Ringᵉ lᵉ Rᵉ
  leq-prop-Large-Preorderᵉ left-ideal-Ring-Large-Preorderᵉ =
    leq-prop-left-ideal-Ringᵉ Rᵉ
  refl-leq-Large-Preorderᵉ left-ideal-Ring-Large-Preorderᵉ =
    refl-leq-left-ideal-Ringᵉ Rᵉ
  transitive-leq-Large-Preorderᵉ left-ideal-Ring-Large-Preorderᵉ =
    transitive-leq-left-ideal-Ringᵉ Rᵉ

  left-ideal-Ring-Large-Posetᵉ :
    Large-Posetᵉ (λ l2ᵉ → l1ᵉ ⊔ lsuc l2ᵉ) (λ l2ᵉ l3ᵉ → l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  large-preorder-Large-Posetᵉ left-ideal-Ring-Large-Posetᵉ =
    left-ideal-Ring-Large-Preorderᵉ
  antisymmetric-leq-Large-Posetᵉ left-ideal-Ring-Large-Posetᵉ =
    antisymmetric-leq-left-ideal-Ringᵉ Rᵉ
```

### The similarity relation on left ideals in a ring

```agda
module _
  {l1ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ)
  where

  sim-prop-left-ideal-Ringᵉ :
    {l2ᵉ l3ᵉ : Level} (Iᵉ : left-ideal-Ringᵉ l2ᵉ Rᵉ) (Jᵉ : left-ideal-Ringᵉ l3ᵉ Rᵉ) →
    Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  sim-prop-left-ideal-Ringᵉ =
    sim-prop-Large-Posetᵉ (left-ideal-Ring-Large-Posetᵉ Rᵉ)

  sim-left-ideal-Ringᵉ :
    {l2ᵉ l3ᵉ : Level} (Iᵉ : left-ideal-Ringᵉ l2ᵉ Rᵉ) (Jᵉ : left-ideal-Ringᵉ l3ᵉ Rᵉ) →
    UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  sim-left-ideal-Ringᵉ = sim-Large-Posetᵉ (left-ideal-Ring-Large-Posetᵉ Rᵉ)

  is-prop-sim-left-ideal-Ringᵉ :
    {l2ᵉ l3ᵉ : Level} (Iᵉ : left-ideal-Ringᵉ l2ᵉ Rᵉ) (Jᵉ : left-ideal-Ringᵉ l3ᵉ Rᵉ) →
    is-propᵉ (sim-left-ideal-Ringᵉ Iᵉ Jᵉ)
  is-prop-sim-left-ideal-Ringᵉ =
    is-prop-sim-Large-Posetᵉ (left-ideal-Ring-Large-Posetᵉ Rᵉ)

  eq-sim-left-ideal-Ringᵉ :
    {l2ᵉ : Level} (Iᵉ Jᵉ : left-ideal-Ringᵉ l2ᵉ Rᵉ) → sim-left-ideal-Ringᵉ Iᵉ Jᵉ → Iᵉ ＝ᵉ Jᵉ
  eq-sim-left-ideal-Ringᵉ = eq-sim-Large-Posetᵉ (left-ideal-Ring-Large-Posetᵉ Rᵉ)
```

## Properties

### The forgetful function from left ideals to subsets preserves inclusions

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  preserves-order-subset-left-ideal-Ringᵉ :
    {l1ᵉ l2ᵉ : Level} (Iᵉ : left-ideal-Ringᵉ l1ᵉ Rᵉ) (Jᵉ : left-ideal-Ringᵉ l2ᵉ Rᵉ) →
    leq-left-ideal-Ringᵉ Rᵉ Iᵉ Jᵉ →
    subset-left-ideal-Ringᵉ Rᵉ Iᵉ ⊆ᵉ subset-left-ideal-Ringᵉ Rᵉ Jᵉ
  preserves-order-subset-left-ideal-Ringᵉ Iᵉ Jᵉ Hᵉ = Hᵉ

  subset-left-ideal-hom-large-poset-Ringᵉ :
    hom-Large-Posetᵉ
      ( λ lᵉ → lᵉ)
      ( left-ideal-Ring-Large-Posetᵉ Rᵉ)
      ( powerset-Large-Posetᵉ (type-Ringᵉ Rᵉ))
  map-hom-Large-Preorderᵉ subset-left-ideal-hom-large-poset-Ringᵉ =
    subset-left-ideal-Ringᵉ Rᵉ
  preserves-order-hom-Large-Preorderᵉ subset-left-ideal-hom-large-poset-Ringᵉ =
    preserves-order-subset-left-ideal-Ringᵉ
```