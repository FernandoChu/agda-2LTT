# The poset of ideals of a ring

```agda
module ring-theory.poset-of-ideals-ringsᵉ where
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

open import ring-theory.ideals-ringsᵉ
open import ring-theory.ringsᵉ
```

</details>

## Idea

Theᵉ [ideals](ring-theory.ideals-rings.mdᵉ) ofᵉ aᵉ [ring](ring-theory.rings.mdᵉ) formᵉ
aᵉ [largeᵉ poset](order-theory.large-posets.mdᵉ) orderedᵉ byᵉ inclusion.ᵉ

## Definition

### The inclusion relation on ideals

```agda
module _
  {l1ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ)
  where

  leq-prop-ideal-Ringᵉ :
    {l2ᵉ l3ᵉ : Level} → ideal-Ringᵉ l2ᵉ Rᵉ → ideal-Ringᵉ l3ᵉ Rᵉ → Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  leq-prop-ideal-Ringᵉ Iᵉ Jᵉ =
    leq-prop-subtypeᵉ
      ( subset-ideal-Ringᵉ Rᵉ Iᵉ)
      ( subset-ideal-Ringᵉ Rᵉ Jᵉ)

  leq-ideal-Ringᵉ :
    {l2ᵉ l3ᵉ : Level} → ideal-Ringᵉ l2ᵉ Rᵉ → ideal-Ringᵉ l3ᵉ Rᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  leq-ideal-Ringᵉ Iᵉ Jᵉ =
    subset-ideal-Ringᵉ Rᵉ Iᵉ ⊆ᵉ subset-ideal-Ringᵉ Rᵉ Jᵉ

  is-prop-leq-ideal-Ringᵉ :
    {l2ᵉ l3ᵉ : Level} (Iᵉ : ideal-Ringᵉ l2ᵉ Rᵉ) (Jᵉ : ideal-Ringᵉ l3ᵉ Rᵉ) →
    is-propᵉ (leq-ideal-Ringᵉ Iᵉ Jᵉ)
  is-prop-leq-ideal-Ringᵉ Iᵉ Jᵉ =
    is-prop-leq-subtypeᵉ (subset-ideal-Ringᵉ Rᵉ Iᵉ) (subset-ideal-Ringᵉ Rᵉ Jᵉ)

  refl-leq-ideal-Ringᵉ :
    {l2ᵉ : Level} → is-reflexiveᵉ (leq-ideal-Ringᵉ {l2ᵉ})
  refl-leq-ideal-Ringᵉ Iᵉ =
    refl-leq-subtypeᵉ (subset-ideal-Ringᵉ Rᵉ Iᵉ)

  transitive-leq-ideal-Ringᵉ :
    {l2ᵉ l3ᵉ l4ᵉ : Level}
    (Iᵉ : ideal-Ringᵉ l2ᵉ Rᵉ)
    (Jᵉ : ideal-Ringᵉ l3ᵉ Rᵉ)
    (Kᵉ : ideal-Ringᵉ l4ᵉ Rᵉ) →
    leq-ideal-Ringᵉ Jᵉ Kᵉ →
    leq-ideal-Ringᵉ Iᵉ Jᵉ →
    leq-ideal-Ringᵉ Iᵉ Kᵉ
  transitive-leq-ideal-Ringᵉ Iᵉ Jᵉ Kᵉ =
    transitive-leq-subtypeᵉ
      ( subset-ideal-Ringᵉ Rᵉ Iᵉ)
      ( subset-ideal-Ringᵉ Rᵉ Jᵉ)
      ( subset-ideal-Ringᵉ Rᵉ Kᵉ)

  antisymmetric-leq-ideal-Ringᵉ :
    {l2ᵉ : Level} → is-antisymmetricᵉ (leq-ideal-Ringᵉ {l2ᵉ})
  antisymmetric-leq-ideal-Ringᵉ Iᵉ Jᵉ Uᵉ Vᵉ =
    eq-has-same-elements-ideal-Ringᵉ Rᵉ Iᵉ Jᵉ (λ xᵉ → Uᵉ xᵉ ,ᵉ Vᵉ xᵉ)
```

### The large poset of ideals

```agda
module _
  {l1ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ)
  where

  ideal-Ring-Large-Preorderᵉ :
    Large-Preorderᵉ (λ l2ᵉ → l1ᵉ ⊔ lsuc l2ᵉ) (λ l2ᵉ l3ᵉ → l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  type-Large-Preorderᵉ ideal-Ring-Large-Preorderᵉ lᵉ = ideal-Ringᵉ lᵉ Rᵉ
  leq-prop-Large-Preorderᵉ ideal-Ring-Large-Preorderᵉ = leq-prop-ideal-Ringᵉ Rᵉ
  refl-leq-Large-Preorderᵉ ideal-Ring-Large-Preorderᵉ = refl-leq-ideal-Ringᵉ Rᵉ
  transitive-leq-Large-Preorderᵉ ideal-Ring-Large-Preorderᵉ =
    transitive-leq-ideal-Ringᵉ Rᵉ

  ideal-Ring-Large-Posetᵉ :
    Large-Posetᵉ (λ l2ᵉ → l1ᵉ ⊔ lsuc l2ᵉ) (λ l2ᵉ l3ᵉ → l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  large-preorder-Large-Posetᵉ ideal-Ring-Large-Posetᵉ = ideal-Ring-Large-Preorderᵉ
  antisymmetric-leq-Large-Posetᵉ ideal-Ring-Large-Posetᵉ =
    antisymmetric-leq-ideal-Ringᵉ Rᵉ
```

### The similarity relation on ideals in a ring

```agda
module _
  {l1ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ)
  where

  sim-prop-ideal-Ringᵉ :
    {l2ᵉ l3ᵉ : Level} (Iᵉ : ideal-Ringᵉ l2ᵉ Rᵉ) (Jᵉ : ideal-Ringᵉ l3ᵉ Rᵉ) →
    Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  sim-prop-ideal-Ringᵉ =
    sim-prop-Large-Posetᵉ (ideal-Ring-Large-Posetᵉ Rᵉ)

  sim-ideal-Ringᵉ :
    {l2ᵉ l3ᵉ : Level} (Iᵉ : ideal-Ringᵉ l2ᵉ Rᵉ) (Jᵉ : ideal-Ringᵉ l3ᵉ Rᵉ) →
    UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  sim-ideal-Ringᵉ = sim-Large-Posetᵉ (ideal-Ring-Large-Posetᵉ Rᵉ)

  is-prop-sim-ideal-Ringᵉ :
    {l2ᵉ l3ᵉ : Level} (Iᵉ : ideal-Ringᵉ l2ᵉ Rᵉ) (Jᵉ : ideal-Ringᵉ l3ᵉ Rᵉ) →
    is-propᵉ (sim-ideal-Ringᵉ Iᵉ Jᵉ)
  is-prop-sim-ideal-Ringᵉ =
    is-prop-sim-Large-Posetᵉ (ideal-Ring-Large-Posetᵉ Rᵉ)

  eq-sim-ideal-Ringᵉ :
    {l2ᵉ : Level} (Iᵉ Jᵉ : ideal-Ringᵉ l2ᵉ Rᵉ) → sim-ideal-Ringᵉ Iᵉ Jᵉ → Iᵉ ＝ᵉ Jᵉ
  eq-sim-ideal-Ringᵉ = eq-sim-Large-Posetᵉ (ideal-Ring-Large-Posetᵉ Rᵉ)
```

## Properties

### The forgetful function from ideals to subsets preserves inclusions

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  preserves-order-subset-ideal-Ringᵉ :
    {l1ᵉ l2ᵉ : Level} (Iᵉ : ideal-Ringᵉ l1ᵉ Rᵉ) (Jᵉ : ideal-Ringᵉ l2ᵉ Rᵉ) →
    leq-ideal-Ringᵉ Rᵉ Iᵉ Jᵉ → subset-ideal-Ringᵉ Rᵉ Iᵉ ⊆ᵉ subset-ideal-Ringᵉ Rᵉ Jᵉ
  preserves-order-subset-ideal-Ringᵉ Iᵉ Jᵉ Hᵉ = Hᵉ

  subset-ideal-hom-large-poset-Ringᵉ :
    hom-Large-Posetᵉ
      ( λ lᵉ → lᵉ)
      ( ideal-Ring-Large-Posetᵉ Rᵉ)
      ( powerset-Large-Posetᵉ (type-Ringᵉ Rᵉ))
  map-hom-Large-Preorderᵉ subset-ideal-hom-large-poset-Ringᵉ =
    subset-ideal-Ringᵉ Rᵉ
  preserves-order-hom-Large-Preorderᵉ subset-ideal-hom-large-poset-Ringᵉ =
    preserves-order-subset-ideal-Ringᵉ
```