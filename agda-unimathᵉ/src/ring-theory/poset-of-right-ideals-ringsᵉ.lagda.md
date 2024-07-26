# The poset of right ideals of a ring

```agda
module ring-theory.poset-of-right-ideals-ringsᵉ where
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

open import ring-theory.right-ideals-ringsᵉ
open import ring-theory.ringsᵉ
```

</details>

## Idea

Theᵉ [rightᵉ ideals](ring-theory.right-ideals-rings.mdᵉ) ofᵉ aᵉ
[ring](ring-theory.rings.mdᵉ) formᵉ aᵉ [largeᵉ poset](order-theory.large-posets.mdᵉ)
orderedᵉ byᵉ inclusion.ᵉ

## Definition

### The inclusion relation on right ideals

```agda
module _
  {l1ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ)
  where

  leq-prop-right-ideal-Ringᵉ :
    {l2ᵉ l3ᵉ : Level} →
    right-ideal-Ringᵉ l2ᵉ Rᵉ → right-ideal-Ringᵉ l3ᵉ Rᵉ → Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  leq-prop-right-ideal-Ringᵉ Iᵉ Jᵉ =
    leq-prop-subtypeᵉ
      ( subset-right-ideal-Ringᵉ Rᵉ Iᵉ)
      ( subset-right-ideal-Ringᵉ Rᵉ Jᵉ)

  leq-right-ideal-Ringᵉ :
    {l2ᵉ l3ᵉ : Level} →
    right-ideal-Ringᵉ l2ᵉ Rᵉ → right-ideal-Ringᵉ l3ᵉ Rᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  leq-right-ideal-Ringᵉ Iᵉ Jᵉ =
    subset-right-ideal-Ringᵉ Rᵉ Iᵉ ⊆ᵉ subset-right-ideal-Ringᵉ Rᵉ Jᵉ

  is-prop-leq-right-ideal-Ringᵉ :
    {l2ᵉ l3ᵉ : Level} (Iᵉ : right-ideal-Ringᵉ l2ᵉ Rᵉ) (Jᵉ : right-ideal-Ringᵉ l3ᵉ Rᵉ) →
    is-propᵉ (leq-right-ideal-Ringᵉ Iᵉ Jᵉ)
  is-prop-leq-right-ideal-Ringᵉ Iᵉ Jᵉ =
    is-prop-leq-subtypeᵉ
      ( subset-right-ideal-Ringᵉ Rᵉ Iᵉ)
      ( subset-right-ideal-Ringᵉ Rᵉ Jᵉ)

  refl-leq-right-ideal-Ringᵉ :
    {l2ᵉ : Level} → is-reflexiveᵉ (leq-right-ideal-Ringᵉ {l2ᵉ})
  refl-leq-right-ideal-Ringᵉ Iᵉ =
    refl-leq-subtypeᵉ (subset-right-ideal-Ringᵉ Rᵉ Iᵉ)

  transitive-leq-right-ideal-Ringᵉ :
    {l2ᵉ l3ᵉ l4ᵉ : Level}
    (Iᵉ : right-ideal-Ringᵉ l2ᵉ Rᵉ)
    (Jᵉ : right-ideal-Ringᵉ l3ᵉ Rᵉ)
    (Kᵉ : right-ideal-Ringᵉ l4ᵉ Rᵉ) →
    leq-right-ideal-Ringᵉ Jᵉ Kᵉ →
    leq-right-ideal-Ringᵉ Iᵉ Jᵉ →
    leq-right-ideal-Ringᵉ Iᵉ Kᵉ
  transitive-leq-right-ideal-Ringᵉ Iᵉ Jᵉ Kᵉ =
    transitive-leq-subtypeᵉ
      ( subset-right-ideal-Ringᵉ Rᵉ Iᵉ)
      ( subset-right-ideal-Ringᵉ Rᵉ Jᵉ)
      ( subset-right-ideal-Ringᵉ Rᵉ Kᵉ)

  antisymmetric-leq-right-ideal-Ringᵉ :
    {l2ᵉ : Level} → is-antisymmetricᵉ (leq-right-ideal-Ringᵉ {l2ᵉ})
  antisymmetric-leq-right-ideal-Ringᵉ Iᵉ Jᵉ Uᵉ Vᵉ =
    eq-has-same-elements-right-ideal-Ringᵉ Rᵉ Iᵉ Jᵉ (λ xᵉ → Uᵉ xᵉ ,ᵉ Vᵉ xᵉ)
```

### The large poset of right ideals

```agda
module _
  {l1ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ)
  where

  right-ideal-Ring-Large-Preorderᵉ :
    Large-Preorderᵉ (λ l2ᵉ → l1ᵉ ⊔ lsuc l2ᵉ) (λ l2ᵉ l3ᵉ → l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  type-Large-Preorderᵉ right-ideal-Ring-Large-Preorderᵉ lᵉ =
    right-ideal-Ringᵉ lᵉ Rᵉ
  leq-prop-Large-Preorderᵉ right-ideal-Ring-Large-Preorderᵉ =
    leq-prop-right-ideal-Ringᵉ Rᵉ
  refl-leq-Large-Preorderᵉ right-ideal-Ring-Large-Preorderᵉ =
    refl-leq-right-ideal-Ringᵉ Rᵉ
  transitive-leq-Large-Preorderᵉ right-ideal-Ring-Large-Preorderᵉ =
    transitive-leq-right-ideal-Ringᵉ Rᵉ

  right-ideal-Ring-Large-Posetᵉ :
    Large-Posetᵉ (λ l2ᵉ → l1ᵉ ⊔ lsuc l2ᵉ) (λ l2ᵉ l3ᵉ → l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  large-preorder-Large-Posetᵉ right-ideal-Ring-Large-Posetᵉ =
    right-ideal-Ring-Large-Preorderᵉ
  antisymmetric-leq-Large-Posetᵉ right-ideal-Ring-Large-Posetᵉ =
    antisymmetric-leq-right-ideal-Ringᵉ Rᵉ
```

### The similarity relation on right ideals in a ring

```agda
module _
  {l1ᵉ : Level} (Rᵉ : Ringᵉ l1ᵉ)
  where

  sim-prop-right-ideal-Ringᵉ :
    {l2ᵉ l3ᵉ : Level} (Iᵉ : right-ideal-Ringᵉ l2ᵉ Rᵉ) (Jᵉ : right-ideal-Ringᵉ l3ᵉ Rᵉ) →
    Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  sim-prop-right-ideal-Ringᵉ =
    sim-prop-Large-Posetᵉ (right-ideal-Ring-Large-Posetᵉ Rᵉ)

  sim-right-ideal-Ringᵉ :
    {l2ᵉ l3ᵉ : Level} (Iᵉ : right-ideal-Ringᵉ l2ᵉ Rᵉ) (Jᵉ : right-ideal-Ringᵉ l3ᵉ Rᵉ) →
    UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  sim-right-ideal-Ringᵉ = sim-Large-Posetᵉ (right-ideal-Ring-Large-Posetᵉ Rᵉ)

  is-prop-sim-right-ideal-Ringᵉ :
    {l2ᵉ l3ᵉ : Level} (Iᵉ : right-ideal-Ringᵉ l2ᵉ Rᵉ) (Jᵉ : right-ideal-Ringᵉ l3ᵉ Rᵉ) →
    is-propᵉ (sim-right-ideal-Ringᵉ Iᵉ Jᵉ)
  is-prop-sim-right-ideal-Ringᵉ =
    is-prop-sim-Large-Posetᵉ (right-ideal-Ring-Large-Posetᵉ Rᵉ)

  eq-sim-right-ideal-Ringᵉ :
    {l2ᵉ : Level} (Iᵉ Jᵉ : right-ideal-Ringᵉ l2ᵉ Rᵉ) →
    sim-right-ideal-Ringᵉ Iᵉ Jᵉ → Iᵉ ＝ᵉ Jᵉ
  eq-sim-right-ideal-Ringᵉ = eq-sim-Large-Posetᵉ (right-ideal-Ring-Large-Posetᵉ Rᵉ)
```

## Properties

### The forgetful function from right ideals to subsets preserves inclusions

```agda
module _
  {lᵉ : Level} (Rᵉ : Ringᵉ lᵉ)
  where

  preserves-order-subset-right-ideal-Ringᵉ :
    {l1ᵉ l2ᵉ : Level} (Iᵉ : right-ideal-Ringᵉ l1ᵉ Rᵉ) (Jᵉ : right-ideal-Ringᵉ l2ᵉ Rᵉ) →
    leq-right-ideal-Ringᵉ Rᵉ Iᵉ Jᵉ →
    subset-right-ideal-Ringᵉ Rᵉ Iᵉ ⊆ᵉ subset-right-ideal-Ringᵉ Rᵉ Jᵉ
  preserves-order-subset-right-ideal-Ringᵉ Iᵉ Jᵉ Hᵉ = Hᵉ

  subset-right-ideal-hom-large-poset-Ringᵉ :
    hom-Large-Posetᵉ
      ( λ lᵉ → lᵉ)
      ( right-ideal-Ring-Large-Posetᵉ Rᵉ)
      ( powerset-Large-Posetᵉ (type-Ringᵉ Rᵉ))
  map-hom-Large-Preorderᵉ subset-right-ideal-hom-large-poset-Ringᵉ =
    subset-right-ideal-Ringᵉ Rᵉ
  preserves-order-hom-Large-Preorderᵉ subset-right-ideal-hom-large-poset-Ringᵉ =
    preserves-order-subset-right-ideal-Ringᵉ
```