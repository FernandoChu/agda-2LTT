# The poset of radical ideals of a commutative ring

```agda
module commutative-algebra.poset-of-radical-ideals-commutative-ringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-ringsᵉ
open import commutative-algebra.poset-of-ideals-commutative-ringsᵉ
open import commutative-algebra.radical-ideals-commutative-ringsᵉ

open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.subtypesᵉ
open import foundation.universe-levelsᵉ

open import order-theory.large-posetsᵉ
open import order-theory.large-preordersᵉ
open import order-theory.order-preserving-maps-large-posetsᵉ
open import order-theory.order-preserving-maps-large-preordersᵉ
open import order-theory.similarity-of-elements-large-posetsᵉ
```

</details>

## Idea

Theᵉ **[largeᵉ poset](order-theory.large-posets.mdᵉ) ofᵉ radicalᵉ ideals**ᵉ in aᵉ
[commutativeᵉ ring](commutative-algebra.commutative-rings.mdᵉ) consistsᵉ ofᵉ
[radicalᵉ ideals](commutative-algebra.radical-ideals-commutative-rings.mdᵉ)
orderedᵉ byᵉ inclusion.ᵉ

## Definition

### The ordering of radical ideals in a commutative ring

```agda
module _
  {l1ᵉ : Level} (Aᵉ : Commutative-Ringᵉ l1ᵉ)
  where

  leq-prop-radical-ideal-Commutative-Ringᵉ :
    {l2ᵉ l3ᵉ : Level} →
    radical-ideal-Commutative-Ringᵉ l2ᵉ Aᵉ →
    radical-ideal-Commutative-Ringᵉ l3ᵉ Aᵉ → Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  leq-prop-radical-ideal-Commutative-Ringᵉ Iᵉ Jᵉ =
    leq-prop-ideal-Commutative-Ringᵉ Aᵉ
      ( ideal-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ)
      ( ideal-radical-ideal-Commutative-Ringᵉ Aᵉ Jᵉ)

  leq-radical-ideal-Commutative-Ringᵉ :
    {l2ᵉ l3ᵉ : Level} →
    radical-ideal-Commutative-Ringᵉ l2ᵉ Aᵉ →
    radical-ideal-Commutative-Ringᵉ l3ᵉ Aᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  leq-radical-ideal-Commutative-Ringᵉ Iᵉ Jᵉ =
    leq-ideal-Commutative-Ringᵉ Aᵉ
      ( ideal-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ)
      ( ideal-radical-ideal-Commutative-Ringᵉ Aᵉ Jᵉ)

  is-prop-leq-radical-ideal-Commutative-Ringᵉ :
    {l2ᵉ l3ᵉ : Level}
    (Iᵉ : radical-ideal-Commutative-Ringᵉ l2ᵉ Aᵉ)
    (Jᵉ : radical-ideal-Commutative-Ringᵉ l3ᵉ Aᵉ) →
    is-propᵉ (leq-radical-ideal-Commutative-Ringᵉ Iᵉ Jᵉ)
  is-prop-leq-radical-ideal-Commutative-Ringᵉ Iᵉ Jᵉ =
    is-prop-leq-ideal-Commutative-Ringᵉ Aᵉ
      ( ideal-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ)
      ( ideal-radical-ideal-Commutative-Ringᵉ Aᵉ Jᵉ)

  refl-leq-radical-ideal-Commutative-Ringᵉ :
    {l2ᵉ : Level} (Iᵉ : radical-ideal-Commutative-Ringᵉ l2ᵉ Aᵉ) →
    leq-radical-ideal-Commutative-Ringᵉ Iᵉ Iᵉ
  refl-leq-radical-ideal-Commutative-Ringᵉ Iᵉ =
    refl-leq-ideal-Commutative-Ringᵉ Aᵉ
      ( ideal-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ)

  transitive-leq-radical-ideal-Commutative-Ringᵉ :
    {l2ᵉ l3ᵉ l4ᵉ : Level}
    (Iᵉ : radical-ideal-Commutative-Ringᵉ l2ᵉ Aᵉ)
    (Jᵉ : radical-ideal-Commutative-Ringᵉ l3ᵉ Aᵉ)
    (Kᵉ : radical-ideal-Commutative-Ringᵉ l4ᵉ Aᵉ) →
    leq-radical-ideal-Commutative-Ringᵉ Jᵉ Kᵉ →
    leq-radical-ideal-Commutative-Ringᵉ Iᵉ Jᵉ →
    leq-radical-ideal-Commutative-Ringᵉ Iᵉ Kᵉ
  transitive-leq-radical-ideal-Commutative-Ringᵉ Iᵉ Jᵉ Kᵉ =
    transitive-leq-ideal-Commutative-Ringᵉ Aᵉ
      ( ideal-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ)
      ( ideal-radical-ideal-Commutative-Ringᵉ Aᵉ Jᵉ)
      ( ideal-radical-ideal-Commutative-Ringᵉ Aᵉ Kᵉ)

  antisymmetric-leq-radical-ideal-Commutative-Ringᵉ :
    {l2ᵉ : Level} (Iᵉ Jᵉ : radical-ideal-Commutative-Ringᵉ l2ᵉ Aᵉ) →
    leq-radical-ideal-Commutative-Ringᵉ Iᵉ Jᵉ →
    leq-radical-ideal-Commutative-Ringᵉ Jᵉ Iᵉ → Iᵉ ＝ᵉ Jᵉ
  antisymmetric-leq-radical-ideal-Commutative-Ringᵉ Iᵉ Jᵉ Hᵉ Kᵉ =
    eq-type-subtypeᵉ
      ( is-radical-ideal-prop-Commutative-Ringᵉ Aᵉ)
      ( antisymmetric-leq-ideal-Commutative-Ringᵉ Aᵉ
        ( ideal-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ)
        ( ideal-radical-ideal-Commutative-Ringᵉ Aᵉ Jᵉ)
        ( Hᵉ)
        ( Kᵉ))
```

### The large preorder of radical ideals in a commutative ring

```agda
module _
  {lᵉ : Level} (Aᵉ : Commutative-Ringᵉ lᵉ)
  where

  radical-ideal-Commutative-Ring-Large-Preorderᵉ :
    Large-Preorderᵉ (λ l1ᵉ → lᵉ ⊔ lsuc l1ᵉ) (λ l1ᵉ l2ᵉ → lᵉ ⊔ l1ᵉ ⊔ l2ᵉ)
  type-Large-Preorderᵉ radical-ideal-Commutative-Ring-Large-Preorderᵉ l1ᵉ =
    radical-ideal-Commutative-Ringᵉ l1ᵉ Aᵉ
  leq-prop-Large-Preorderᵉ radical-ideal-Commutative-Ring-Large-Preorderᵉ =
    leq-prop-radical-ideal-Commutative-Ringᵉ Aᵉ
  refl-leq-Large-Preorderᵉ radical-ideal-Commutative-Ring-Large-Preorderᵉ =
    refl-leq-radical-ideal-Commutative-Ringᵉ Aᵉ
  transitive-leq-Large-Preorderᵉ radical-ideal-Commutative-Ring-Large-Preorderᵉ =
    transitive-leq-radical-ideal-Commutative-Ringᵉ Aᵉ
```

### The large poset of radical ideals in a commutative ring

```agda
module _
  {lᵉ : Level} (Aᵉ : Commutative-Ringᵉ lᵉ)
  where

  radical-ideal-Commutative-Ring-Large-Posetᵉ :
    Large-Posetᵉ (λ l1ᵉ → lᵉ ⊔ lsuc l1ᵉ) (λ l1ᵉ l2ᵉ → lᵉ ⊔ l1ᵉ ⊔ l2ᵉ)
  large-preorder-Large-Posetᵉ radical-ideal-Commutative-Ring-Large-Posetᵉ =
    radical-ideal-Commutative-Ring-Large-Preorderᵉ Aᵉ
  antisymmetric-leq-Large-Posetᵉ radical-ideal-Commutative-Ring-Large-Posetᵉ =
    antisymmetric-leq-radical-ideal-Commutative-Ringᵉ Aᵉ
```

### Similarity of radical ideals in a commutative ring

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Aᵉ : Commutative-Ringᵉ l1ᵉ)
  (Iᵉ : radical-ideal-Commutative-Ringᵉ l2ᵉ Aᵉ)
  (Jᵉ : radical-ideal-Commutative-Ringᵉ l3ᵉ Aᵉ)
  where

  sim-prop-radical-ideal-Commutative-Ringᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  sim-prop-radical-ideal-Commutative-Ringᵉ =
    sim-prop-Large-Posetᵉ (radical-ideal-Commutative-Ring-Large-Posetᵉ Aᵉ) Iᵉ Jᵉ

  sim-radical-ideal-Commutative-Ringᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  sim-radical-ideal-Commutative-Ringᵉ =
    sim-Large-Posetᵉ (radical-ideal-Commutative-Ring-Large-Posetᵉ Aᵉ) Iᵉ Jᵉ

  is-prop-sim-radical-ideal-Commutative-Ringᵉ :
    is-propᵉ sim-radical-ideal-Commutative-Ringᵉ
  is-prop-sim-radical-ideal-Commutative-Ringᵉ =
    is-prop-sim-Large-Posetᵉ (radical-ideal-Commutative-Ring-Large-Posetᵉ Aᵉ) Iᵉ Jᵉ
```

### The inclusion of radical ideals into ideals of a commutative ring

```agda
module _
  {lᵉ : Level} (Aᵉ : Commutative-Ringᵉ lᵉ)
  where

  preserves-order-ideal-radical-ideal-Commutative-Ringᵉ :
    {l1ᵉ l2ᵉ : Level}
    (Iᵉ : radical-ideal-Commutative-Ringᵉ l1ᵉ Aᵉ)
    (Jᵉ : radical-ideal-Commutative-Ringᵉ l2ᵉ Aᵉ) →
    leq-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ Jᵉ →
    leq-ideal-Commutative-Ringᵉ Aᵉ
      ( ideal-radical-ideal-Commutative-Ringᵉ Aᵉ Iᵉ)
      ( ideal-radical-ideal-Commutative-Ringᵉ Aᵉ Jᵉ)
  preserves-order-ideal-radical-ideal-Commutative-Ringᵉ Iᵉ Jᵉ Hᵉ = Hᵉ

  ideal-radical-ideal-hom-large-poset-Commutative-Ringᵉ :
    hom-Large-Posetᵉ
      ( λ lᵉ → lᵉ)
      ( radical-ideal-Commutative-Ring-Large-Posetᵉ Aᵉ)
      ( ideal-Commutative-Ring-Large-Posetᵉ Aᵉ)
  map-hom-Large-Preorderᵉ
    ideal-radical-ideal-hom-large-poset-Commutative-Ringᵉ =
    ideal-radical-ideal-Commutative-Ringᵉ Aᵉ
  preserves-order-hom-Large-Preorderᵉ
    ideal-radical-ideal-hom-large-poset-Commutative-Ringᵉ =
    preserves-order-ideal-radical-ideal-Commutative-Ringᵉ
```