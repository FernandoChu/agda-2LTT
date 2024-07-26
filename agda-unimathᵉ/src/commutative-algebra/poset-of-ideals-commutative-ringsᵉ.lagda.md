# The poset of ideals of a commutative ring

```agda
module commutative-algebra.poset-of-ideals-commutative-ringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-ringsᵉ
open import commutative-algebra.ideals-commutative-ringsᵉ

open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.universe-levelsᵉ

open import order-theory.large-posetsᵉ
open import order-theory.large-preordersᵉ

open import ring-theory.poset-of-ideals-ringsᵉ
```

</details>

## Idea

Theᵉ **[largeᵉ poset](order-theory.large-posets.mdᵉ) ofᵉ
[ideals](commutative-algebra.ideals-commutative-rings.md)**ᵉ in aᵉ
[commutativeᵉ ring](commutative-algebra.commutative-rings.mdᵉ) `A`ᵉ consistsᵉ ofᵉ
idealsᵉ in `A`ᵉ andᵉ isᵉ orderedᵉ byᵉ inclusion.ᵉ

## Definition

### The inclusion relation on ideals in a commutative ring

```agda
module _
  {l1ᵉ : Level} (Aᵉ : Commutative-Ringᵉ l1ᵉ)
  where

  leq-prop-ideal-Commutative-Ringᵉ :
    {l2ᵉ l3ᵉ : Level}
    (Iᵉ : ideal-Commutative-Ringᵉ l2ᵉ Aᵉ) (Jᵉ : ideal-Commutative-Ringᵉ l3ᵉ Aᵉ) →
    Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  leq-prop-ideal-Commutative-Ringᵉ =
    leq-prop-ideal-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)

  leq-ideal-Commutative-Ringᵉ :
    {l2ᵉ l3ᵉ : Level}
    (Iᵉ : ideal-Commutative-Ringᵉ l2ᵉ Aᵉ) (Jᵉ : ideal-Commutative-Ringᵉ l3ᵉ Aᵉ) →
    UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  leq-ideal-Commutative-Ringᵉ =
    leq-ideal-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)

  is-prop-leq-ideal-Commutative-Ringᵉ :
    {l2ᵉ l3ᵉ : Level}
    (Iᵉ : ideal-Commutative-Ringᵉ l2ᵉ Aᵉ) (Jᵉ : ideal-Commutative-Ringᵉ l3ᵉ Aᵉ) →
    is-propᵉ (leq-ideal-Commutative-Ringᵉ Iᵉ Jᵉ)
  is-prop-leq-ideal-Commutative-Ringᵉ =
    is-prop-leq-ideal-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)

  refl-leq-ideal-Commutative-Ringᵉ :
    {l2ᵉ : Level}
    (Iᵉ : ideal-Commutative-Ringᵉ l2ᵉ Aᵉ) → leq-ideal-Commutative-Ringᵉ Iᵉ Iᵉ
  refl-leq-ideal-Commutative-Ringᵉ =
    refl-leq-ideal-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)

  transitive-leq-ideal-Commutative-Ringᵉ :
    {l2ᵉ l3ᵉ l4ᵉ : Level}
    (Iᵉ : ideal-Commutative-Ringᵉ l2ᵉ Aᵉ)
    (Jᵉ : ideal-Commutative-Ringᵉ l3ᵉ Aᵉ)
    (Kᵉ : ideal-Commutative-Ringᵉ l4ᵉ Aᵉ) →
    leq-ideal-Commutative-Ringᵉ Jᵉ Kᵉ →
    leq-ideal-Commutative-Ringᵉ Iᵉ Jᵉ →
    leq-ideal-Commutative-Ringᵉ Iᵉ Kᵉ
  transitive-leq-ideal-Commutative-Ringᵉ =
    transitive-leq-ideal-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)

  antisymmetric-leq-ideal-Commutative-Ringᵉ :
    {l2ᵉ : Level} (Iᵉ Jᵉ : ideal-Commutative-Ringᵉ l2ᵉ Aᵉ) →
    leq-ideal-Commutative-Ringᵉ Iᵉ Jᵉ → leq-ideal-Commutative-Ringᵉ Jᵉ Iᵉ → Iᵉ ＝ᵉ Jᵉ
  antisymmetric-leq-ideal-Commutative-Ringᵉ =
    antisymmetric-leq-ideal-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)
```

### The large preorder of ideals in a commutative ring

```agda
module _
  {lᵉ : Level} (Aᵉ : Commutative-Ringᵉ lᵉ)
  where

  ideal-Commutative-Ring-Large-Preorderᵉ :
    Large-Preorderᵉ (λ l1ᵉ → lᵉ ⊔ lsuc l1ᵉ) (λ l1ᵉ l2ᵉ → lᵉ ⊔ l1ᵉ ⊔ l2ᵉ)
  type-Large-Preorderᵉ ideal-Commutative-Ring-Large-Preorderᵉ l1ᵉ =
    ideal-Commutative-Ringᵉ l1ᵉ Aᵉ
  leq-prop-Large-Preorderᵉ ideal-Commutative-Ring-Large-Preorderᵉ =
    leq-prop-ideal-Commutative-Ringᵉ Aᵉ
  refl-leq-Large-Preorderᵉ ideal-Commutative-Ring-Large-Preorderᵉ =
    refl-leq-ideal-Commutative-Ringᵉ Aᵉ
  transitive-leq-Large-Preorderᵉ ideal-Commutative-Ring-Large-Preorderᵉ =
    transitive-leq-ideal-Commutative-Ringᵉ Aᵉ
```

### The large poset of ideals in a commutative ring

```agda
module _
  {lᵉ : Level} (Aᵉ : Commutative-Ringᵉ lᵉ)
  where

  ideal-Commutative-Ring-Large-Posetᵉ :
    Large-Posetᵉ (λ l1ᵉ → lᵉ ⊔ lsuc l1ᵉ) (λ l1ᵉ l2ᵉ → lᵉ ⊔ l1ᵉ ⊔ l2ᵉ)
  large-preorder-Large-Posetᵉ ideal-Commutative-Ring-Large-Posetᵉ =
    ideal-Commutative-Ring-Large-Preorderᵉ Aᵉ
  antisymmetric-leq-Large-Posetᵉ ideal-Commutative-Ring-Large-Posetᵉ =
    antisymmetric-leq-ideal-Commutative-Ringᵉ Aᵉ
```

### The similarity relation on ideals in a commutative ring

```agda
module _
  {lᵉ : Level} (Aᵉ : Commutative-Ringᵉ lᵉ)
  where

  sim-prop-ideal-Commutative-Ringᵉ :
    {l1ᵉ l2ᵉ : Level}
    (Iᵉ : ideal-Commutative-Ringᵉ l1ᵉ Aᵉ) (Jᵉ : ideal-Commutative-Ringᵉ l2ᵉ Aᵉ) →
    Propᵉ (lᵉ ⊔ l1ᵉ ⊔ l2ᵉ)
  sim-prop-ideal-Commutative-Ringᵉ =
    sim-prop-ideal-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)

  sim-ideal-Commutative-Ringᵉ :
    {l1ᵉ l2ᵉ : Level}
    (Iᵉ : ideal-Commutative-Ringᵉ l1ᵉ Aᵉ) (Jᵉ : ideal-Commutative-Ringᵉ l2ᵉ Aᵉ) →
    UUᵉ (lᵉ ⊔ l1ᵉ ⊔ l2ᵉ)
  sim-ideal-Commutative-Ringᵉ =
    sim-ideal-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)

  is-prop-sim-ideal-Commutative-Ringᵉ :
    {l1ᵉ l2ᵉ : Level}
    (Iᵉ : ideal-Commutative-Ringᵉ l1ᵉ Aᵉ) (Jᵉ : ideal-Commutative-Ringᵉ l2ᵉ Aᵉ) →
    is-propᵉ (sim-ideal-Commutative-Ringᵉ Iᵉ Jᵉ)
  is-prop-sim-ideal-Commutative-Ringᵉ =
    is-prop-sim-ideal-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)

  eq-sim-ideal-Commutative-Ringᵉ :
    {l1ᵉ : Level} (Iᵉ Jᵉ : ideal-Commutative-Ringᵉ l1ᵉ Aᵉ) →
    sim-ideal-Commutative-Ringᵉ Iᵉ Jᵉ → Iᵉ ＝ᵉ Jᵉ
  eq-sim-ideal-Commutative-Ringᵉ =
    eq-sim-ideal-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)
```