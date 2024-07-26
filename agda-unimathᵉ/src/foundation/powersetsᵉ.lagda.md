# Powersets

```agda
module foundation.powersetsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.subtypesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.setsᵉ

open import order-theory.large-posetsᵉ
open import order-theory.large-preordersᵉ
open import order-theory.posetsᵉ
open import order-theory.preordersᵉ
```

</details>

## Idea

Theᵉ **powerset**ᵉ ofᵉ aᵉ typeᵉ isᵉ theᵉ setᵉ ofᵉ allᵉ
[subtypes](foundation-core.subtypes.mdᵉ) with respectᵉ to aᵉ givenᵉ universeᵉ level.ᵉ

## Definition

```agda
powersetᵉ :
  {l1ᵉ : Level} (l2ᵉ : Level) → UUᵉ l1ᵉ → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
powersetᵉ = subtypeᵉ
```

## Properties

### The powerset is a set

```agda
module _
  {l1ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ)
  where

  is-set-powersetᵉ : {l2ᵉ : Level} → is-setᵉ (powersetᵉ l2ᵉ Aᵉ)
  is-set-powersetᵉ = is-set-subtypeᵉ

  powerset-Setᵉ : (l2ᵉ : Level) → Setᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
  powerset-Setᵉ l2ᵉ = subtype-Setᵉ l2ᵉ Aᵉ
```

### The powerset large preorder

```agda
module _
  {l1ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ)
  where

  powerset-Large-Preorderᵉ :
    Large-Preorderᵉ (λ lᵉ → l1ᵉ ⊔ lsuc lᵉ) (λ l2ᵉ l3ᵉ → l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  type-Large-Preorderᵉ powerset-Large-Preorderᵉ lᵉ = subtypeᵉ lᵉ Aᵉ
  leq-prop-Large-Preorderᵉ powerset-Large-Preorderᵉ = leq-prop-subtypeᵉ
  refl-leq-Large-Preorderᵉ powerset-Large-Preorderᵉ = refl-leq-subtypeᵉ
  transitive-leq-Large-Preorderᵉ powerset-Large-Preorderᵉ = transitive-leq-subtypeᵉ
```

### The powerset large poset

```agda
module _
  {l1ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ)
  where

  powerset-Large-Posetᵉ :
    Large-Posetᵉ (λ lᵉ → l1ᵉ ⊔ lsuc lᵉ) (λ l2ᵉ l3ᵉ → l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  large-preorder-Large-Posetᵉ powerset-Large-Posetᵉ = powerset-Large-Preorderᵉ Aᵉ
  antisymmetric-leq-Large-Posetᵉ powerset-Large-Posetᵉ Pᵉ Qᵉ =
    antisymmetric-leq-subtypeᵉ Pᵉ Qᵉ
```

### The powerset preorder at a universe level

```agda
module _
  {l1ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ)
  where

  powerset-Preorderᵉ : (l2ᵉ : Level) → Preorderᵉ (l1ᵉ ⊔ lsuc l2ᵉ) (l1ᵉ ⊔ l2ᵉ)
  powerset-Preorderᵉ = preorder-Large-Preorderᵉ (powerset-Large-Preorderᵉ Aᵉ)
```

### The powerset poset at a universe level

```agda
module _
  {l1ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ)
  where

  powerset-Posetᵉ : (l2ᵉ : Level) → Posetᵉ (l1ᵉ ⊔ lsuc l2ᵉ) (l1ᵉ ⊔ l2ᵉ)
  powerset-Posetᵉ = poset-Large-Posetᵉ (powerset-Large-Posetᵉ Aᵉ)
```