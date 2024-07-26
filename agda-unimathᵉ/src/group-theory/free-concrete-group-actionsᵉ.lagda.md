# Free concrete group actions

```agda
module group-theory.free-concrete-group-actionsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.function-typesᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.concrete-group-actionsᵉ
open import group-theory.concrete-groupsᵉ

open import higher-group-theory.free-higher-group-actionsᵉ
```

</details>

## Idea

Considerᵉ aᵉ [concreteᵉ group](group-theory.concrete-groups.mdᵉ) `G`ᵉ andᵉ aᵉ
[concreteᵉ groupᵉ action](group-theory.concrete-group-actions.mdᵉ) ofᵉ `G`ᵉ onᵉ `X`.ᵉ
Weᵉ sayᵉ thatᵉ `X`ᵉ isᵉ **free**ᵉ ifᵉ itsᵉ typeᵉ ofᵉ
[orbits](group-theory.orbits-concrete-group-actions.mdᵉ) isᵉ aᵉ
[set](foundation.sets.md).ᵉ

[Equivalently](foundation.logical-equivalences.md),ᵉ weᵉ sayᵉ thatᵉ `X`ᵉ isᵉ
**abstractlyᵉ free**ᵉ ifᵉ forᵉ anyᵉ elementᵉ `xᵉ : Xᵉ (shᵉ G)`ᵉ ofᵉ theᵉ underlyingᵉ typeᵉ ofᵉ
`X`ᵉ theᵉ actionᵉ mapᵉ

```text
  gᵉ ↦ᵉ mul-action-Concrete-Groupᵉ Gᵉ Xᵉ gᵉ xᵉ
```

isᵉ anᵉ [embedding](foundation.embeddings.md).ᵉ

## Definition

### The predicate of being a free concrete group action

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Concrete-Groupᵉ l1ᵉ) (Xᵉ : action-Concrete-Groupᵉ l2ᵉ Gᵉ)
  where

  is-free-prop-action-Concrete-Groupᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  is-free-prop-action-Concrete-Groupᵉ =
    is-free-prop-action-∞-Groupᵉ (∞-group-Concrete-Groupᵉ Gᵉ) (type-Setᵉ ∘ᵉ Xᵉ)

  is-free-action-Concrete-Groupᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-free-action-Concrete-Groupᵉ =
    is-free-action-∞-Groupᵉ (∞-group-Concrete-Groupᵉ Gᵉ) (type-Setᵉ ∘ᵉ Xᵉ)

  is-prop-is-free-action-Concrete-Groupᵉ : is-propᵉ is-free-action-Concrete-Groupᵉ
  is-prop-is-free-action-Concrete-Groupᵉ =
    is-prop-is-free-action-∞-Groupᵉ (∞-group-Concrete-Groupᵉ Gᵉ) (type-Setᵉ ∘ᵉ Xᵉ)
```

### The predicate of being an abstractly free concrete group action

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Concrete-Groupᵉ l1ᵉ) (Xᵉ : action-Concrete-Groupᵉ l2ᵉ Gᵉ)
  where

  is-abstractly-free-prop-action-Concrete-Groupᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  is-abstractly-free-prop-action-Concrete-Groupᵉ =
    is-abstractly-free-prop-action-∞-Groupᵉ
      ( ∞-group-Concrete-Groupᵉ Gᵉ)
      ( type-Setᵉ ∘ᵉ Xᵉ)

  is-abstractly-free-action-Concrete-Groupᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-abstractly-free-action-Concrete-Groupᵉ =
    is-abstractly-free-action-∞-Groupᵉ
      ( ∞-group-Concrete-Groupᵉ Gᵉ)
      ( type-Setᵉ ∘ᵉ Xᵉ)

  is-prop-is-abstractly-free-action-Concrete-Groupᵉ :
    is-propᵉ is-abstractly-free-action-Concrete-Groupᵉ
  is-prop-is-abstractly-free-action-Concrete-Groupᵉ =
    is-prop-is-abstractly-free-action-∞-Groupᵉ
      ( ∞-group-Concrete-Groupᵉ Gᵉ)
      ( type-Setᵉ ∘ᵉ Xᵉ)
```

### Free concrete group actions

```agda
free-action-Concrete-Groupᵉ :
  {l1ᵉ : Level} (l2ᵉ : Level) → Concrete-Groupᵉ l1ᵉ → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
free-action-Concrete-Groupᵉ l2ᵉ Gᵉ =
  Σᵉ (action-Concrete-Groupᵉ l2ᵉ Gᵉ) (is-free-action-Concrete-Groupᵉ Gᵉ)
```

## Properties

### A concrete group action is free if and only if it is abstractly free

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Concrete-Groupᵉ l1ᵉ) (Xᵉ : action-Concrete-Groupᵉ l2ᵉ Gᵉ)
  where

  is-abstractly-free-is-free-action-Concrete-Groupᵉ :
    is-free-action-Concrete-Groupᵉ Gᵉ Xᵉ →
    is-abstractly-free-action-Concrete-Groupᵉ Gᵉ Xᵉ
  is-abstractly-free-is-free-action-Concrete-Groupᵉ =
    is-abstractly-free-is-free-action-∞-Groupᵉ
      ( ∞-group-Concrete-Groupᵉ Gᵉ)
      ( type-Setᵉ ∘ᵉ Xᵉ)

  is-free-is-abstractly-free-action-Concrete-Groupᵉ :
    is-abstractly-free-action-Concrete-Groupᵉ Gᵉ Xᵉ →
    is-free-action-Concrete-Groupᵉ Gᵉ Xᵉ
  is-free-is-abstractly-free-action-Concrete-Groupᵉ =
    is-free-is-abstractly-free-action-∞-Groupᵉ
      ( ∞-group-Concrete-Groupᵉ Gᵉ)
      ( type-Setᵉ ∘ᵉ Xᵉ)
```