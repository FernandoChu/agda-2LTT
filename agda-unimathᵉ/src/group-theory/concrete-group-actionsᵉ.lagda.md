# Concrete group actions

```agda
module group-theory.concrete-group-actionsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.function-typesᵉ
open import foundation.setsᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.concrete-groupsᵉ
```

</details>

## Idea

Givenᵉ aᵉ [concreteᵉ group](group-theory.concrete-groups.mdᵉ) `G`,ᵉ aᵉ **concreteᵉ
actionᵉ of**ᵉ `G`ᵉ onᵉ aᵉ typeᵉ isᵉ definedᵉ to beᵉ aᵉ typeᵉ familyᵉ overᵉ `BG`.ᵉ Givenᵉ aᵉ typeᵉ
familyᵉ `X`ᵉ overᵉ `BG`,ᵉ theᵉ typeᵉ beingᵉ actedᵉ onᵉ isᵉ theᵉ typeᵉ `Xᵉ *`,ᵉ andᵉ theᵉ actionᵉ
ofᵉ `G`ᵉ onᵉ `Xᵉ *`ᵉ isᵉ givenᵉ byᵉ transport.ᵉ

## Definition

```agda
module _
  {l1ᵉ : Level} (l2ᵉ : Level) (Gᵉ : Concrete-Groupᵉ l1ᵉ)
  where

  action-Concrete-Groupᵉ : UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
  action-Concrete-Groupᵉ = classifying-type-Concrete-Groupᵉ Gᵉ → Setᵉ l2ᵉ

module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Concrete-Groupᵉ l1ᵉ) (Xᵉ : action-Concrete-Groupᵉ l2ᵉ Gᵉ)
  where

  set-action-Concrete-Groupᵉ : Setᵉ l2ᵉ
  set-action-Concrete-Groupᵉ = Xᵉ (shape-Concrete-Groupᵉ Gᵉ)

  type-action-Concrete-Groupᵉ : UUᵉ l2ᵉ
  type-action-Concrete-Groupᵉ = type-Setᵉ set-action-Concrete-Groupᵉ

  is-set-type-action-Concrete-Groupᵉ : is-setᵉ type-action-Concrete-Groupᵉ
  is-set-type-action-Concrete-Groupᵉ = is-set-type-Setᵉ set-action-Concrete-Groupᵉ

  mul-action-Concrete-Groupᵉ :
    type-Concrete-Groupᵉ Gᵉ →
    type-action-Concrete-Groupᵉ → type-action-Concrete-Groupᵉ
  mul-action-Concrete-Groupᵉ gᵉ xᵉ = trᵉ (type-Setᵉ ∘ᵉ Xᵉ) gᵉ xᵉ
```