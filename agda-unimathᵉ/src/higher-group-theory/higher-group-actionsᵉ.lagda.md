# Higher group actions

```agda
module higher-group-theory.higher-group-actionsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.identity-typesᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.universe-levelsᵉ

open import higher-group-theory.higher-groupsᵉ
```

</details>

## Idea

Anᵉ **actionᵉ ofᵉ aᵉ [higherᵉ group](higher-group-theory.higher-groups.md)**ᵉ `G`ᵉ onᵉ aᵉ
typeᵉ isᵉ justᵉ aᵉ typeᵉ familyᵉ overᵉ `BG`.ᵉ

## Definition

```agda
action-∞-Groupᵉ :
  {l1ᵉ : Level} (l2ᵉ : Level) (Gᵉ : ∞-Groupᵉ l1ᵉ) → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
action-∞-Groupᵉ l2ᵉ Gᵉ = classifying-type-∞-Groupᵉ Gᵉ → UUᵉ l2ᵉ

module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : ∞-Groupᵉ l1ᵉ) (Xᵉ : action-∞-Groupᵉ l2ᵉ Gᵉ)
  where

  type-action-∞-Groupᵉ : UUᵉ l2ᵉ
  type-action-∞-Groupᵉ = Xᵉ (shape-∞-Groupᵉ Gᵉ)

  mul-action-∞-Groupᵉ :
    type-∞-Groupᵉ Gᵉ → type-action-∞-Groupᵉ → type-action-∞-Groupᵉ
  mul-action-∞-Groupᵉ = trᵉ Xᵉ

  associative-mul-action-∞-Groupᵉ :
    (hᵉ gᵉ : type-∞-Groupᵉ Gᵉ) (xᵉ : type-action-∞-Groupᵉ) →
    (mul-action-∞-Groupᵉ (mul-∞-Groupᵉ Gᵉ hᵉ gᵉ) xᵉ) ＝ᵉ
    (mul-action-∞-Groupᵉ gᵉ (mul-action-∞-Groupᵉ hᵉ xᵉ))
  associative-mul-action-∞-Groupᵉ = tr-concatᵉ {Bᵉ = Xᵉ}

  unit-law-mul-action-∞-Groupᵉ :
    (xᵉ : type-action-∞-Groupᵉ) → mul-action-∞-Groupᵉ reflᵉ xᵉ ＝ᵉ xᵉ
  unit-law-mul-action-∞-Groupᵉ xᵉ = reflᵉ
```