# Fixed points of higher group actions

```agda
module higher-group-theory.fixed-points-higher-group-actionsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levelsᵉ

open import higher-group-theory.higher-group-actionsᵉ
open import higher-group-theory.higher-groupsᵉ
```

</details>

## Idea

Theᵉ typeᵉ ofᵉ fixedᵉ pointsᵉ ofᵉ aᵉ higherᵉ groupᵉ actionᵉ `Xᵉ : BGᵉ → UU`ᵉ isᵉ theᵉ typeᵉ ofᵉ
sectionsᵉ `(uᵉ : BGᵉ) → Xᵉ u`.ᵉ

## Definition

```agda
fixed-point-action-∞-Groupᵉ :
  {l1ᵉ l2ᵉ : Level} (Gᵉ : ∞-Groupᵉ l1ᵉ) (Xᵉ : action-∞-Groupᵉ l2ᵉ Gᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
fixed-point-action-∞-Groupᵉ Gᵉ Xᵉ = (uᵉ : classifying-type-∞-Groupᵉ Gᵉ) → Xᵉ uᵉ
```