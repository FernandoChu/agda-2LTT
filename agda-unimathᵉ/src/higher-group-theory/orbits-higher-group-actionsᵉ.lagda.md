# Orbits of higher group actions

```agda
module higher-group-theory.orbits-higher-group-actionsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import higher-group-theory.higher-group-actionsᵉ
open import higher-group-theory.higher-groupsᵉ
```

</details>

## Idea

Theᵉ typeᵉ ofᵉ orbitsᵉ ofᵉ aᵉ higherᵉ groupᵉ actionᵉ `X`ᵉ actedᵉ uponᵉ byᵉ `G`ᵉ isᵉ theᵉ totalᵉ
spaceᵉ ofᵉ `X`.ᵉ

## Definition

```agda
orbit-action-∞-Groupᵉ :
  {l1ᵉ l2ᵉ : Level} (Gᵉ : ∞-Groupᵉ l1ᵉ) (Xᵉ : action-∞-Groupᵉ l2ᵉ Gᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
orbit-action-∞-Groupᵉ Gᵉ Xᵉ = Σᵉ (classifying-type-∞-Groupᵉ Gᵉ) Xᵉ
```