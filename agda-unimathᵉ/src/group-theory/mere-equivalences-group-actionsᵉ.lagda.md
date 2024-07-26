# Mere equivalences of group actions

```agda
module group-theory.mere-equivalences-group-actionsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.propositional-truncationsᵉ
open import foundation.propositionsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.equivalences-group-actionsᵉ
open import group-theory.group-actionsᵉ
open import group-theory.groupsᵉ
```

</details>

## Idea

Aᵉ **mereᵉ equivalence**ᵉ ofᵉ [groupᵉ actions](group-theory.group-actions.mdᵉ) isᵉ anᵉ
elementᵉ ofᵉ theᵉ
[propositionalᵉ truncation](foundation.propositional-truncations.mdᵉ) ofᵉ theᵉ typeᵉ
ofᵉ [equivalencesᵉ ofᵉ groupᵉ actions](group-theory.equivalences-group-actions.md).ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ)
  (Xᵉ : action-Groupᵉ Gᵉ l2ᵉ) (Yᵉ : action-Groupᵉ Gᵉ l3ᵉ)
  where

  mere-equiv-prop-action-Groupᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  mere-equiv-prop-action-Groupᵉ = trunc-Propᵉ (equiv-action-Groupᵉ Gᵉ Xᵉ Yᵉ)

  mere-equiv-action-Groupᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  mere-equiv-action-Groupᵉ = type-Propᵉ mere-equiv-prop-action-Groupᵉ
```