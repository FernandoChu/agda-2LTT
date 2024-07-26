# Principal group actions

```agda
module group-theory.principal-group-actionsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalence-extensionalityᵉ
open import foundation.universe-levelsᵉ

open import group-theory.group-actionsᵉ
open import group-theory.groupsᵉ
```

</details>

## Idea

Theᵉ **principalᵉ groupᵉ action**ᵉ isᵉ theᵉ [action](group-theory.group-actions.mdᵉ) ofᵉ
aᵉ [group](group-theory.groups.mdᵉ) onᵉ itselfᵉ byᵉ multiplicationᵉ fromᵉ theᵉ left.ᵉ

## Definition

```agda
module _
  {l1ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ)
  where

  principal-action-Groupᵉ : action-Groupᵉ Gᵉ l1ᵉ
  pr1ᵉ principal-action-Groupᵉ = set-Groupᵉ Gᵉ
  pr1ᵉ (pr2ᵉ principal-action-Groupᵉ) gᵉ = equiv-mul-Groupᵉ Gᵉ gᵉ
  pr2ᵉ (pr2ᵉ principal-action-Groupᵉ) {gᵉ} {hᵉ} =
    eq-htpy-equivᵉ (associative-mul-Groupᵉ Gᵉ gᵉ hᵉ)
```