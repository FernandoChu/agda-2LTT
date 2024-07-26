# Eilenberg-Mac Lane spaces

```agda
module higher-group-theory.eilenberg-mac-lane-spacesᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.0-connected-typesᵉ
open import foundation.cartesian-product-typesᵉ
open import foundation.connected-typesᵉ
open import foundation.truncated-typesᵉ
open import foundation.truncation-levelsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.abelian-groupsᵉ
open import group-theory.groupsᵉ

open import structured-types.equivalences-h-spacesᵉ
open import structured-types.pointed-equivalencesᵉ
open import structured-types.pointed-typesᵉ

open import synthetic-homotopy-theory.iterated-loop-spacesᵉ
open import synthetic-homotopy-theory.loop-spacesᵉ
```

</details>

## Idea

Thereᵉ areᵉ manyᵉ waysᵉ to sayᵉ whatᵉ anᵉ _Eilenberg-Macᵉ Laneᵉ spaceᵉ_ is.ᵉ Theᵉ basicᵉ ideaᵉ
isᵉ thatᵉ aᵉ [pointed](structured-types.pointed-types.mdᵉ)
[connected](foundation.0-connected-types.mdᵉ) typeᵉ `X`ᵉ isᵉ anᵉ Eilenberg-Macᵉ Laneᵉ
spaceᵉ ifᵉ onlyᵉ oneᵉ ofᵉ itsᵉ homotopyᵉ groupsᵉ `πᵉ nᵉ X`ᵉ isᵉ
[nontrivial](group-theory.nontrivial-groups.md).ᵉ However,ᵉ recallᵉ thatᵉ theᵉ
conditionᵉ ofᵉ beingᵉ [`n`-truncated](foundation-core.truncated-types.mdᵉ) isᵉ
slightlyᵉ strongerᵉ thanᵉ theᵉ conditionᵉ thatᵉ theᵉ homotopyᵉ groupsᵉ `πᵉ iᵉ X`ᵉ areᵉ
[trivial](group-theory.trivial-groups.mdᵉ) forᵉ allᵉ `iᵉ >ᵉ n`.ᵉ Indeed,ᵉ unlikeᵉ in theᵉ
settingᵉ ofᵉ topologicalᵉ spacesᵉ orᵉ simplicialᵉ sets,ᵉ univalentᵉ typeᵉ theoryᵉ allowsᵉ
forᵉ theᵉ possibilityᵉ ofᵉ ∞-connectedᵉ types,ᵉ i.e.,ᵉ typesᵉ ofᵉ whichᵉ allᵉ homotopyᵉ
groupsᵉ areᵉ trivial.ᵉ Inᵉ orderᵉ to avoidᵉ examplesᵉ ofᵉ Eilenberg-Macᵉ Laneᵉ spacesᵉ
possiblyᵉ involvingᵉ nontrivialᵉ ∞-connectedᵉ types,ᵉ weᵉ willᵉ slightlyᵉ strengthenᵉ theᵉ
definitionᵉ ofᵉ Eilenberg-Macᵉ Laneᵉ spaces.ᵉ Weᵉ sayᵉ thatᵉ aᵉ pointedᵉ typeᵉ `X`isᵉ anᵉ
{{#conceptᵉ "Eilenberg-Macᵉ Laneᵉ space"ᵉ}} if`X`is`n-1`-connectedᵉ andᵉ
`n`-truncated.ᵉ Underᵉ thisᵉ definitionᵉ thereᵉ isᵉ anᵉ
[equivalence](category-theory.equivalences-of-categories.mdᵉ) betweenᵉ theᵉ
[categoryᵉ ofᵉ groups](group-theory.category-of-groups.md),ᵉ resp.ᵉ theᵉ
[categoryᵉ ofᵉ abelianᵉ groups](group-theory.category-of-abelian-groups.md),ᵉ andᵉ
theᵉ categoryᵉ ofᵉ Eilenberg-Macᵉ Laneᵉ spacesᵉ ofᵉ dimensionᵉ `1`,ᵉ resp.ᵉ `nᵉ ≥ᵉ 2`.ᵉ

Considerᵉ aᵉ [group](group-theory.groups.mdᵉ) `G`ᵉ andᵉ aᵉ
[naturalᵉ number](elementary-number-theory.natural-numbers.mdᵉ) `nᵉ ≥ᵉ 1`.ᵉ Aᵉ pointedᵉ
typeᵉ `X`ᵉ isᵉ saidᵉ to beᵉ anᵉ Eilenberg-Macᵉ Laneᵉ spaceᵉ ofᵉ typeᵉ `Kᵉ Gᵉ n`ᵉ ifᵉ `X`ᵉ isᵉ
[`(n-1)`-connected](foundation.connected-types.mdᵉ) andᵉ
[`n`-truncated](foundation-core.truncated-types.md),ᵉ andᵉ moreoverᵉ theᵉ `n`-thᵉ
homotopyᵉ groupᵉ `πᵉ nᵉ X`ᵉ isᵉ [isomorphic](group-theory.isomorphisms-groups.mdᵉ) to
`G`.ᵉ

Thereᵉ isᵉ alsoᵉ aᵉ recursiveᵉ definitionᵉ ofᵉ whatᵉ itᵉ meansᵉ forᵉ aᵉ pointedᵉ typeᵉ `X`ᵉ to
beᵉ anᵉ $n$-thᵉ
{{#conceptᵉ "Eilenberg-Macᵉ Laneᵉ space"ᵉ Agda=is-eilenberg-mac-lane-space-Groupᵉ}}:

-ᵉ Weᵉ sayᵉ thatᵉ `X`ᵉ isᵉ aᵉ **firstᵉ Eilenberg-Macᵉ Laneᵉ space**ᵉ ifᵉ `X`ᵉ isᵉ
  `0`-connectedᵉ andᵉ thereᵉ isᵉ aᵉ
  [pointedᵉ equivalence](structured-types.pointed-equivalences.mdᵉ)

  ```text
    Ωᵉ Xᵉ ≃ᵉ Gᵉ
  ```

  thatᵉ mapsᵉ concatenationᵉ in theᵉ
  [loopᵉ space](synthetic-homotopy-theory.loop-spaces.mdᵉ) `Ωᵉ X`ᵉ to theᵉ groupᵉ
  operationᵉ onᵉ `G`.ᵉ

-ᵉ Weᵉ sayᵉ thatᵉ `X`ᵉ isᵉ anᵉ `(n+1)`-stᵉ Eilenberg-Macᵉ Laneᵉ spaceᵉ ifᵉ `X`ᵉ isᵉ
  `0`-connectedᵉ andᵉ `Ωᵉ X`ᵉ isᵉ anᵉ `n`-thᵉ Eilenberg-Macᵉ Laneᵉ space.ᵉ

## Definitions

### Eilenberg-Mac Lane spaces

Weᵉ introduceᵉ theᵉ mostᵉ generalᵉ notionᵉ ofᵉ anᵉ (unspecifiedᵉ) Eilenberg-Macᵉ Laneᵉ
spaceᵉ to beᵉ aᵉ pointedᵉ `n`-connectedᵉ `(n+1)`-truncatedᵉ type.ᵉ Eilenberg-Macᵉ Laneᵉ
spacesᵉ in thisᵉ definitionᵉ aren'tᵉ equippedᵉ with aᵉ groupᵉ isomorphismᵉ fromᵉ theirᵉ
nontrivialᵉ homotopyᵉ groupᵉ to aᵉ givenᵉ groupᵉ `G`,ᵉ soᵉ in thisᵉ senseᵉ theyᵉ areᵉ
"unspecified".ᵉ

```agda
module _
  {l1ᵉ : Level} (kᵉ : 𝕋ᵉ) (Xᵉ : Pointed-Typeᵉ l1ᵉ)
  where

  is-eilenberg-mac-lane-space-𝕋ᵉ : UUᵉ l1ᵉ
  is-eilenberg-mac-lane-space-𝕋ᵉ =
    is-connectedᵉ kᵉ (type-Pointed-Typeᵉ Xᵉ) ×ᵉ
    is-truncᵉ (succ-𝕋ᵉ kᵉ) (type-Pointed-Typeᵉ Xᵉ)

module _
  {l1ᵉ : Level} (nᵉ : ℕᵉ) (Xᵉ : Pointed-Typeᵉ l1ᵉ)
  where

  is-eilenberg-mac-lane-spaceᵉ : UUᵉ l1ᵉ
  is-eilenberg-mac-lane-spaceᵉ =
    is-eilenberg-mac-lane-space-𝕋ᵉ
      ( truncation-level-minus-one-ℕᵉ nᵉ)
      ( Xᵉ)
```

### Eilenberg-Mac Lane spaces specified by groups

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ)
  where

  is-eilenberg-mac-lane-space-Groupᵉ :
    (nᵉ : ℕᵉ) (Xᵉ : Pointed-Typeᵉ l2ᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-eilenberg-mac-lane-space-Groupᵉ 0 Xᵉ =
    pointed-type-Groupᵉ Gᵉ ≃∗ᵉ Xᵉ
  is-eilenberg-mac-lane-space-Groupᵉ (succ-ℕᵉ nᵉ) Xᵉ =
    is-connectedᵉ (truncation-level-ℕᵉ nᵉ) (type-Pointed-Typeᵉ Xᵉ) ×ᵉ
    equiv-H-Spaceᵉ (h-space-Groupᵉ Gᵉ) (Ω-H-Spaceᵉ (iterated-loop-spaceᵉ nᵉ Xᵉ))
```

### Eilenberg-Mac Lane spaces specified by abelian groups

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : Abᵉ l1ᵉ)
  where

  is-eilenberg-mac-lane-space-Abᵉ :
    (nᵉ : ℕᵉ) (Xᵉ : Pointed-Typeᵉ l2ᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-eilenberg-mac-lane-space-Abᵉ =
    is-eilenberg-mac-lane-space-Groupᵉ (group-Abᵉ Aᵉ)
```