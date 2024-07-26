# Deloopable groups

```agda
module higher-group-theory.deloopable-groupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import group-theory.groupsᵉ

open import higher-group-theory.deloopable-h-spacesᵉ
```

</details>

## Idea

Aᵉ {{#conceptᵉ "delooping"ᵉ Disambiguation="group"ᵉ Agda=delooping-Groupᵉ}} ofᵉ aᵉ
[group](group-theory.groups.mdᵉ) `G`ᵉ isᵉ aᵉ
[delooping](higher-group-theory.deloopable-h-spaces.mdᵉ) ofᵉ theᵉ underlyingᵉ
[H-space](structured-types.h-spaces.mdᵉ) ofᵉ `G`.ᵉ Inᵉ otherᵉ words,ᵉ aᵉ deloopingᵉ ofᵉ aᵉ
groupᵉ `G`ᵉ consistsᵉ ofᵉ aᵉ [higherᵉ group](higher-group-theory.higher-groups.mdᵉ)
`H`,ᵉ whichᵉ isᵉ definedᵉ to beᵉ aᵉ [pointed](structured-types.pointed-types.mdᵉ)
[connected](foundation.0-connected-types.mdᵉ) type,ᵉ equippedᵉ with anᵉ
[equivalenceᵉ ofᵉ H-spaces](structured-types.equivalences-h-spaces.mdᵉ)
`Gᵉ ≃ᵉ h-space-∞-Groupᵉ H`ᵉ fromᵉ `G`ᵉ to theᵉ underlyingᵉ H-spaceᵉ ofᵉ `H`.ᵉ

## Definitions

### Deloopings of groups of a given universe level

```agda
module _
  {l1ᵉ : Level} (l2ᵉ : Level) (Gᵉ : Groupᵉ l1ᵉ)
  where

  delooping-Group-Levelᵉ : UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
  delooping-Group-Levelᵉ = delooping-H-Space-Levelᵉ l2ᵉ (h-space-Groupᵉ Gᵉ)
```

### Deloopings of groups

```agda
module _
  {l1ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ)
  where

  delooping-Groupᵉ : UUᵉ (lsuc l1ᵉ)
  delooping-Groupᵉ = delooping-Group-Levelᵉ l1ᵉ Gᵉ
```

## See also

-ᵉ [Eilenberg-Macᵉ Laneᵉ spaces](higher-group-theory.eilenberg-mac-lane-spaces.mdᵉ)