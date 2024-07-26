# Transitive group actions

```agda
module group-theory.transitive-group-actionsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.existential-quantificationᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.surjective-mapsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.group-actionsᵉ
open import group-theory.groupsᵉ
```

</details>

## Idea

Aᵉ [group](group-theory.groups.mdᵉ) `G`ᵉ isᵉ saidᵉ to **actᵉ transitively**ᵉ onᵉ aᵉ
[set](foundation-core.sets.mdᵉ) `X`ᵉ ifᵉ forᵉ everyᵉ `xᵉ : X`ᵉ theᵉ mapᵉ

```text
  gᵉ ↦ᵉ gxᵉ : Gᵉ → Xᵉ
```

isᵉ [surjective](foundation.surjective-maps.md).ᵉ Inᵉ otherᵉ words,ᵉ aᵉ
[groupᵉ action](group-theory.group-actions.mdᵉ) isᵉ transitiveᵉ ifᵉ anyᵉ twoᵉ elementsᵉ
areᵉ in theᵉ sameᵉ [orbit](group-theory.orbits-group-actions.md).ᵉ

## Definitions

### The predicate of being a transitive `G`-set

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Xᵉ : action-Groupᵉ Gᵉ l2ᵉ)
  where

  is-transitive-prop-action-Groupᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  is-transitive-prop-action-Groupᵉ =
    Π-Propᵉ
      ( type-action-Groupᵉ Gᵉ Xᵉ)
      ( λ xᵉ → is-surjective-Propᵉ (λ gᵉ → mul-action-Groupᵉ Gᵉ Xᵉ gᵉ xᵉ))

  is-transitive-action-Groupᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-transitive-action-Groupᵉ = type-Propᵉ is-transitive-prop-action-Groupᵉ

  is-prop-is-transitive-action-Groupᵉ : is-propᵉ is-transitive-action-Groupᵉ
  is-prop-is-transitive-action-Groupᵉ =
    is-prop-type-Propᵉ is-transitive-prop-action-Groupᵉ
```

## External links

-ᵉ [transitiveᵉ action](https://ncatlab.org/nlab/show/transitive+actionᵉ) atᵉ $n$Labᵉ
-ᵉ [Transitivityᵉ propertiesᵉ ofᵉ groupᵉ actions](https://en.wikipedia.org/wiki/Group_action#Transitivity_propertiesᵉ)
  atᵉ Wikipediaᵉ
-ᵉ [Transitiveᵉ Groupᵉ Action](https://mathworld.wolfram.com/TransitiveGroupAction.htmlᵉ)
  atᵉ Wolframᵉ MathWorldᵉ
-ᵉ [Transitiveᵉ groupᵉ action](https://groupprops.subwiki.org/wiki/Transitive_group_actionᵉ)
  atᵉ Grouppropsᵉ