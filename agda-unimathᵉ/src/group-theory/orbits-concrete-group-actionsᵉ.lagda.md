# Orbits of concrete group actions

```agda
module group-theory.orbits-concrete-group-actionsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.function-typesᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ

open import group-theory.concrete-group-actionsᵉ
open import group-theory.concrete-groupsᵉ
```

</details>

## Idea

Theᵉ typeᵉ ofᵉ **orbits**ᵉ ofᵉ aᵉ
[concreteᵉ groupᵉ action](group-theory.concrete-group-actions.mdᵉ) ofᵉ `G`ᵉ onᵉ `X`ᵉ isᵉ
definedᵉ to beᵉ theᵉ [totalᵉ space](foundation.dependent-pair-types.mdᵉ)

```text
  Σᵉ (uᵉ : BG),ᵉ Xᵉ u.ᵉ
```

ofᵉ theᵉ typeᵉ familyᵉ `X`ᵉ overᵉ theᵉ classifyingᵉ typeᵉ ofᵉ theᵉ
[concreteᵉ group](group-theory.concrete-groups.mdᵉ) `G`.ᵉ Theᵉ ideaᵉ isᵉ thatᵉ theᵉ
"standard"ᵉ elementsᵉ ofᵉ thisᵉ typeᵉ areᵉ ofᵉ theᵉ formᵉ `(*ᵉ ,ᵉ x)`,ᵉ where `x`ᵉ isᵉ anᵉ
elementᵉ ofᵉ theᵉ underlyingᵉ [set](foundation-core.sets.mdᵉ) `Xᵉ *`ᵉ ofᵉ `X`,ᵉ andᵉ thatᵉ
theᵉ typeᵉ ofᵉ [identifications](foundation-core.identity-types.mdᵉ) fromᵉ `(*ᵉ ,ᵉ x)`ᵉ
to `(*ᵉ ,ᵉ y)`ᵉ isᵉ [equivalent](foundation-core.equivalences.mdᵉ) to theᵉ typeᵉ

```text
  Σᵉ (gᵉ : G),ᵉ gᵉ xᵉ ＝ᵉ y.ᵉ
```

Inᵉ otherᵉ words,ᵉ identificationsᵉ betweenᵉ theᵉ elementsᵉ `(*ᵉ ,ᵉ x)`ᵉ andᵉ `(*ᵉ ,ᵉ y)`ᵉ in
theᵉ typeᵉ ofᵉ orbitsᵉ ofᵉ `X`ᵉ areᵉ equivalentlyᵉ describedᵉ asᵉ groupᵉ elementsᵉ `g`ᵉ suchᵉ
thatᵉ `gᵉ xᵉ ＝ᵉ y`.ᵉ

Noteᵉ thatᵉ theᵉ typeᵉ ofᵉ orbitsᵉ ofᵉ aᵉ concreteᵉ groupᵉ isᵉ typicallyᵉ aᵉ
[`1`-type](foundation-core.1-types.md).ᵉ Inᵉ
[Freeᵉ concreteᵉ groupᵉ actions](group-theory.free-concrete-group-actions.mdᵉ) weᵉ
willᵉ showᵉ thatᵉ theᵉ typeᵉ ofᵉ orbitsᵉ isᵉ aᵉ setᵉ ifᵉ andᵉ onlyᵉ ifᵉ theᵉ actionᵉ ofᵉ `G`ᵉ onᵉ
`X`ᵉ isᵉ free,ᵉ andᵉ in
[Transitiveᵉ concreteᵉ groupᵉ actions](group-theory.transitive-concrete-group-actions.mdᵉ)
weᵉ willᵉ showᵉ thatᵉ theᵉ typeᵉ ofᵉ orbitsᵉ isᵉ
[`0`-connected](foundation.0-connected-types.mdᵉ) ifᵉ andᵉ onlyᵉ ifᵉ theᵉ actionᵉ isᵉ
transitive.ᵉ

## Definition

```agda
orbit-action-Concrete-Groupᵉ :
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Concrete-Groupᵉ l1ᵉ) (Xᵉ : action-Concrete-Groupᵉ l2ᵉ Gᵉ) →
  UUᵉ (l1ᵉ ⊔ l2ᵉ)
orbit-action-Concrete-Groupᵉ Gᵉ Xᵉ =
  Σᵉ (classifying-type-Concrete-Groupᵉ Gᵉ) (type-Setᵉ ∘ᵉ Xᵉ)
```

## See also

-ᵉ [Freeᵉ concreteᵉ groupᵉ actions](group-theory.free-concrete-group-actions.mdᵉ)
-ᵉ [Transitiveᵉ concreteᵉ groupᵉ actions](group-theory.transitive-concrete-group-actions.mdᵉ)