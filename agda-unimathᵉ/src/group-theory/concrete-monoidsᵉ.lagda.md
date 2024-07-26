# Concrete monoids

```agda
module group-theory.concrete-monoidsᵉ where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categoriesᵉ

open import foundation.0-connected-typesᵉ
open import foundation.cartesian-product-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import group-theory.cores-monoidsᵉ
open import group-theory.monoidsᵉ
open import group-theory.torsorsᵉ
```

</details>

## Idea

Aᵉ **concreteᵉ monoid**,ᵉ orᵉ **univalentᵉ monoid**,ᵉ isᵉ theᵉ homotopyᵉ typeᵉ theoreticᵉ
analogueᵉ ofᵉ [monoids](group-theory.monoids.md).ᵉ Weᵉ defineᵉ itᵉ asᵉ aᵉ
[category](category-theory.categories.mdᵉ) whoseᵉ typeᵉ ofᵉ objectsᵉ isᵉ
[pointed](structured-types.pointed-types.mdᵉ) andᵉ
[connected](foundation.0-connected-types.md).ᵉ

## Definition

```agda
is-concrete-monoid-Categoryᵉ : {l1ᵉ l2ᵉ : Level} → Categoryᵉ l1ᵉ l2ᵉ → UUᵉ l1ᵉ
is-concrete-monoid-Categoryᵉ Cᵉ = obj-Categoryᵉ Cᵉ ×ᵉ is-0-connectedᵉ (obj-Categoryᵉ Cᵉ)

Concrete-Monoidᵉ : (l1ᵉ l2ᵉ : Level) → UUᵉ (lsuc l1ᵉ ⊔ lsuc l2ᵉ)
Concrete-Monoidᵉ l1ᵉ l2ᵉ = Σᵉ (Categoryᵉ l1ᵉ l2ᵉ) (is-concrete-monoid-Categoryᵉ)

module _
  {l1ᵉ l2ᵉ : Level} (Mᵉ : Concrete-Monoidᵉ l1ᵉ l2ᵉ)
  where

  category-Concrete-Monoidᵉ : Categoryᵉ l1ᵉ l2ᵉ
  category-Concrete-Monoidᵉ = pr1ᵉ Mᵉ

  is-concrete-monoid-category-Concrete-Monoidᵉ :
    is-concrete-monoid-Categoryᵉ category-Concrete-Monoidᵉ
  is-concrete-monoid-category-Concrete-Monoidᵉ = pr2ᵉ Mᵉ
```

## Properties

### Concrete monoids from monoids

Givenᵉ aᵉ monoid,ᵉ weᵉ canᵉ defineᵉ itsᵉ associatedᵉ concreteᵉ monoid.ᵉ Theᵉ typeᵉ ofᵉ
objectsᵉ isᵉ theᵉ [classifyingᵉ type](group-theory.concrete-groups.mdᵉ) ofᵉ theᵉ
[core](group-theory.cores-monoids.mdᵉ) ofᵉ theᵉ monoid.ᵉ Moreover,ᵉ weᵉ mustᵉ takeᵉ careᵉ
in howᵉ weᵉ defineᵉ theᵉ familyᵉ ofᵉ homomorphisms.ᵉ Theyᵉ cannotᵉ simplyᵉ beᵉ theᵉ constantᵉ
family,ᵉ asᵉ [transportingᵉ along](foundation.transport-along-identifications.mdᵉ)
anᵉ [invertibleᵉ element](group-theory.invertible-elements-monoids.mdᵉ) shouldᵉ
correspondᵉ to multiplyingᵉ byᵉ theᵉ elementᵉ in theᵉ family.ᵉ

```agda
module _
  {lᵉ : Level} (Mᵉ : Monoidᵉ lᵉ)
  where

  obj-concrete-monoid-Monoidᵉ : UUᵉ (lsuc lᵉ)
  obj-concrete-monoid-Monoidᵉ = classifying-type-Groupᵉ (core-Monoidᵉ Mᵉ)
```

Theᵉ remainderᵉ ofᵉ theᵉ constructionᵉ remainsᵉ to beᵉ writtenᵉ down.ᵉ Weᵉ noteᵉ thatᵉ thisᵉ
isᵉ preciselyᵉ theᵉ Rezkᵉ completionᵉ ofᵉ theᵉ oneᵉ objectᵉ precategoryᵉ associatedᵉ to aᵉ
monoid.ᵉ