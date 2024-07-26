# Wild representations of monoids

```agda
module group-theory.wild-representations-monoidsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.endomorphismsᵉ
open import foundation.function-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ

open import group-theory.monoidsᵉ

open import structured-types.morphisms-wild-monoidsᵉ
```

</details>

## Idea

Aᵉ coherentᵉ actionᵉ ofᵉ aᵉ [monoid](group-theory.monoids.mdᵉ) `M`ᵉ onᵉ aᵉ typeᵉ `X`ᵉ
requiresᵉ anᵉ infiniteᵉ hierarchyᵉ ofᵉ explicitᵉ coherences.ᵉ Instead,ᵉ asᵉ aᵉ firstᵉ orderᵉ
approximation,ᵉ weᵉ canᵉ considerᵉ **wildᵉ representations**ᵉ ofᵉ `M`ᵉ onᵉ `X`,ᵉ
consistingᵉ ofᵉ aᵉ
[wildᵉ monoidᵉ homomorphism](structured-types.morphisms-wild-monoids.mdᵉ) fromᵉ `M`ᵉ
to theᵉ [wildᵉ monoid](structured-types.wild-monoids.mdᵉ) ofᵉ
[endomorphisms](foundation.endomorphisms.mdᵉ) onᵉ `X`.ᵉ

## Definition

### Wild representations of a monoid in a type

```agda
wild-representation-type-Monoidᵉ :
  (l1ᵉ : Level) {l2ᵉ : Level} (Mᵉ : Monoidᵉ l2ᵉ) → UUᵉ (lsuc l1ᵉ ⊔ l2ᵉ)
wild-representation-type-Monoidᵉ l1ᵉ Mᵉ =
  Σᵉ ( UUᵉ l1ᵉ)
    ( λ Xᵉ → hom-Wild-Monoidᵉ (wild-monoid-Monoidᵉ Mᵉ) (endo-Wild-Monoidᵉ Xᵉ))

module _
  {l1ᵉ l2ᵉ : Level} (Mᵉ : Monoidᵉ l1ᵉ)
  (ρᵉ : wild-representation-type-Monoidᵉ l2ᵉ Mᵉ)
  where

  type-wild-representation-type-Monoidᵉ : UUᵉ l2ᵉ
  type-wild-representation-type-Monoidᵉ = pr1ᵉ ρᵉ

  hom-action-wild-representation-type-Monoidᵉ :
    hom-Wild-Monoidᵉ
      ( wild-monoid-Monoidᵉ Mᵉ)
      ( endo-Wild-Monoidᵉ type-wild-representation-type-Monoidᵉ)
  hom-action-wild-representation-type-Monoidᵉ = pr2ᵉ ρᵉ

  action-wild-representation-type-Monoidᵉ :
    type-Monoidᵉ Mᵉ → endoᵉ type-wild-representation-type-Monoidᵉ
  action-wild-representation-type-Monoidᵉ =
    map-hom-Wild-Monoidᵉ
      ( wild-monoid-Monoidᵉ Mᵉ)
      ( endo-Wild-Monoidᵉ type-wild-representation-type-Monoidᵉ)
      ( hom-action-wild-representation-type-Monoidᵉ)

  preserves-mul-action-wild-representation-type-Monoidᵉ :
    { xᵉ yᵉ : type-Monoidᵉ Mᵉ} →
    ( action-wild-representation-type-Monoidᵉ (mul-Monoidᵉ Mᵉ xᵉ yᵉ)) ＝ᵉ
    ( ( action-wild-representation-type-Monoidᵉ xᵉ) ∘ᵉ
      ( action-wild-representation-type-Monoidᵉ yᵉ))
  preserves-mul-action-wild-representation-type-Monoidᵉ =
    preserves-mul-hom-Wild-Monoidᵉ
      ( wild-monoid-Monoidᵉ Mᵉ)
      ( endo-Wild-Monoidᵉ type-wild-representation-type-Monoidᵉ)
      ( hom-action-wild-representation-type-Monoidᵉ)

  preserves-unit-action-wild-representation-type-Monoidᵉ :
    action-wild-representation-type-Monoidᵉ (unit-Monoidᵉ Mᵉ) ＝ᵉ idᵉ
  preserves-unit-action-wild-representation-type-Monoidᵉ =
    preserves-unit-map-hom-Wild-Monoidᵉ
      ( wild-monoid-Monoidᵉ Mᵉ)
      ( endo-Wild-Monoidᵉ type-wild-representation-type-Monoidᵉ)
      ( hom-action-wild-representation-type-Monoidᵉ)
```