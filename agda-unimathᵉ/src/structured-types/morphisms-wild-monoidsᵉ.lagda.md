# Morphisms of wild monoids

```agda
module structured-types.morphisms-wild-monoidsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ

open import group-theory.homomorphisms-semigroupsᵉ

open import structured-types.morphisms-h-spacesᵉ
open import structured-types.pointed-mapsᵉ
open import structured-types.wild-monoidsᵉ
```

</details>

## Idea

**Morphisms**ᵉ betweenᵉ twoᵉ [wildᵉ monoids](structured-types.wild-monoids.mdᵉ) areᵉ
mapsᵉ thatᵉ preserveᵉ theᵉ unitᵉ andᵉ multiplication.ᵉ Weᵉ onlyᵉ requireᵉ theᵉ unitᵉ andᵉ
multiplicationᵉ to beᵉ preserved.ᵉ Thisᵉ isᵉ becauseᵉ weᵉ wouldᵉ needᵉ furtherᵉ coherenceᵉ
in wildᵉ monoidsᵉ ifᵉ weᵉ wantᵉ morphismsᵉ listᵉ $Xᵉ → M$ᵉ to preserveᵉ theᵉ unitalᵉ
associator.ᵉ

## Definition

### Homomorphisms of wild monoids

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Mᵉ : Wild-Monoidᵉ l1ᵉ) (Nᵉ : Wild-Monoidᵉ l2ᵉ)
  where

  hom-Wild-Monoidᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  hom-Wild-Monoidᵉ =
    hom-H-Spaceᵉ
      ( h-space-Wild-Monoidᵉ Mᵉ)
      ( h-space-Wild-Monoidᵉ Nᵉ)

  pointed-map-hom-Wild-Monoidᵉ :
    hom-Wild-Monoidᵉ →
    pointed-type-Wild-Monoidᵉ Mᵉ →∗ᵉ pointed-type-Wild-Monoidᵉ Nᵉ
  pointed-map-hom-Wild-Monoidᵉ fᵉ = pr1ᵉ fᵉ

  map-hom-Wild-Monoidᵉ :
    hom-Wild-Monoidᵉ → type-Wild-Monoidᵉ Mᵉ → type-Wild-Monoidᵉ Nᵉ
  map-hom-Wild-Monoidᵉ fᵉ = pr1ᵉ (pr1ᵉ fᵉ)

  preserves-unit-map-hom-Wild-Monoidᵉ :
    (fᵉ : hom-Wild-Monoidᵉ) →
    (map-hom-Wild-Monoidᵉ fᵉ (unit-Wild-Monoidᵉ Mᵉ)) ＝ᵉ (unit-Wild-Monoidᵉ Nᵉ)
  preserves-unit-map-hom-Wild-Monoidᵉ fᵉ = pr2ᵉ (pr1ᵉ fᵉ)

  preserves-unital-mul-map-hom-Wild-Monoidᵉ :
    (fᵉ : hom-Wild-Monoidᵉ) →
    preserves-unital-mul-pointed-map-H-Spaceᵉ
      ( h-space-Wild-Monoidᵉ Mᵉ)
      ( h-space-Wild-Monoidᵉ Nᵉ)
      ( pointed-map-hom-Wild-Monoidᵉ fᵉ)
  preserves-unital-mul-map-hom-Wild-Monoidᵉ fᵉ = pr2ᵉ fᵉ

  preserves-mul-hom-Wild-Monoidᵉ :
    (fᵉ : hom-Wild-Monoidᵉ) →
    preserves-mulᵉ
      ( mul-Wild-Monoidᵉ Mᵉ)
      ( mul-Wild-Monoidᵉ Nᵉ)
      ( map-hom-Wild-Monoidᵉ fᵉ)
  preserves-mul-hom-Wild-Monoidᵉ fᵉ = pr1ᵉ (pr2ᵉ fᵉ)

  preserves-left-unit-law-mul-map-hom-Wild-Monoidᵉ :
    ( fᵉ : hom-Wild-Monoidᵉ) →
    preserves-left-unit-law-mul-pointed-map-H-Spaceᵉ
      ( h-space-Wild-Monoidᵉ Mᵉ)
      ( h-space-Wild-Monoidᵉ Nᵉ)
      ( pointed-map-hom-Wild-Monoidᵉ fᵉ)
      ( preserves-mul-hom-Wild-Monoidᵉ fᵉ)
  preserves-left-unit-law-mul-map-hom-Wild-Monoidᵉ fᵉ =
    pr1ᵉ (pr2ᵉ (pr2ᵉ fᵉ))

  preserves-right-unit-law-mul-map-hom-Wild-Monoidᵉ :
    (fᵉ : hom-Wild-Monoidᵉ) →
    preserves-right-unit-law-mul-pointed-map-H-Spaceᵉ
      ( h-space-Wild-Monoidᵉ Mᵉ)
      ( h-space-Wild-Monoidᵉ Nᵉ)
      ( pointed-map-hom-Wild-Monoidᵉ fᵉ)
      ( preserves-mul-hom-Wild-Monoidᵉ fᵉ)
  preserves-right-unit-law-mul-map-hom-Wild-Monoidᵉ fᵉ =
    pr1ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ fᵉ)))

  preserves-coh-unit-laws-map-hom-Wild-Monoidᵉ :
    (fᵉ : hom-Wild-Monoidᵉ) →
    preserves-coherence-unit-laws-mul-pointed-map-H-Spaceᵉ
      ( h-space-Wild-Monoidᵉ Mᵉ)
      ( h-space-Wild-Monoidᵉ Nᵉ)
      ( pointed-map-hom-Wild-Monoidᵉ fᵉ)
      ( preserves-mul-hom-Wild-Monoidᵉ fᵉ)
      ( preserves-left-unit-law-mul-map-hom-Wild-Monoidᵉ fᵉ)
      ( preserves-right-unit-law-mul-map-hom-Wild-Monoidᵉ fᵉ)
  preserves-coh-unit-laws-map-hom-Wild-Monoidᵉ fᵉ =
    pr2ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ fᵉ)))
```