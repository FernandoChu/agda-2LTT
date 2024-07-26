# Retracts of sequential diagrams

```agda
module synthetic-homotopy-theory.retracts-of-sequential-diagramsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.commuting-squares-of-mapsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equality-dependent-function-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.homotopy-inductionᵉ
open import foundation.identity-typesᵉ
open import foundation.retractionsᵉ
open import foundation.retracts-of-typesᵉ
open import foundation.universe-levelsᵉ

open import synthetic-homotopy-theory.morphisms-sequential-diagramsᵉ
open import synthetic-homotopy-theory.sequential-diagramsᵉ
```

</details>

## Idea

Aᵉ
{{#conceptᵉ "retract"ᵉ Disambiguation="sequentialᵉ diagram"ᵉ Agda=retract-sequential-diagramᵉ}}
ofᵉ sequentialᵉ diagramsᵉ `A`ᵉ ofᵉ `B`ᵉ isᵉ aᵉ
[morphismᵉ ofᵉ sequentialᵉ diagrams](synthetic-homotopy-theory.morphisms-sequential-diagrams.mdᵉ)
`Bᵉ → A`ᵉ thatᵉ isᵉ aᵉ retraction.ᵉ

## Definitions

### The predicate of being a retraction of sequential diagrams

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : sequential-diagramᵉ l1ᵉ) (Bᵉ : sequential-diagramᵉ l2ᵉ)
  (iᵉ : hom-sequential-diagramᵉ Aᵉ Bᵉ) (rᵉ : hom-sequential-diagramᵉ Bᵉ Aᵉ)
  where

  is-retraction-hom-sequential-diagramᵉ : UUᵉ l1ᵉ
  is-retraction-hom-sequential-diagramᵉ =
    htpy-hom-sequential-diagramᵉ Aᵉ
      ( comp-hom-sequential-diagramᵉ Aᵉ Bᵉ Aᵉ rᵉ iᵉ)
      ( id-hom-sequential-diagramᵉ Aᵉ)
```

### The type of retractions of a morphism of sequential diagrams

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : sequential-diagramᵉ l1ᵉ) (Bᵉ : sequential-diagramᵉ l2ᵉ)
  (iᵉ : hom-sequential-diagramᵉ Aᵉ Bᵉ)
  where

  retraction-hom-sequential-diagramᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  retraction-hom-sequential-diagramᵉ =
    Σᵉ (hom-sequential-diagramᵉ Bᵉ Aᵉ) (is-retraction-hom-sequential-diagramᵉ Aᵉ Bᵉ iᵉ)

  module _
    (rᵉ : retraction-hom-sequential-diagramᵉ)
    where

    hom-retraction-hom-sequential-diagramᵉ : hom-sequential-diagramᵉ Bᵉ Aᵉ
    hom-retraction-hom-sequential-diagramᵉ = pr1ᵉ rᵉ

    is-retraction-hom-retraction-hom-sequential-diagramᵉ :
      is-retraction-hom-sequential-diagramᵉ Aᵉ Bᵉ iᵉ
        ( hom-retraction-hom-sequential-diagramᵉ)
    is-retraction-hom-retraction-hom-sequential-diagramᵉ = pr2ᵉ rᵉ
```

### The predicate that a sequential diagram `A` is a retract of a sequential diagram `B`

```agda
retract-sequential-diagramᵉ :
  {l1ᵉ l2ᵉ : Level} (Bᵉ : sequential-diagramᵉ l2ᵉ) (Aᵉ : sequential-diagramᵉ l1ᵉ) →
  UUᵉ (l1ᵉ ⊔ l2ᵉ)
retract-sequential-diagramᵉ Bᵉ Aᵉ =
  Σᵉ (hom-sequential-diagramᵉ Aᵉ Bᵉ) (retraction-hom-sequential-diagramᵉ Aᵉ Bᵉ)
```

### The higher coherence in the definition of retracts of sequential diagrams

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : sequential-diagramᵉ l1ᵉ) (Bᵉ : sequential-diagramᵉ l2ᵉ)
  (iᵉ : hom-sequential-diagramᵉ Aᵉ Bᵉ) (rᵉ : hom-sequential-diagramᵉ Bᵉ Aᵉ)
  where

  coherence-retract-sequential-diagramᵉ :
    ( (nᵉ : ℕᵉ) →
      is-retractionᵉ
        ( map-hom-sequential-diagramᵉ Bᵉ iᵉ nᵉ)
        ( map-hom-sequential-diagramᵉ Aᵉ rᵉ nᵉ)) →
    UUᵉ l1ᵉ
  coherence-retract-sequential-diagramᵉ =
    coherence-htpy-hom-sequential-diagramᵉ Aᵉ
      ( comp-hom-sequential-diagramᵉ Aᵉ Bᵉ Aᵉ rᵉ iᵉ)
      ( id-hom-sequential-diagramᵉ Aᵉ)
```

### The binary relation `A B ↦ A retract-of-sequential-diagram B` asserting that `A` is a retract of the sequential diagram `B`

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : sequential-diagramᵉ l1ᵉ) (Bᵉ : sequential-diagramᵉ l2ᵉ)
  where

  infix 6 _retract-of-sequential-diagramᵉ_

  _retract-of-sequential-diagramᵉ_ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  _retract-of-sequential-diagramᵉ_ = retract-sequential-diagramᵉ Bᵉ Aᵉ

module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : sequential-diagramᵉ l1ᵉ) (Bᵉ : sequential-diagramᵉ l2ᵉ)
  (Rᵉ : Aᵉ retract-of-sequential-diagramᵉ Bᵉ)
  where

  inclusion-retract-sequential-diagramᵉ : hom-sequential-diagramᵉ Aᵉ Bᵉ
  inclusion-retract-sequential-diagramᵉ = pr1ᵉ Rᵉ

  map-inclusion-retract-sequential-diagramᵉ :
    (nᵉ : ℕᵉ) → family-sequential-diagramᵉ Aᵉ nᵉ → family-sequential-diagramᵉ Bᵉ nᵉ
  map-inclusion-retract-sequential-diagramᵉ =
    map-hom-sequential-diagramᵉ Bᵉ inclusion-retract-sequential-diagramᵉ

  naturality-inclusion-retract-sequential-diagramᵉ :
    naturality-hom-sequential-diagramᵉ Aᵉ Bᵉ
      ( map-inclusion-retract-sequential-diagramᵉ)
  naturality-inclusion-retract-sequential-diagramᵉ =
    naturality-map-hom-sequential-diagramᵉ Bᵉ
      ( inclusion-retract-sequential-diagramᵉ)

  retraction-retract-sequential-diagramᵉ :
    retraction-hom-sequential-diagramᵉ Aᵉ Bᵉ inclusion-retract-sequential-diagramᵉ
  retraction-retract-sequential-diagramᵉ = pr2ᵉ Rᵉ

  hom-retraction-retract-sequential-diagramᵉ : hom-sequential-diagramᵉ Bᵉ Aᵉ
  hom-retraction-retract-sequential-diagramᵉ =
    hom-retraction-hom-sequential-diagramᵉ Aᵉ Bᵉ
      ( inclusion-retract-sequential-diagramᵉ)
      ( retraction-retract-sequential-diagramᵉ)

  map-hom-retraction-retract-sequential-diagramᵉ :
    (nᵉ : ℕᵉ) → family-sequential-diagramᵉ Bᵉ nᵉ → family-sequential-diagramᵉ Aᵉ nᵉ
  map-hom-retraction-retract-sequential-diagramᵉ =
    map-hom-sequential-diagramᵉ Aᵉ hom-retraction-retract-sequential-diagramᵉ

  naturality-hom-retraction-retract-sequential-diagramᵉ :
    naturality-hom-sequential-diagramᵉ Bᵉ Aᵉ
      ( map-hom-retraction-retract-sequential-diagramᵉ)
  naturality-hom-retraction-retract-sequential-diagramᵉ =
    naturality-map-hom-sequential-diagramᵉ Aᵉ
      ( hom-retraction-retract-sequential-diagramᵉ)

  is-retraction-hom-retraction-retract-sequential-diagramᵉ :
    is-retraction-hom-sequential-diagramᵉ Aᵉ Bᵉ
      ( inclusion-retract-sequential-diagramᵉ)
      ( hom-retraction-retract-sequential-diagramᵉ)
  is-retraction-hom-retraction-retract-sequential-diagramᵉ =
    is-retraction-hom-retraction-hom-sequential-diagramᵉ Aᵉ Bᵉ
      ( inclusion-retract-sequential-diagramᵉ)
      ( retraction-retract-sequential-diagramᵉ)

  is-retraction-map-hom-retraction-retract-sequential-diagramᵉ :
    (nᵉ : ℕᵉ) →
    is-retractionᵉ
      ( map-inclusion-retract-sequential-diagramᵉ nᵉ)
      ( map-hom-retraction-retract-sequential-diagramᵉ nᵉ)
  is-retraction-map-hom-retraction-retract-sequential-diagramᵉ =
    htpy-htpy-hom-sequential-diagramᵉ Aᵉ
      ( is-retraction-hom-retraction-retract-sequential-diagramᵉ)

  retract-family-retract-sequential-diagramᵉ :
    (nᵉ : ℕᵉ) →
    ( family-sequential-diagramᵉ Aᵉ nᵉ) retract-ofᵉ
    ( family-sequential-diagramᵉ Bᵉ nᵉ)
  pr1ᵉ (retract-family-retract-sequential-diagramᵉ nᵉ) =
    map-inclusion-retract-sequential-diagramᵉ nᵉ
  pr1ᵉ (pr2ᵉ (retract-family-retract-sequential-diagramᵉ nᵉ)) =
    map-hom-retraction-retract-sequential-diagramᵉ nᵉ
  pr2ᵉ (pr2ᵉ (retract-family-retract-sequential-diagramᵉ nᵉ)) =
    is-retraction-map-hom-retraction-retract-sequential-diagramᵉ nᵉ

  coh-retract-sequential-diagramᵉ :
    coherence-retract-sequential-diagramᵉ Aᵉ Bᵉ
      ( inclusion-retract-sequential-diagramᵉ)
      ( hom-retraction-retract-sequential-diagramᵉ)
      ( is-retraction-map-hom-retraction-retract-sequential-diagramᵉ)
  coh-retract-sequential-diagramᵉ =
    coherence-htpy-htpy-hom-sequential-diagramᵉ Aᵉ
      ( is-retraction-hom-retraction-retract-sequential-diagramᵉ)
```

## See also

-ᵉ [Retractsᵉ ofᵉ maps](foundation.retracts-of-maps.mdᵉ)