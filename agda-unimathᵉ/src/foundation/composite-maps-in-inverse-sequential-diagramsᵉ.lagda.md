# Composite maps in inverse sequential diagrams

```agda
module foundation.composite-maps-in-inverse-sequential-diagramsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ

open import foundation.dependent-inverse-sequential-diagramsᵉ
open import foundation.inverse-sequential-diagramsᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.function-typesᵉ
```

</details>

## Idea

Givenᵉ aᵉ ([dependent](foundation.dependent-inverse-sequential-diagrams.mdᵉ))
[inverseᵉ sequentialᵉ diagram](foundation.inverse-sequential-diagrams.mdᵉ) `A`,ᵉ weᵉ
canᵉ extractᵉ theᵉ **compositeᵉ mapᵉ fromᵉ `Aₙ₊ᵣ`ᵉ to `Aₙ`**.ᵉ

## Definitions

### Composite maps in inverse sequential diagrams

```agda
comp-map-inverse-sequential-diagramᵉ :
  {lᵉ : Level} (Aᵉ : inverse-sequential-diagramᵉ lᵉ) (nᵉ rᵉ : ℕᵉ) →
  family-inverse-sequential-diagramᵉ Aᵉ (nᵉ +ℕᵉ rᵉ) →
  family-inverse-sequential-diagramᵉ Aᵉ nᵉ
comp-map-inverse-sequential-diagramᵉ Aᵉ nᵉ zero-ℕᵉ = idᵉ
comp-map-inverse-sequential-diagramᵉ Aᵉ nᵉ (succ-ℕᵉ rᵉ) =
  comp-map-inverse-sequential-diagramᵉ Aᵉ nᵉ rᵉ ∘ᵉ
  map-inverse-sequential-diagramᵉ Aᵉ (nᵉ +ℕᵉ rᵉ)
```

### Composite maps in dependent inverse sequential diagrams

```agda
comp-map-dependent-inverse-sequential-diagramᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : inverse-sequential-diagramᵉ l1ᵉ}
  (Bᵉ : dependent-inverse-sequential-diagramᵉ l2ᵉ Aᵉ)
  (nᵉ rᵉ : ℕᵉ) (xᵉ : family-inverse-sequential-diagramᵉ Aᵉ (nᵉ +ℕᵉ rᵉ)) →
  family-dependent-inverse-sequential-diagramᵉ Bᵉ (nᵉ +ℕᵉ rᵉ) xᵉ →
  family-dependent-inverse-sequential-diagramᵉ Bᵉ nᵉ
    ( comp-map-inverse-sequential-diagramᵉ Aᵉ nᵉ rᵉ xᵉ)
comp-map-dependent-inverse-sequential-diagramᵉ Bᵉ nᵉ zero-ℕᵉ xᵉ yᵉ = yᵉ
comp-map-dependent-inverse-sequential-diagramᵉ {Aᵉ = Aᵉ} Bᵉ nᵉ (succ-ℕᵉ rᵉ) xᵉ yᵉ =
  comp-map-dependent-inverse-sequential-diagramᵉ Bᵉ nᵉ rᵉ
    ( map-inverse-sequential-diagramᵉ Aᵉ (nᵉ +ℕᵉ rᵉ) xᵉ)
    ( map-dependent-inverse-sequential-diagramᵉ Bᵉ (nᵉ +ℕᵉ rᵉ) xᵉ yᵉ)
```

## Table of files about sequential limits

Theᵉ followingᵉ tableᵉ listsᵉ filesᵉ thatᵉ areᵉ aboutᵉ sequentialᵉ limitsᵉ asᵉ aᵉ generalᵉ
concept.ᵉ

{{#includeᵉ tables/sequential-limits.mdᵉ}}