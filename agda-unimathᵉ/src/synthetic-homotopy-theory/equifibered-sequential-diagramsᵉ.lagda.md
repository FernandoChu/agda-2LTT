# Equifibered sequential diagrams

```agda
module synthetic-homotopy-theory.equifibered-sequential-diagramsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.universe-levelsᵉ

open import synthetic-homotopy-theory.dependent-sequential-diagramsᵉ
open import synthetic-homotopy-theory.sequential-diagramsᵉ
```

</details>

## Idea

Anᵉ
{{#conceptᵉ "equifiberedᵉ sequentialᵉ diagram"ᵉ Disambiguation="overᵉ aᵉ sequentialᵉ diagram"ᵉ Agda=equifibered-sequential-diagramᵉ}}
overᵉ aᵉ [sequentialᵉ diagram](synthetic-homotopy-theory.sequential-diagrams.mdᵉ)
`(A,ᵉ a)`ᵉ consistsᵉ ofᵉ aᵉ typeᵉ familyᵉ `Bᵉ : (nᵉ : ℕᵉ) → Aₙᵉ → 𝒰`ᵉ
[equipped](foundation.structure.mdᵉ) with aᵉ familyᵉ ofᵉ fiberwiseᵉ equivalencesᵉ

```text
bₙᵉ : (aᵉ : Aₙᵉ) → Bₙᵉ aᵉ ≃ᵉ Bₙ₊₁ᵉ (aₙᵉ aᵉ) .ᵉ
```

Theᵉ termᵉ "equifibered"ᵉ comesᵉ fromᵉ theᵉ equivalentᵉ definitionᵉ asᵉ
[dependentᵉ sequentialᵉ diagrams](synthetic-homotopy-theory.dependent-sequential-diagrams.mdᵉ)
overᵉ `(A,ᵉ a)`ᵉ

```text
     b₀ᵉ      b₁ᵉ      b₂ᵉ
 B₀ᵉ --->ᵉ B₁ᵉ --->ᵉ B₂ᵉ --->ᵉ ⋯ᵉ
 |       |       |
 |       |       |
 ↡ᵉ       ↡ᵉ       ↡ᵉ
 A₀ᵉ --->ᵉ A₁ᵉ --->ᵉ A₂ᵉ --->ᵉ ⋯ᵉ ,ᵉ
     a₀ᵉ      a₁ᵉ      a₂ᵉ
```

whichᵉ areᵉ saidᵉ to beᵉ "fiberedᵉ overᵉ `A`",ᵉ whoseᵉ mapsᵉ `bₙ`ᵉ areᵉ equivalences.ᵉ

## Definitions

### Equifibered sequential diagrams

```agda
module _
  {l1ᵉ : Level} (Aᵉ : sequential-diagramᵉ l1ᵉ)
  where

  equifibered-sequential-diagramᵉ : (lᵉ : Level) → UUᵉ (l1ᵉ ⊔ lsuc lᵉ)
  equifibered-sequential-diagramᵉ lᵉ =
    Σᵉ ( (nᵉ : ℕᵉ) → family-sequential-diagramᵉ Aᵉ nᵉ → UUᵉ lᵉ)
      ( λ Bᵉ →
        (nᵉ : ℕᵉ) (aᵉ : family-sequential-diagramᵉ Aᵉ nᵉ) →
        Bᵉ nᵉ aᵉ ≃ᵉ Bᵉ (succ-ℕᵉ nᵉ) (map-sequential-diagramᵉ Aᵉ nᵉ aᵉ))
```

### Components of an equifibered sequential diagram

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ}
  (Bᵉ : equifibered-sequential-diagramᵉ Aᵉ l2ᵉ)
  where

  family-equifibered-sequential-diagramᵉ :
    (nᵉ : ℕᵉ) → family-sequential-diagramᵉ Aᵉ nᵉ → UUᵉ l2ᵉ
  family-equifibered-sequential-diagramᵉ = pr1ᵉ Bᵉ

  equiv-equifibered-sequential-diagramᵉ :
    (nᵉ : ℕᵉ) (aᵉ : family-sequential-diagramᵉ Aᵉ nᵉ) →
    family-equifibered-sequential-diagramᵉ nᵉ aᵉ ≃ᵉ
    family-equifibered-sequential-diagramᵉ
      ( succ-ℕᵉ nᵉ)
      ( map-sequential-diagramᵉ Aᵉ nᵉ aᵉ)
  equiv-equifibered-sequential-diagramᵉ = pr2ᵉ Bᵉ

  map-equifibered-sequential-diagramᵉ :
    (nᵉ : ℕᵉ) (aᵉ : family-sequential-diagramᵉ Aᵉ nᵉ) →
    family-equifibered-sequential-diagramᵉ nᵉ aᵉ →
    family-equifibered-sequential-diagramᵉ
      ( succ-ℕᵉ nᵉ)
      ( map-sequential-diagramᵉ Aᵉ nᵉ aᵉ)
  map-equifibered-sequential-diagramᵉ nᵉ aᵉ =
    map-equivᵉ (equiv-equifibered-sequential-diagramᵉ nᵉ aᵉ)

  is-equiv-map-equifibered-sequential-diagramᵉ :
    (nᵉ : ℕᵉ) (aᵉ : family-sequential-diagramᵉ Aᵉ nᵉ) →
    is-equivᵉ (map-equifibered-sequential-diagramᵉ nᵉ aᵉ)
  is-equiv-map-equifibered-sequential-diagramᵉ nᵉ aᵉ =
    is-equiv-map-equivᵉ (equiv-equifibered-sequential-diagramᵉ nᵉ aᵉ)

  dependent-sequential-diagram-equifibered-sequential-diagramᵉ :
    dependent-sequential-diagramᵉ Aᵉ l2ᵉ
  pr1ᵉ dependent-sequential-diagram-equifibered-sequential-diagramᵉ =
    family-equifibered-sequential-diagramᵉ
  pr2ᵉ dependent-sequential-diagram-equifibered-sequential-diagramᵉ =
    map-equifibered-sequential-diagramᵉ
```

### The predicate on dependent sequential diagrams of being equifibered

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ}
  where

  is-equifibered-dependent-sequential-diagramᵉ :
    (Bᵉ : dependent-sequential-diagramᵉ Aᵉ l2ᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-equifibered-dependent-sequential-diagramᵉ Bᵉ =
    (nᵉ : ℕᵉ) (aᵉ : family-sequential-diagramᵉ Aᵉ nᵉ) →
    is-equivᵉ (map-dependent-sequential-diagramᵉ Bᵉ nᵉ aᵉ)

  is-equifibered-dependent-sequential-diagram-equifibered-sequential-diagramᵉ :
    (Bᵉ : equifibered-sequential-diagramᵉ Aᵉ l2ᵉ) →
    is-equifibered-dependent-sequential-diagramᵉ
      ( dependent-sequential-diagram-equifibered-sequential-diagramᵉ Bᵉ)
  is-equifibered-dependent-sequential-diagram-equifibered-sequential-diagramᵉ Bᵉ =
    is-equiv-map-equifibered-sequential-diagramᵉ Bᵉ
```

## Properties

### Dependent sequential diagrams which are equifibered are equifibered sequential diagrams

Toᵉ constructᵉ anᵉ equifiberedᵉ sequentialᵉ diagramᵉ overᵉ `A`,ᵉ itᵉ sufficesᵉ to
constructᵉ aᵉ dependentᵉ sequentialᵉ diagramᵉ `(B,ᵉ b)`ᵉ overᵉ `A`,ᵉ andᵉ showᵉ thatᵉ theᵉ
mapsᵉ `bₙ`ᵉ areᵉ equivalences.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ}
  (Bᵉ : dependent-sequential-diagramᵉ Aᵉ l2ᵉ)
  where

  equifibered-sequential-diagram-dependent-sequential-diagramᵉ :
    is-equifibered-dependent-sequential-diagramᵉ Bᵉ →
    equifibered-sequential-diagramᵉ Aᵉ l2ᵉ
  pr1ᵉ (equifibered-sequential-diagram-dependent-sequential-diagramᵉ _) =
    family-dependent-sequential-diagramᵉ Bᵉ
  pr2ᵉ (equifibered-sequential-diagram-dependent-sequential-diagramᵉ is-equiv-mapᵉ)
    nᵉ aᵉ =
    (map-dependent-sequential-diagramᵉ Bᵉ nᵉ aᵉ ,ᵉ is-equiv-mapᵉ nᵉ aᵉ)
```