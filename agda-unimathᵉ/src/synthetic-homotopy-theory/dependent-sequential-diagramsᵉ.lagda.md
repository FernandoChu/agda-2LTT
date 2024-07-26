# Dependent sequential diagrams

```agda
module synthetic-homotopy-theory.dependent-sequential-diagramsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.function-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.universe-levelsᵉ

open import synthetic-homotopy-theory.sequential-diagramsᵉ
```

</details>

## Idea

Aᵉ **dependentᵉ sequentialᵉ diagram**ᵉ overᵉ aᵉ
[sequentialᵉ diagram](synthetic-homotopy-theory.sequential-diagrams.mdᵉ) `(A,ᵉ a)`ᵉ
isᵉ aᵉ [sequence](foundation.dependent-sequences.mdᵉ) ofᵉ familiesᵉ ofᵉ typesᵉ
`Bᵉ : (nᵉ : ℕᵉ) → Aₙᵉ → 𝒰`ᵉ overᵉ theᵉ typesᵉ in theᵉ baseᵉ sequentialᵉ diagram,ᵉ equippedᵉ
with fiberwiseᵉ mapsᵉ

```text
bₙᵉ : (xᵉ : Aₙᵉ) → Bₙᵉ xᵉ → Bₙ₊₁ᵉ (aₙᵉ x).ᵉ
```

Theyᵉ canᵉ beᵉ thoughtᵉ ofᵉ asᵉ aᵉ familyᵉ ofᵉ sequentialᵉ diagramsᵉ

```text
       bₙ(xᵉ)           bₙ₊₁(aₙ(xᵉ))
 Bₙ(xᵉ) ---->ᵉ Bₙ₊₁(aₙ(xᵉ)) ------->ᵉ Bₙ₊₂(aₙ₊₁(aₙ(xᵉ))) ---->ᵉ ⋯,ᵉ
```

oneᵉ forᵉ eachᵉ `xᵉ : Aₙ`,ᵉ orᵉ asᵉ aᵉ sequenceᵉ fiberedᵉ overᵉ `(A,ᵉ a)`,ᵉ visualisedᵉ asᵉ

```text
     b₀ᵉ      b₁ᵉ      b₂ᵉ
 B₀ᵉ --->ᵉ B₁ᵉ --->ᵉ B₂ᵉ --->ᵉ ⋯ᵉ
 |       |       |
 |       |       |
 ↡ᵉ       ↡ᵉ       ↡ᵉ
 A₀ᵉ --->ᵉ A₁ᵉ --->ᵉ A₂ᵉ --->ᵉ ⋯.ᵉ
     a₀ᵉ      a₁ᵉ      a₂ᵉ
```

## Definitions

### Dependent sequential diagrams

```agda
dependent-sequential-diagramᵉ :
  { l1ᵉ : Level} → (Aᵉ : sequential-diagramᵉ l1ᵉ) →
  ( l2ᵉ : Level) → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
dependent-sequential-diagramᵉ Aᵉ l2ᵉ =
  Σᵉ ( ( nᵉ : ℕᵉ) → family-sequential-diagramᵉ Aᵉ nᵉ → UUᵉ l2ᵉ)
    ( λ Bᵉ →
      ( nᵉ : ℕᵉ) (xᵉ : family-sequential-diagramᵉ Aᵉ nᵉ) →
      Bᵉ nᵉ xᵉ → Bᵉ (succ-ℕᵉ nᵉ) (map-sequential-diagramᵉ Aᵉ nᵉ xᵉ))
```

### Components of a dependent sequential diagram

```agda
module _
  { l1ᵉ l2ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ}
  ( Bᵉ : dependent-sequential-diagramᵉ Aᵉ l2ᵉ)
  where

  family-dependent-sequential-diagramᵉ :
    ( nᵉ : ℕᵉ) → family-sequential-diagramᵉ Aᵉ nᵉ → UUᵉ l2ᵉ
  family-dependent-sequential-diagramᵉ = pr1ᵉ Bᵉ

  map-dependent-sequential-diagramᵉ :
    ( nᵉ : ℕᵉ) (xᵉ : family-sequential-diagramᵉ Aᵉ nᵉ) →
    family-dependent-sequential-diagramᵉ nᵉ xᵉ →
    family-dependent-sequential-diagramᵉ
      ( succ-ℕᵉ nᵉ)
      ( map-sequential-diagramᵉ Aᵉ nᵉ xᵉ)
  map-dependent-sequential-diagramᵉ = pr2ᵉ Bᵉ
```

### Constant dependent sequential diagrams

Constantᵉ dependentᵉ sequentialᵉ diagramsᵉ areᵉ dependentᵉ sequentialᵉ diagramsᵉ where
theᵉ dependentᵉ typeᵉ familyᵉ `B`ᵉ isᵉ [constant](foundation.constant-maps.md).ᵉ

```agda
module _
  { l1ᵉ l2ᵉ : Level} (Aᵉ : sequential-diagramᵉ l1ᵉ) (Bᵉ : sequential-diagramᵉ l2ᵉ)
  where

  constant-dependent-sequential-diagramᵉ : dependent-sequential-diagramᵉ Aᵉ l2ᵉ
  pr1ᵉ constant-dependent-sequential-diagramᵉ nᵉ _ = family-sequential-diagramᵉ Bᵉ nᵉ
  pr2ᵉ constant-dependent-sequential-diagramᵉ nᵉ _ = map-sequential-diagramᵉ Bᵉ nᵉ
```

### Sections of dependent sequential diagrams

Aᵉ **sectionᵉ ofᵉ aᵉ dependentᵉ sequentialᵉ diagram**ᵉ `(B,ᵉ b)`ᵉ isᵉ aᵉ
[sequence](foundation.dependent-sequences.mdᵉ) ofᵉ sectionsᵉ
`sₙᵉ : (xᵉ : Aₙᵉ) → Bₙ(x)`ᵉ satisfyingᵉ theᵉ naturalityᵉ conditionᵉ thatᵉ allᵉ squaresᵉ ofᵉ
theᵉ formᵉ

```text
          bₙ(xᵉ)
  Bₙ(xᵉ) ------->ᵉ Bₙ₊₁(aₙ(xᵉ))
    ∧ᵉ                ∧ᵉ
 sₙᵉ |                | sₙ₊₁ᵉ
    |                |
 (xᵉ : Aₙᵉ) --->ᵉ (aₙ(xᵉ) : Aₙ₊₁ᵉ)
           aₙᵉ
```

[commute](foundation.commuting-squares-of-maps.md).ᵉ

```agda
module _
  { l1ᵉ l2ᵉ : Level} (Aᵉ : sequential-diagramᵉ l1ᵉ)
  ( Bᵉ : dependent-sequential-diagramᵉ Aᵉ l2ᵉ)
  where

  naturality-section-dependent-sequential-diagramᵉ :
    ( sᵉ :
      ( nᵉ : ℕᵉ) (xᵉ : family-sequential-diagramᵉ Aᵉ nᵉ) →
      family-dependent-sequential-diagramᵉ Bᵉ nᵉ xᵉ) →
    UUᵉ (l1ᵉ ⊔ l2ᵉ)
  naturality-section-dependent-sequential-diagramᵉ sᵉ =
    ( nᵉ : ℕᵉ) →
    ( map-dependent-sequential-diagramᵉ Bᵉ nᵉ _ ∘ᵉ sᵉ nᵉ) ~ᵉ
    ( sᵉ (succ-ℕᵉ nᵉ) ∘ᵉ map-sequential-diagramᵉ Aᵉ nᵉ)

  section-dependent-sequential-diagramᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  section-dependent-sequential-diagramᵉ =
    Σᵉ ( ( nᵉ : ℕᵉ) (xᵉ : family-sequential-diagramᵉ Aᵉ nᵉ) →
        family-dependent-sequential-diagramᵉ Bᵉ nᵉ xᵉ)
      ( λ sᵉ → naturality-section-dependent-sequential-diagramᵉ sᵉ)
```

### Components of sections of dependent sequential diagrams

```agda
module _
  { l1ᵉ l2ᵉ : Level} (Aᵉ : sequential-diagramᵉ l1ᵉ)
  ( Bᵉ : dependent-sequential-diagramᵉ Aᵉ l2ᵉ)
  ( sᵉ : section-dependent-sequential-diagramᵉ Aᵉ Bᵉ)
  where

  map-section-dependent-sequential-diagramᵉ :
    ( nᵉ : ℕᵉ) (xᵉ : family-sequential-diagramᵉ Aᵉ nᵉ) →
    family-dependent-sequential-diagramᵉ Bᵉ nᵉ xᵉ
  map-section-dependent-sequential-diagramᵉ = pr1ᵉ sᵉ

  naturality-map-section-dependent-sequential-diagramᵉ :
    naturality-section-dependent-sequential-diagramᵉ Aᵉ Bᵉ
      map-section-dependent-sequential-diagramᵉ
  naturality-map-section-dependent-sequential-diagramᵉ = pr2ᵉ sᵉ
```

## References

{{#bibliographyᵉ}} {{#referenceᵉ SvDR20ᵉ}}