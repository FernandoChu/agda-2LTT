# Dependent inverse sequential diagrams of types

```agda
module foundation.dependent-inverse-sequential-diagramsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.inverse-sequential-diagramsᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.function-typesᵉ
open import foundation-core.homotopiesᵉ
```

</details>

## Idea

Aᵉ **dependentᵉ inverseᵉ sequentialᵉ diagram**ᵉ `B`ᵉ overᵉ aᵉ baseᵉ
[inverseᵉ sequentialᵉ diagram](foundation.inverse-sequential-diagrams.mdᵉ) `A`ᵉ isᵉ aᵉ
[sequence](foundation.sequences.mdᵉ) ofᵉ familiesᵉ overᵉ eachᵉ `Aₙ`ᵉ togetherᵉ with
mapsᵉ ofᵉ fibersᵉ

```text
  gₙᵉ : (xₙ₊₁ᵉ : Aₙ₊₁ᵉ) → Bₙ₊₁(xₙ₊₁ᵉ) → Bₙ(fₙ(xₙ₊₁)),ᵉ
```

where `f`ᵉ isᵉ theᵉ sequenceᵉ ofᵉ mapsᵉ ofᵉ theᵉ baseᵉ inverseᵉ sequentialᵉ diagram,ᵉ givingᵉ
aᵉ dependentᵉ sequentialᵉ diagramᵉ ofᵉ mapsᵉ thatᵉ extendᵉ infinitelyᵉ to theᵉ leftᵉ:

```text
     g₃ᵉ      g₂ᵉ      g₁ᵉ      g₀ᵉ
  ⋯ᵉ --->ᵉ B₃ᵉ --->ᵉ B₂ᵉ --->ᵉ B₁ᵉ --->ᵉ B₀.ᵉ
```

## Definitions

### Dependent inverse sequential diagrams of types

```agda
sequence-map-dependent-inverse-sequential-diagramᵉ :
  {l1ᵉ l2ᵉ : Level} (Aᵉ : inverse-sequential-diagramᵉ l1ᵉ) →
  ((nᵉ : ℕᵉ) → family-inverse-sequential-diagramᵉ Aᵉ nᵉ → UUᵉ l2ᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
sequence-map-dependent-inverse-sequential-diagramᵉ Aᵉ Bᵉ =
  (nᵉ : ℕᵉ) (xᵉ : family-inverse-sequential-diagramᵉ Aᵉ (succ-ℕᵉ nᵉ)) →
  Bᵉ (succ-ℕᵉ nᵉ) xᵉ → Bᵉ nᵉ (map-inverse-sequential-diagramᵉ Aᵉ nᵉ xᵉ)

dependent-inverse-sequential-diagramᵉ :
  {l1ᵉ : Level} (l2ᵉ : Level) (Aᵉ : inverse-sequential-diagramᵉ l1ᵉ) →
  UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
dependent-inverse-sequential-diagramᵉ l2ᵉ Aᵉ =
  Σᵉ ( (nᵉ : ℕᵉ) → family-inverse-sequential-diagramᵉ Aᵉ nᵉ → UUᵉ l2ᵉ)
    ( sequence-map-dependent-inverse-sequential-diagramᵉ Aᵉ)

family-dependent-inverse-sequential-diagramᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : inverse-sequential-diagramᵉ l1ᵉ} →
  dependent-inverse-sequential-diagramᵉ l2ᵉ Aᵉ →
  (nᵉ : ℕᵉ) → family-inverse-sequential-diagramᵉ Aᵉ nᵉ → UUᵉ l2ᵉ
family-dependent-inverse-sequential-diagramᵉ = pr1ᵉ

map-dependent-inverse-sequential-diagramᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : inverse-sequential-diagramᵉ l1ᵉ}
  (Bᵉ : dependent-inverse-sequential-diagramᵉ l2ᵉ Aᵉ) →
  (nᵉ : ℕᵉ) (xᵉ : family-inverse-sequential-diagramᵉ Aᵉ (succ-ℕᵉ nᵉ)) →
  family-dependent-inverse-sequential-diagramᵉ Bᵉ (succ-ℕᵉ nᵉ) xᵉ →
  family-dependent-inverse-sequential-diagramᵉ Bᵉ nᵉ
    ( map-inverse-sequential-diagramᵉ Aᵉ nᵉ xᵉ)
map-dependent-inverse-sequential-diagramᵉ = pr2ᵉ
```

### Constant dependent inverse sequential diagrams of types

```agda
const-dependent-inverse-sequential-diagramᵉ :
  {l1ᵉ l2ᵉ : Level}
  (Aᵉ : inverse-sequential-diagramᵉ l1ᵉ) → inverse-sequential-diagramᵉ l2ᵉ →
  dependent-inverse-sequential-diagramᵉ l2ᵉ Aᵉ
pr1ᵉ (const-dependent-inverse-sequential-diagramᵉ Aᵉ Bᵉ) nᵉ _ =
  family-inverse-sequential-diagramᵉ Bᵉ nᵉ
pr2ᵉ (const-dependent-inverse-sequential-diagramᵉ Aᵉ Bᵉ) nᵉ _ =
  map-inverse-sequential-diagramᵉ Bᵉ nᵉ
```

### Sections of a dependent inverse sequential diagram

Aᵉ **sectionᵉ ofᵉ aᵉ dependentᵉ inverseᵉ sequentialᵉ diagramᵉ `(Bᵉ ,ᵉ g)`ᵉ overᵉ `(Aᵉ ,ᵉ f)`**ᵉ
isᵉ aᵉ choiceᵉ ofᵉ sectionsᵉ `hₙ`ᵉ ofᵉ eachᵉ `Bₙ`ᵉ thatᵉ varyᵉ naturallyᵉ overᵉ `A`,ᵉ byᵉ whichᵉ
weᵉ meanᵉ thatᵉ theᵉ diagramsᵉ

```text
            gₙᵉ
      Bₙ₊₁ᵉ --->ᵉ Bₙᵉ
      ∧ᵉ         ∧ᵉ
  hₙ₊₁|ᵉ         | hₙᵉ
      |         |
      Aₙ₊₁ᵉ --->ᵉ Aₙᵉ
            fₙᵉ
```

commuteᵉ forᵉ eachᵉ `nᵉ : ℕ`.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : inverse-sequential-diagramᵉ l1ᵉ)
  (Bᵉ : dependent-inverse-sequential-diagramᵉ l2ᵉ Aᵉ)
  where

  naturality-section-dependent-inverse-sequential-diagramᵉ :
    (hᵉ :
      (nᵉ : ℕᵉ) (xᵉ : family-inverse-sequential-diagramᵉ Aᵉ nᵉ) →
      family-dependent-inverse-sequential-diagramᵉ Bᵉ nᵉ xᵉ)
    (nᵉ : ℕᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  naturality-section-dependent-inverse-sequential-diagramᵉ hᵉ nᵉ =
    hᵉ nᵉ ∘ᵉ map-inverse-sequential-diagramᵉ Aᵉ nᵉ ~ᵉ
    map-dependent-inverse-sequential-diagramᵉ Bᵉ nᵉ _ ∘ᵉ hᵉ (succ-ℕᵉ nᵉ)

  section-dependent-inverse-sequential-diagramᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  section-dependent-inverse-sequential-diagramᵉ =
    Σᵉ ( (nᵉ : ℕᵉ) (xᵉ : family-inverse-sequential-diagramᵉ Aᵉ nᵉ) →
        family-dependent-inverse-sequential-diagramᵉ Bᵉ nᵉ xᵉ)
      ( λ hᵉ → (nᵉ : ℕᵉ) →
        naturality-section-dependent-inverse-sequential-diagramᵉ hᵉ nᵉ)

  map-section-dependent-inverse-sequential-diagramᵉ :
    section-dependent-inverse-sequential-diagramᵉ →
    (nᵉ : ℕᵉ) (xᵉ : family-inverse-sequential-diagramᵉ Aᵉ nᵉ) →
    family-dependent-inverse-sequential-diagramᵉ Bᵉ nᵉ xᵉ
  map-section-dependent-inverse-sequential-diagramᵉ = pr1ᵉ

  naturality-map-section-dependent-inverse-sequential-diagramᵉ :
    (fᵉ : section-dependent-inverse-sequential-diagramᵉ) (nᵉ : ℕᵉ) →
    naturality-section-dependent-inverse-sequential-diagramᵉ
      ( map-section-dependent-inverse-sequential-diagramᵉ fᵉ)
      ( nᵉ)
  naturality-map-section-dependent-inverse-sequential-diagramᵉ = pr2ᵉ
```

## Operations

### Right shifting a dependent inverse sequential diagram

Weᵉ canᵉ **rightᵉ shift**ᵉ aᵉ dependentᵉ inverseᵉ sequentialᵉ diagramᵉ ofᵉ typesᵉ byᵉ
forgettingᵉ theᵉ firstᵉ terms.ᵉ

```agda
right-shift-dependent-inverse-sequential-diagramᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : inverse-sequential-diagramᵉ l1ᵉ} →
  dependent-inverse-sequential-diagramᵉ l2ᵉ Aᵉ →
  dependent-inverse-sequential-diagramᵉ l2ᵉ
    ( right-shift-inverse-sequential-diagramᵉ Aᵉ)
pr1ᵉ (right-shift-dependent-inverse-sequential-diagramᵉ Bᵉ) nᵉ =
  family-dependent-inverse-sequential-diagramᵉ Bᵉ (succ-ℕᵉ nᵉ)
pr2ᵉ (right-shift-dependent-inverse-sequential-diagramᵉ Bᵉ) nᵉ =
  map-dependent-inverse-sequential-diagramᵉ Bᵉ (succ-ℕᵉ nᵉ)
```

### Left shifting a dependent inverse sequential diagram

Weᵉ canᵉ **leftᵉ shift**ᵉ aᵉ dependentᵉ inverseᵉ sequentialᵉ diagramᵉ ofᵉ typesᵉ byᵉ paddingᵉ
itᵉ with theᵉ [terminalᵉ type](foundation.unit-type.mdᵉ) `unit`.ᵉ

```agda
left-shift-dependent-inverse-sequential-diagramᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : inverse-sequential-diagramᵉ l1ᵉ} →
  dependent-inverse-sequential-diagramᵉ l2ᵉ Aᵉ →
  dependent-inverse-sequential-diagramᵉ l2ᵉ
    ( left-shift-inverse-sequential-diagramᵉ Aᵉ)
pr1ᵉ (left-shift-dependent-inverse-sequential-diagramᵉ {l2ᵉ = l2ᵉ} Bᵉ) 0 xᵉ =
  raise-unitᵉ l2ᵉ
pr1ᵉ (left-shift-dependent-inverse-sequential-diagramᵉ Bᵉ) (succ-ℕᵉ nᵉ) =
  family-dependent-inverse-sequential-diagramᵉ Bᵉ nᵉ
pr2ᵉ (left-shift-dependent-inverse-sequential-diagramᵉ Bᵉ) 0 xᵉ =
  raise-terminal-mapᵉ (family-dependent-inverse-sequential-diagramᵉ Bᵉ 0 xᵉ)
pr2ᵉ (left-shift-dependent-inverse-sequential-diagramᵉ Bᵉ) (succ-ℕᵉ nᵉ) =
  map-dependent-inverse-sequential-diagramᵉ Bᵉ nᵉ
```

## Table of files about sequential limits

Theᵉ followingᵉ tableᵉ listsᵉ filesᵉ thatᵉ areᵉ aboutᵉ sequentialᵉ limitsᵉ asᵉ aᵉ generalᵉ
concept.ᵉ

{{#includeᵉ tables/sequential-limits.mdᵉ}}