# Inverse sequential diagrams of types

```agda
module foundation.inverse-sequential-diagramsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.iterating-functionsᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Anᵉ
{{#conceptᵉ "inverseᵉ sequentialᵉ diagram"ᵉ Disambiguation="types"ᵉ Agda=inverse-sequential-diagramᵉ}}
ofᵉ typesᵉ `A`ᵉ isᵉ aᵉ [sequence](foundation.sequences.mdᵉ) ofᵉ typesᵉ togetherᵉ with
mapsᵉ betweenᵉ everyᵉ twoᵉ consecutiveᵉ typesᵉ

```text
  fₙᵉ : Aₙ₊₁ᵉ → Aₙᵉ
```

givingᵉ aᵉ sequentialᵉ diagramᵉ ofᵉ mapsᵉ thatᵉ extendᵉ infinitelyᵉ to theᵉ leftᵉ:

```text
     f₃ᵉ      f₂ᵉ      f₁ᵉ      f₀ᵉ
  ⋯ᵉ --->ᵉ A₃ᵉ --->ᵉ A₂ᵉ --->ᵉ A₁ᵉ --->ᵉ A₀.ᵉ
```

Thisᵉ isᵉ in contrastᵉ to theᵉ notionᵉ ofᵉ
[sequentialᵉ diagram](synthetic-homotopy-theory.sequential-diagrams.md),ᵉ whichᵉ
extendᵉ infinitelyᵉ to theᵉ right,ᵉ henceᵉ isᵉ theᵉ formalᵉ dualᵉ to inverseᵉ sequentialᵉ
diagrams.ᵉ

## Definitions

### Inverse sequential diagrams of types

```agda
sequence-map-inverse-sequential-diagramᵉ : {lᵉ : Level} → (ℕᵉ → UUᵉ lᵉ) → UUᵉ lᵉ
sequence-map-inverse-sequential-diagramᵉ Aᵉ = (nᵉ : ℕᵉ) → Aᵉ (succ-ℕᵉ nᵉ) → Aᵉ nᵉ

inverse-sequential-diagramᵉ : (lᵉ : Level) → UUᵉ (lsuc lᵉ)
inverse-sequential-diagramᵉ lᵉ =
  Σᵉ (ℕᵉ → UUᵉ lᵉ) (sequence-map-inverse-sequential-diagramᵉ)

family-inverse-sequential-diagramᵉ :
  {lᵉ : Level} → inverse-sequential-diagramᵉ lᵉ → ℕᵉ → UUᵉ lᵉ
family-inverse-sequential-diagramᵉ = pr1ᵉ

map-inverse-sequential-diagramᵉ :
  {lᵉ : Level} (Aᵉ : inverse-sequential-diagramᵉ lᵉ) (nᵉ : ℕᵉ) →
  family-inverse-sequential-diagramᵉ Aᵉ (succ-ℕᵉ nᵉ) →
  family-inverse-sequential-diagramᵉ Aᵉ nᵉ
map-inverse-sequential-diagramᵉ = pr2ᵉ
```

## Operations

### Right shifting an inverse sequential diagram

Weᵉ canᵉ **rightᵉ shift**ᵉ anᵉ inverseᵉ sequentialᵉ diagramᵉ ofᵉ typesᵉ byᵉ forgettingᵉ theᵉ
firstᵉ terms.ᵉ

```agda
right-shift-inverse-sequential-diagramᵉ :
  {lᵉ : Level} → inverse-sequential-diagramᵉ lᵉ → inverse-sequential-diagramᵉ lᵉ
pr1ᵉ (right-shift-inverse-sequential-diagramᵉ Aᵉ) nᵉ =
  family-inverse-sequential-diagramᵉ Aᵉ (succ-ℕᵉ nᵉ)
pr2ᵉ (right-shift-inverse-sequential-diagramᵉ Aᵉ) nᵉ =
  map-inverse-sequential-diagramᵉ Aᵉ (succ-ℕᵉ nᵉ)

iterated-right-shift-inverse-sequential-diagramᵉ :
  {lᵉ : Level} (nᵉ : ℕᵉ) →
  inverse-sequential-diagramᵉ lᵉ → inverse-sequential-diagramᵉ lᵉ
iterated-right-shift-inverse-sequential-diagramᵉ nᵉ =
  iterateᵉ nᵉ right-shift-inverse-sequential-diagramᵉ
```

### Left shifting an inverse sequential diagram

Weᵉ canᵉ **leftᵉ shift**ᵉ anᵉ inverseᵉ sequentialᵉ diagramᵉ ofᵉ typesᵉ byᵉ paddingᵉ itᵉ with
theᵉ [terminalᵉ type](foundation.unit-type.mdᵉ) `unit`.ᵉ

```agda
left-shift-inverse-sequential-diagramᵉ :
  {lᵉ : Level} → inverse-sequential-diagramᵉ lᵉ → inverse-sequential-diagramᵉ lᵉ
pr1ᵉ (left-shift-inverse-sequential-diagramᵉ {lᵉ} Aᵉ) 0 = raise-unitᵉ lᵉ
pr1ᵉ (left-shift-inverse-sequential-diagramᵉ Aᵉ) (succ-ℕᵉ nᵉ) =
  family-inverse-sequential-diagramᵉ Aᵉ nᵉ
pr2ᵉ (left-shift-inverse-sequential-diagramᵉ Aᵉ) 0 =
  raise-terminal-mapᵉ (family-inverse-sequential-diagramᵉ Aᵉ 0ᵉ)
pr2ᵉ (left-shift-inverse-sequential-diagramᵉ Aᵉ) (succ-ℕᵉ nᵉ) =
  map-inverse-sequential-diagramᵉ Aᵉ nᵉ

iterated-left-shift-inverse-sequential-diagramᵉ :
  {lᵉ : Level} (nᵉ : ℕᵉ) →
  inverse-sequential-diagramᵉ lᵉ → inverse-sequential-diagramᵉ lᵉ
iterated-left-shift-inverse-sequential-diagramᵉ nᵉ =
  iterateᵉ nᵉ left-shift-inverse-sequential-diagramᵉ
```

### Postcomposition inverse sequential diagrams

Givenᵉ anᵉ inverseᵉ sequentialᵉ diagramᵉ `A`ᵉ andᵉ aᵉ typeᵉ `X`ᵉ thereᵉ isᵉ anᵉ inverseᵉ
sequentialᵉ diagramᵉ `Xᵉ → A`ᵉ definedᵉ byᵉ levelwiseᵉ postcompositionᵉ

```text
                    (f₂ᵉ ∘ᵉ -ᵉ)          (f₁ᵉ ∘ᵉ -ᵉ)          (f₀ᵉ ∘ᵉ -ᵉ)
  ⋯ᵉ ----->ᵉ (Xᵉ → A₃ᵉ) ------->ᵉ (Xᵉ → A₂ᵉ) ------->ᵉ (Xᵉ → A₁ᵉ) ------->ᵉ (Xᵉ → A₀).ᵉ
```

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Xᵉ : UUᵉ l1ᵉ) (Aᵉ : inverse-sequential-diagramᵉ l2ᵉ)
  where

  postcomp-inverse-sequential-diagramᵉ : inverse-sequential-diagramᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ postcomp-inverse-sequential-diagramᵉ nᵉ =
    Xᵉ → family-inverse-sequential-diagramᵉ Aᵉ nᵉ
  pr2ᵉ postcomp-inverse-sequential-diagramᵉ nᵉ gᵉ xᵉ =
    map-inverse-sequential-diagramᵉ Aᵉ nᵉ (gᵉ xᵉ)
```

## Table of files about sequential limits

Theᵉ followingᵉ tableᵉ listsᵉ filesᵉ thatᵉ areᵉ aboutᵉ sequentialᵉ limitsᵉ asᵉ aᵉ generalᵉ
concept.ᵉ

{{#includeᵉ tables/sequential-limits.mdᵉ}}