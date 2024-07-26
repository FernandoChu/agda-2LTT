# Morphisms of dependent sequential diagrams

```agda
module synthetic-homotopy-theory.morphisms-dependent-sequential-diagramsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.commuting-squares-of-mapsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import synthetic-homotopy-theory.dependent-sequential-diagramsᵉ
open import synthetic-homotopy-theory.sequential-diagramsᵉ
```

</details>

## Idea

Considerᵉ twoᵉ
[dependentᵉ sequentialᵉ diagrams](synthetic-homotopy-theory.dependent-sequential-diagrams.mdᵉ)

```text
     b₀ᵉ      b₁ᵉ      b₂ᵉ            c₀ᵉ      c₁ᵉ      c₂ᵉ
 B₀ᵉ --->ᵉ B₁ᵉ --->ᵉ B₂ᵉ --->ᵉ ⋯ᵉ     C₀ᵉ --->ᵉ C₁ᵉ --->ᵉ C₂ᵉ --->ᵉ ⋯ᵉ
 |       |       |             |       |       |
 |       |       |             |       |       |
 ↡ᵉ       ↡ᵉ       ↡ᵉ             ↡ᵉ       ↡ᵉ       ↡ᵉ
 A₀ᵉ --->ᵉ A₁ᵉ --->ᵉ A₂ᵉ --->ᵉ ⋯ᵉ     A₀ᵉ --->ᵉ A₁ᵉ --->ᵉ A₂ᵉ --->ᵉ ⋯ᵉ .ᵉ
     a₀ᵉ      a₁ᵉ      a₂ᵉ            a₀ᵉ      a₁ᵉ      a₂ᵉ
```

Aᵉ
{{#conceptᵉ "morphismᵉ ofᵉ dependentᵉ sequentialᵉ diagrams"ᵉ Agda=hom-dependent-sequential-diagramᵉ}}
betweenᵉ themᵉ isᵉ aᵉ familyᵉ ofᵉ fiberwiseᵉ mapsᵉ

```text
hₙᵉ : (aᵉ : Aₙᵉ) → Bₙᵉ aᵉ → Cₙᵉ aᵉ
```

[equipped](foundation.structure.mdᵉ) with aᵉ familyᵉ ofᵉ fiberwiseᵉ
[homotopies](foundation-core.homotopies.mdᵉ) makingᵉ theᵉ squaresᵉ

```text
                 hₙᵉ aᵉ
     Bₙᵉ aᵉ ----------------->ᵉ Cₙᵉ aᵉ
       |                       |
  bₙᵉ aᵉ |                       | cₙᵉ aᵉ
       |                       |
       ∨ᵉ                       ∨ᵉ
  Bₙ₊₁ᵉ (aₙᵉ aᵉ) ---------->ᵉ Cₙ₊₁ᵉ (aₙᵉ aᵉ)
              hₙ₊₁ᵉ (aₙᵉ aᵉ)
```

[commute](foundation-core.commuting-squares-of-maps.md).ᵉ

## Definitions

### Morphisms of dependent sequential diagrams

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ}
  (Bᵉ : dependent-sequential-diagramᵉ Aᵉ l2ᵉ)
  (Cᵉ : dependent-sequential-diagramᵉ Aᵉ l3ᵉ)
  where

  coherence-hom-dependent-sequential-diagramᵉ :
    ( (nᵉ : ℕᵉ) (aᵉ : family-sequential-diagramᵉ Aᵉ nᵉ) →
      family-dependent-sequential-diagramᵉ Bᵉ nᵉ aᵉ →
      family-dependent-sequential-diagramᵉ Cᵉ nᵉ aᵉ) →
    UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  coherence-hom-dependent-sequential-diagramᵉ hᵉ =
    (nᵉ : ℕᵉ) (aᵉ : family-sequential-diagramᵉ Aᵉ nᵉ) →
    coherence-square-mapsᵉ
      ( hᵉ nᵉ aᵉ)
      ( map-dependent-sequential-diagramᵉ Bᵉ nᵉ aᵉ)
      ( map-dependent-sequential-diagramᵉ Cᵉ nᵉ aᵉ)
      ( hᵉ (succ-ℕᵉ nᵉ) (map-sequential-diagramᵉ Aᵉ nᵉ aᵉ))

  hom-dependent-sequential-diagramᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  hom-dependent-sequential-diagramᵉ =
    Σᵉ ( (nᵉ : ℕᵉ) (aᵉ : family-sequential-diagramᵉ Aᵉ nᵉ) →
        family-dependent-sequential-diagramᵉ Bᵉ nᵉ aᵉ →
        family-dependent-sequential-diagramᵉ Cᵉ nᵉ aᵉ)
      ( coherence-hom-dependent-sequential-diagramᵉ)
```

### Components of a morphism of sequential diagrams

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ}
  {Bᵉ : dependent-sequential-diagramᵉ Aᵉ l2ᵉ}
  (Cᵉ : dependent-sequential-diagramᵉ Aᵉ l3ᵉ)
  (hᵉ : hom-dependent-sequential-diagramᵉ Bᵉ Cᵉ)
  where

  map-hom-dependent-sequential-diagramᵉ :
    (nᵉ : ℕᵉ) (aᵉ : family-sequential-diagramᵉ Aᵉ nᵉ) →
    family-dependent-sequential-diagramᵉ Bᵉ nᵉ aᵉ →
    family-dependent-sequential-diagramᵉ Cᵉ nᵉ aᵉ
  map-hom-dependent-sequential-diagramᵉ = pr1ᵉ hᵉ

  coh-hom-dependent-sequential-diagramᵉ :
    coherence-hom-dependent-sequential-diagramᵉ Bᵉ Cᵉ
      ( map-hom-dependent-sequential-diagramᵉ)
  coh-hom-dependent-sequential-diagramᵉ = pr2ᵉ hᵉ
```