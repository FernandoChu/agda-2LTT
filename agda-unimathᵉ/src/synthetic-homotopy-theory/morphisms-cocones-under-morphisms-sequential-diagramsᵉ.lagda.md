# Morphisms of cocones under morphisms of sequential diagrams

```agda
module synthetic-homotopy-theory.morphisms-cocones-under-morphisms-sequential-diagramsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.commuting-prisms-of-mapsᵉ
open import foundation.commuting-squares-of-mapsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import synthetic-homotopy-theory.cocones-under-sequential-diagramsᵉ
open import synthetic-homotopy-theory.morphisms-sequential-diagramsᵉ
open import synthetic-homotopy-theory.sequential-diagramsᵉ
```

</details>

## Idea

Considerᵉ twoᵉ
[sequentialᵉ diagrams](synthetic-homotopy-theory.sequential-diagrams.mdᵉ) `(A,ᵉ a)`ᵉ
andᵉ `(B,ᵉ b)`,ᵉ equippedᵉ with
[cocones](synthetic-homotopy-theory.cocones-under-sequential-diagrams.mdᵉ)
`cᵉ : Aᵉ → X`ᵉ andᵉ `c'ᵉ : Bᵉ → Y`,ᵉ respectively,ᵉ andᵉ aᵉ
[morphismᵉ ofᵉ sequentialᵉ diagrams](synthetic-homotopy-theory.morphisms-sequential-diagrams.mdᵉ)
`hᵉ : Aᵉ → B`.ᵉ Thenᵉ aᵉ
{{#conceptᵉ "morphismᵉ ofᵉ cocones"ᵉ Disambiguation="underᵉ aᵉ morphismᵉ ofᵉ sequentialᵉ diagrams"ᵉ Agda=hom-cocone-hom-sequential-diagramᵉ}}
underᵉ `h`ᵉ isᵉ aᵉ tripleᵉ `(u,ᵉ H,ᵉ K)`,ᵉ with `uᵉ : Xᵉ → Y`ᵉ aᵉ mapᵉ ofᵉ verticesᵉ ofᵉ theᵉ
coforks,ᵉ `H`ᵉ aᵉ familyᵉ ofᵉ [homotopies](foundation-core.homotopies.mdᵉ) witnessingᵉ
thatᵉ theᵉ squareᵉ

```text
           iₙᵉ
     Aₙᵉ ------->ᵉ Xᵉ
     |           |
  hₙᵉ |           | uᵉ
     |           |
     ∨ᵉ           ∨ᵉ
     Bₙᵉ ------->ᵉ Yᵉ
           i'ₙᵉ
```

[commutes](foundation-core.commuting-squares-of-maps.mdᵉ) forᵉ everyᵉ `n`,ᵉ andᵉ `K`ᵉ
aᵉ familyᵉ ofᵉ coherenceᵉ data fillingᵉ theᵉ insidesᵉ ofᵉ theᵉ resultingᵉ
[prism](foundation.commuting-prisms-of-maps.mdᵉ) boundariesᵉ

```text
            Aₙ₊₁ᵉ
       aₙᵉ  ∧ᵉ |  \ᵉ  iₙ₊₁ᵉ
         /ᵉ   |    \ᵉ
       /ᵉ     |      ∨ᵉ
     Aₙᵉ ----------->ᵉ Xᵉ
     |   iₙᵉ  |       |
     |       | hₙ₊₁ᵉ  |
  hₙᵉ |       ∨ᵉ       | uᵉ
     |      Bₙ₊₁ᵉ     |
     |  bₙᵉ ∧ᵉ   \i'ₙ₊₁|ᵉ
     |   /ᵉ       \ᵉ   |
     ∨ᵉ /ᵉ           ∨ᵉ ∨ᵉ
     Bₙᵉ ----------->ᵉ Yᵉ
            i'ₙᵉ
```

forᵉ everyᵉ `n`.ᵉ

## Definition

### Morphisms of cocones under morphisms of sequential diagrams

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  {Aᵉ : sequential-diagramᵉ l1ᵉ} {Xᵉ : UUᵉ l2ᵉ} (cᵉ : cocone-sequential-diagramᵉ Aᵉ Xᵉ)
  {Bᵉ : sequential-diagramᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ} (c'ᵉ : cocone-sequential-diagramᵉ Bᵉ Yᵉ)
  (hᵉ : hom-sequential-diagramᵉ Aᵉ Bᵉ)
  where

  coherence-map-cocone-hom-cocone-hom-sequential-diagramᵉ :
    (Xᵉ → Yᵉ) → UUᵉ (l1ᵉ ⊔ l4ᵉ)
  coherence-map-cocone-hom-cocone-hom-sequential-diagramᵉ uᵉ =
    (nᵉ : ℕᵉ) →
    coherence-square-mapsᵉ
      ( map-cocone-sequential-diagramᵉ cᵉ nᵉ)
      ( map-hom-sequential-diagramᵉ Bᵉ hᵉ nᵉ)
      ( uᵉ)
      ( map-cocone-sequential-diagramᵉ c'ᵉ nᵉ)

  coherence-hom-cocone-hom-sequential-diagramᵉ :
    (uᵉ : Xᵉ → Yᵉ) →
    coherence-map-cocone-hom-cocone-hom-sequential-diagramᵉ uᵉ →
    UUᵉ (l1ᵉ ⊔ l4ᵉ)
  coherence-hom-cocone-hom-sequential-diagramᵉ uᵉ Hᵉ =
    (nᵉ : ℕᵉ) →
    vertical-coherence-prism-mapsᵉ
      ( map-cocone-sequential-diagramᵉ cᵉ nᵉ)
      ( map-cocone-sequential-diagramᵉ cᵉ (succ-ℕᵉ nᵉ))
      ( map-sequential-diagramᵉ Aᵉ nᵉ)
      ( map-cocone-sequential-diagramᵉ c'ᵉ nᵉ)
      ( map-cocone-sequential-diagramᵉ c'ᵉ (succ-ℕᵉ nᵉ))
      ( map-sequential-diagramᵉ Bᵉ nᵉ)
      ( map-hom-sequential-diagramᵉ Bᵉ hᵉ nᵉ)
      ( map-hom-sequential-diagramᵉ Bᵉ hᵉ (succ-ℕᵉ nᵉ))
      ( uᵉ)
      ( coherence-cocone-sequential-diagramᵉ cᵉ nᵉ)
      ( Hᵉ nᵉ)
      ( Hᵉ (succ-ℕᵉ nᵉ))
      ( naturality-map-hom-sequential-diagramᵉ Bᵉ hᵉ nᵉ)
      ( coherence-cocone-sequential-diagramᵉ c'ᵉ nᵉ)

  hom-cocone-hom-sequential-diagramᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l4ᵉ)
  hom-cocone-hom-sequential-diagramᵉ =
    Σᵉ ( Xᵉ → Yᵉ)
      ( λ uᵉ →
        Σᵉ ( coherence-map-cocone-hom-cocone-hom-sequential-diagramᵉ uᵉ)
          ( coherence-hom-cocone-hom-sequential-diagramᵉ uᵉ))
```

### Components of a morphism of cocones under a morphism of sequential diagrams

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  {Aᵉ : sequential-diagramᵉ l1ᵉ} {Xᵉ : UUᵉ l2ᵉ} (cᵉ : cocone-sequential-diagramᵉ Aᵉ Xᵉ)
  {Bᵉ : sequential-diagramᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ} (c'ᵉ : cocone-sequential-diagramᵉ Bᵉ Yᵉ)
  {hᵉ : hom-sequential-diagramᵉ Aᵉ Bᵉ}
  (mᵉ : hom-cocone-hom-sequential-diagramᵉ cᵉ c'ᵉ hᵉ)
  where

  map-hom-cocone-hom-sequential-diagramᵉ : Xᵉ → Yᵉ
  map-hom-cocone-hom-sequential-diagramᵉ = pr1ᵉ mᵉ

  coh-map-cocone-hom-cocone-hom-sequential-diagramᵉ :
    coherence-map-cocone-hom-cocone-hom-sequential-diagramᵉ cᵉ c'ᵉ hᵉ
      ( map-hom-cocone-hom-sequential-diagramᵉ)
  coh-map-cocone-hom-cocone-hom-sequential-diagramᵉ = pr1ᵉ (pr2ᵉ mᵉ)

  coh-hom-cocone-hom-sequential-diagramᵉ :
    coherence-hom-cocone-hom-sequential-diagramᵉ cᵉ c'ᵉ hᵉ
      ( map-hom-cocone-hom-sequential-diagramᵉ)
      ( coh-map-cocone-hom-cocone-hom-sequential-diagramᵉ)
  coh-hom-cocone-hom-sequential-diagramᵉ = pr2ᵉ (pr2ᵉ mᵉ)
```