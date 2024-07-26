# Commuting tetrahedra of maps

```agda
module foundation.commuting-tetrahedra-of-mapsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ

open import foundation-core.commuting-triangles-of-mapsᵉ
open import foundation-core.homotopiesᵉ
```

</details>

## Idea

Aᵉ {{#conceptᵉ "commutingᵉ tetrahedronᵉ ofᵉ maps"ᵉ Agda=coherence-tetrahedron-mapsᵉ}}
isᵉ aᵉ commutingᵉ diagramᵉ ofᵉ theᵉ formᵉ

```text
  Aᵉ ---------->ᵉ Bᵉ
  |  \ᵉ       ∧ᵉ  |
  |    \ᵉ   /ᵉ    |
  |      /ᵉ      |
  |    /ᵉ   \ᵉ    |
  ∨ᵉ  /ᵉ       ∨ᵉ  ∨ᵉ
  Xᵉ ---------->ᵉ Y.ᵉ
```

## Definition

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (topᵉ : Aᵉ → Bᵉ) (leftᵉ : Aᵉ → Xᵉ) (rightᵉ : Bᵉ → Yᵉ) (bottomᵉ : Xᵉ → Yᵉ)
  (diagonal-upᵉ : Xᵉ → Bᵉ) (diagonal-downᵉ : Aᵉ → Yᵉ)
  (upper-leftᵉ : coherence-triangle-mapsᵉ topᵉ diagonal-upᵉ leftᵉ)
  (lower-rightᵉ : coherence-triangle-mapsᵉ bottomᵉ rightᵉ diagonal-upᵉ)
  (upper-rightᵉ : coherence-triangle-mapsᵉ diagonal-downᵉ rightᵉ topᵉ)
  (lower-leftᵉ : coherence-triangle-mapsᵉ diagonal-downᵉ bottomᵉ leftᵉ)
  where

  coherence-tetrahedron-mapsᵉ : UUᵉ (l1ᵉ ⊔ l4ᵉ)
  coherence-tetrahedron-mapsᵉ =
    ( upper-rightᵉ ∙hᵉ (rightᵉ ·lᵉ upper-leftᵉ)) ~ᵉ
    ( lower-leftᵉ ∙hᵉ (lower-rightᵉ ·rᵉ leftᵉ))

  coherence-tetrahedron-maps'ᵉ : UUᵉ (l1ᵉ ⊔ l4ᵉ)
  coherence-tetrahedron-maps'ᵉ =
    ( lower-leftᵉ ∙hᵉ (lower-rightᵉ ·rᵉ leftᵉ)) ~ᵉ
    ( upper-rightᵉ ∙hᵉ (rightᵉ ·lᵉ upper-leftᵉ))
```