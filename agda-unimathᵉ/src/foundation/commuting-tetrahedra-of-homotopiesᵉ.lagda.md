# Commuting tetrahedra of homotopies

```agda
module foundation.commuting-tetrahedra-of-homotopiesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-triangles-of-homotopiesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.homotopiesᵉ
```

</details>

## Idea

Aᵉ
{{#conceptᵉ "commutingᵉ tetrahedronᵉ ofᵉ homotopies"ᵉ Agda=coherence-tetrahedron-homotopiesᵉ}}
isᵉ aᵉ commutingᵉ diagramᵉ ofᵉ theᵉ formᵉ

```text
             topᵉ
       fᵉ ---------->ᵉ gᵉ
       |  \ᵉ       ∧ᵉ  |
       |    \ᵉ   /ᵉ    |
  leftᵉ |      /ᵉ      | rightᵉ
       |    /ᵉ   \ᵉ    |
       ∨ᵉ  /ᵉ       ∨ᵉ  ∨ᵉ
       hᵉ ---------->ᵉ i.ᵉ
            bottomᵉ
```

where `f`,ᵉ `g`,ᵉ `h`,ᵉ andᵉ `i`ᵉ areᵉ functions.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  {fᵉ gᵉ hᵉ iᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ}
  (topᵉ : fᵉ ~ᵉ gᵉ) (leftᵉ : fᵉ ~ᵉ hᵉ) (rightᵉ : gᵉ ~ᵉ iᵉ) (bottomᵉ : hᵉ ~ᵉ iᵉ)
  (diagonal-upᵉ : hᵉ ~ᵉ gᵉ) (diagonal-downᵉ : fᵉ ~ᵉ iᵉ)
  (upper-leftᵉ : coherence-triangle-homotopiesᵉ topᵉ diagonal-upᵉ leftᵉ)
  (lower-rightᵉ : coherence-triangle-homotopiesᵉ bottomᵉ rightᵉ diagonal-upᵉ)
  (upper-rightᵉ : coherence-triangle-homotopiesᵉ diagonal-downᵉ rightᵉ topᵉ)
  (lower-leftᵉ : coherence-triangle-homotopiesᵉ diagonal-downᵉ bottomᵉ leftᵉ)
  where

  coherence-tetrahedron-homotopiesᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  coherence-tetrahedron-homotopiesᵉ =
    ( ( upper-rightᵉ) ∙hᵉ
      ( right-whisker-concat-coherence-triangle-homotopiesᵉ
        ( topᵉ)
        ( diagonal-upᵉ)
        ( leftᵉ)
        ( upper-leftᵉ)
        ( rightᵉ))) ~ᵉ
    ( ( lower-leftᵉ) ∙hᵉ
      ( left-whisker-concat-coherence-triangle-homotopiesᵉ
        ( leftᵉ)
        ( bottomᵉ)
        ( rightᵉ)
        ( diagonal-upᵉ)
        ( lower-rightᵉ)) ∙hᵉ
      ( assoc-htpyᵉ leftᵉ diagonal-upᵉ rightᵉ))

  coherence-tetrahedron-homotopies'ᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  coherence-tetrahedron-homotopies'ᵉ =
    ( ( lower-leftᵉ) ∙hᵉ
      ( left-whisker-concat-coherence-triangle-homotopiesᵉ
        ( leftᵉ)
        ( bottomᵉ)
        ( rightᵉ)
        ( diagonal-upᵉ)
        ( lower-rightᵉ)) ∙hᵉ
      ( assoc-htpyᵉ leftᵉ diagonal-upᵉ rightᵉ)) ~ᵉ
    ( ( upper-rightᵉ) ∙hᵉ
      ( right-whisker-concat-coherence-triangle-homotopiesᵉ
        ( topᵉ)
        ( diagonal-upᵉ)
        ( leftᵉ)
        ( upper-leftᵉ)
        ( rightᵉ)))
```