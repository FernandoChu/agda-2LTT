# Functoriality of sequential colimits

```agda
module synthetic-homotopy-theory.functoriality-sequential-colimitsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.commuting-prisms-of-mapsᵉ
open import foundation.commuting-squares-of-homotopiesᵉ
open import foundation.commuting-squares-of-mapsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.retractionsᵉ
open import foundation.retracts-of-typesᵉ
open import foundation.sectionsᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ

open import synthetic-homotopy-theory.cocones-under-sequential-diagramsᵉ
open import synthetic-homotopy-theory.equivalences-sequential-diagramsᵉ
open import synthetic-homotopy-theory.morphisms-sequential-diagramsᵉ
open import synthetic-homotopy-theory.retracts-of-sequential-diagramsᵉ
open import synthetic-homotopy-theory.sequential-colimitsᵉ
open import synthetic-homotopy-theory.sequential-diagramsᵉ
open import synthetic-homotopy-theory.universal-property-sequential-colimitsᵉ
```

</details>

## Idea

Givenᵉ twoᵉ
[sequentialᵉ diagrams](synthetic-homotopy-theory.sequential-diagrams.mdᵉ) `(A,ᵉ a)`ᵉ
andᵉ `(B,ᵉ b)`,ᵉ theirᵉ
[sequentialᵉ colimits](synthetic-homotopy-theory.universal-property-sequential-colimits.mdᵉ)
`X`ᵉ andᵉ `Y`,ᵉ andᵉ aᵉ
[morphism](synthetic-homotopy-theory.morphisms-sequential-diagrams.mdᵉ)
`fᵉ : (A,ᵉ aᵉ) → (B,ᵉ b)`,ᵉ thereᵉ isᵉ aᵉ uniqueᵉ mapᵉ `gᵉ : Xᵉ → Y`,ᵉ suchᵉ thatᵉ theᵉ diagramᵉ

```text
        a₀ᵉ      a₁ᵉ      a₂ᵉ
    A₀ᵉ --->ᵉ A₁ᵉ --->ᵉ A₂ᵉ --->ᵉ ⋯ᵉ --->ᵉ Xᵉ
    |       |       |              |
 f₀ᵉ |       | f₁ᵉ    | f₂ᵉ           | gᵉ
    ∨ᵉ       ∨ᵉ       ∨ᵉ              ∨ᵉ
    B₀ᵉ --->ᵉ B₁ᵉ --->ᵉ B₂ᵉ --->ᵉ ⋯ᵉ --->ᵉ Yᵉ
        b₀ᵉ      b₁ᵉ      b₂ᵉ
```

[commutes](foundation.commuting-squares-of-maps.md).ᵉ

Theᵉ uniqueᵉ mapᵉ correspondingᵉ to theᵉ identityᵉ morphismᵉ isᵉ theᵉ identityᵉ mapᵉ
`idᵉ : Xᵉ → X`,ᵉ andᵉ theᵉ uniqueᵉ mapᵉ correspondingᵉ to aᵉ compositeᵉ ofᵉ twoᵉ morphismsᵉ
isᵉ theᵉ compositeᵉ ofᵉ theᵉ twoᵉ uniqueᵉ mapsᵉ forᵉ theᵉ individualᵉ morphisms.ᵉ

Inᵉ particular,ᵉ whenᵉ weᵉ alsoᵉ considerᵉ existenceᵉ ofᵉ theᵉ
[standardᵉ sequentialᵉ colimits](synthetic-homotopy-theory.sequential-colimits.md),ᵉ
weᵉ obtainᵉ aᵉ functorialᵉ actionᵉ takingᵉ sequentialᵉ diagramsᵉ andᵉ morphismsᵉ betweenᵉ
themᵉ to theirᵉ colimitsᵉ andᵉ mapsᵉ betweenᵉ them.ᵉ

```text
  (A,ᵉ aᵉ)    A∞ᵉ
    |       |
  fᵉ |   ↦ᵉ   | f∞ᵉ
    ∨ᵉ       ∨ᵉ
  (B,ᵉ bᵉ)    B∞ᵉ  .ᵉ
```

Additionally,ᵉ anᵉ
[equivalenceᵉ ofᵉ sequentialᵉ diagrams](synthetic-homotopy-theory.equivalences-sequential-diagrams.mdᵉ)
inducesᵉ anᵉ [equivalence](foundation.equivalences.mdᵉ) ofᵉ theirᵉ colimits.ᵉ

## Properties

### A morphism of sequential diagrams induces a map of cocones

```agda
module _
  { l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ} {Bᵉ : sequential-diagramᵉ l2ᵉ}
  ( fᵉ : hom-sequential-diagramᵉ Aᵉ Bᵉ) {Xᵉ : UUᵉ l3ᵉ}
  where

  map-cocone-hom-sequential-diagramᵉ :
    cocone-sequential-diagramᵉ Bᵉ Xᵉ → cocone-sequential-diagramᵉ Aᵉ Xᵉ
  map-cocone-hom-sequential-diagramᵉ cᵉ =
    comp-hom-sequential-diagramᵉ Aᵉ Bᵉ (constant-sequential-diagramᵉ Xᵉ) cᵉ fᵉ
```

### A morphism of sequential diagrams induces a map of sequential colimits

Theᵉ uniqueᵉ mapᵉ `gᵉ : Xᵉ → Y`ᵉ suchᵉ thatᵉ theᵉ diagramᵉ

```text
        a₀ᵉ      a₁ᵉ      a₂ᵉ
    A₀ᵉ --->ᵉ A₁ᵉ --->ᵉ A₂ᵉ --->ᵉ ⋯ᵉ --->ᵉ Xᵉ
    |       |       |              |
 f₀ᵉ |       | f₁ᵉ    | f₂ᵉ           | gᵉ
    ∨ᵉ       ∨ᵉ       ∨ᵉ              ∨ᵉ
    B₀ᵉ --->ᵉ B₁ᵉ --->ᵉ B₂ᵉ --->ᵉ ⋯ᵉ --->ᵉ Yᵉ
        b₀ᵉ      b₁ᵉ      b₂ᵉ
```

commutesᵉ thenᵉ inducesᵉ aᵉ
[cocone](synthetic-homotopy-theory.cocones-under-sequential-diagrams.mdᵉ) underᵉ
`(A,ᵉ a)`ᵉ with codomainᵉ `Y`,ᵉ whichᵉ isᵉ homotopicᵉ to theᵉ coconeᵉ underᵉ `(B,ᵉ b)`ᵉ
precomposedᵉ byᵉ `f`.ᵉ

Thisᵉ homotopyᵉ ofᵉ coconesᵉ providesᵉ
[verticalᵉ commutingᵉ prismsᵉ ofᵉ maps](foundation.commuting-prisms-of-maps.md),ᵉ

```text
          Aₙ₊₁ᵉ
         ∧ᵉ | \ᵉ
       /ᵉ   |   \ᵉ
     /ᵉ     |fₙ₊₁ᵉ ∨ᵉ
    Aₙᵉ --------->ᵉ Xᵉ
    |      |      |
    |      ∨ᵉ      |
 fₙᵉ |     Bₙ₊₁ᵉ    | gᵉ
    |    ∧ᵉ   \ᵉ    |
    |  /ᵉ       \ᵉ  |
    ∨/ᵉ           ∨∨ᵉ
    Bₙᵉ --------->ᵉ Yᵉ ,ᵉ
```

where theᵉ [triangles](foundation-core.commuting-triangles-of-maps.mdᵉ) areᵉ
coherencesᵉ ofᵉ theᵉ coconesᵉ ofᵉ theᵉ sequentialᵉ colimits,ᵉ theᵉ backᵉ leftᵉ
[square](foundation-core.commuting-triangles-of-maps.mdᵉ) isᵉ coherenceᵉ ofᵉ `f`,ᵉ
andᵉ theᵉ frontᵉ andᵉ backᵉ rightᵉ squaresᵉ areᵉ providedᵉ byᵉ uniquenessᵉ ofᵉ `g`.ᵉ

```agda
module _
  { l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ} {Bᵉ : sequential-diagramᵉ l2ᵉ}
  { Xᵉ : UUᵉ l3ᵉ} {cᵉ : cocone-sequential-diagramᵉ Aᵉ Xᵉ}
  ( up-cᵉ : universal-property-sequential-colimitᵉ cᵉ)
  { Yᵉ : UUᵉ l4ᵉ} (c'ᵉ : cocone-sequential-diagramᵉ Bᵉ Yᵉ)
  ( fᵉ : hom-sequential-diagramᵉ Aᵉ Bᵉ)
  where

  map-sequential-colimit-hom-sequential-diagramᵉ : Xᵉ → Yᵉ
  map-sequential-colimit-hom-sequential-diagramᵉ =
    map-universal-property-sequential-colimitᵉ up-cᵉ
      ( map-cocone-hom-sequential-diagramᵉ fᵉ c'ᵉ)

  htpy-cocone-map-sequential-colimit-hom-sequential-diagramᵉ :
    htpy-cocone-sequential-diagramᵉ
      ( cocone-map-sequential-diagramᵉ cᵉ
        ( map-sequential-colimit-hom-sequential-diagramᵉ))
      ( map-cocone-hom-sequential-diagramᵉ fᵉ c'ᵉ)
  htpy-cocone-map-sequential-colimit-hom-sequential-diagramᵉ =
    htpy-cocone-universal-property-sequential-colimitᵉ up-cᵉ
      ( map-cocone-hom-sequential-diagramᵉ fᵉ c'ᵉ)

  htpy-htpy-cocone-map-sequential-colimit-hom-sequential-diagramᵉ :
    ( nᵉ : ℕᵉ) →
    coherence-square-mapsᵉ
      ( map-hom-sequential-diagramᵉ Bᵉ fᵉ nᵉ)
      ( map-cocone-sequential-diagramᵉ cᵉ nᵉ)
      ( map-cocone-sequential-diagramᵉ c'ᵉ nᵉ)
      ( map-sequential-colimit-hom-sequential-diagramᵉ)
  htpy-htpy-cocone-map-sequential-colimit-hom-sequential-diagramᵉ =
    htpy-htpy-cocone-sequential-diagramᵉ
      ( htpy-cocone-map-sequential-colimit-hom-sequential-diagramᵉ)

  coherence-htpy-cocone-map-sequential-colimit-hom-sequential-diagramᵉ :
    ( nᵉ : ℕᵉ) →
    coherence-square-homotopiesᵉ
      ( htpy-htpy-cocone-map-sequential-colimit-hom-sequential-diagramᵉ nᵉ)
      ( ( map-sequential-colimit-hom-sequential-diagramᵉ) ·lᵉ
        ( coherence-cocone-sequential-diagramᵉ cᵉ nᵉ))
      ( coherence-cocone-sequential-diagramᵉ
        ( map-cocone-hom-sequential-diagramᵉ fᵉ c'ᵉ)
        ( nᵉ))
      ( ( htpy-htpy-cocone-map-sequential-colimit-hom-sequential-diagramᵉ
          ( succ-ℕᵉ nᵉ)) ·rᵉ
        ( map-sequential-diagramᵉ Aᵉ nᵉ))
  coherence-htpy-cocone-map-sequential-colimit-hom-sequential-diagramᵉ =
    coherence-htpy-htpy-cocone-sequential-diagramᵉ
      htpy-cocone-map-sequential-colimit-hom-sequential-diagramᵉ

  prism-htpy-cocone-map-sequential-colimit-hom-sequential-diagramᵉ :
    ( nᵉ : ℕᵉ) →
    vertical-coherence-prism-mapsᵉ
      ( map-cocone-sequential-diagramᵉ cᵉ nᵉ)
      ( map-cocone-sequential-diagramᵉ cᵉ (succ-ℕᵉ nᵉ))
      ( map-sequential-diagramᵉ Aᵉ nᵉ)
      ( map-cocone-sequential-diagramᵉ c'ᵉ nᵉ)
      ( map-cocone-sequential-diagramᵉ c'ᵉ (succ-ℕᵉ nᵉ))
      ( map-sequential-diagramᵉ Bᵉ nᵉ)
      ( map-hom-sequential-diagramᵉ Bᵉ fᵉ nᵉ)
      ( map-hom-sequential-diagramᵉ Bᵉ fᵉ (succ-ℕᵉ nᵉ))
      ( map-sequential-colimit-hom-sequential-diagramᵉ)
      ( coherence-cocone-sequential-diagramᵉ cᵉ nᵉ)
      ( inv-htpyᵉ
        ( htpy-htpy-cocone-map-sequential-colimit-hom-sequential-diagramᵉ nᵉ))
      ( inv-htpyᵉ
        ( htpy-htpy-cocone-map-sequential-colimit-hom-sequential-diagramᵉ
          ( succ-ℕᵉ nᵉ)))
      ( naturality-map-hom-sequential-diagramᵉ Bᵉ fᵉ nᵉ)
      ( coherence-cocone-sequential-diagramᵉ c'ᵉ nᵉ)
  prism-htpy-cocone-map-sequential-colimit-hom-sequential-diagramᵉ nᵉ =
    rotate-vertical-coherence-prism-mapsᵉ
      ( map-cocone-sequential-diagramᵉ cᵉ nᵉ)
      ( map-cocone-sequential-diagramᵉ cᵉ (succ-ℕᵉ nᵉ))
      ( map-sequential-diagramᵉ Aᵉ nᵉ)
      ( map-cocone-sequential-diagramᵉ c'ᵉ nᵉ)
      ( map-cocone-sequential-diagramᵉ c'ᵉ (succ-ℕᵉ nᵉ))
      ( map-sequential-diagramᵉ Bᵉ nᵉ)
      ( map-hom-sequential-diagramᵉ Bᵉ fᵉ nᵉ)
      ( map-hom-sequential-diagramᵉ Bᵉ fᵉ (succ-ℕᵉ nᵉ))
      ( map-sequential-colimit-hom-sequential-diagramᵉ)
      ( coherence-cocone-sequential-diagramᵉ cᵉ nᵉ)
      ( htpy-htpy-cocone-map-sequential-colimit-hom-sequential-diagramᵉ nᵉ)
      ( htpy-htpy-cocone-map-sequential-colimit-hom-sequential-diagramᵉ
        ( succ-ℕᵉ nᵉ))
      ( naturality-map-hom-sequential-diagramᵉ Bᵉ fᵉ nᵉ)
      ( coherence-cocone-sequential-diagramᵉ c'ᵉ nᵉ)
      ( inv-htpyᵉ
        ( coherence-htpy-cocone-map-sequential-colimit-hom-sequential-diagramᵉ
          ( nᵉ)))
```

### Homotopies between morphisms of sequential diagrams induce homotopies of corresponding maps between sequential colimits

```agda
module _
  { l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ} {Bᵉ : sequential-diagramᵉ l2ᵉ}
  { Xᵉ : UUᵉ l3ᵉ} {cᵉ : cocone-sequential-diagramᵉ Aᵉ Xᵉ}
  ( up-cᵉ : universal-property-sequential-colimitᵉ cᵉ)
  { Yᵉ : UUᵉ l4ᵉ} (c'ᵉ : cocone-sequential-diagramᵉ Bᵉ Yᵉ)
  { fᵉ gᵉ : hom-sequential-diagramᵉ Aᵉ Bᵉ} (Hᵉ : htpy-hom-sequential-diagramᵉ Bᵉ fᵉ gᵉ)
  where

  htpy-map-sequential-colimit-htpy-hom-sequential-diagramᵉ :
    map-sequential-colimit-hom-sequential-diagramᵉ up-cᵉ c'ᵉ fᵉ ~ᵉ
    map-sequential-colimit-hom-sequential-diagramᵉ up-cᵉ c'ᵉ gᵉ
  htpy-map-sequential-colimit-htpy-hom-sequential-diagramᵉ =
    htpy-eqᵉ
      ( apᵉ
        ( map-sequential-colimit-hom-sequential-diagramᵉ up-cᵉ c'ᵉ)
        ( eq-htpy-sequential-diagramᵉ _ _ fᵉ gᵉ Hᵉ))
```

### The identity morphism induces the identity map

```agda
module _
  { l1ᵉ l2ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ} {Xᵉ : UUᵉ l2ᵉ}
  { cᵉ : cocone-sequential-diagramᵉ Aᵉ Xᵉ}
  ( up-cᵉ : universal-property-sequential-colimitᵉ cᵉ)
  where

  htpy-preserves-id-map-sequential-colimit-hom-sequential-diagramᵉ :
    htpy-out-of-sequential-colimitᵉ cᵉ
      ( map-sequential-colimit-hom-sequential-diagramᵉ up-cᵉ cᵉ
        ( id-hom-sequential-diagramᵉ Aᵉ))
      ( idᵉ)
  pr1ᵉ htpy-preserves-id-map-sequential-colimit-hom-sequential-diagramᵉ =
    htpy-htpy-cocone-map-sequential-colimit-hom-sequential-diagramᵉ up-cᵉ cᵉ
      ( id-hom-sequential-diagramᵉ Aᵉ)
  pr2ᵉ htpy-preserves-id-map-sequential-colimit-hom-sequential-diagramᵉ nᵉ =
    ( coherence-htpy-cocone-map-sequential-colimit-hom-sequential-diagramᵉ up-cᵉ cᵉ
      ( id-hom-sequential-diagramᵉ Aᵉ)
      ( nᵉ)) ∙hᵉ
    ( ap-concat-htpyᵉ _
      ( ( right-unit-htpyᵉ) ∙hᵉ
        ( inv-htpyᵉ
          ( left-unit-law-left-whisker-compᵉ
            ( coherence-cocone-sequential-diagramᵉ cᵉ nᵉ)))))

  preserves-id-map-sequential-colimit-hom-sequential-diagramᵉ :
    ( map-sequential-colimit-hom-sequential-diagramᵉ up-cᵉ cᵉ
      ( id-hom-sequential-diagramᵉ Aᵉ)) ~ᵉ
    ( idᵉ)
  preserves-id-map-sequential-colimit-hom-sequential-diagramᵉ =
    htpy-htpy-out-of-sequential-colimitᵉ up-cᵉ
      ( htpy-preserves-id-map-sequential-colimit-hom-sequential-diagramᵉ)
```

### Composition of morphisms induces composition of functions

```agda
module _
  { l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level}
  { Aᵉ : sequential-diagramᵉ l1ᵉ} {Bᵉ : sequential-diagramᵉ l2ᵉ}
  { Cᵉ : sequential-diagramᵉ l3ᵉ}
  { Xᵉ : UUᵉ l4ᵉ} {cᵉ : cocone-sequential-diagramᵉ Aᵉ Xᵉ}
  ( up-cᵉ : universal-property-sequential-colimitᵉ cᵉ)
  { Yᵉ : UUᵉ l5ᵉ} {c'ᵉ : cocone-sequential-diagramᵉ Bᵉ Yᵉ}
  ( up-c'ᵉ : universal-property-sequential-colimitᵉ c'ᵉ)
  { Zᵉ : UUᵉ l6ᵉ} (c''ᵉ : cocone-sequential-diagramᵉ Cᵉ Zᵉ)
  ( gᵉ : hom-sequential-diagramᵉ Bᵉ Cᵉ) (fᵉ : hom-sequential-diagramᵉ Aᵉ Bᵉ)
  where

  htpy-preserves-comp-map-sequential-colimit-hom-sequential-diagramᵉ :
    htpy-out-of-sequential-colimitᵉ cᵉ
      ( map-sequential-colimit-hom-sequential-diagramᵉ up-cᵉ c''ᵉ
        ( comp-hom-sequential-diagramᵉ Aᵉ Bᵉ Cᵉ gᵉ fᵉ))
      ( ( map-sequential-colimit-hom-sequential-diagramᵉ up-c'ᵉ c''ᵉ gᵉ) ∘ᵉ
        ( map-sequential-colimit-hom-sequential-diagramᵉ up-cᵉ c'ᵉ fᵉ))
  pr1ᵉ htpy-preserves-comp-map-sequential-colimit-hom-sequential-diagramᵉ nᵉ =
    ( htpy-htpy-cocone-map-sequential-colimit-hom-sequential-diagramᵉ up-cᵉ c''ᵉ
      ( comp-hom-sequential-diagramᵉ Aᵉ Bᵉ Cᵉ gᵉ fᵉ)
      ( nᵉ)) ∙hᵉ
    ( pasting-vertical-coherence-square-mapsᵉ
      ( map-cocone-sequential-diagramᵉ cᵉ nᵉ)
      ( map-hom-sequential-diagramᵉ Bᵉ fᵉ nᵉ)
      ( map-sequential-colimit-hom-sequential-diagramᵉ up-cᵉ c'ᵉ fᵉ)
      ( map-cocone-sequential-diagramᵉ c'ᵉ nᵉ)
      ( map-hom-sequential-diagramᵉ Cᵉ gᵉ nᵉ)
      ( map-sequential-colimit-hom-sequential-diagramᵉ up-c'ᵉ c''ᵉ gᵉ)
      ( map-cocone-sequential-diagramᵉ c''ᵉ nᵉ)
      ( inv-htpyᵉ
        ( htpy-htpy-cocone-map-sequential-colimit-hom-sequential-diagramᵉ up-cᵉ c'ᵉ
          ( fᵉ)
          ( nᵉ)))
      ( inv-htpyᵉ
        ( htpy-htpy-cocone-map-sequential-colimit-hom-sequential-diagramᵉ up-c'ᵉ
          ( c''ᵉ)
          ( gᵉ)
          ( nᵉ))))
  pr2ᵉ htpy-preserves-comp-map-sequential-colimit-hom-sequential-diagramᵉ nᵉ =
    ( right-whisker-concat-coherence-square-homotopiesᵉ
      ( htpy-htpy-cocone-map-sequential-colimit-hom-sequential-diagramᵉ up-cᵉ c''ᵉ
        ( comp-hom-sequential-diagramᵉ Aᵉ Bᵉ Cᵉ gᵉ fᵉ)
        ( nᵉ))
      ( ( map-sequential-colimit-hom-sequential-diagramᵉ up-cᵉ c''ᵉ
          ( comp-hom-sequential-diagramᵉ Aᵉ Bᵉ Cᵉ gᵉ fᵉ)) ·lᵉ
        ( coherence-cocone-sequential-diagramᵉ cᵉ nᵉ))
      ( coherence-cocone-sequential-diagramᵉ
        ( map-cocone-hom-sequential-diagramᵉ
          ( comp-hom-sequential-diagramᵉ Aᵉ Bᵉ Cᵉ gᵉ fᵉ)
          ( c''ᵉ))
        ( nᵉ))
      ( ( htpy-htpy-cocone-map-sequential-colimit-hom-sequential-diagramᵉ
          ( up-cᵉ)
          ( c''ᵉ)
          ( comp-hom-sequential-diagramᵉ Aᵉ Bᵉ Cᵉ gᵉ fᵉ)
          ( succ-ℕᵉ nᵉ)) ·rᵉ
        ( map-sequential-diagramᵉ Aᵉ nᵉ))
      ( coherence-htpy-cocone-map-sequential-colimit-hom-sequential-diagramᵉ up-cᵉ
        ( c''ᵉ)
        ( comp-hom-sequential-diagramᵉ Aᵉ Bᵉ Cᵉ gᵉ fᵉ)
        ( nᵉ))
      ( _)) ∙hᵉ
    ( ap-concat-htpyᵉ
      ( htpy-htpy-cocone-map-sequential-colimit-hom-sequential-diagramᵉ up-cᵉ c''ᵉ
        ( comp-hom-sequential-diagramᵉ Aᵉ Bᵉ Cᵉ gᵉ fᵉ)
        ( nᵉ))
      ( ( assoc-htpyᵉ
          ( ( coherence-cocone-sequential-diagramᵉ c''ᵉ nᵉ) ·rᵉ
            ( ( map-hom-sequential-diagramᵉ Cᵉ gᵉ nᵉ) ∘ᵉ
              ( map-hom-sequential-diagramᵉ Bᵉ fᵉ nᵉ)))
          ( map-cocone-sequential-diagramᵉ c''ᵉ (succ-ℕᵉ nᵉ) ·lᵉ _)
          ( _)) ∙hᵉ
        ( pasting-vertical-coherence-prism-mapsᵉ
          ( map-cocone-sequential-diagramᵉ cᵉ nᵉ)
          ( map-cocone-sequential-diagramᵉ cᵉ (succ-ℕᵉ nᵉ))
          ( map-sequential-diagramᵉ Aᵉ nᵉ)
          ( map-cocone-sequential-diagramᵉ c'ᵉ nᵉ)
          ( map-cocone-sequential-diagramᵉ c'ᵉ (succ-ℕᵉ nᵉ))
          ( map-sequential-diagramᵉ Bᵉ nᵉ)
          ( map-hom-sequential-diagramᵉ Bᵉ fᵉ nᵉ)
          ( map-hom-sequential-diagramᵉ Bᵉ fᵉ (succ-ℕᵉ nᵉ))
          ( map-sequential-colimit-hom-sequential-diagramᵉ up-cᵉ c'ᵉ fᵉ)
          ( map-cocone-sequential-diagramᵉ c''ᵉ nᵉ)
          ( map-cocone-sequential-diagramᵉ c''ᵉ (succ-ℕᵉ nᵉ))
          ( map-sequential-diagramᵉ Cᵉ nᵉ)
          ( map-hom-sequential-diagramᵉ Cᵉ gᵉ nᵉ)
          ( map-hom-sequential-diagramᵉ Cᵉ gᵉ (succ-ℕᵉ nᵉ))
          ( map-sequential-colimit-hom-sequential-diagramᵉ up-c'ᵉ c''ᵉ gᵉ)
          ( coherence-cocone-sequential-diagramᵉ cᵉ nᵉ)
          ( inv-htpyᵉ
            ( htpy-htpy-cocone-map-sequential-colimit-hom-sequential-diagramᵉ
              ( up-cᵉ)
              ( c'ᵉ)
              ( fᵉ)
              ( nᵉ)))
          ( inv-htpyᵉ
            ( htpy-htpy-cocone-map-sequential-colimit-hom-sequential-diagramᵉ
              ( up-cᵉ)
              ( c'ᵉ)
              ( fᵉ)
              ( succ-ℕᵉ nᵉ)))
          ( naturality-map-hom-sequential-diagramᵉ Bᵉ fᵉ nᵉ)
          ( coherence-cocone-sequential-diagramᵉ c'ᵉ nᵉ)
          ( inv-htpyᵉ
            ( htpy-htpy-cocone-map-sequential-colimit-hom-sequential-diagramᵉ
              ( up-c'ᵉ)
              ( c''ᵉ)
              ( gᵉ)
              ( nᵉ)))
          ( inv-htpyᵉ
            ( htpy-htpy-cocone-map-sequential-colimit-hom-sequential-diagramᵉ
              ( up-c'ᵉ)
              ( c''ᵉ)
              ( gᵉ)
              ( succ-ℕᵉ nᵉ)))
          ( naturality-map-hom-sequential-diagramᵉ Cᵉ gᵉ nᵉ)
          ( coherence-cocone-sequential-diagramᵉ c''ᵉ nᵉ)
          ( prism-htpy-cocone-map-sequential-colimit-hom-sequential-diagramᵉ up-cᵉ
            ( c'ᵉ)
            ( fᵉ)
            ( nᵉ))
          ( prism-htpy-cocone-map-sequential-colimit-hom-sequential-diagramᵉ
            ( up-c'ᵉ)
            ( c''ᵉ)
            ( gᵉ)
            ( nᵉ))))) ∙hᵉ
    ( inv-htpy-assoc-htpyᵉ
      ( htpy-htpy-cocone-map-sequential-colimit-hom-sequential-diagramᵉ up-cᵉ c''ᵉ
        ( comp-hom-sequential-diagramᵉ Aᵉ Bᵉ Cᵉ gᵉ fᵉ)
        ( nᵉ))
      ( _)
      ( ( ( map-sequential-colimit-hom-sequential-diagramᵉ up-c'ᵉ c''ᵉ gᵉ) ∘ᵉ
          ( map-sequential-colimit-hom-sequential-diagramᵉ up-cᵉ c'ᵉ fᵉ)) ·lᵉ
        ( coherence-cocone-sequential-diagramᵉ cᵉ nᵉ)))

  preserves-comp-map-sequential-colimit-hom-sequential-diagramᵉ :
    ( map-sequential-colimit-hom-sequential-diagramᵉ up-cᵉ c''ᵉ
      ( comp-hom-sequential-diagramᵉ Aᵉ Bᵉ Cᵉ gᵉ fᵉ)) ~ᵉ
    ( ( map-sequential-colimit-hom-sequential-diagramᵉ up-c'ᵉ c''ᵉ gᵉ) ∘ᵉ
      ( map-sequential-colimit-hom-sequential-diagramᵉ up-cᵉ c'ᵉ fᵉ))
  preserves-comp-map-sequential-colimit-hom-sequential-diagramᵉ =
    htpy-htpy-out-of-sequential-colimitᵉ up-cᵉ
      ( htpy-preserves-comp-map-sequential-colimit-hom-sequential-diagramᵉ)
```

### A retract of sequential diagrams induces a retract of sequential colimits

Additionally,ᵉ theᵉ underlyingᵉ mapᵉ ofᵉ theᵉ retractionᵉ isᵉ strictlyᵉ equalᵉ to theᵉ mapᵉ
inducedᵉ byᵉ theᵉ retractionᵉ ofᵉ sequentialᵉ diagrams.ᵉ

```agda
module _
  { l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ} {Bᵉ : sequential-diagramᵉ l2ᵉ}
  { Xᵉ : UUᵉ l3ᵉ} {cᵉ : cocone-sequential-diagramᵉ Aᵉ Xᵉ}
  ( up-cᵉ : universal-property-sequential-colimitᵉ cᵉ)
  { Yᵉ : UUᵉ l4ᵉ} {c'ᵉ : cocone-sequential-diagramᵉ Bᵉ Yᵉ}
  ( up-c'ᵉ : universal-property-sequential-colimitᵉ c'ᵉ)
  ( Rᵉ : Aᵉ retract-of-sequential-diagramᵉ Bᵉ)
  where

  map-inclusion-sequential-colimit-retract-sequential-diagramᵉ : Xᵉ → Yᵉ
  map-inclusion-sequential-colimit-retract-sequential-diagramᵉ =
    map-sequential-colimit-hom-sequential-diagramᵉ up-cᵉ c'ᵉ
      ( inclusion-retract-sequential-diagramᵉ Aᵉ Bᵉ Rᵉ)

  map-sequential-colimit-retract-sequential-diagramᵉ : Yᵉ → Xᵉ
  map-sequential-colimit-retract-sequential-diagramᵉ =
    map-sequential-colimit-hom-sequential-diagramᵉ up-c'ᵉ cᵉ
      ( hom-retraction-retract-sequential-diagramᵉ Aᵉ Bᵉ Rᵉ)

  abstract
    is-retraction-map-sequential-colimit-retract-sequential-diagramᵉ :
      is-retractionᵉ
        ( map-inclusion-sequential-colimit-retract-sequential-diagramᵉ)
        ( map-sequential-colimit-retract-sequential-diagramᵉ)
    is-retraction-map-sequential-colimit-retract-sequential-diagramᵉ =
      ( inv-htpyᵉ
        ( preserves-comp-map-sequential-colimit-hom-sequential-diagramᵉ up-cᵉ
          ( up-c'ᵉ)
          ( cᵉ)
          ( hom-retraction-retract-sequential-diagramᵉ Aᵉ Bᵉ Rᵉ)
          ( inclusion-retract-sequential-diagramᵉ Aᵉ Bᵉ Rᵉ))) ∙hᵉ
      ( htpy-map-sequential-colimit-htpy-hom-sequential-diagramᵉ up-cᵉ cᵉ
        ( is-retraction-hom-retraction-retract-sequential-diagramᵉ Aᵉ Bᵉ Rᵉ)) ∙hᵉ
      ( preserves-id-map-sequential-colimit-hom-sequential-diagramᵉ up-cᵉ)

  retraction-sequential-colimit-retract-sequential-diagramᵉ :
    retractionᵉ map-inclusion-sequential-colimit-retract-sequential-diagramᵉ
  pr1ᵉ retraction-sequential-colimit-retract-sequential-diagramᵉ =
    map-sequential-colimit-retract-sequential-diagramᵉ
  pr2ᵉ retraction-sequential-colimit-retract-sequential-diagramᵉ =
    is-retraction-map-sequential-colimit-retract-sequential-diagramᵉ

  retract-sequential-colimit-retract-sequential-diagramᵉ :
    Xᵉ retract-ofᵉ Yᵉ
  pr1ᵉ retract-sequential-colimit-retract-sequential-diagramᵉ =
    map-inclusion-sequential-colimit-retract-sequential-diagramᵉ
  pr2ᵉ retract-sequential-colimit-retract-sequential-diagramᵉ =
    retraction-sequential-colimit-retract-sequential-diagramᵉ
```

### An equivalence of sequential diagrams induces an equivalence of sequential colimits

Additionally,ᵉ theᵉ underlyingᵉ mapᵉ ofᵉ theᵉ inverseᵉ equivalenceᵉ isᵉ definitionallyᵉ
equalᵉ to theᵉ mapᵉ inducedᵉ byᵉ theᵉ inverseᵉ ofᵉ theᵉ equivalenceᵉ ofᵉ sequentialᵉ
diagrams,ᵉ i.e.ᵉ itᵉ isᵉ theᵉ uniqueᵉ mapᵉ `gᵉ : Yᵉ → X`ᵉ makingᵉ theᵉ diagramᵉ

```text
           b₀ᵉ      b₁ᵉ      b₂ᵉ
       B₀ᵉ --->ᵉ B₁ᵉ --->ᵉ B₂ᵉ --->ᵉ ⋯ᵉ --->ᵉ Yᵉ
       |       |       |              |
  e₀⁻¹ᵉ |       | e₁⁻¹ᵉ  | e₂⁻¹ᵉ         | gᵉ
       ∨ᵉ       ∨ᵉ       ∨ᵉ              ∨ᵉ
       A₀ᵉ --->ᵉ A₁ᵉ --->ᵉ A₂ᵉ --->ᵉ ⋯ᵉ --->ᵉ Xᵉ
           a₀ᵉ      a₁ᵉ      a₂ᵉ
```

commute.ᵉ

```agda
module _
  { l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ} {Bᵉ : sequential-diagramᵉ l2ᵉ}
  { Xᵉ : UUᵉ l3ᵉ} {cᵉ : cocone-sequential-diagramᵉ Aᵉ Xᵉ}
  ( up-cᵉ : universal-property-sequential-colimitᵉ cᵉ)
  { Yᵉ : UUᵉ l4ᵉ} {c'ᵉ : cocone-sequential-diagramᵉ Bᵉ Yᵉ}
  ( up-c'ᵉ : universal-property-sequential-colimitᵉ c'ᵉ)
  ( eᵉ : equiv-sequential-diagramᵉ Aᵉ Bᵉ)
  where

  map-equiv-sequential-colimit-equiv-sequential-diagramᵉ : Xᵉ → Yᵉ
  map-equiv-sequential-colimit-equiv-sequential-diagramᵉ =
    map-sequential-colimit-hom-sequential-diagramᵉ up-cᵉ c'ᵉ
      ( hom-equiv-sequential-diagramᵉ Bᵉ eᵉ)

  map-inv-equiv-sequential-colimit-equiv-sequential-diagramᵉ : Yᵉ → Xᵉ
  map-inv-equiv-sequential-colimit-equiv-sequential-diagramᵉ =
    map-sequential-colimit-hom-sequential-diagramᵉ up-c'ᵉ cᵉ
      ( hom-inv-equiv-sequential-diagramᵉ Bᵉ eᵉ)

  abstract
    is-section-map-inv-equiv-sequential-colimit-equiv-sequential-diagramᵉ :
      is-sectionᵉ
        ( map-equiv-sequential-colimit-equiv-sequential-diagramᵉ)
        ( map-inv-equiv-sequential-colimit-equiv-sequential-diagramᵉ)
    is-section-map-inv-equiv-sequential-colimit-equiv-sequential-diagramᵉ =
      ( inv-htpyᵉ
        ( preserves-comp-map-sequential-colimit-hom-sequential-diagramᵉ up-c'ᵉ
          ( up-cᵉ)
          ( c'ᵉ)
          ( hom-equiv-sequential-diagramᵉ Bᵉ eᵉ)
          ( hom-inv-equiv-sequential-diagramᵉ Bᵉ eᵉ))) ∙hᵉ
      ( htpy-map-sequential-colimit-htpy-hom-sequential-diagramᵉ up-c'ᵉ c'ᵉ
        ( is-section-inv-equiv-sequential-diagramᵉ _ eᵉ)) ∙hᵉ
      ( preserves-id-map-sequential-colimit-hom-sequential-diagramᵉ up-c'ᵉ)

    is-retraction-map-inv-equiv-sequential-colimit-equiv-sequential-diagramᵉ :
      is-retractionᵉ
        ( map-equiv-sequential-colimit-equiv-sequential-diagramᵉ)
        ( map-inv-equiv-sequential-colimit-equiv-sequential-diagramᵉ)
    is-retraction-map-inv-equiv-sequential-colimit-equiv-sequential-diagramᵉ =
      is-retraction-map-sequential-colimit-retract-sequential-diagramᵉ up-cᵉ up-c'ᵉ
        ( retract-equiv-sequential-diagramᵉ eᵉ)

  is-equiv-map-equiv-sequential-colimit-equiv-sequential-diagramᵉ :
    is-equivᵉ map-equiv-sequential-colimit-equiv-sequential-diagramᵉ
  is-equiv-map-equiv-sequential-colimit-equiv-sequential-diagramᵉ =
    is-equiv-is-invertibleᵉ
      ( map-inv-equiv-sequential-colimit-equiv-sequential-diagramᵉ)
      ( is-section-map-inv-equiv-sequential-colimit-equiv-sequential-diagramᵉ)
      ( is-retraction-map-inv-equiv-sequential-colimit-equiv-sequential-diagramᵉ)

  equiv-sequential-colimit-equiv-sequential-diagramᵉ : Xᵉ ≃ᵉ Yᵉ
  pr1ᵉ equiv-sequential-colimit-equiv-sequential-diagramᵉ =
    map-equiv-sequential-colimit-equiv-sequential-diagramᵉ
  pr2ᵉ equiv-sequential-colimit-equiv-sequential-diagramᵉ =
    is-equiv-map-equiv-sequential-colimit-equiv-sequential-diagramᵉ
```

### Functoriality of taking the standard sequential colimit

Allᵉ ofᵉ theᵉ aboveᵉ specializesᵉ to theᵉ caseᵉ where `X`ᵉ isᵉ theᵉ standardᵉ sequentialᵉ
colimitᵉ `A∞`ᵉ andᵉ `Y`ᵉ isᵉ theᵉ standardᵉ sequentialᵉ colimitᵉ `B∞`.ᵉ Inᵉ thatᵉ case,ᵉ weᵉ
denoteᵉ theᵉ uniqueᵉ mapᵉ `g`ᵉ correspondingᵉ to aᵉ morphismᵉ ofᵉ diagramsᵉ `f`ᵉ byᵉ
`f∞ᵉ : A∞ᵉ → B∞`.ᵉ

#### A morphism of sequential diagrams induces a map of standard sequential colimits

```agda
module _
  { l1ᵉ l2ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ} (Bᵉ : sequential-diagramᵉ l2ᵉ)
  ( fᵉ : hom-sequential-diagramᵉ Aᵉ Bᵉ)
  where

  map-hom-standard-sequential-colimitᵉ :
    standard-sequential-colimitᵉ Aᵉ → standard-sequential-colimitᵉ Bᵉ
  map-hom-standard-sequential-colimitᵉ =
    map-sequential-colimit-hom-sequential-diagramᵉ
      ( up-standard-sequential-colimitᵉ)
      ( cocone-standard-sequential-colimitᵉ Bᵉ)
      ( fᵉ)

  htpy-cocone-map-hom-standard-sequential-colimitᵉ :
    htpy-cocone-sequential-diagramᵉ
      ( cocone-map-sequential-diagramᵉ
        ( cocone-standard-sequential-colimitᵉ Aᵉ)
        ( map-hom-standard-sequential-colimitᵉ))
      ( map-cocone-hom-sequential-diagramᵉ fᵉ
        ( cocone-standard-sequential-colimitᵉ Bᵉ))
  htpy-cocone-map-hom-standard-sequential-colimitᵉ =
    htpy-cocone-map-sequential-colimit-hom-sequential-diagramᵉ
      ( up-standard-sequential-colimitᵉ)
      ( cocone-standard-sequential-colimitᵉ Bᵉ)
      ( fᵉ)

  htpy-htpy-cocone-map-hom-standard-sequential-colimitᵉ :
    ( nᵉ : ℕᵉ) →
    coherence-square-mapsᵉ
      ( map-hom-sequential-diagramᵉ Bᵉ fᵉ nᵉ)
      ( map-cocone-standard-sequential-colimitᵉ nᵉ)
      ( map-cocone-standard-sequential-colimitᵉ nᵉ)
      ( map-hom-standard-sequential-colimitᵉ)
  htpy-htpy-cocone-map-hom-standard-sequential-colimitᵉ =
    htpy-htpy-cocone-map-sequential-colimit-hom-sequential-diagramᵉ
      ( up-standard-sequential-colimitᵉ)
      ( cocone-standard-sequential-colimitᵉ Bᵉ)
      ( fᵉ)

  coherence-htpy-cocone-map-hom-standard-sequential-colimitᵉ :
    ( nᵉ : ℕᵉ) →
    coherence-square-homotopiesᵉ
      ( htpy-htpy-cocone-map-hom-standard-sequential-colimitᵉ nᵉ)
      ( ( map-hom-standard-sequential-colimitᵉ) ·lᵉ
        ( coherence-cocone-standard-sequential-colimitᵉ nᵉ))
      ( coherence-cocone-sequential-diagramᵉ
          ( map-cocone-hom-sequential-diagramᵉ fᵉ
            ( cocone-standard-sequential-colimitᵉ Bᵉ))
          ( nᵉ))
      ( ( htpy-htpy-cocone-map-hom-standard-sequential-colimitᵉ (succ-ℕᵉ nᵉ)) ·rᵉ
        ( map-sequential-diagramᵉ Aᵉ nᵉ))
  coherence-htpy-cocone-map-hom-standard-sequential-colimitᵉ =
    coherence-htpy-cocone-map-sequential-colimit-hom-sequential-diagramᵉ
      ( up-standard-sequential-colimitᵉ)
      ( cocone-standard-sequential-colimitᵉ Bᵉ)
      ( fᵉ)

  prism-htpy-cocone-map-hom-standard-sequential-colimitᵉ :
    ( nᵉ : ℕᵉ) →
    vertical-coherence-prism-mapsᵉ
      ( map-cocone-standard-sequential-colimitᵉ nᵉ)
      ( map-cocone-standard-sequential-colimitᵉ (succ-ℕᵉ nᵉ))
      ( map-sequential-diagramᵉ Aᵉ nᵉ)
      ( map-cocone-standard-sequential-colimitᵉ nᵉ)
      ( map-cocone-standard-sequential-colimitᵉ (succ-ℕᵉ nᵉ))
      ( map-sequential-diagramᵉ Bᵉ nᵉ)
      ( map-hom-sequential-diagramᵉ Bᵉ fᵉ nᵉ)
      ( map-hom-sequential-diagramᵉ Bᵉ fᵉ (succ-ℕᵉ nᵉ))
      ( map-hom-standard-sequential-colimitᵉ)
      ( coherence-cocone-standard-sequential-colimitᵉ nᵉ)
      ( inv-htpyᵉ (htpy-htpy-cocone-map-hom-standard-sequential-colimitᵉ nᵉ))
      ( inv-htpyᵉ
        ( htpy-htpy-cocone-map-hom-standard-sequential-colimitᵉ (succ-ℕᵉ nᵉ)))
      ( naturality-map-hom-sequential-diagramᵉ Bᵉ fᵉ nᵉ)
      ( coherence-cocone-standard-sequential-colimitᵉ nᵉ)
  prism-htpy-cocone-map-hom-standard-sequential-colimitᵉ =
    prism-htpy-cocone-map-sequential-colimit-hom-sequential-diagramᵉ
      ( up-standard-sequential-colimitᵉ)
      ( cocone-standard-sequential-colimitᵉ Bᵉ)
      ( fᵉ)
```

#### Homotopies between morphisms of sequential diagrams induce homotopies of maps of standard sequential colimits

```agda
module _
  { l1ᵉ l2ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ} {Bᵉ : sequential-diagramᵉ l2ᵉ}
  { fᵉ gᵉ : hom-sequential-diagramᵉ Aᵉ Bᵉ} (Hᵉ : htpy-hom-sequential-diagramᵉ Bᵉ fᵉ gᵉ)
  where

  htpy-map-hom-standard-sequential-colimit-htpy-hom-sequential-diagramᵉ :
    map-hom-standard-sequential-colimitᵉ Bᵉ fᵉ ~ᵉ
    map-hom-standard-sequential-colimitᵉ Bᵉ gᵉ
  htpy-map-hom-standard-sequential-colimit-htpy-hom-sequential-diagramᵉ =
    htpy-map-sequential-colimit-htpy-hom-sequential-diagramᵉ
      ( up-standard-sequential-colimitᵉ)
      ( cocone-standard-sequential-colimitᵉ Bᵉ)
      ( Hᵉ)
```

#### The identity morphism induces the identity map on the standard sequential colimit

Weᵉ haveᵉ `id∞ᵉ ~ᵉ idᵉ : A∞ᵉ → A∞`.ᵉ

```agda
module _
  { l1ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ}
  where

  preserves-id-map-hom-standard-sequential-colimitᵉ :
    ( map-hom-standard-sequential-colimitᵉ Aᵉ
      ( id-hom-sequential-diagramᵉ Aᵉ)) ~ᵉ
    ( idᵉ)
  preserves-id-map-hom-standard-sequential-colimitᵉ =
    preserves-id-map-sequential-colimit-hom-sequential-diagramᵉ
      ( up-standard-sequential-colimitᵉ)
```

#### Forming standard sequential colimits preserves composition of morphisms of sequential diagrams

Weᵉ haveᵉ `(fᵉ ∘ᵉ g)∞ᵉ ~ᵉ (f∞ᵉ ∘ᵉ g∞ᵉ) : A∞ᵉ → C∞`.ᵉ

```agda
module _
  { l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ} {Bᵉ : sequential-diagramᵉ l2ᵉ}
  { Cᵉ : sequential-diagramᵉ l3ᵉ}
  ( gᵉ : hom-sequential-diagramᵉ Bᵉ Cᵉ) (fᵉ : hom-sequential-diagramᵉ Aᵉ Bᵉ)
  where

  preserves-comp-map-hom-standard-sequential-colimitᵉ :
    ( map-hom-standard-sequential-colimitᵉ Cᵉ
      ( comp-hom-sequential-diagramᵉ Aᵉ Bᵉ Cᵉ gᵉ fᵉ)) ~ᵉ
    ( ( map-hom-standard-sequential-colimitᵉ Cᵉ gᵉ) ∘ᵉ
      ( map-hom-standard-sequential-colimitᵉ Bᵉ fᵉ))
  preserves-comp-map-hom-standard-sequential-colimitᵉ =
    preserves-comp-map-sequential-colimit-hom-sequential-diagramᵉ
      ( up-standard-sequential-colimitᵉ)
      ( up-standard-sequential-colimitᵉ)
      ( cocone-standard-sequential-colimitᵉ Cᵉ)
      ( gᵉ)
      ( fᵉ)
```

#### An equivalence of sequential diagrams induces an equivalence of standard sequential colimits

Additionally,ᵉ theᵉ underlyingᵉ mapᵉ ofᵉ theᵉ inverseᵉ equivalenceᵉ isᵉ definitionallyᵉ
equalᵉ to theᵉ mapᵉ inducedᵉ byᵉ theᵉ inverseᵉ ofᵉ theᵉ equivalenceᵉ ofᵉ sequentialᵉ
diagrams,ᵉ i.e.ᵉ `(e∞)⁻¹ᵉ = (e⁻¹)∞`.ᵉ

```agda
module _
  { l1ᵉ l2ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ} {Bᵉ : sequential-diagramᵉ l2ᵉ}
  ( eᵉ : equiv-sequential-diagramᵉ Aᵉ Bᵉ)
  where

  map-equiv-standard-sequential-colimitᵉ :
    standard-sequential-colimitᵉ Aᵉ → standard-sequential-colimitᵉ Bᵉ
  map-equiv-standard-sequential-colimitᵉ =
    map-equiv-sequential-colimit-equiv-sequential-diagramᵉ
      ( up-standard-sequential-colimitᵉ)
      ( up-standard-sequential-colimitᵉ)
      ( eᵉ)

  map-inv-equiv-standard-sequential-colimitᵉ :
    standard-sequential-colimitᵉ Bᵉ → standard-sequential-colimitᵉ Aᵉ
  map-inv-equiv-standard-sequential-colimitᵉ =
    map-inv-equiv-sequential-colimit-equiv-sequential-diagramᵉ
      ( up-standard-sequential-colimitᵉ)
      ( up-standard-sequential-colimitᵉ)
      ( eᵉ)

  equiv-equiv-standard-sequential-colimitᵉ :
    standard-sequential-colimitᵉ Aᵉ ≃ᵉ standard-sequential-colimitᵉ Bᵉ
  equiv-equiv-standard-sequential-colimitᵉ =
    equiv-sequential-colimit-equiv-sequential-diagramᵉ
      ( up-standard-sequential-colimitᵉ)
      ( up-standard-sequential-colimitᵉ)
      ( eᵉ)
```

#### A retract of sequential diagrams induces a retract of standard sequential colimits

Additionally,ᵉ theᵉ underlyingᵉ mapᵉ ofᵉ theᵉ retractionᵉ isᵉ definitionallyᵉ equalᵉ to
theᵉ mapᵉ inducedᵉ byᵉ theᵉ retractionᵉ ofᵉ sequentialᵉ diagrams.ᵉ

```agda
module _
  { l1ᵉ l2ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ} {Bᵉ : sequential-diagramᵉ l2ᵉ}
  ( Rᵉ : Aᵉ retract-of-sequential-diagramᵉ Bᵉ)
  where

  map-inclusion-retract-standard-sequential-colimitᵉ :
    standard-sequential-colimitᵉ Aᵉ → standard-sequential-colimitᵉ Bᵉ
  map-inclusion-retract-standard-sequential-colimitᵉ =
    map-hom-standard-sequential-colimitᵉ Bᵉ
      ( inclusion-retract-sequential-diagramᵉ Aᵉ Bᵉ Rᵉ)

  map-hom-retraction-retract-standard-sequential-colimitᵉ :
    standard-sequential-colimitᵉ Bᵉ → standard-sequential-colimitᵉ Aᵉ
  map-hom-retraction-retract-standard-sequential-colimitᵉ =
    map-hom-standard-sequential-colimitᵉ Aᵉ
      ( hom-retraction-retract-sequential-diagramᵉ Aᵉ Bᵉ Rᵉ)

  retract-retract-standard-sequential-colimitᵉ :
    (standard-sequential-colimitᵉ Aᵉ) retract-ofᵉ (standard-sequential-colimitᵉ Bᵉ)
  retract-retract-standard-sequential-colimitᵉ =
    retract-sequential-colimit-retract-sequential-diagramᵉ
      ( up-standard-sequential-colimitᵉ)
      ( up-standard-sequential-colimitᵉ)
      ( Rᵉ)
```

## References

{{#bibliographyᵉ}} {{#referenceᵉ SvDR20ᵉ}}