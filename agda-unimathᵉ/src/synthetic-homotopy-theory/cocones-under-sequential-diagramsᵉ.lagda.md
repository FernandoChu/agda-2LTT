# Cocones under sequential diagrams

```agda
module synthetic-homotopy-theory.cocones-under-sequential-diagramsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.binary-homotopiesᵉ
open import foundation.commuting-squares-of-homotopiesᵉ
open import foundation.commuting-triangles-of-mapsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.postcomposition-functionsᵉ
open import foundation.structure-identity-principleᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ

open import synthetic-homotopy-theory.dependent-sequential-diagramsᵉ
open import synthetic-homotopy-theory.equifibered-sequential-diagramsᵉ
open import synthetic-homotopy-theory.sequential-diagramsᵉ
```

</details>

## Idea

Aᵉ
{{#conceptᵉ "cocone"ᵉ Disambiguation="sequentialᵉ diagram"ᵉ Agda=cocone-sequential-diagramᵉ}}
underᵉ aᵉ [sequentialᵉ diagram](synthetic-homotopy-theory.sequential-diagrams.mdᵉ)
`(A,ᵉ a)`ᵉ with codomainᵉ `Xᵉ : 𝒰`ᵉ consistsᵉ ofᵉ aᵉ familyᵉ ofᵉ mapsᵉ `iₙᵉ : Aᵉ nᵉ → C`ᵉ andᵉ aᵉ
familyᵉ ofᵉ [homotopies](foundation.homotopies.mdᵉ) `Hₙ`ᵉ assertingᵉ thatᵉ theᵉ
trianglesᵉ

```text
       aₙᵉ
 Aₙᵉ ------>ᵉ Aₙ₊₁ᵉ
   \ᵉ       /ᵉ
    \ᵉ     /ᵉ
  iₙᵉ \ᵉ   /ᵉ iₙ₊₁ᵉ
      ∨ᵉ ∨ᵉ
       Xᵉ
```

[commute](foundation.commuting-triangles-of-maps.md).ᵉ

## Definitions

### Cocones under sequential diagrams

```agda
module _
  { l1ᵉ l2ᵉ : Level} (Aᵉ : sequential-diagramᵉ l1ᵉ) (Xᵉ : UUᵉ l2ᵉ)
  where

  cocone-sequential-diagramᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  cocone-sequential-diagramᵉ =
    Σᵉ ( ( nᵉ : ℕᵉ) → family-sequential-diagramᵉ Aᵉ nᵉ → Xᵉ)
      ( λ iᵉ →
        ( nᵉ : ℕᵉ) →
        coherence-triangle-mapsᵉ
          ( iᵉ nᵉ)
          ( iᵉ (succ-ℕᵉ nᵉ))
          ( map-sequential-diagramᵉ Aᵉ nᵉ))
```

### Components of cocones under sequential diagrams

```agda
module _
  { l1ᵉ l2ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ} {Xᵉ : UUᵉ l2ᵉ}
  ( cᵉ : cocone-sequential-diagramᵉ Aᵉ Xᵉ)
  where

  map-cocone-sequential-diagramᵉ : (nᵉ : ℕᵉ) → family-sequential-diagramᵉ Aᵉ nᵉ → Xᵉ
  map-cocone-sequential-diagramᵉ = pr1ᵉ cᵉ

  coherence-cocone-sequential-diagramᵉ :
    ( nᵉ : ℕᵉ) →
    coherence-triangle-mapsᵉ
      ( map-cocone-sequential-diagramᵉ nᵉ)
      ( map-cocone-sequential-diagramᵉ (succ-ℕᵉ nᵉ))
      ( map-sequential-diagramᵉ Aᵉ nᵉ)
  coherence-cocone-sequential-diagramᵉ = pr2ᵉ cᵉ

  first-map-cocone-sequential-diagramᵉ : family-sequential-diagramᵉ Aᵉ 0 → Xᵉ
  first-map-cocone-sequential-diagramᵉ = map-cocone-sequential-diagramᵉ 0
```

### Homotopies of cocones under a sequential diagram

Aᵉ **homotopy**ᵉ betweenᵉ twoᵉ coconesᵉ `(X,ᵉ i,ᵉ H)`ᵉ andᵉ `(X,ᵉ j,ᵉ L)`ᵉ with theᵉ sameᵉ
vertexᵉ consistsᵉ ofᵉ aᵉ [sequence](foundation.dependent-sequences.mdᵉ) ofᵉ
[homotopies](foundation.homotopies.mdᵉ) `Kₙᵉ : iₙᵉ ~ᵉ jₙ`ᵉ andᵉ aᵉ coherenceᵉ datumᵉ
fillingᵉ theᵉ "pinchedᵉ cylinder"ᵉ with theᵉ facesᵉ `Kₙ`,ᵉ `Hₙ`,ᵉ `Lₙ`ᵉ andᵉ `Kₙ₊₁`.ᵉ

Theᵉ coherenceᵉ datumᵉ mayᵉ beᵉ betterᵉ understoodᵉ byᵉ viewingᵉ aᵉ coconeᵉ asᵉ aᵉ
[morphism](synthetic-homotopy-theory.morphisms-sequential-diagrams.mdᵉ) fromᵉ
`(A,ᵉ a)`ᵉ to theᵉ constantᵉ coconeᵉ `(nᵉ ↦ᵉ X,ᵉ nᵉ ↦ᵉ id)`ᵉ —ᵉ theᵉ twoᵉ typesᵉ areᵉ strictlyᵉ
equal.ᵉ Thenᵉ aᵉ homotopyᵉ ofᵉ coconesᵉ isᵉ aᵉ regularᵉ homotopyᵉ ofᵉ morphismsᵉ ofᵉ
sequentialᵉ diagrams.ᵉ

```agda
module _
  { l1ᵉ l2ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ} {Xᵉ : UUᵉ l2ᵉ}
  ( cᵉ c'ᵉ : cocone-sequential-diagramᵉ Aᵉ Xᵉ)
  where

  coherence-htpy-cocone-sequential-diagramᵉ :
    ( (nᵉ : ℕᵉ) →
      map-cocone-sequential-diagramᵉ cᵉ nᵉ ~ᵉ map-cocone-sequential-diagramᵉ c'ᵉ nᵉ) →
    UUᵉ (l1ᵉ ⊔ l2ᵉ)
  coherence-htpy-cocone-sequential-diagramᵉ Kᵉ =
    ( nᵉ : ℕᵉ) →
    coherence-square-homotopiesᵉ
      ( Kᵉ nᵉ)
      ( coherence-cocone-sequential-diagramᵉ cᵉ nᵉ)
      ( coherence-cocone-sequential-diagramᵉ c'ᵉ nᵉ)
      ( Kᵉ (succ-ℕᵉ nᵉ) ·rᵉ map-sequential-diagramᵉ Aᵉ nᵉ)

  htpy-cocone-sequential-diagramᵉ :
    UUᵉ (l1ᵉ ⊔ l2ᵉ)
  htpy-cocone-sequential-diagramᵉ =
    Σᵉ ( ( nᵉ : ℕᵉ) →
        ( map-cocone-sequential-diagramᵉ cᵉ nᵉ) ~ᵉ
        ( map-cocone-sequential-diagramᵉ c'ᵉ nᵉ))
      ( coherence-htpy-cocone-sequential-diagramᵉ)
```

### Components of a homotopy of cocones under a sequential diagram

```agda
module _
  { l1ᵉ l2ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ} {Xᵉ : UUᵉ l2ᵉ}
  { cᵉ c'ᵉ : cocone-sequential-diagramᵉ Aᵉ Xᵉ}
  ( Hᵉ : htpy-cocone-sequential-diagramᵉ cᵉ c'ᵉ)
  where

  htpy-htpy-cocone-sequential-diagramᵉ :
    ( nᵉ : ℕᵉ) →
    ( map-cocone-sequential-diagramᵉ cᵉ nᵉ) ~ᵉ
    ( map-cocone-sequential-diagramᵉ c'ᵉ nᵉ)
  htpy-htpy-cocone-sequential-diagramᵉ = pr1ᵉ Hᵉ

  coherence-htpy-htpy-cocone-sequential-diagramᵉ :
    coherence-htpy-cocone-sequential-diagramᵉ cᵉ c'ᵉ
      ( htpy-htpy-cocone-sequential-diagramᵉ)
  coherence-htpy-htpy-cocone-sequential-diagramᵉ = pr2ᵉ Hᵉ
```

### Inverting homotopies of cocones under sequential diagrams

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ} {Xᵉ : UUᵉ l2ᵉ}
  {cᵉ c'ᵉ : cocone-sequential-diagramᵉ Aᵉ Xᵉ}
  (Hᵉ : htpy-cocone-sequential-diagramᵉ cᵉ c'ᵉ)
  where

  inv-htpy-cocone-sequential-diagramᵉ : htpy-cocone-sequential-diagramᵉ c'ᵉ cᵉ
  pr1ᵉ inv-htpy-cocone-sequential-diagramᵉ nᵉ =
    inv-htpyᵉ (htpy-htpy-cocone-sequential-diagramᵉ Hᵉ nᵉ)
  pr2ᵉ inv-htpy-cocone-sequential-diagramᵉ nᵉ =
    horizontal-inv-coherence-square-homotopiesᵉ
      ( htpy-htpy-cocone-sequential-diagramᵉ Hᵉ nᵉ)
      ( coherence-cocone-sequential-diagramᵉ cᵉ nᵉ)
      ( coherence-cocone-sequential-diagramᵉ c'ᵉ nᵉ)
      ( ( htpy-htpy-cocone-sequential-diagramᵉ Hᵉ (succ-ℕᵉ nᵉ)) ·rᵉ
        ( map-sequential-diagramᵉ Aᵉ nᵉ))
      ( coherence-htpy-htpy-cocone-sequential-diagramᵉ Hᵉ nᵉ)
```

### Concatenation of homotopies of cocones under a sequential diagram

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ} {Xᵉ : UUᵉ l2ᵉ}
  {cᵉ c'ᵉ c''ᵉ : cocone-sequential-diagramᵉ Aᵉ Xᵉ}
  (Hᵉ : htpy-cocone-sequential-diagramᵉ cᵉ c'ᵉ)
  (Kᵉ : htpy-cocone-sequential-diagramᵉ c'ᵉ c''ᵉ)
  where

  concat-htpy-cocone-sequential-diagramᵉ : htpy-cocone-sequential-diagramᵉ cᵉ c''ᵉ
  pr1ᵉ concat-htpy-cocone-sequential-diagramᵉ nᵉ =
    ( htpy-htpy-cocone-sequential-diagramᵉ Hᵉ nᵉ) ∙hᵉ
    ( htpy-htpy-cocone-sequential-diagramᵉ Kᵉ nᵉ)
  pr2ᵉ concat-htpy-cocone-sequential-diagramᵉ nᵉ =
    horizontal-pasting-coherence-square-homotopiesᵉ
      ( htpy-htpy-cocone-sequential-diagramᵉ Hᵉ nᵉ)
      ( htpy-htpy-cocone-sequential-diagramᵉ Kᵉ nᵉ)
      ( coherence-cocone-sequential-diagramᵉ cᵉ nᵉ)
      ( coherence-cocone-sequential-diagramᵉ c'ᵉ nᵉ)
      ( coherence-cocone-sequential-diagramᵉ c''ᵉ nᵉ)
      ( ( htpy-htpy-cocone-sequential-diagramᵉ Hᵉ (succ-ℕᵉ nᵉ)) ·rᵉ
        ( map-sequential-diagramᵉ Aᵉ nᵉ))
      ( ( htpy-htpy-cocone-sequential-diagramᵉ Kᵉ (succ-ℕᵉ nᵉ)) ·rᵉ
        ( map-sequential-diagramᵉ Aᵉ nᵉ))
      ( coherence-htpy-htpy-cocone-sequential-diagramᵉ Hᵉ nᵉ)
      ( coherence-htpy-htpy-cocone-sequential-diagramᵉ Kᵉ nᵉ)
```

### Postcomposing cocones under a sequential diagram with a map

Givenᵉ aᵉ coconeᵉ `c`ᵉ with vertexᵉ `X`ᵉ underᵉ `(A,ᵉ a)`ᵉ andᵉ aᵉ mapᵉ `fᵉ : Xᵉ → Y`,ᵉ weᵉ mayᵉ
extendᵉ `c`ᵉ to aᵉ coconeᵉ with vertexᵉ `Y`.ᵉ

```agda
module _
  { l1ᵉ l2ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ} {Xᵉ : UUᵉ l2ᵉ}
  ( cᵉ : cocone-sequential-diagramᵉ Aᵉ Xᵉ)
  where

  cocone-map-sequential-diagramᵉ :
    { lᵉ : Level} {Yᵉ : UUᵉ lᵉ} →
    ( Xᵉ → Yᵉ) → cocone-sequential-diagramᵉ Aᵉ Yᵉ
  pr1ᵉ (cocone-map-sequential-diagramᵉ fᵉ) nᵉ =
    fᵉ ∘ᵉ map-cocone-sequential-diagramᵉ cᵉ nᵉ
  pr2ᵉ (cocone-map-sequential-diagramᵉ fᵉ) nᵉ =
    fᵉ ·lᵉ (coherence-cocone-sequential-diagramᵉ cᵉ nᵉ)
```

### Postcomposition cocones under postcomposition sequential diagrams

```agda
module _
  { l1ᵉ l2ᵉ l3ᵉ : Level} (Xᵉ : UUᵉ l1ᵉ) (Aᵉ : sequential-diagramᵉ l2ᵉ) {Yᵉ : UUᵉ l3ᵉ}
  ( cᵉ : cocone-sequential-diagramᵉ Aᵉ Yᵉ)
  where

  cocone-postcomp-sequential-diagramᵉ :
    cocone-sequential-diagramᵉ (postcomp-sequential-diagramᵉ Xᵉ Aᵉ) (Xᵉ → Yᵉ)
  pr1ᵉ cocone-postcomp-sequential-diagramᵉ nᵉ gᵉ xᵉ =
    map-cocone-sequential-diagramᵉ cᵉ nᵉ (gᵉ xᵉ)
  pr2ᵉ cocone-postcomp-sequential-diagramᵉ nᵉ gᵉ =
    htpy-postcompᵉ Xᵉ (coherence-cocone-sequential-diagramᵉ cᵉ nᵉ) gᵉ
```

### Equifibered sequential diagrams induced by type families over cocones under sequential diagrams

Givenᵉ aᵉ sequentialᵉ diagramᵉ `(A,ᵉ a)`ᵉ andᵉ aᵉ coconeᵉ `c`ᵉ underᵉ itᵉ with vertexᵉ `X`,ᵉ
andᵉ aᵉ typeᵉ familyᵉ `Pᵉ : Xᵉ → 𝒰`,ᵉ weᵉ mayᵉ composeᵉ themᵉ togetherᵉ to getᵉ

```text
       aₙᵉ
 Aₙᵉ ------>ᵉ Aₙ₊₁ᵉ
   \ᵉ       /ᵉ
    \ᵉ  Hₙᵉ /ᵉ
  iₙᵉ \ᵉ   /ᵉ iₙ₊₁ᵉ
      ∨ᵉ ∨ᵉ
       Xᵉ
       | Pᵉ
       ∨ᵉ
       𝒰ᵉ ,ᵉ
```

whichᵉ givesᵉ usᵉ aᵉ collectionᵉ ofᵉ typeᵉ familiesᵉ `Pₙᵉ : Aₙᵉ → 𝒰`,ᵉ andᵉ aᵉ collectionᵉ ofᵉ
equivalencesᵉ `Pₙᵉ aᵉ ≃ᵉ Pₙ₊₁ᵉ (aₙᵉ a)`ᵉ inducedᵉ byᵉ
[transporting](foundation-core.transport-along-identifications.mdᵉ) in `P`ᵉ alongᵉ
`Hₙ`.ᵉ Thisᵉ data comesᵉ togetherᵉ to formᵉ anᵉ
[equifiberedᵉ sequentialᵉ diagram](synthetic-homotopy-theory.equifibered-sequential-diagrams.mdᵉ)
overᵉ `A`.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ}
  {Xᵉ : UUᵉ l2ᵉ} (cᵉ : cocone-sequential-diagramᵉ Aᵉ Xᵉ)
  (Pᵉ : Xᵉ → UUᵉ l3ᵉ)
  where

  equifibered-sequential-diagram-family-coconeᵉ :
    equifibered-sequential-diagramᵉ Aᵉ l3ᵉ
  pr1ᵉ equifibered-sequential-diagram-family-coconeᵉ nᵉ aᵉ =
    Pᵉ (map-cocone-sequential-diagramᵉ cᵉ nᵉ aᵉ)
  pr2ᵉ equifibered-sequential-diagram-family-coconeᵉ nᵉ aᵉ =
    equiv-trᵉ Pᵉ (coherence-cocone-sequential-diagramᵉ cᵉ nᵉ aᵉ)

  dependent-sequential-diagram-family-coconeᵉ : dependent-sequential-diagramᵉ Aᵉ l3ᵉ
  dependent-sequential-diagram-family-coconeᵉ =
    dependent-sequential-diagram-equifibered-sequential-diagramᵉ
      ( equifibered-sequential-diagram-family-coconeᵉ)

  is-equifibered-dependent-sequential-diagram-family-coconeᵉ :
    is-equifibered-dependent-sequential-diagramᵉ
      ( dependent-sequential-diagram-family-coconeᵉ)
  is-equifibered-dependent-sequential-diagram-family-coconeᵉ =
    is-equifibered-dependent-sequential-diagram-equifibered-sequential-diagramᵉ
      ( equifibered-sequential-diagram-family-coconeᵉ)
```

## Properties

### Characterization of identity types of cocones under sequential diagrams

[Equality](foundation.identity-types.mdᵉ) ofᵉ coconesᵉ with theᵉ sameᵉ vertexᵉ isᵉ
capturedᵉ byᵉ aᵉ homotopyᵉ betweenᵉ them.ᵉ

```agda
module _
  { l1ᵉ l2ᵉ : Level} (Aᵉ : sequential-diagramᵉ l1ᵉ) {Xᵉ : UUᵉ l2ᵉ}
  ( cᵉ : cocone-sequential-diagramᵉ Aᵉ Xᵉ)
  where

  refl-htpy-cocone-sequential-diagramᵉ :
    htpy-cocone-sequential-diagramᵉ cᵉ cᵉ
  pr1ᵉ refl-htpy-cocone-sequential-diagramᵉ nᵉ = refl-htpyᵉ
  pr2ᵉ refl-htpy-cocone-sequential-diagramᵉ nᵉ = right-unit-htpyᵉ

  htpy-eq-cocone-sequential-diagramᵉ :
    ( c'ᵉ : cocone-sequential-diagramᵉ Aᵉ Xᵉ) → ( cᵉ ＝ᵉ c'ᵉ) →
    htpy-cocone-sequential-diagramᵉ cᵉ c'ᵉ
  htpy-eq-cocone-sequential-diagramᵉ .cᵉ reflᵉ =
    refl-htpy-cocone-sequential-diagramᵉ

  abstract
    is-torsorial-htpy-cocone-sequential-diagramᵉ :
      is-torsorialᵉ (htpy-cocone-sequential-diagramᵉ cᵉ)
    is-torsorial-htpy-cocone-sequential-diagramᵉ =
      is-torsorial-Eq-structureᵉ
        ( is-torsorial-binary-htpyᵉ (map-cocone-sequential-diagramᵉ cᵉ))
        ( ( map-cocone-sequential-diagramᵉ cᵉ) ,ᵉ
          ( ev-pairᵉ refl-htpyᵉ))
        ( is-torsorial-binary-htpyᵉ
          ( λ nᵉ → coherence-cocone-sequential-diagramᵉ cᵉ nᵉ ∙hᵉ refl-htpyᵉ))

    is-equiv-htpy-eq-cocone-sequential-diagramᵉ :
      ( c'ᵉ : cocone-sequential-diagramᵉ Aᵉ Xᵉ) →
      is-equivᵉ (htpy-eq-cocone-sequential-diagramᵉ c'ᵉ)
    is-equiv-htpy-eq-cocone-sequential-diagramᵉ =
      fundamental-theorem-idᵉ
        ( is-torsorial-htpy-cocone-sequential-diagramᵉ)
        ( htpy-eq-cocone-sequential-diagramᵉ)

  extensionality-cocone-sequential-diagramᵉ :
    ( c'ᵉ : cocone-sequential-diagramᵉ Aᵉ Xᵉ) →
    ( cᵉ ＝ᵉ c'ᵉ) ≃ᵉ htpy-cocone-sequential-diagramᵉ cᵉ c'ᵉ
  pr1ᵉ (extensionality-cocone-sequential-diagramᵉ c'ᵉ) =
    htpy-eq-cocone-sequential-diagramᵉ c'ᵉ
  pr2ᵉ (extensionality-cocone-sequential-diagramᵉ c'ᵉ) =
    is-equiv-htpy-eq-cocone-sequential-diagramᵉ c'ᵉ

  eq-htpy-cocone-sequential-diagramᵉ :
    ( c'ᵉ : cocone-sequential-diagramᵉ Aᵉ Xᵉ) →
    htpy-cocone-sequential-diagramᵉ cᵉ c'ᵉ →
    cᵉ ＝ᵉ c'ᵉ
  eq-htpy-cocone-sequential-diagramᵉ c'ᵉ =
    map-inv-equivᵉ (extensionality-cocone-sequential-diagramᵉ c'ᵉ)
```

### Postcomposing a cocone under a sequential diagram by identity is the identity

```agda
module _
  { l1ᵉ l2ᵉ : Level} (Aᵉ : sequential-diagramᵉ l1ᵉ) {Xᵉ : UUᵉ l2ᵉ}
  ( cᵉ : cocone-sequential-diagramᵉ Aᵉ Xᵉ)
  where

  htpy-cocone-map-id-sequential-diagramᵉ :
    htpy-cocone-sequential-diagramᵉ (cocone-map-sequential-diagramᵉ cᵉ idᵉ) cᵉ
  pr1ᵉ htpy-cocone-map-id-sequential-diagramᵉ nᵉ =
    refl-htpyᵉ
  pr2ᵉ htpy-cocone-map-id-sequential-diagramᵉ nᵉ =
    ( right-unit-htpyᵉ) ∙hᵉ
    ( left-unit-law-left-whisker-compᵉ
      ( coherence-cocone-sequential-diagramᵉ cᵉ nᵉ))

  cocone-map-id-sequential-diagramᵉ : cocone-map-sequential-diagramᵉ cᵉ idᵉ ＝ᵉ cᵉ
  cocone-map-id-sequential-diagramᵉ =
    eq-htpy-cocone-sequential-diagramᵉ Aᵉ _ _
      ( htpy-cocone-map-id-sequential-diagramᵉ)
```

### Postcomposing cocones under a sequential colimit distributes over function composition

Inᵉ otherᵉ words,ᵉ extendingᵉ aᵉ coconeᵉ `c`ᵉ with vertexᵉ `X`ᵉ byᵉ theᵉ mapᵉ
`kᵉ ∘ᵉ hᵉ : Xᵉ → Z`ᵉ resultsᵉ in theᵉ sameᵉ coconeᵉ asᵉ firstᵉ extendingᵉ byᵉ `h`ᵉ andᵉ thenᵉ byᵉ
`k`.ᵉ

```agda
module _
  { l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Aᵉ : sequential-diagramᵉ l1ᵉ)
  { Xᵉ : UUᵉ l2ᵉ} {Yᵉ : UUᵉ l3ᵉ} {Zᵉ : UUᵉ l4ᵉ}
  ( cᵉ : cocone-sequential-diagramᵉ Aᵉ Xᵉ)
  where

  htpy-cocone-map-comp-sequential-diagramᵉ :
    ( hᵉ : Xᵉ → Yᵉ) (kᵉ : Yᵉ → Zᵉ) →
    htpy-cocone-sequential-diagramᵉ
      ( cocone-map-sequential-diagramᵉ cᵉ (kᵉ ∘ᵉ hᵉ))
      ( cocone-map-sequential-diagramᵉ (cocone-map-sequential-diagramᵉ cᵉ hᵉ) kᵉ)
  pr1ᵉ (htpy-cocone-map-comp-sequential-diagramᵉ hᵉ kᵉ) nᵉ =
    refl-htpyᵉ
  pr2ᵉ (htpy-cocone-map-comp-sequential-diagramᵉ hᵉ kᵉ) nᵉ =
    ( right-unit-htpyᵉ) ∙hᵉ
    ( inv-preserves-comp-left-whisker-compᵉ kᵉ hᵉ
      ( coherence-cocone-sequential-diagramᵉ cᵉ nᵉ))

  cocone-map-comp-sequential-diagramᵉ :
    ( hᵉ : Xᵉ → Yᵉ) (kᵉ : Yᵉ → Zᵉ) →
    cocone-map-sequential-diagramᵉ cᵉ (kᵉ ∘ᵉ hᵉ) ＝ᵉ
    cocone-map-sequential-diagramᵉ (cocone-map-sequential-diagramᵉ cᵉ hᵉ) kᵉ
  cocone-map-comp-sequential-diagramᵉ hᵉ kᵉ =
    eq-htpy-cocone-sequential-diagramᵉ Aᵉ
      ( cocone-map-sequential-diagramᵉ cᵉ (kᵉ ∘ᵉ hᵉ))
      ( cocone-map-sequential-diagramᵉ (cocone-map-sequential-diagramᵉ cᵉ hᵉ) kᵉ)
      ( htpy-cocone-map-comp-sequential-diagramᵉ hᵉ kᵉ)
```

## References

{{#bibliographyᵉ}} {{#referenceᵉ SvDR20ᵉ}}