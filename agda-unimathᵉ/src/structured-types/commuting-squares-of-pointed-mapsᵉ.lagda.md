# Commuting squares of pointed maps

```agda
module structured-types.commuting-squares-of-pointed-mapsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.commuting-squares-of-identificationsᵉ
open import foundation.commuting-squares-of-mapsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.function-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ

open import structured-types.pointed-homotopiesᵉ
open import structured-types.pointed-mapsᵉ
open import structured-types.pointed-typesᵉ
open import structured-types.whiskering-pointed-homotopies-compositionᵉ
```

</details>

## Idea

Considerᵉ aᵉ squareᵉ ofᵉ [pointedᵉ maps](structured-types.pointed-maps.mdᵉ)

```text
            topᵉ
       Aᵉ -------->ᵉ Xᵉ
       |           |
  leftᵉ |           | rightᵉ
       ∨ᵉ           ∨ᵉ
       Bᵉ -------->ᵉ Y.ᵉ
          bottomᵉ
```

Suchᵉ aᵉ squareᵉ isᵉ saidᵉ to beᵉ aᵉ
{{#conceptᵉ "commutingᵉ square"ᵉ Disambiguation="pointedᵉ maps"ᵉ Agda=coherence-square-pointed-mapsᵉ}}
ofᵉ pointedᵉ mapsᵉ ifᵉ thereᵉ isᵉ aᵉ
[pointedᵉ homotopy](structured-types.pointed-homotopies.mdᵉ)

```text
  bottomᵉ ∘∗ᵉ leftᵉ ~∗ᵉ rightᵉ ∘∗ᵉ top.ᵉ
```

Suchᵉ aᵉ homotopyᵉ isᵉ referredᵉ to asᵉ theᵉ
{{#conceptᵉ "coherence"ᵉ Disambiguation="commutingᵉ squaresᵉ ofᵉ pointedᵉ maps"ᵉ Agda=coherence-square-pointed-mapsᵉ}}
ofᵉ theᵉ commutingᵉ squareᵉ ofᵉ pointedᵉ maps.ᵉ

## Definitions

### Coherences of commuting squares of pointed maps

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  {Aᵉ : Pointed-Typeᵉ l1ᵉ} {Bᵉ : Pointed-Typeᵉ l2ᵉ}
  {Cᵉ : Pointed-Typeᵉ l3ᵉ} {Xᵉ : Pointed-Typeᵉ l4ᵉ}
  (topᵉ : Cᵉ →∗ᵉ Bᵉ) (leftᵉ : Cᵉ →∗ᵉ Aᵉ) (rightᵉ : Bᵉ →∗ᵉ Xᵉ) (bottomᵉ : Aᵉ →∗ᵉ Xᵉ)
  where

  coherence-square-pointed-mapsᵉ : UUᵉ (l3ᵉ ⊔ l4ᵉ)
  coherence-square-pointed-mapsᵉ =
    bottomᵉ ∘∗ᵉ leftᵉ ~∗ᵉ rightᵉ ∘∗ᵉ topᵉ

  coherence-square-maps-coherence-square-pointed-mapsᵉ :
    coherence-square-pointed-mapsᵉ →
    coherence-square-mapsᵉ
      ( map-pointed-mapᵉ topᵉ)
      ( map-pointed-mapᵉ leftᵉ)
      ( map-pointed-mapᵉ rightᵉ)
      ( map-pointed-mapᵉ bottomᵉ)
  coherence-square-maps-coherence-square-pointed-mapsᵉ =
    htpy-pointed-htpyᵉ
```

## Operations

### Left whiskering of coherences of commuting squares of pointed maps

Considerᵉ aᵉ commutingᵉ squareᵉ ofᵉ pointedᵉ mapsᵉ

```text
            topᵉ
       Aᵉ -------->ᵉ Xᵉ
       |           |
  leftᵉ |           | rightᵉ
       ∨ᵉ           ∨ᵉ
       Bᵉ -------->ᵉ Yᵉ
          bottomᵉ
```

andᵉ considerᵉ aᵉ pointedᵉ mapᵉ `fᵉ : Yᵉ →∗ᵉ Z`.ᵉ Thenᵉ theᵉ squareᵉ

```text
              topᵉ
       Aᵉ ------------->ᵉ Xᵉ
       |                |
  leftᵉ |                | fᵉ ∘∗ᵉ rightᵉ
       ∨ᵉ                ∨ᵉ
       Bᵉ ------------->ᵉ Zᵉ
          fᵉ ∘∗ᵉ bottomᵉ
```

alsoᵉ commutes.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level}
  {Aᵉ : Pointed-Typeᵉ l1ᵉ} {Bᵉ : Pointed-Typeᵉ l2ᵉ}
  {Xᵉ : Pointed-Typeᵉ l3ᵉ} {Yᵉ : Pointed-Typeᵉ l4ᵉ} {Zᵉ : Pointed-Typeᵉ l5ᵉ}
  (fᵉ : Yᵉ →∗ᵉ Zᵉ)
  (topᵉ : Aᵉ →∗ᵉ Xᵉ) (leftᵉ : Aᵉ →∗ᵉ Bᵉ) (rightᵉ : Xᵉ →∗ᵉ Yᵉ) (bottomᵉ : Bᵉ →∗ᵉ Yᵉ)
  (sᵉ : coherence-square-pointed-mapsᵉ topᵉ leftᵉ rightᵉ bottomᵉ)
  where

  left-whisker-comp-coherence-square-pointed-mapsᵉ :
    coherence-square-pointed-mapsᵉ topᵉ leftᵉ (fᵉ ∘∗ᵉ rightᵉ) (fᵉ ∘∗ᵉ bottomᵉ)
  left-whisker-comp-coherence-square-pointed-mapsᵉ =
    concat-pointed-htpyᵉ
      ( associative-comp-pointed-mapᵉ fᵉ bottomᵉ leftᵉ)
      ( concat-pointed-htpyᵉ
        ( left-whisker-comp-pointed-htpyᵉ fᵉ _ _ sᵉ)
        ( inv-associative-comp-pointed-mapᵉ fᵉ rightᵉ topᵉ))
```

### Left whiskering of coherences of commuting squares of pointed maps

Considerᵉ aᵉ commutingᵉ squareᵉ ofᵉ pointedᵉ mapsᵉ

```text
            topᵉ
       Aᵉ -------->ᵉ Xᵉ
       |           |
  leftᵉ |           | rightᵉ
       ∨ᵉ           ∨ᵉ
       Bᵉ -------->ᵉ Yᵉ
          bottomᵉ
```

andᵉ considerᵉ aᵉ pointedᵉ mapᵉ `fᵉ : Zᵉ →∗ᵉ A`.ᵉ Thenᵉ theᵉ squareᵉ

```text
               fᵉ ∘∗ᵉ topᵉ
            Aᵉ ---------->ᵉ Xᵉ
            |             |
  leftᵉ ∘∗ᵉ fᵉ |             | rightᵉ
            ∨ᵉ             ∨ᵉ
            Bᵉ ---------->ᵉ Zᵉ
                bottomᵉ
```

alsoᵉ commutes.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level}
  {Aᵉ : Pointed-Typeᵉ l1ᵉ} {Bᵉ : Pointed-Typeᵉ l2ᵉ}
  {Xᵉ : Pointed-Typeᵉ l3ᵉ} {Yᵉ : Pointed-Typeᵉ l4ᵉ} {Zᵉ : Pointed-Typeᵉ l5ᵉ}
  (topᵉ : Aᵉ →∗ᵉ Xᵉ) (leftᵉ : Aᵉ →∗ᵉ Bᵉ) (rightᵉ : Xᵉ →∗ᵉ Yᵉ) (bottomᵉ : Bᵉ →∗ᵉ Yᵉ)
  (sᵉ : coherence-square-pointed-mapsᵉ topᵉ leftᵉ rightᵉ bottomᵉ)
  (fᵉ : Zᵉ →∗ᵉ Aᵉ)
  where

  right-whisker-comp-coherence-square-pointed-mapsᵉ :
    coherence-square-pointed-mapsᵉ (topᵉ ∘∗ᵉ fᵉ) (leftᵉ ∘∗ᵉ fᵉ) rightᵉ bottomᵉ
  right-whisker-comp-coherence-square-pointed-mapsᵉ =
    concat-pointed-htpyᵉ
      ( inv-associative-comp-pointed-mapᵉ bottomᵉ leftᵉ fᵉ)
      ( concat-pointed-htpyᵉ
        ( right-whisker-comp-pointed-htpyᵉ _ _ sᵉ fᵉ)
        ( associative-comp-pointed-mapᵉ rightᵉ topᵉ fᵉ))
```

### Horizontal pasting of coherences of commuting squares of pointed maps

Considerᵉ twoᵉ commutingᵉ squaresᵉ ofᵉ pointedᵉ maps,ᵉ asᵉ in theᵉ diagramᵉ

```text
            top-leftᵉ         top-rightᵉ
       Aᵉ ------------->ᵉ Bᵉ -------------->ᵉ Cᵉ
       |                |                 |
  leftᵉ |                | middleᵉ          | rightᵉ
       ∨ᵉ                ∨ᵉ                 ∨ᵉ
       Dᵉ ------------->ᵉ Eᵉ -------------->ᵉ Fᵉ
          bottom-leftᵉ      bottom-rightᵉ
```

with pointedᵉ homotopiesᵉ

```text
  Hᵉ : bottom-leftᵉ ∘∗ᵉ leftᵉ ~∗ᵉ middleᵉ ∘∗ᵉ topᵉ
  Kᵉ : bottom-rightᵉ ∘∗ᵉ middleᵉ ~∗ᵉ rightᵉ ∘∗ᵉ top-right.ᵉ
```

Theᵉ
{{#conceptᵉ "horizontalᵉ pasting"ᵉ Disambiguation="commutingᵉ squaresᵉ ofᵉ pointedᵉ maps"ᵉ Agda=horizontal-pasting-coherence-square-pointed-mapsᵉ}}
ofᵉ theseᵉ coherencesᵉ ofᵉ commutingᵉ squaresᵉ ofᵉ pointedᵉ mapsᵉ isᵉ theᵉ coherenceᵉ ofᵉ theᵉ
commutingᵉ squareᵉ

```text
             top-rightᵉ ∘∗ᵉ top-leftᵉ
       Aᵉ ----------------------------->ᵉ Cᵉ
       |                                |
  leftᵉ |                                | rightᵉ
       ∨ᵉ                                ∨ᵉ
       Dᵉ ----------------------------->ᵉ Fᵉ
          bottom-rightᵉ ∘∗ᵉ bottom-leftᵉ
```

obtainedᵉ byᵉ concatenationᵉ ofᵉ theᵉ followingᵉ threeᵉ pointedᵉ homotopiesᵉ:

```text
  (bottom-rightᵉ ∘∗ᵉ bottom-leftᵉ) ∘∗ᵉ leftᵉ
  ~∗ᵉ (bottom-rightᵉ ∘∗ᵉ middleᵉ) ∘∗ᵉ top-leftᵉ
  ~∗ᵉ bottom-rightᵉ ∘∗ᵉ (middleᵉ ∘∗ᵉ top-leftᵉ)
  ~∗ᵉ rightᵉ ∘∗ᵉ (top-rightᵉ ∘∗ᵉ top-left).ᵉ
```

Theᵉ firstᵉ andᵉ thirdᵉ homotopyᵉ in thisᵉ concatenationᵉ areᵉ theᵉ whiskeringsᵉ ofᵉ
coherencesᵉ ofᵉ
[commutingᵉ trianglesᵉ ofᵉ pointedᵉ maps](structured-types.commuting-triangles-of-pointed-maps.md).ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level}
  {Aᵉ : Pointed-Typeᵉ l1ᵉ} {Bᵉ : Pointed-Typeᵉ l2ᵉ}
  {Xᵉ : Pointed-Typeᵉ l3ᵉ} {Yᵉ : Pointed-Typeᵉ l4ᵉ}
  {Uᵉ : Pointed-Typeᵉ l5ᵉ} {Vᵉ : Pointed-Typeᵉ l6ᵉ}
  (top-leftᵉ : Aᵉ →∗ᵉ Xᵉ) (top-rightᵉ : Xᵉ →∗ᵉ Uᵉ)
  (leftᵉ : Aᵉ →∗ᵉ Bᵉ) (middleᵉ : Xᵉ →∗ᵉ Yᵉ) (rightᵉ : Uᵉ →∗ᵉ Vᵉ)
  (bottom-leftᵉ : Bᵉ →∗ᵉ Yᵉ) (bottom-rightᵉ : Yᵉ →∗ᵉ Vᵉ)
  (left-squareᵉ :
    coherence-square-pointed-mapsᵉ top-leftᵉ leftᵉ middleᵉ bottom-leftᵉ)
  (right-squareᵉ :
    coherence-square-pointed-mapsᵉ top-rightᵉ middleᵉ rightᵉ bottom-rightᵉ)
  where

  horizontal-pasting-coherence-square-pointed-mapsᵉ :
    coherence-square-pointed-mapsᵉ
      ( top-rightᵉ ∘∗ᵉ top-leftᵉ)
      ( leftᵉ)
      ( rightᵉ)
      ( bottom-rightᵉ ∘∗ᵉ bottom-leftᵉ)
  horizontal-pasting-coherence-square-pointed-mapsᵉ =
    concat-pointed-htpyᵉ
      ( left-whisker-comp-coherence-square-pointed-mapsᵉ
        ( bottom-rightᵉ)
        ( top-leftᵉ)
        ( leftᵉ)
        ( middleᵉ)
        ( bottom-leftᵉ)
        ( left-squareᵉ))
      ( concat-pointed-htpyᵉ
        ( associative-comp-pointed-mapᵉ bottom-rightᵉ middleᵉ top-leftᵉ)
        ( right-whisker-comp-coherence-square-pointed-mapsᵉ
          ( top-rightᵉ)
          ( middleᵉ)
          ( rightᵉ)
          ( bottom-rightᵉ)
          ( right-squareᵉ)
          ( top-leftᵉ)))
```

### Vertical pasting of coherences of commuting squares of pointed maps

Considerᵉ twoᵉ commutingᵉ squaresᵉ ofᵉ pointedᵉ maps,ᵉ asᵉ in theᵉ diagramᵉ

```text
                   topᵉ
              Aᵉ -------->ᵉ Bᵉ
              |           |
     top-leftᵉ |           | top-rightᵉ
              ∨ᵉ  middleᵉ   ∨ᵉ
              Cᵉ -------->ᵉ Dᵉ
              |           |
  bottom-leftᵉ |           | bottom-rightᵉ
              ∨ᵉ           ∨ᵉ
              Eᵉ -------->ᵉ Fᵉ
                 bottomᵉ
```

with pointedᵉ homotopiesᵉ

```text
  Hᵉ : middleᵉ ∘∗ᵉ top-leftᵉ ~∗ᵉ top-rightᵉ ∘∗ᵉ topᵉ
  Kᵉ : bottomᵉ ∘∗ᵉ bottom-leftᵉ ~∗ᵉ  bottom-rightᵉ ∘∗ᵉ middle.ᵉ
```

Theᵉ
{{#conceptᵉ "verticalᵉ pasting"ᵉ Disambiguation="commutingᵉ squaresᵉ ofᵉ pointedᵉ maps"ᵉ Agda=vertical-pasting-coherence-square-pointed-mapsᵉ}}
ofᵉ theseᵉ coherencesᵉ ofᵉ commutingᵉ squaresᵉ ofᵉ pointedᵉ mapsᵉ isᵉ theᵉ coherenceᵉ ofᵉ theᵉ
commutingᵉ squareᵉ

```text
                               topᵉ
                          Aᵉ -------->ᵉ Bᵉ
                          |           |
  bottom-leftᵉ ∘∗ᵉ top-leftᵉ |           | bottom-rightᵉ ∘∗ᵉ top-rightᵉ
                          ∨ᵉ           ∨ᵉ
                          Eᵉ -------->ᵉ Fᵉ
                             bottomᵉ
```

obtainedᵉ byᵉ concatenationᵉ ofᵉ theᵉ followingᵉ threeᵉ pointedᵉ homotopiesᵉ:

```text
  bottomᵉ ∘∗ᵉ (bottom-leftᵉ ∘∗ᵉ top-leftᵉ)
  ~∗ᵉ bottom-rightᵉ ∘∗ᵉ (middleᵉ ∘∗ᵉ top-leftᵉ)
  ~∗ᵉ (bottom-rightᵉ ∘∗ᵉ middleᵉ) ∘∗ᵉ top-leftᵉ
  ~∗ᵉ (bottom-rightᵉ ∘∗ᵉ top-rightᵉ) ∘∗ᵉ top.ᵉ
```

Theᵉ firstᵉ andᵉ thirdᵉ homotopyᵉ in thisᵉ concatenationᵉ areᵉ theᵉ whiskeringsᵉ ofᵉ
coherencesᵉ ofᵉ
[commutingᵉ trianglesᵉ ofᵉ pointedᵉ maps](structured-types.commuting-triangles-of-pointed-maps.md).ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level}
  {Aᵉ : Pointed-Typeᵉ l1ᵉ} {Bᵉ : Pointed-Typeᵉ l2ᵉ}
  {Cᵉ : Pointed-Typeᵉ l3ᵉ} {Dᵉ : Pointed-Typeᵉ l4ᵉ}
  {Eᵉ : Pointed-Typeᵉ l5ᵉ} {Fᵉ : Pointed-Typeᵉ l6ᵉ}
  (topᵉ : Aᵉ →∗ᵉ Bᵉ) (top-leftᵉ : Aᵉ →∗ᵉ Cᵉ) (top-rightᵉ : Bᵉ →∗ᵉ Dᵉ) (middleᵉ : Cᵉ →∗ᵉ Dᵉ)
  (bottom-leftᵉ : Cᵉ →∗ᵉ Eᵉ) (bottom-rightᵉ : Dᵉ →∗ᵉ Fᵉ) (bottomᵉ : Eᵉ →∗ᵉ Fᵉ)
  (top-squareᵉ : coherence-square-pointed-mapsᵉ topᵉ top-leftᵉ top-rightᵉ middleᵉ)
  (bottom-squareᵉ :
    coherence-square-pointed-mapsᵉ middleᵉ bottom-leftᵉ bottom-rightᵉ bottomᵉ)
  where

  vertical-pasting-coherence-square-pointed-mapsᵉ :
    coherence-square-pointed-mapsᵉ
      ( topᵉ)
      ( bottom-leftᵉ ∘∗ᵉ top-leftᵉ)
      ( bottom-rightᵉ ∘∗ᵉ top-rightᵉ)
      ( bottomᵉ)
  vertical-pasting-coherence-square-pointed-mapsᵉ =
    concat-pointed-htpyᵉ
      ( right-whisker-comp-coherence-square-pointed-mapsᵉ
        ( middleᵉ)
        ( bottom-leftᵉ)
        ( bottom-rightᵉ)
        ( bottomᵉ)
        ( bottom-squareᵉ)
        ( top-leftᵉ))
      ( concat-pointed-htpyᵉ
        ( inv-associative-comp-pointed-mapᵉ bottom-rightᵉ middleᵉ top-leftᵉ)
        ( left-whisker-comp-coherence-square-pointed-mapsᵉ
          ( bottom-rightᵉ)
          ( topᵉ)
          ( top-leftᵉ)
          ( top-rightᵉ)
          ( middleᵉ)
          ( top-squareᵉ)))
```