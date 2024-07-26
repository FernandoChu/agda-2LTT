# Commuting squares of identifications

```agda
module foundation-core.commuting-squares-of-identificationsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.function-typesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.retractionsᵉ
open import foundation-core.sectionsᵉ
open import foundation-core.whiskering-identifications-concatenationᵉ
```

</details>

## Idea

Aᵉ squareᵉ ofᵉ [identifications](foundation-core.identity-types.mdᵉ)

```text
           topᵉ
       xᵉ ------->ᵉ yᵉ
       |          |
  leftᵉ |          | rightᵉ
       ∨ᵉ          ∨ᵉ
       zᵉ ------->ᵉ wᵉ
          bottomᵉ
```

isᵉ saidᵉ to beᵉ aᵉ
{{#conceptᵉ "commutingᵉ square"ᵉ Disambiguation="identifications"ᵉ Agda=coherence-square-identificationsᵉ}}
ifᵉ thereᵉ isᵉ anᵉ identificationᵉ `leftᵉ ∙ᵉ bottomᵉ ＝ᵉ topᵉ ∙ᵉ right`.ᵉ Suchᵉ anᵉ
identificationᵉ isᵉ calledᵉ aᵉ
{{#conceptᵉ "coherence"ᵉ Disambiguation="commutingᵉ squareᵉ ofᵉ identifications"ᵉ Agda=coherence-square-identificationsᵉ}}
ofᵉ theᵉ square.ᵉ

## Definitions

### Commuting squares of identifications

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {xᵉ yᵉ zᵉ wᵉ : Aᵉ}
  (topᵉ : xᵉ ＝ᵉ yᵉ) (leftᵉ : xᵉ ＝ᵉ zᵉ) (rightᵉ : yᵉ ＝ᵉ wᵉ) (bottomᵉ : zᵉ ＝ᵉ wᵉ)
  where

  coherence-square-identificationsᵉ : UUᵉ lᵉ
  coherence-square-identificationsᵉ = leftᵉ ∙ᵉ bottomᵉ ＝ᵉ topᵉ ∙ᵉ rightᵉ
```

### Horizontally constant squares

{{#conceptᵉ "Horizontallyᵉ constantᵉ squares"ᵉ Disambiguation="identifications"ᵉ Agda=horizontal-refl-coherence-square-identificationsᵉ}}
areᵉ commutingᵉ squaresᵉ ofᵉ identificationsᵉ ofᵉ theᵉ formᵉ

```text
       reflᵉ
    aᵉ ----->ᵉ aᵉ
    |        |
  pᵉ |        | pᵉ
    ∨ᵉ        ∨ᵉ
    bᵉ ----->ᵉ b.ᵉ
       reflᵉ
```

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {aᵉ bᵉ : Aᵉ} (pᵉ : aᵉ ＝ᵉ bᵉ)
  where

  horizontal-refl-coherence-square-identificationsᵉ :
    coherence-square-identificationsᵉ reflᵉ pᵉ pᵉ reflᵉ
  horizontal-refl-coherence-square-identificationsᵉ = right-unitᵉ
```

### Vertically constant squares

{{#conceptᵉ "Verticallyᵉ constantᵉ squares"ᵉ Disambiguation="identifications"ᵉ Agda=vertical-refl-coherence-square-identificationsᵉ}}
areᵉ commutingᵉ squaresᵉ ofᵉ identificationsᵉ ofᵉ theᵉ formᵉ

```text
           pᵉ
       aᵉ ----->ᵉ bᵉ
       |        |
  reflᵉ |        | reflᵉ
       ∨ᵉ        ∨ᵉ
       aᵉ ----->ᵉ b.ᵉ
           pᵉ
```

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {aᵉ bᵉ : Aᵉ} (pᵉ : aᵉ ＝ᵉ bᵉ)
  where

  vertical-refl-coherence-square-identificationsᵉ :
    coherence-square-identificationsᵉ pᵉ reflᵉ reflᵉ pᵉ
  vertical-refl-coherence-square-identificationsᵉ = invᵉ right-unitᵉ
```

### Squares with `refl` on the top and bottom

Givenᵉ anᵉ identificationᵉ `αᵉ : pᵉ ＝ᵉ q`,ᵉ weᵉ canᵉ obtainᵉ aᵉ coherenceᵉ squareᵉ with
`refl`ᵉ onᵉ theᵉ topᵉ andᵉ bottom,ᵉ likeᵉ theᵉ diagramᵉ below.ᵉ

```text
       reflᵉ
    aᵉ ----->ᵉ aᵉ
    |        |
  pᵉ |        | qᵉ
    ∨ᵉ        ∨ᵉ
    bᵉ ----->ᵉ bᵉ
       reflᵉ
```

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {aᵉ bᵉ : Aᵉ} (pᵉ qᵉ : aᵉ ＝ᵉ bᵉ)
  where

  coherence-square-identifications-horizontal-reflᵉ :
    pᵉ ＝ᵉ qᵉ →
    coherence-square-identificationsᵉ
      ( reflᵉ)
      ( pᵉ)
      ( qᵉ)
      ( reflᵉ)
  coherence-square-identifications-horizontal-reflᵉ αᵉ =
    right-unitᵉ ∙ᵉ αᵉ
```

Conversely,ᵉ givenᵉ aᵉ coherenceᵉ squareᵉ asᵉ above,ᵉ weᵉ canᵉ obtainᵉ anᵉ equalityᵉ
`pᵉ ＝ᵉ q`.ᵉ

```agda
  inv-coherence-square-identifications-horizontal-reflᵉ :
    coherence-square-identificationsᵉ
      ( reflᵉ)
      ( pᵉ)
      ( qᵉ)
      ( reflᵉ) →
    pᵉ ＝ᵉ qᵉ
  inv-coherence-square-identifications-horizontal-reflᵉ αᵉ =
    invᵉ right-unitᵉ ∙ᵉ αᵉ
```

### Squares with `refl` on the left and right

Givenᵉ anᵉ identificationᵉ `αᵉ : pᵉ ＝ᵉ q`,ᵉ weᵉ canᵉ obtainᵉ aᵉ coherenceᵉ squareᵉ with
`refl`ᵉ onᵉ theᵉ leftᵉ andᵉ right,ᵉ likeᵉ theᵉ diagramᵉ below.ᵉ

```text
           qᵉ
       aᵉ ----->ᵉ bᵉ
       |        |
  reflᵉ |        | reflᵉ
       ∨ᵉ        ∨ᵉ
       aᵉ ----->ᵉ bᵉ
           pᵉ
```

```agda
  coherence-square-identifications-vertical-reflᵉ :
    pᵉ ＝ᵉ qᵉ →
    coherence-square-identificationsᵉ
      ( qᵉ)
      ( reflᵉ)
      ( reflᵉ)
      ( pᵉ)
  coherence-square-identifications-vertical-reflᵉ αᵉ =
    αᵉ ∙ᵉ invᵉ right-unitᵉ
```

Conversely,ᵉ givenᵉ aᵉ coherenceᵉ squareᵉ asᵉ above,ᵉ weᵉ canᵉ obtainᵉ anᵉ equalityᵉ
`ᵉ pᵉ ＝ᵉ q`.ᵉ

```agda
  inv-coherence-square-identifications-vertical-reflᵉ :
    coherence-square-identificationsᵉ
      ( qᵉ)
      ( reflᵉ)
      ( reflᵉ)
      ( pᵉ) →
    pᵉ ＝ᵉ qᵉ
  inv-coherence-square-identifications-vertical-reflᵉ αᵉ =
    αᵉ ∙ᵉ right-unitᵉ
```

## Operations

### Inverting squares of identifications horizontally

Givenᵉ aᵉ commutingᵉ squareᵉ ofᵉ identificationsᵉ

```text
           topᵉ
       xᵉ ------->ᵉ yᵉ
       |          |
  leftᵉ |          | rightᵉ
       ∨ᵉ          ∨ᵉ
       zᵉ ------->ᵉ w,ᵉ
          bottomᵉ
```

theᵉ squareᵉ ofᵉ identificationsᵉ

```text
             invᵉ topᵉ
        yᵉ ------------>ᵉ xᵉ
        |               |
  rightᵉ |               | leftᵉ
        ∨ᵉ               ∨ᵉ
        wᵉ ------------>ᵉ zᵉ
           invᵉ bottomᵉ
```

commutes.ᵉ

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {xᵉ yᵉ zᵉ wᵉ : Aᵉ}
  where

  horizontal-inv-coherence-square-identificationsᵉ :
    (topᵉ : xᵉ ＝ᵉ yᵉ) (leftᵉ : xᵉ ＝ᵉ zᵉ) (rightᵉ : yᵉ ＝ᵉ wᵉ) (bottomᵉ : zᵉ ＝ᵉ wᵉ) →
    coherence-square-identificationsᵉ topᵉ leftᵉ rightᵉ bottomᵉ →
    coherence-square-identificationsᵉ (invᵉ topᵉ) rightᵉ leftᵉ (invᵉ bottomᵉ)
  horizontal-inv-coherence-square-identificationsᵉ reflᵉ leftᵉ rightᵉ bottomᵉ cohᵉ =
    invᵉ (right-transpose-eq-concatᵉ leftᵉ bottomᵉ rightᵉ cohᵉ)
```

### Inverting squares of identifications vertically

Givenᵉ aᵉ commutingᵉ squareᵉ ofᵉ identificationsᵉ

```text
           topᵉ
       xᵉ ------->ᵉ yᵉ
       |          |
  leftᵉ |          | rightᵉ
       ∨ᵉ          ∨ᵉ
       zᵉ ------->ᵉ w,ᵉ
          bottomᵉ
```

theᵉ squareᵉ ofᵉ identificationsᵉ

```text
              bottomᵉ
           zᵉ ------->ᵉ wᵉ
           |          |
  invᵉ leftᵉ |          | invᵉ rightᵉ
           ∨ᵉ          ∨ᵉ
           xᵉ ------->ᵉ yᵉ
               topᵉ
```

commutes.ᵉ

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {xᵉ yᵉ zᵉ wᵉ : Aᵉ}
  where

  vertical-inv-coherence-square-identificationsᵉ :
    (topᵉ : xᵉ ＝ᵉ yᵉ) (leftᵉ : xᵉ ＝ᵉ zᵉ) (rightᵉ : yᵉ ＝ᵉ wᵉ) (bottomᵉ : zᵉ ＝ᵉ wᵉ) →
    coherence-square-identificationsᵉ topᵉ leftᵉ rightᵉ bottomᵉ →
    coherence-square-identificationsᵉ bottomᵉ (invᵉ leftᵉ) (invᵉ rightᵉ) topᵉ
  vertical-inv-coherence-square-identificationsᵉ topᵉ reflᵉ rightᵉ bottomᵉ cohᵉ =
    right-transpose-eq-concatᵉ topᵉ rightᵉ (bottomᵉ) (invᵉ cohᵉ)
```

### Functions acting on squares of identifications

Givenᵉ aᵉ commutingᵉ squareᵉ ofᵉ identificationsᵉ

```text
           topᵉ
       xᵉ ------->ᵉ yᵉ
       |          |
  leftᵉ |          | rightᵉ
       ∨ᵉ          ∨ᵉ
       zᵉ ------->ᵉ wᵉ
          bottomᵉ
```

in aᵉ typeᵉ `A`,ᵉ andᵉ givenᵉ aᵉ mapᵉ `fᵉ : Aᵉ → B`,ᵉ theᵉ squareᵉ ofᵉ identificationsᵉ

```text
                 apᵉ fᵉ topᵉ
           fᵉ xᵉ ----------->ᵉ fᵉ yᵉ
            |                |
  apᵉ fᵉ leftᵉ |                | apᵉ fᵉ rightᵉ
            ∨ᵉ                ∨ᵉ
            zᵉ ------------->ᵉ wᵉ
               apᵉ fᵉ bottomᵉ
```

commutes.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {xᵉ yᵉ zᵉ wᵉ : Aᵉ} (fᵉ : Aᵉ → Bᵉ)
  where

  map-coherence-square-identificationsᵉ :
    (topᵉ : xᵉ ＝ᵉ yᵉ) (leftᵉ : xᵉ ＝ᵉ zᵉ) (rightᵉ : yᵉ ＝ᵉ wᵉ) (bottomᵉ : zᵉ ＝ᵉ wᵉ) →
    coherence-square-identificationsᵉ topᵉ leftᵉ rightᵉ bottomᵉ →
    coherence-square-identificationsᵉ
      ( apᵉ fᵉ topᵉ)
      ( apᵉ fᵉ leftᵉ)
      ( apᵉ fᵉ rightᵉ)
      ( apᵉ fᵉ bottomᵉ)
  map-coherence-square-identificationsᵉ reflᵉ reflᵉ _ _ cohᵉ = apᵉ (apᵉ fᵉ) cohᵉ
```

### Concatenating identifications of edges and coherences of commuting squares of identifications

Considerᵉ aᵉ commutingᵉ squareᵉ ofᵉ identificationsᵉ andᵉ anᵉ identificationᵉ ofᵉ oneᵉ ofᵉ
theᵉ fourᵉ sidesᵉ with anotherᵉ identification,ᵉ asᵉ forᵉ exampleᵉ in theᵉ diagramᵉ belowᵉ:

```text
             topᵉ
       aᵉ --------->ᵉ bᵉ
       |           | |
  leftᵉ |     rightᵉ |=|ᵉ right'ᵉ
       ∨ᵉ           ∨ᵉ ∨ᵉ
       cᵉ --------->ᵉ d.ᵉ
           bottomᵉ
```

Thenᵉ anyᵉ identificationᵉ witnessingᵉ thatᵉ theᵉ squareᵉ commutesᵉ canᵉ beᵉ concatenatedᵉ
with theᵉ identificationᵉ onᵉ theᵉ side,ᵉ to obtainᵉ aᵉ newᵉ commutingᵉ squareᵉ ofᵉ
identifications.ᵉ

**Note.**ᵉ Toᵉ avoidᵉ cyclicᵉ module dependenciesᵉ weᵉ willᵉ giveᵉ directᵉ proofsᵉ thatᵉ
concatenatingᵉ identificationsᵉ ofᵉ edgesᵉ ofᵉ aᵉ squareᵉ with theᵉ coherenceᵉ ofᵉ itsᵉ
commutativityᵉ isᵉ anᵉ equivalence.ᵉ

#### Concatenating identifications of the top edge with a coherence of a commuting square of identifications

Considerᵉ aᵉ commutingᵉ diagramᵉ ofᵉ identificationsᵉ

```text
           top'ᵉ
         ------->ᵉ
       xᵉ ------->ᵉ yᵉ
       |   topᵉ    |
  leftᵉ |          | rightᵉ
       ∨ᵉ          ∨ᵉ
       zᵉ ------->ᵉ w.ᵉ
          bottomᵉ
```

with anᵉ identificationᵉ `topᵉ ＝ᵉ top'`.ᵉ Thenᵉ weᵉ getᵉ anᵉ equivalenceᵉ

```text
           topᵉ                             top'ᵉ
       xᵉ ------->ᵉ yᵉ                    xᵉ ------->ᵉ yᵉ
       |          |                    |          |
  leftᵉ |          | rightᵉ    ≃ᵉ    leftᵉ |          | rightᵉ
       ∨ᵉ          ∨ᵉ                    ∨ᵉ          ∨ᵉ
       zᵉ ------->ᵉ wᵉ                    zᵉ ------->ᵉ w.ᵉ
          bottomᵉ                          bottomᵉ
```

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {xᵉ yᵉ zᵉ wᵉ : Aᵉ}
  (topᵉ : xᵉ ＝ᵉ yᵉ) (leftᵉ : xᵉ ＝ᵉ zᵉ) (rightᵉ : yᵉ ＝ᵉ wᵉ) (bottomᵉ : zᵉ ＝ᵉ wᵉ)
  {top'ᵉ : xᵉ ＝ᵉ yᵉ} (sᵉ : topᵉ ＝ᵉ top'ᵉ)
  where

  concat-top-identification-coherence-square-identificationsᵉ :
    coherence-square-identificationsᵉ topᵉ leftᵉ rightᵉ bottomᵉ →
    coherence-square-identificationsᵉ top'ᵉ leftᵉ rightᵉ bottomᵉ
  concat-top-identification-coherence-square-identificationsᵉ tᵉ =
    tᵉ ∙ᵉ apᵉ (concat'ᵉ _ rightᵉ) sᵉ

  inv-concat-top-identification-coherence-square-identificationsᵉ :
    coherence-square-identificationsᵉ top'ᵉ leftᵉ rightᵉ bottomᵉ →
    coherence-square-identificationsᵉ topᵉ leftᵉ rightᵉ bottomᵉ
  inv-concat-top-identification-coherence-square-identificationsᵉ tᵉ =
    tᵉ ∙ᵉ invᵉ (apᵉ (concat'ᵉ _ rightᵉ) sᵉ)

  is-section-inv-concat-top-identification-coherence-square-identificationsᵉ :
    is-sectionᵉ
      concat-top-identification-coherence-square-identificationsᵉ
      inv-concat-top-identification-coherence-square-identificationsᵉ
  is-section-inv-concat-top-identification-coherence-square-identificationsᵉ =
    is-section-inv-concat'ᵉ (apᵉ (concat'ᵉ _ rightᵉ) sᵉ)

  is-retraction-inv-concat-top-identification-coherence-square-identificationsᵉ :
    is-retractionᵉ
      concat-top-identification-coherence-square-identificationsᵉ
      inv-concat-top-identification-coherence-square-identificationsᵉ
  is-retraction-inv-concat-top-identification-coherence-square-identificationsᵉ =
    is-retraction-inv-concat'ᵉ (apᵉ (concat'ᵉ _ rightᵉ) sᵉ)
```

Weᵉ record thatᵉ thisᵉ constructionᵉ isᵉ anᵉ equivalenceᵉ in
[`foundation.commuting-squares-of-identifications`](foundation.commuting-squares-of-identifications.md).ᵉ

#### Concatenating identifications of the left edge with a coherence of a commuting square of identifications

Considerᵉ aᵉ commutingᵉ diagramᵉ ofᵉ identificationsᵉ

```text
              topᵉ
         xᵉ ------->ᵉ yᵉ
        | |         |
  left'ᵉ | | leftᵉ    | rightᵉ
        ∨ᵉ ∨ᵉ         ∨ᵉ
         zᵉ ------->ᵉ w.ᵉ
            bottomᵉ
```

with anᵉ identificationᵉ `leftᵉ ＝ᵉ left'`.ᵉ Thenᵉ weᵉ getᵉ anᵉ equivalenceᵉ

```text
           topᵉ                              topᵉ
       xᵉ ------->ᵉ yᵉ                     xᵉ ------->ᵉ yᵉ
       |          |                     |          |
  leftᵉ |          | rightᵉ    ≃ᵉ    left'ᵉ |          | rightᵉ
       ∨ᵉ          ∨ᵉ                     ∨ᵉ          ∨ᵉ
       zᵉ ------->ᵉ wᵉ                     zᵉ ------->ᵉ w.ᵉ
          bottomᵉ                           bottomᵉ
```

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {xᵉ yᵉ zᵉ wᵉ : Aᵉ}
  (topᵉ : xᵉ ＝ᵉ yᵉ) (leftᵉ : xᵉ ＝ᵉ zᵉ) (rightᵉ : yᵉ ＝ᵉ wᵉ) (bottomᵉ : zᵉ ＝ᵉ wᵉ)
  {left'ᵉ : xᵉ ＝ᵉ zᵉ} (sᵉ : leftᵉ ＝ᵉ left'ᵉ)
  where

  concat-left-identification-coherence-square-identificationsᵉ :
    coherence-square-identificationsᵉ topᵉ leftᵉ rightᵉ bottomᵉ →
    coherence-square-identificationsᵉ topᵉ left'ᵉ rightᵉ bottomᵉ
  concat-left-identification-coherence-square-identificationsᵉ tᵉ =
    invᵉ (apᵉ (concat'ᵉ _ bottomᵉ) sᵉ) ∙ᵉ tᵉ

  inv-concat-left-identification-coherence-square-identificationsᵉ :
    coherence-square-identificationsᵉ topᵉ left'ᵉ rightᵉ bottomᵉ →
    coherence-square-identificationsᵉ topᵉ leftᵉ rightᵉ bottomᵉ
  inv-concat-left-identification-coherence-square-identificationsᵉ tᵉ =
    apᵉ (concat'ᵉ _ bottomᵉ) sᵉ ∙ᵉ tᵉ

  is-section-inv-concat-left-identification-coherence-square-identificationsᵉ :
    is-sectionᵉ
      concat-left-identification-coherence-square-identificationsᵉ
      inv-concat-left-identification-coherence-square-identificationsᵉ
  is-section-inv-concat-left-identification-coherence-square-identificationsᵉ =
    is-retraction-inv-concatᵉ (apᵉ (concat'ᵉ _ bottomᵉ) sᵉ)

  is-retraction-inv-concat-left-identification-coherence-square-identificationsᵉ :
    is-retractionᵉ
      concat-left-identification-coherence-square-identificationsᵉ
      inv-concat-left-identification-coherence-square-identificationsᵉ
  is-retraction-inv-concat-left-identification-coherence-square-identificationsᵉ =
    is-section-inv-concatᵉ (apᵉ (concat'ᵉ _ bottomᵉ) sᵉ)
```

Weᵉ record thatᵉ thisᵉ constructionᵉ isᵉ anᵉ equivalenceᵉ in
[`foundation.commuting-squares-of-identifications`](foundation.commuting-squares-of-identifications.md).ᵉ

#### Concatenating identifications of the right edge with a coherence of a commuting square of identifications

Considerᵉ aᵉ commutingᵉ diagramᵉ ofᵉ identificationsᵉ

```text
            topᵉ
       xᵉ ------->ᵉ yᵉ
       |         | |
  leftᵉ |   rightᵉ | | right'ᵉ
       ∨ᵉ         ∨ᵉ ∨ᵉ
       zᵉ ------->ᵉ w.ᵉ
          bottomᵉ
```

with anᵉ identificationᵉ `rightᵉ ＝ᵉ right'`.ᵉ Thenᵉ weᵉ getᵉ anᵉ equivalenceᵉ

```text
           topᵉ                             topᵉ
       xᵉ ------->ᵉ yᵉ                    xᵉ ------->ᵉ yᵉ
       |          |                    |          |
  leftᵉ |          | rightᵉ    ≃ᵉ    leftᵉ |          | right'ᵉ
       ∨ᵉ          ∨ᵉ                    ∨ᵉ          ∨ᵉ
       zᵉ ------->ᵉ wᵉ                    zᵉ ------->ᵉ w.ᵉ
          bottomᵉ                          bottomᵉ
```

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {xᵉ yᵉ zᵉ wᵉ : Aᵉ}
  (topᵉ : xᵉ ＝ᵉ yᵉ) (leftᵉ : xᵉ ＝ᵉ zᵉ) (rightᵉ : yᵉ ＝ᵉ wᵉ) (bottomᵉ : zᵉ ＝ᵉ wᵉ)
  {right'ᵉ : yᵉ ＝ᵉ wᵉ} (sᵉ : rightᵉ ＝ᵉ right'ᵉ)
  where

  concat-right-identification-coherence-square-identificationsᵉ :
    coherence-square-identificationsᵉ topᵉ leftᵉ rightᵉ bottomᵉ →
    coherence-square-identificationsᵉ topᵉ leftᵉ right'ᵉ bottomᵉ
  concat-right-identification-coherence-square-identificationsᵉ tᵉ =
    tᵉ ∙ᵉ apᵉ (concatᵉ topᵉ _) sᵉ

  inv-concat-right-identification-coherence-square-identificationsᵉ :
    coherence-square-identificationsᵉ topᵉ leftᵉ right'ᵉ bottomᵉ →
    coherence-square-identificationsᵉ topᵉ leftᵉ rightᵉ bottomᵉ
  inv-concat-right-identification-coherence-square-identificationsᵉ tᵉ =
    tᵉ ∙ᵉ invᵉ (apᵉ (concatᵉ topᵉ _) sᵉ)

  is-section-inv-concat-right-identification-coherence-square-identificationsᵉ :
    is-sectionᵉ
      concat-right-identification-coherence-square-identificationsᵉ
      inv-concat-right-identification-coherence-square-identificationsᵉ
  is-section-inv-concat-right-identification-coherence-square-identificationsᵉ =
    is-section-inv-concat'ᵉ (apᵉ (concatᵉ topᵉ _) sᵉ)

  is-retraction-inv-concat-right-identification-coherence-square-identificationsᵉ :
    is-retractionᵉ
      concat-right-identification-coherence-square-identificationsᵉ
      inv-concat-right-identification-coherence-square-identificationsᵉ
  is-retraction-inv-concat-right-identification-coherence-square-identificationsᵉ =
    is-retraction-inv-concat'ᵉ (apᵉ (concatᵉ topᵉ _) sᵉ)
```

Weᵉ record thatᵉ thisᵉ constructionᵉ isᵉ anᵉ equivalenceᵉ in
[`foundation.commuting-squares-of-identifications`](foundation.commuting-squares-of-identifications.md).ᵉ

#### Concatenating identifications of the bottom edge with a coherence of a commuting square of identifications

Considerᵉ aᵉ commutingᵉ diagramᵉ ofᵉ identificationsᵉ

```text
            topᵉ
       xᵉ ------->ᵉ yᵉ
       |          |
  leftᵉ |          | rightᵉ
       ∨ᵉ  bottomᵉ  ∨ᵉ
       zᵉ ------->ᵉ w.ᵉ
         ------->ᵉ
          bottom'ᵉ
```

with anᵉ identificationᵉ `bottomᵉ ＝ᵉ bottom'`.ᵉ Thenᵉ weᵉ getᵉ anᵉ equivalenceᵉ

```text
           topᵉ                             topᵉ
       xᵉ ------->ᵉ yᵉ                    xᵉ ------->ᵉ yᵉ
       |          |                    |          |
  leftᵉ |          | rightᵉ    ≃ᵉ    leftᵉ |          | rightᵉ
       ∨ᵉ          ∨ᵉ                    ∨ᵉ          ∨ᵉ
       zᵉ ------->ᵉ wᵉ                    zᵉ ------->ᵉ w.ᵉ
          bottomᵉ                          bottom'ᵉ
```

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {xᵉ yᵉ zᵉ wᵉ : Aᵉ}
  (topᵉ : xᵉ ＝ᵉ yᵉ) (leftᵉ : xᵉ ＝ᵉ zᵉ) (rightᵉ : yᵉ ＝ᵉ wᵉ) (bottomᵉ : zᵉ ＝ᵉ wᵉ)
  {bottom'ᵉ : zᵉ ＝ᵉ wᵉ} (sᵉ : bottomᵉ ＝ᵉ bottom'ᵉ)
  where

  concat-bottom-identification-coherence-square-identificationsᵉ :
    coherence-square-identificationsᵉ topᵉ leftᵉ rightᵉ bottomᵉ →
    coherence-square-identificationsᵉ topᵉ leftᵉ rightᵉ bottom'ᵉ
  concat-bottom-identification-coherence-square-identificationsᵉ tᵉ =
    invᵉ (apᵉ (concatᵉ leftᵉ _) sᵉ) ∙ᵉ tᵉ

  inv-concat-bottom-identification-coherence-square-identificationsᵉ :
    coherence-square-identificationsᵉ topᵉ leftᵉ rightᵉ bottom'ᵉ →
    coherence-square-identificationsᵉ topᵉ leftᵉ rightᵉ bottomᵉ
  inv-concat-bottom-identification-coherence-square-identificationsᵉ tᵉ =
    apᵉ (concatᵉ leftᵉ _) sᵉ ∙ᵉ tᵉ

  is-section-inv-concat-bottom-identification-coherence-square-identificationsᵉ :
    is-sectionᵉ
      concat-bottom-identification-coherence-square-identificationsᵉ
      inv-concat-bottom-identification-coherence-square-identificationsᵉ
  is-section-inv-concat-bottom-identification-coherence-square-identificationsᵉ =
    is-retraction-inv-concatᵉ (apᵉ (concatᵉ leftᵉ _) sᵉ)

  is-retraction-inv-concat-bottom-identification-coherence-square-identificationsᵉ :
    is-retractionᵉ
      concat-bottom-identification-coherence-square-identificationsᵉ
      inv-concat-bottom-identification-coherence-square-identificationsᵉ
  is-retraction-inv-concat-bottom-identification-coherence-square-identificationsᵉ =
    is-section-inv-concatᵉ (apᵉ (concatᵉ leftᵉ _) sᵉ)
```

Weᵉ record thatᵉ thisᵉ constructionᵉ isᵉ anᵉ equivalenceᵉ in
[`foundation.commuting-squares-of-identifications`](foundation.commuting-squares-of-identifications.md).ᵉ

### Whiskering and splicing coherences of commuting squares of identifications

Givenᵉ aᵉ commutingᵉ squareᵉ ofᵉ identificationsᵉ

```text
           topᵉ
       xᵉ ------->ᵉ yᵉ
       |          |
  leftᵉ |          | rightᵉ
       ∨ᵉ          ∨ᵉ
       zᵉ ------->ᵉ w,ᵉ
          bottomᵉ
```

weᵉ mayᵉ considerᵉ fourᵉ waysᵉ ofᵉ attachingᵉ newᵉ identificationsᵉ to itᵉ:

1.ᵉ Prependingᵉ `pᵉ : uᵉ ＝ᵉ x`ᵉ to theᵉ leftᵉ givesᵉ usᵉ aᵉ commutingᵉ squareᵉ

   ```text
                pᵉ ∙ᵉ topᵉ
              uᵉ ------->ᵉ yᵉ
              |          |
     pᵉ ∙ᵉ leftᵉ |          | rightᵉ
              ∨ᵉ          ∨ᵉ
              zᵉ ------->ᵉ w.ᵉ
                 bottomᵉ
   ```

   Moreᵉ precisely,ᵉ weᵉ haveᵉ anᵉ equivalenceᵉ

   ```text
     (leftᵉ ∙ᵉ bottomᵉ ＝ᵉ topᵉ ∙ᵉ rightᵉ) ≃ᵉ ((pᵉ ∙ᵉ leftᵉ) ∙ᵉ bottomᵉ ＝ᵉ (pᵉ ∙ᵉ topᵉ) ∙ᵉ right).ᵉ
   ```

2.ᵉ Appendingᵉ anᵉ identificationᵉ `pᵉ : wᵉ ＝ᵉ u`ᵉ to theᵉ rightᵉ givesᵉ aᵉ commutingᵉ
   squareᵉ ofᵉ identificationsᵉ

   ```text
                   topᵉ
           xᵉ ------------>ᵉ yᵉ
           |               |
      leftᵉ |               | rightᵉ ∙ᵉ pᵉ
           ∨ᵉ               ∨ᵉ
           zᵉ ------------>ᵉ u.ᵉ
              bottomᵉ ∙ᵉ pᵉ
   ```

   Moreᵉ precisely,ᵉ weᵉ haveᵉ anᵉ equivalenceᵉ

   ```text
     (leftᵉ ∙ᵉ bottomᵉ ＝ᵉ topᵉ ∙ᵉ rightᵉ) ≃ᵉ (leftᵉ ∙ᵉ (bottomᵉ ∙ᵉ pᵉ) ＝ᵉ topᵉ ∙ᵉ (rightᵉ ∙ᵉ p)).ᵉ
   ```

3.ᵉ Splicingᵉ anᵉ identificationᵉ `pᵉ : zᵉ ＝ᵉ u`ᵉ andᵉ itsᵉ inverseᵉ intoᵉ theᵉ middleᵉ givesᵉ
   aᵉ commutingᵉ squareᵉ ofᵉ identificationsᵉ

   ```text
                      topᵉ
              xᵉ -------------->ᵉ yᵉ
              |                 |
     leftᵉ ∙ᵉ pᵉ |                 | rightᵉ
              ∨ᵉ                 ∨ᵉ
              uᵉ -------------->ᵉ w.ᵉ
                 p⁻¹ᵉ ∙ᵉ bottomᵉ
   ```

   Moreᵉ precisely,ᵉ weᵉ haveᵉ anᵉ equivalenceᵉ

   ```text
     (leftᵉ ∙ᵉ bottomᵉ ＝ᵉ topᵉ ∙ᵉ rightᵉ) ≃ᵉ ((leftᵉ ∙ᵉ pᵉ) ∙ᵉ (p⁻¹ᵉ ∙ᵉ bottomᵉ) ＝ᵉ topᵉ ∙ᵉ right).ᵉ
   ```

   Similarly,ᵉ weᵉ haveᵉ anᵉ equivalenceᵉ

   ```text
     (leftᵉ ∙ᵉ bottomᵉ ＝ᵉ topᵉ ∙ᵉ rightᵉ) ≃ᵉ ((leftᵉ ∙ᵉ p⁻¹ᵉ) ∙ᵉ (pᵉ ∙ᵉ bottomᵉ) ＝ᵉ topᵉ ∙ᵉ right).ᵉ
   ```

4.ᵉ Splicingᵉ anᵉ identificationᵉ `pᵉ : yᵉ ＝ᵉ u`ᵉ andᵉ itsᵉ inverseᵉ intoᵉ theᵉ middleᵉ givesᵉ
   aᵉ commutingᵉ squareᵉ ofᵉ identificationsᵉ

   ```text
             topᵉ ∙ᵉ pᵉ
          xᵉ -------->ᵉ uᵉ
          |           |
     leftᵉ |           | p⁻¹ᵉ ∙ᵉ rightᵉ
          ∨ᵉ           ∨ᵉ
          zᵉ -------->ᵉ w.ᵉ
             bottomᵉ
   ```

   Moreᵉ precisely,ᵉ weᵉ haveᵉ anᵉ equivalenceᵉ

   ```text
     (leftᵉ ∙ᵉ bottomᵉ ＝ᵉ topᵉ ∙ᵉ rightᵉ) ≃ᵉ (leftᵉ ∙ᵉ bottomᵉ ＝ᵉ (topᵉ ∙ᵉ pᵉ) ∙ᵉ (p⁻¹ᵉ ∙ᵉ right)).ᵉ
   ```

   Similarly,ᵉ weᵉ haveᵉ anᵉ equivalenceᵉ

   ```text
     (leftᵉ ∙ᵉ bottomᵉ ＝ᵉ topᵉ ∙ᵉ rightᵉ) ≃ᵉ (leftᵉ ∙ᵉ bottomᵉ ＝ᵉ (topᵉ ∙ᵉ p⁻¹ᵉ) ∙ᵉ (pᵉ ∙ᵉ right)).ᵉ
   ```

Theseᵉ operationsᵉ areᵉ usefulᵉ in proofsᵉ involvingᵉ pathᵉ algebra,ᵉ becauseᵉ takingᵉ
`equiv-right-whisker-concat-coherence-square-identifications`ᵉ asᵉ anᵉ example,ᵉ itᵉ
providesᵉ usᵉ with twoᵉ mapsᵉ: theᵉ forwardᵉ directionᵉ statesᵉ
`(pᵉ ∙ᵉ rᵉ ＝ᵉ qᵉ ∙ᵉ sᵉ) → (pᵉ ∙ᵉ (rᵉ ∙ᵉ tᵉ)) ＝ᵉ qᵉ ∙ᵉ (sᵉ ∙ᵉ t))`,ᵉ whichᵉ allowsᵉ oneᵉ to appendᵉ
anᵉ identificationᵉ withoutᵉ needingᵉ to reassociateᵉ onᵉ theᵉ right,ᵉ andᵉ theᵉ backwardsᵉ
directionᵉ converselyᵉ allowsᵉ oneᵉ to cancelᵉ outᵉ anᵉ identificationᵉ in parentheses.ᵉ

#### Left whiskering coherences of commuting squares of identifications

Forᵉ anyᵉ identificationᵉ `pᵉ : uᵉ ＝ᵉ x`ᵉ weᵉ obtainᵉ anᵉ equivalenceᵉ

```text
           topᵉ                                pᵉ ∙ᵉ topᵉ
       xᵉ ------->ᵉ yᵉ                         uᵉ ------->ᵉ yᵉ
       |          |                         |          |
  leftᵉ |          | rightᵉ    ≃ᵉ     pᵉ ∙ᵉ leftᵉ |          | rightᵉ
       ∨ᵉ          ∨ᵉ                         ∨ᵉ          ∨ᵉ
       zᵉ ------->ᵉ wᵉ                         zᵉ ------->ᵉ wᵉ
          bottomᵉ                               bottomᵉ
```

ofᵉ coherencesᵉ ofᵉ commutingᵉ squaresᵉ ofᵉ identifications.ᵉ

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {xᵉ yᵉ zᵉ wᵉ uᵉ : Aᵉ}
  where

  left-whisker-concat-coherence-square-identificationsᵉ :
    (pᵉ : uᵉ ＝ᵉ xᵉ)
    (topᵉ : xᵉ ＝ᵉ yᵉ) (leftᵉ : xᵉ ＝ᵉ zᵉ) (rightᵉ : yᵉ ＝ᵉ wᵉ) (bottomᵉ : zᵉ ＝ᵉ wᵉ) →
    coherence-square-identificationsᵉ topᵉ leftᵉ rightᵉ bottomᵉ →
    coherence-square-identificationsᵉ (pᵉ ∙ᵉ topᵉ) (pᵉ ∙ᵉ leftᵉ) rightᵉ bottomᵉ
  left-whisker-concat-coherence-square-identificationsᵉ
    reflᵉ topᵉ leftᵉ rightᵉ bottomᵉ =
    idᵉ

  left-unwhisker-concat-coherence-square-identificationsᵉ :
    (pᵉ : uᵉ ＝ᵉ xᵉ)
    (topᵉ : xᵉ ＝ᵉ yᵉ) (leftᵉ : xᵉ ＝ᵉ zᵉ) (rightᵉ : yᵉ ＝ᵉ wᵉ) (bottomᵉ : zᵉ ＝ᵉ wᵉ) →
    coherence-square-identificationsᵉ (pᵉ ∙ᵉ topᵉ) (pᵉ ∙ᵉ leftᵉ) rightᵉ bottomᵉ →
    coherence-square-identificationsᵉ topᵉ leftᵉ rightᵉ bottomᵉ
  left-unwhisker-concat-coherence-square-identificationsᵉ
    reflᵉ topᵉ leftᵉ rightᵉ bottomᵉ =
    idᵉ
```

#### Right whiskering coherences of commuting squares of identifications

Forᵉ anyᵉ identificationᵉ `pᵉ : wᵉ ＝ᵉ u`ᵉ weᵉ obtainᵉ anᵉ equivalenceᵉ

```text
           topᵉ                                 topᵉ
       xᵉ ------->ᵉ yᵉ                     xᵉ ------------>ᵉ yᵉ
       |          |                     |               |
  leftᵉ |          | rightᵉ    ≃ᵉ     leftᵉ |               | rightᵉ ∙ᵉ pᵉ
       ∨ᵉ          ∨ᵉ                     ∨ᵉ               ∨ᵉ
       zᵉ ------->ᵉ wᵉ                     zᵉ ------------>ᵉ wᵉ
          bottomᵉ                           bottomᵉ ∙ᵉ pᵉ
```

ofᵉ coherencesᵉ ofᵉ commutingᵉ squaresᵉ ofᵉ identifications.ᵉ

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {xᵉ yᵉ zᵉ wᵉ : Aᵉ}
  (topᵉ : xᵉ ＝ᵉ yᵉ) (leftᵉ : xᵉ ＝ᵉ zᵉ) (rightᵉ : yᵉ ＝ᵉ wᵉ) (bottomᵉ : zᵉ ＝ᵉ wᵉ)
  where

  right-whisker-concat-coherence-square-identificationsᵉ :
    coherence-square-identificationsᵉ topᵉ leftᵉ rightᵉ bottomᵉ →
    {uᵉ : Aᵉ} (pᵉ : wᵉ ＝ᵉ uᵉ) →
    coherence-square-identificationsᵉ topᵉ leftᵉ (rightᵉ ∙ᵉ pᵉ) (bottomᵉ ∙ᵉ pᵉ)
  right-whisker-concat-coherence-square-identificationsᵉ sᵉ reflᵉ =
    concat-bottom-identification-coherence-square-identificationsᵉ
      ( topᵉ)
      ( leftᵉ)
      ( rightᵉ ∙ᵉ reflᵉ)
      ( bottomᵉ)
      ( invᵉ right-unitᵉ)
      ( concat-right-identification-coherence-square-identificationsᵉ
        ( topᵉ)
        ( leftᵉ)
        ( rightᵉ)
        ( bottomᵉ)
        ( invᵉ right-unitᵉ)
        ( sᵉ))

  right-unwhisker-cohernece-square-identificationsᵉ :
    {uᵉ : Aᵉ} (pᵉ : wᵉ ＝ᵉ uᵉ) →
    coherence-square-identificationsᵉ topᵉ leftᵉ (rightᵉ ∙ᵉ pᵉ) (bottomᵉ ∙ᵉ pᵉ) →
    coherence-square-identificationsᵉ topᵉ leftᵉ rightᵉ bottomᵉ
  right-unwhisker-cohernece-square-identificationsᵉ reflᵉ =
    ( inv-concat-right-identification-coherence-square-identificationsᵉ
      ( topᵉ)
      ( leftᵉ)
      ( rightᵉ)
      ( bottomᵉ)
      ( invᵉ right-unitᵉ)) ∘ᵉ
    ( inv-concat-bottom-identification-coherence-square-identificationsᵉ
      ( topᵉ)
      ( leftᵉ)
      ( rightᵉ ∙ᵉ reflᵉ)
      ( bottomᵉ)
      ( invᵉ right-unitᵉ))
```

### Double whiskering of commuting squares of identifications

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {xᵉ yᵉ zᵉ uᵉ vᵉ wᵉ : Aᵉ}
  where

  double-whisker-coherence-square-identificationsᵉ :
    (pᵉ : xᵉ ＝ᵉ yᵉ)
    (topᵉ : yᵉ ＝ᵉ uᵉ) (leftᵉ : yᵉ ＝ᵉ zᵉ) (rightᵉ : uᵉ ＝ᵉ vᵉ) (bottomᵉ : zᵉ ＝ᵉ vᵉ)
    (sᵉ : vᵉ ＝ᵉ wᵉ) →
    coherence-square-identificationsᵉ topᵉ leftᵉ rightᵉ bottomᵉ →
    coherence-square-identificationsᵉ
      ( pᵉ ∙ᵉ topᵉ)
      ( pᵉ ∙ᵉ leftᵉ)
      ( rightᵉ ∙ᵉ sᵉ)
      ( bottomᵉ ∙ᵉ sᵉ)
  double-whisker-coherence-square-identificationsᵉ
    pᵉ topᵉ leftᵉ rightᵉ bottomᵉ qᵉ Hᵉ =
    left-whisker-concat-coherence-square-identificationsᵉ pᵉ topᵉ leftᵉ
      ( rightᵉ ∙ᵉ qᵉ)
      ( bottomᵉ ∙ᵉ qᵉ)
    ( right-whisker-concat-coherence-square-identificationsᵉ
      ( topᵉ)
      ( leftᵉ)
      ( rightᵉ)
      ( bottomᵉ)
      ( Hᵉ)
      ( qᵉ))
```

#### Left splicing coherences of commuting squares of identifications

Forᵉ anyᵉ inverseᵉ pairᵉ ofᵉ identificationsᵉ `pᵉ : yᵉ ＝ᵉ u`ᵉ andᵉ `qᵉ : uᵉ ＝ᵉ y`ᵉ equippedᵉ
with `αᵉ : invᵉ pᵉ ＝ᵉ q`ᵉ weᵉ obtainᵉ anᵉ equivalenceᵉ

```text
           topᵉ                                    topᵉ
       xᵉ ------->ᵉ yᵉ                         xᵉ ----------->ᵉ yᵉ
       |          |                         |              |
  leftᵉ |          | rightᵉ    ≃ᵉ     leftᵉ ∙ᵉ pᵉ |              | rightᵉ
       ∨ᵉ          ∨ᵉ                         ∨ᵉ              ∨ᵉ
       zᵉ ------->ᵉ wᵉ                         uᵉ ----------->ᵉ wᵉ
          bottomᵉ                               qᵉ ∙ᵉ bottomᵉ
```

ofᵉ coherencesᵉ ofᵉ commutingᵉ squaresᵉ ofᵉ identifications.ᵉ

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {xᵉ yᵉ zᵉ wᵉ : Aᵉ}
  (topᵉ : xᵉ ＝ᵉ yᵉ) (leftᵉ : xᵉ ＝ᵉ zᵉ) (rightᵉ : yᵉ ＝ᵉ wᵉ) (bottomᵉ : zᵉ ＝ᵉ wᵉ)
  where

  left-splice-coherence-square-identificationsᵉ :
    {uᵉ : Aᵉ} (pᵉ : zᵉ ＝ᵉ uᵉ) (qᵉ : uᵉ ＝ᵉ zᵉ) (αᵉ : invᵉ pᵉ ＝ᵉ qᵉ) →
    coherence-square-identificationsᵉ topᵉ leftᵉ rightᵉ bottomᵉ →
    coherence-square-identificationsᵉ topᵉ (leftᵉ ∙ᵉ pᵉ) rightᵉ (qᵉ ∙ᵉ bottomᵉ)
  left-splice-coherence-square-identificationsᵉ reflᵉ .reflᵉ reflᵉ =
    concat-left-identification-coherence-square-identificationsᵉ
      ( topᵉ)
      ( leftᵉ)
      ( rightᵉ)
      ( bottomᵉ)
      ( invᵉ right-unitᵉ)

  left-unsplice-coherence-square-identificationsᵉ :
    {uᵉ : Aᵉ} (pᵉ : zᵉ ＝ᵉ uᵉ) (qᵉ : uᵉ ＝ᵉ zᵉ) (αᵉ : invᵉ pᵉ ＝ᵉ qᵉ) →
    coherence-square-identificationsᵉ topᵉ (leftᵉ ∙ᵉ pᵉ) rightᵉ (qᵉ ∙ᵉ bottomᵉ) →
    coherence-square-identificationsᵉ topᵉ leftᵉ rightᵉ bottomᵉ
  left-unsplice-coherence-square-identificationsᵉ reflᵉ .reflᵉ reflᵉ =
    inv-concat-left-identification-coherence-square-identificationsᵉ
      ( topᵉ)
      ( leftᵉ)
      ( rightᵉ)
      ( bottomᵉ)
      ( invᵉ right-unitᵉ)
```

#### Right splicing coherences of commuting squares of identifications

Forᵉ anyᵉ inverseᵉ pairᵉ ofᵉ identificationsᵉ `pᵉ : yᵉ ＝ᵉ u`ᵉ andᵉ `qᵉ : uᵉ ＝ᵉ y`ᵉ equippedᵉ
with `αᵉ : invᵉ pᵉ ＝ᵉ q`ᵉ weᵉ obtainᵉ anᵉ equivalenceᵉ

```text
           topᵉ                             topᵉ ∙ᵉ pᵉ
       xᵉ ------->ᵉ yᵉ                     xᵉ -------->ᵉ uᵉ
       |          |                     |           |
  leftᵉ |          | rightᵉ    ≃ᵉ     leftᵉ |           | qᵉ ∙ᵉ rightᵉ
       ∨ᵉ          ∨ᵉ                     ∨ᵉ           ∨ᵉ
       zᵉ ------->ᵉ wᵉ                     zᵉ -------->ᵉ wᵉ
          bottomᵉ                           bottomᵉ
```

ofᵉ coherencesᵉ ofᵉ commutingᵉ squaresᵉ ofᵉ identifications.ᵉ

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {xᵉ yᵉ zᵉ wᵉ : Aᵉ}
  (topᵉ : xᵉ ＝ᵉ yᵉ) (leftᵉ : xᵉ ＝ᵉ zᵉ) (rightᵉ : yᵉ ＝ᵉ wᵉ) (bottomᵉ : zᵉ ＝ᵉ wᵉ)
  where

  right-splice-coherence-square-identificationsᵉ :
    {uᵉ : Aᵉ} (pᵉ : yᵉ ＝ᵉ uᵉ) (qᵉ : uᵉ ＝ᵉ yᵉ) (αᵉ : invᵉ pᵉ ＝ᵉ qᵉ) →
    coherence-square-identificationsᵉ topᵉ leftᵉ rightᵉ bottomᵉ →
    coherence-square-identificationsᵉ (topᵉ ∙ᵉ pᵉ) leftᵉ (invᵉ pᵉ ∙ᵉ rightᵉ) bottomᵉ
  right-splice-coherence-square-identificationsᵉ reflᵉ .reflᵉ reflᵉ =
    concat-top-identification-coherence-square-identificationsᵉ
      ( topᵉ)
      ( leftᵉ)
      ( rightᵉ)
      ( bottomᵉ)
      ( invᵉ right-unitᵉ)

  right-unsplice-coherence-square-identificationsᵉ :
    {uᵉ : Aᵉ} (pᵉ : yᵉ ＝ᵉ uᵉ) (qᵉ : uᵉ ＝ᵉ yᵉ) (αᵉ : invᵉ pᵉ ＝ᵉ qᵉ) →
    coherence-square-identificationsᵉ (topᵉ ∙ᵉ pᵉ) leftᵉ (invᵉ pᵉ ∙ᵉ rightᵉ) bottomᵉ →
    coherence-square-identificationsᵉ topᵉ leftᵉ rightᵉ bottomᵉ
  right-unsplice-coherence-square-identificationsᵉ reflᵉ .reflᵉ reflᵉ =
    inv-concat-top-identification-coherence-square-identificationsᵉ
      ( topᵉ)
      ( leftᵉ)
      ( rightᵉ)
      ( bottomᵉ)
      ( invᵉ right-unitᵉ)
```

### Horizontally pasting squares of identifications

Considerᵉ twoᵉ squaresᵉ ofᵉ identificationsᵉ asᵉ in theᵉ diagramᵉ

```text
            top-leftᵉ         top-rightᵉ
       aᵉ ------------->ᵉ bᵉ ------------->ᵉ cᵉ
       |                |                |
  leftᵉ |                | middleᵉ         | rightᵉ
       ∨ᵉ                ∨ᵉ                ∨ᵉ
       dᵉ ------------->ᵉ eᵉ ------------->ᵉ fᵉ
          bottom-leftᵉ      bottom-rightᵉ
```

with `sᵉ : leftᵉ ∙ᵉ bottom-leftᵉ ＝ᵉ top-leftᵉ ∙ᵉ middle`ᵉ andᵉ
`tᵉ : middleᵉ ∙ᵉ bottom-rightᵉ ＝ᵉ top-rightᵉ ∙ᵉ right`.ᵉ Thenᵉ theᵉ outerᵉ squareᵉ
commutes.ᵉ

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {aᵉ bᵉ cᵉ dᵉ eᵉ fᵉ : Aᵉ}
  (top-leftᵉ : aᵉ ＝ᵉ bᵉ) (top-rightᵉ : bᵉ ＝ᵉ cᵉ)
  (leftᵉ : aᵉ ＝ᵉ dᵉ) (middleᵉ : bᵉ ＝ᵉ eᵉ) (rightᵉ : cᵉ ＝ᵉ fᵉ)
  (bottom-leftᵉ : dᵉ ＝ᵉ eᵉ) (bottom-rightᵉ : eᵉ ＝ᵉ fᵉ)
  where

  horizontal-pasting-coherence-square-identificationsᵉ :
    coherence-square-identificationsᵉ top-leftᵉ leftᵉ middleᵉ bottom-leftᵉ →
    coherence-square-identificationsᵉ top-rightᵉ middleᵉ rightᵉ bottom-rightᵉ →
    coherence-square-identificationsᵉ
      (top-leftᵉ ∙ᵉ top-rightᵉ) leftᵉ rightᵉ (bottom-leftᵉ ∙ᵉ bottom-rightᵉ)
  horizontal-pasting-coherence-square-identificationsᵉ sᵉ tᵉ =
    ( right-whisker-concat-coherence-square-identificationsᵉ
      ( top-leftᵉ)
      ( leftᵉ)
      ( middleᵉ)
      ( bottom-leftᵉ)
      ( sᵉ)
      ( bottom-rightᵉ)) ∙ᵉ
    ( ( invᵉ (assocᵉ top-leftᵉ middleᵉ bottom-rightᵉ)) ∙ᵉ
      ( left-whisker-concat-coherence-square-identificationsᵉ
        ( top-leftᵉ)
        ( top-rightᵉ)
        ( middleᵉ)
        ( rightᵉ)
        ( bottom-rightᵉ)
        ( tᵉ)))
```

### Vertically pasting squares of identifications

Considerᵉ twoᵉ squaresᵉ ofᵉ identificationsᵉ asᵉ in theᵉ diagramᵉ

```text
                  topᵉ
              aᵉ -------->ᵉ bᵉ
              |           |
     top-leftᵉ |           | top-rightᵉ
              ∨ᵉ  middleᵉ   ∨ᵉ
              cᵉ -------->ᵉ dᵉ
              |           |
  bottom-leftᵉ |           | bottom-rightᵉ
              ∨ᵉ           ∨ᵉ
              eᵉ -------->ᵉ fᵉ
                 bottomᵉ
```

with `sᵉ : top-leftᵉ ∙ᵉ middleᵉ ＝ᵉ topᵉ ∙ᵉ top-right`ᵉ andᵉ
`tᵉ : bottom-leftᵉ ∙ᵉ bottomᵉ ＝ᵉ middleᵉ ∙ᵉ bottom-right`.ᵉ Thenᵉ theᵉ outerᵉ squareᵉ
commutes.ᵉ

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {aᵉ bᵉ cᵉ dᵉ eᵉ fᵉ : Aᵉ}
  (topᵉ : aᵉ ＝ᵉ bᵉ) (top-leftᵉ : aᵉ ＝ᵉ cᵉ) (top-rightᵉ : bᵉ ＝ᵉ dᵉ)
  (middleᵉ : cᵉ ＝ᵉ dᵉ) (bottom-leftᵉ : cᵉ ＝ᵉ eᵉ) (bottom-rightᵉ : dᵉ ＝ᵉ fᵉ)
  (bottomᵉ : eᵉ ＝ᵉ fᵉ)
  where

  vertical-pasting-coherence-square-identificationsᵉ :
    coherence-square-identificationsᵉ topᵉ top-leftᵉ top-rightᵉ middleᵉ →
    coherence-square-identificationsᵉ middleᵉ bottom-leftᵉ bottom-rightᵉ bottomᵉ →
    coherence-square-identificationsᵉ
      topᵉ (top-leftᵉ ∙ᵉ bottom-leftᵉ) (top-rightᵉ ∙ᵉ bottom-rightᵉ) bottomᵉ
  vertical-pasting-coherence-square-identificationsᵉ sᵉ tᵉ =
    ( left-whisker-concat-coherence-square-identificationsᵉ
      ( top-leftᵉ)
      ( middleᵉ)
      ( bottom-leftᵉ)
      ( bottom-rightᵉ)
      ( bottomᵉ)
      ( tᵉ)) ∙ᵉ
    ( ( assocᵉ top-leftᵉ middleᵉ bottom-rightᵉ) ∙ᵉ
      ( right-whisker-concat-coherence-square-identificationsᵉ
        ( topᵉ)
        ( top-leftᵉ)
        ( top-rightᵉ)
        ( middleᵉ)
        ( sᵉ)
        ( bottom-rightᵉ)))
```

## Properties

### Left unit law for horizontal pasting of commuting squares of identifications

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {aᵉ bᵉ cᵉ dᵉ : Aᵉ}
  where

  left-unit-law-horizontal-pasting-coherence-square-identificationsᵉ :
    (topᵉ : aᵉ ＝ᵉ bᵉ) (leftᵉ : aᵉ ＝ᵉ cᵉ) (rightᵉ : bᵉ ＝ᵉ dᵉ) (bottomᵉ : cᵉ ＝ᵉ dᵉ)
    (sᵉ : coherence-square-identificationsᵉ topᵉ leftᵉ rightᵉ bottomᵉ) →
    horizontal-pasting-coherence-square-identificationsᵉ
      ( reflᵉ)
      ( topᵉ)
      ( leftᵉ)
      ( leftᵉ)
      ( rightᵉ)
      ( reflᵉ)
      ( bottomᵉ)
      ( horizontal-refl-coherence-square-identificationsᵉ leftᵉ)
      ( sᵉ) ＝ᵉ
    sᵉ
  left-unit-law-horizontal-pasting-coherence-square-identificationsᵉ
    reflᵉ reflᵉ rightᵉ reflᵉ sᵉ = reflᵉ
```

### Right unit law for horizontal pasting of commuting squares of identifications

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {aᵉ bᵉ cᵉ dᵉ : Aᵉ}
  where

  right-unit-law-horizontal-pasting-coherence-square-identificationsᵉ :
    (topᵉ : aᵉ ＝ᵉ bᵉ) (leftᵉ : aᵉ ＝ᵉ cᵉ) (rightᵉ : bᵉ ＝ᵉ dᵉ) (bottomᵉ : cᵉ ＝ᵉ dᵉ)
    (sᵉ : coherence-square-identificationsᵉ topᵉ leftᵉ rightᵉ bottomᵉ) →
    horizontal-pasting-coherence-square-identificationsᵉ
      ( topᵉ)
      ( reflᵉ)
      ( leftᵉ)
      ( rightᵉ)
      ( rightᵉ)
      ( bottomᵉ)
      ( reflᵉ)
      ( sᵉ)
      ( horizontal-refl-coherence-square-identificationsᵉ rightᵉ) ∙ᵉ
    right-whisker-concatᵉ right-unitᵉ rightᵉ ＝ᵉ
    left-whisker-concatᵉ leftᵉ right-unitᵉ ∙ᵉ sᵉ
  right-unit-law-horizontal-pasting-coherence-square-identificationsᵉ
    reflᵉ reflᵉ .reflᵉ reflᵉ reflᵉ =
    reflᵉ
```

### Left unit law for vertical pasting of commuting squares of identifications

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {aᵉ bᵉ cᵉ dᵉ : Aᵉ}
  where

  left-unit-law-vertical-pasting-coherence-square-identificationsᵉ :
    (topᵉ : aᵉ ＝ᵉ bᵉ) (leftᵉ : aᵉ ＝ᵉ cᵉ) (rightᵉ : bᵉ ＝ᵉ dᵉ) (bottomᵉ : cᵉ ＝ᵉ dᵉ)
    (sᵉ : coherence-square-identificationsᵉ topᵉ leftᵉ rightᵉ bottomᵉ) →
    vertical-pasting-coherence-square-identificationsᵉ
      ( topᵉ)
      ( reflᵉ)
      ( reflᵉ)
      ( topᵉ)
      ( leftᵉ)
      ( rightᵉ)
      ( bottomᵉ)
      ( vertical-refl-coherence-square-identificationsᵉ topᵉ)
      ( sᵉ) ＝ᵉ
    sᵉ
  left-unit-law-vertical-pasting-coherence-square-identificationsᵉ
    reflᵉ reflᵉ .reflᵉ reflᵉ reflᵉ = reflᵉ
```

### Right unit law for vertical pasting of commuting squares of identifications

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {aᵉ bᵉ cᵉ dᵉ : Aᵉ}
  where

  right-unit-law-vertical-pasting-coherence-square-identificationsᵉ :
    (topᵉ : aᵉ ＝ᵉ bᵉ) (leftᵉ : aᵉ ＝ᵉ cᵉ) (rightᵉ : bᵉ ＝ᵉ dᵉ) (bottomᵉ : cᵉ ＝ᵉ dᵉ)
    (sᵉ : coherence-square-identificationsᵉ topᵉ leftᵉ rightᵉ bottomᵉ) →
    vertical-pasting-coherence-square-identificationsᵉ
      ( topᵉ)
      ( leftᵉ)
      ( rightᵉ)
      ( bottomᵉ)
      ( reflᵉ)
      ( reflᵉ)
      ( bottomᵉ)
      ( sᵉ)
      ( vertical-refl-coherence-square-identificationsᵉ bottomᵉ) ∙ᵉ
    left-whisker-concatᵉ topᵉ right-unitᵉ ＝ᵉ
    right-whisker-concatᵉ right-unitᵉ bottomᵉ ∙ᵉ sᵉ
  right-unit-law-vertical-pasting-coherence-square-identificationsᵉ
    reflᵉ reflᵉ .(reflᵉ ∙ᵉ reflᵉ) reflᵉ reflᵉ =
    reflᵉ
```

### Computing the right whiskering of a vertically constant square with an identification

Considerᵉ theᵉ verticallyᵉ constantᵉ squareᵉ ofᵉ identificationsᵉ

```text
           pᵉ
       xᵉ ----->ᵉ yᵉ
       |        |
  reflᵉ |        | reflᵉ
       ∨ᵉ        ∨ᵉ
       xᵉ ----->ᵉ yᵉ
           pᵉ
```

atᵉ anᵉ identificationᵉ `pᵉ : xᵉ ＝ᵉ y`,ᵉ andᵉ considerᵉ anᵉ identificationᵉ `qᵉ : yᵉ ＝ᵉ z`.ᵉ
Thenᵉ theᵉ rightᵉ whiskeringᵉ ofᵉ theᵉ aboveᵉ squareᵉ with `q`ᵉ isᵉ theᵉ commutingᵉ squareᵉ
ofᵉ identificationsᵉ

```text
            pᵉ
       xᵉ ------->ᵉ yᵉ
       |          |
  reflᵉ |   reflᵉ   | qᵉ
       ∨ᵉ          ∨ᵉ
       xᵉ ------->ᵉ zᵉ
          pᵉ ∙ᵉ qᵉ
```

```agda
module _
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  where

  right-whisker-concat-vertical-refl-coherence-square-identificationsᵉ :
    {xᵉ yᵉ zᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) (qᵉ : yᵉ ＝ᵉ zᵉ) →
    right-whisker-concat-coherence-square-identificationsᵉ pᵉ reflᵉ reflᵉ pᵉ
      ( vertical-refl-coherence-square-identificationsᵉ pᵉ)
      ( qᵉ) ＝ᵉ
    reflᵉ
  right-whisker-concat-vertical-refl-coherence-square-identificationsᵉ
    reflᵉ reflᵉ =
    reflᵉ
```

### Computing the right whiskering of a horizontally constant square with an identification

Considerᵉ aᵉ horizontallyᵉ constantᵉ commutingᵉ squareᵉ ofᵉ identificationsᵉ

```text
       reflᵉ
    xᵉ ----->ᵉ xᵉ
    |        |
  pᵉ |        | pᵉ
    ∨ᵉ        ∨ᵉ
    yᵉ ----->ᵉ yᵉ
       reflᵉ
```

atᵉ anᵉ identificationᵉ `p`ᵉ andᵉ considerᵉ anᵉ identificationᵉ `qᵉ : yᵉ ＝ᵉ z`.ᵉ Thenᵉ theᵉ
rightᵉ whiskeringᵉ ofᵉ theᵉ aboveᵉ squareᵉ with `q`ᵉ isᵉ theᵉ squareᵉ

```text
       reflᵉ
    xᵉ ----->ᵉ xᵉ
    |        |
  pᵉ |  reflᵉ  | pᵉ ∙ᵉ qᵉ
    ∨ᵉ        ∨ᵉ
    yᵉ ----->ᵉ z.ᵉ
        qᵉ
```

```agda
module _
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  where

  right-whisker-concat-horizontal-refl-coherence-square-identificationsᵉ :
    {xᵉ yᵉ zᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) (qᵉ : yᵉ ＝ᵉ zᵉ) →
    right-whisker-concat-coherence-square-identificationsᵉ reflᵉ pᵉ pᵉ reflᵉ
      ( horizontal-refl-coherence-square-identificationsᵉ pᵉ)
      ( qᵉ) ＝ᵉ
    reflᵉ
  right-whisker-concat-horizontal-refl-coherence-square-identificationsᵉ
    reflᵉ reflᵉ =
    reflᵉ
```

### Computing the left whiskering of a horizontally constant square with an identification

Considerᵉ anᵉ identificationᵉ `pᵉ : xᵉ ＝ᵉ y`ᵉ andᵉ aᵉ horizontallyᵉ constantᵉ commutingᵉ
squareᵉ ofᵉ identificationsᵉ

```text
       reflᵉ
    yᵉ ----->ᵉ yᵉ
    |        |
  qᵉ |        | qᵉ
    ∨ᵉ        ∨ᵉ
    zᵉ ----->ᵉ zᵉ
       reflᵉ
```

atᵉ anᵉ identificationᵉ `qᵉ : yᵉ ＝ᵉ z`.ᵉ Theᵉ theᵉ leftᵉ whiskeringᵉ ofᵉ theᵉ aboveᵉ squareᵉ
with `p`ᵉ isᵉ theᵉ commutingᵉ squareᵉ

```text
                                  qᵉ ∙ᵉ reflᵉ
        xᵉ ------------------------------------------------------>ᵉ yᵉ
        |                                                         |
  qᵉ ∙ᵉ pᵉ |  right-unitᵉ ∙ᵉ invᵉ (right-whisker-concatᵉ right-unitᵉ pᵉ)   | pᵉ
        ∨ᵉ                                                         ∨ᵉ
        zᵉ ------------------------------------------------------>ᵉ z.ᵉ
                                   reflᵉ
```

```agda
module _
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  where

  left-whisker-concat-horizontal-refl-coherence-square-identificationsᵉ :
    {xᵉ yᵉ zᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) (qᵉ : yᵉ ＝ᵉ zᵉ) →
    left-whisker-concat-coherence-square-identificationsᵉ pᵉ reflᵉ qᵉ qᵉ reflᵉ
      ( horizontal-refl-coherence-square-identificationsᵉ qᵉ) ∙ᵉ
    right-whisker-concatᵉ right-unitᵉ qᵉ ＝ᵉ
    right-unitᵉ
  left-whisker-concat-horizontal-refl-coherence-square-identificationsᵉ
    reflᵉ reflᵉ =
    reflᵉ

  left-whisker-concat-horizontal-refl-coherence-square-identifications'ᵉ :
    {xᵉ yᵉ zᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) (qᵉ : yᵉ ＝ᵉ zᵉ) →
    left-whisker-concat-coherence-square-identificationsᵉ pᵉ reflᵉ qᵉ qᵉ reflᵉ
      ( horizontal-refl-coherence-square-identificationsᵉ qᵉ) ＝ᵉ
    right-unitᵉ ∙ᵉ invᵉ (right-whisker-concatᵉ right-unitᵉ qᵉ)
  left-whisker-concat-horizontal-refl-coherence-square-identifications'ᵉ
    reflᵉ reflᵉ =
    reflᵉ
```

### Computing the left whiskering of a vertically constant square with an identification

Considerᵉ theᵉ verticallyᵉ constantᵉ squareᵉ ofᵉ identificationsᵉ

```text
           qᵉ
       yᵉ ----->ᵉ zᵉ
       |        |
  reflᵉ |        | reflᵉ
       ∨ᵉ        ∨ᵉ
       yᵉ ----->ᵉ zᵉ
           qᵉ
```

atᵉ anᵉ identificationᵉ `qᵉ : yᵉ ＝ᵉ z`ᵉ andᵉ considerᵉ anᵉ identificationᵉ `pᵉ : xᵉ ＝ᵉ y`.ᵉ
Thenᵉ theᵉ leftᵉ whiskeringᵉ ofᵉ theᵉ aboveᵉ squareᵉ with `p`ᵉ isᵉ theᵉ squareᵉ

```text
                                    pᵉ ∙ᵉ qᵉ
           xᵉ --------------------------------------------------->ᵉ zᵉ
           |                                                      |
  pᵉ ∙ᵉ reflᵉ |  right-whisker-concatᵉ right-unitᵉ qᵉ ∙ᵉ invᵉ right-unitᵉ  | reflᵉ
           ∨ᵉ                                                      ∨ᵉ
           yᵉ --------------------------------------------------->ᵉ z.ᵉ
                                      qᵉ
```

```agda
module _
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  where

  left-whisker-concat-vertical-refl-coherence-square-identificationsᵉ :
    {xᵉ yᵉ zᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) (qᵉ : yᵉ ＝ᵉ zᵉ) →
    left-whisker-concat-coherence-square-identificationsᵉ pᵉ qᵉ reflᵉ reflᵉ qᵉ
      ( vertical-refl-coherence-square-identificationsᵉ qᵉ) ∙ᵉ
    right-unitᵉ ＝ᵉ
    right-whisker-concatᵉ right-unitᵉ qᵉ
  left-whisker-concat-vertical-refl-coherence-square-identificationsᵉ
    reflᵉ reflᵉ =
    reflᵉ

  left-whisker-concat-vertical-refl-coherence-square-identifications'ᵉ :
    {xᵉ yᵉ zᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) (qᵉ : yᵉ ＝ᵉ zᵉ) →
    left-whisker-concat-coherence-square-identificationsᵉ pᵉ qᵉ reflᵉ reflᵉ qᵉ
      ( vertical-refl-coherence-square-identificationsᵉ qᵉ) ＝ᵉ
    right-whisker-concatᵉ right-unitᵉ qᵉ ∙ᵉ invᵉ right-unitᵉ
  left-whisker-concat-vertical-refl-coherence-square-identifications'ᵉ
    reflᵉ reflᵉ =
    reflᵉ
```

### Left whiskering horizontal concatenations of squares with identifications

Considerᵉ aᵉ commutingᵉ diagramᵉ ofᵉ identificationsᵉ ofᵉ theᵉ formᵉ

```text
            top-leftᵉ        top-rightᵉ
       aᵉ ------------->ᵉ cᵉ ------------->ᵉ eᵉ
       |                |                |
  leftᵉ |                | middleᵉ         | rightᵉ
       ∨ᵉ                ∨ᵉ                ∨ᵉ
       bᵉ ------------->ᵉ dᵉ ------------->ᵉ fᵉ
          bottom-leftᵉ      bottom-rightᵉ
```

andᵉ considerᵉ anᵉ identificationᵉ `pᵉ : xᵉ ＝ᵉ a`.ᵉ Thenᵉ theᵉ leftᵉ whiskeringᵉ ofᵉ `p`ᵉ andᵉ
theᵉ horizontalᵉ concatenationᵉ ofᵉ coherencesᵉ ofᵉ commutingᵉ squaresᵉ isᵉ upᵉ to
associativityᵉ theᵉ horizontalᵉ concatenationᵉ ofᵉ theᵉ squaresᵉ

```text
              pᵉ ∙ᵉ top-leftᵉ      top-rightᵉ
           xᵉ ------------->ᵉ cᵉ ------------->ᵉ eᵉ
           |                |                |
  pᵉ ∙ᵉ leftᵉ |                | middleᵉ         | rightᵉ
           ∨ᵉ                ∨ᵉ                ∨ᵉ
           bᵉ ------------->ᵉ dᵉ ------------->ᵉ fᵉ
              bottom-leftᵉ      bottom-rightᵉ
```

where theᵉ leftᵉ squareᵉ isᵉ theᵉ leftᵉ whiskeringᵉ ofᵉ `p`ᵉ andᵉ theᵉ originalᵉ leftᵉ
square.ᵉ

```agda
module _
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  where

  left-whisker-concat-horizontal-pasting-coherence-square-identificationsᵉ :
    {xᵉ aᵉ bᵉ cᵉ dᵉ eᵉ fᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ aᵉ)
    (top-leftᵉ : aᵉ ＝ᵉ cᵉ) (top-rightᵉ : cᵉ ＝ᵉ eᵉ)
    (leftᵉ : aᵉ ＝ᵉ bᵉ) (middleᵉ : cᵉ ＝ᵉ dᵉ) (rightᵉ : eᵉ ＝ᵉ fᵉ)
    (bottom-leftᵉ : bᵉ ＝ᵉ dᵉ) (bottom-rightᵉ : dᵉ ＝ᵉ fᵉ)
    (lᵉ : coherence-square-identificationsᵉ top-leftᵉ leftᵉ middleᵉ bottom-leftᵉ)
    (rᵉ : coherence-square-identificationsᵉ top-rightᵉ middleᵉ rightᵉ bottom-rightᵉ) →
    left-whisker-concat-coherence-square-identificationsᵉ pᵉ
      ( top-leftᵉ ∙ᵉ top-rightᵉ)
      ( leftᵉ)
      ( rightᵉ)
      ( bottom-leftᵉ ∙ᵉ bottom-rightᵉ)
      ( horizontal-pasting-coherence-square-identificationsᵉ
        ( top-leftᵉ)
        ( top-rightᵉ)
        ( leftᵉ)
        ( middleᵉ)
        ( rightᵉ)
        ( bottom-leftᵉ)
        ( bottom-rightᵉ)
        ( lᵉ)
        ( rᵉ)) ＝ᵉ
    horizontal-pasting-coherence-square-identificationsᵉ
      ( pᵉ ∙ᵉ top-leftᵉ)
      ( top-rightᵉ)
      ( pᵉ ∙ᵉ leftᵉ)
      ( middleᵉ)
      ( rightᵉ)
      ( bottom-leftᵉ)
      ( bottom-rightᵉ)
      ( left-whisker-concat-coherence-square-identificationsᵉ pᵉ
        ( top-leftᵉ)
        ( leftᵉ)
        ( middleᵉ)
        ( bottom-leftᵉ)
        ( lᵉ))
      ( rᵉ) ∙ᵉ
    right-whisker-concatᵉ
      ( assocᵉ pᵉ top-leftᵉ top-rightᵉ)
      ( rightᵉ)
  left-whisker-concat-horizontal-pasting-coherence-square-identificationsᵉ
    reflᵉ top-leftᵉ top-rightᵉ leftᵉ middleᵉ rightᵉ bottom-leftᵉ bottom-rightᵉ lᵉ rᵉ =
    invᵉ right-unitᵉ
```

### Left whiskering vertical concatenations of squares with identifications

Considerᵉ twoᵉ squaresᵉ ofᵉ identificationsᵉ asᵉ in theᵉ diagramᵉ

```text
                  topᵉ
              aᵉ -------->ᵉ bᵉ
              |           |
     top-leftᵉ |           | top-rightᵉ
              ∨ᵉ  middleᵉ   ∨ᵉ
              cᵉ -------->ᵉ dᵉ
              |           |
  bottom-leftᵉ |           | bottom-rightᵉ
              ∨ᵉ           ∨ᵉ
              eᵉ -------->ᵉ fᵉ
                 bottomᵉ
```

andᵉ considerᵉ anᵉ identificationᵉ `pᵉ : xᵉ ＝ᵉ a`.ᵉ Thenᵉ theᵉ leftᵉ whiskeringᵉ ofᵉ `p`ᵉ
with theᵉ verticalᵉ pastingᵉ ofᵉ theᵉ twoᵉ squaresᵉ aboveᵉ isᵉ upᵉ to associativityᵉ theᵉ
verticalᵉ pastingᵉ ofᵉ theᵉ squaresᵉ

```text
                  pᵉ ∙ᵉ topᵉ
               xᵉ -------->ᵉ bᵉ
               |           |
  pᵉ ∙ᵉ top-leftᵉ |           | top-rightᵉ
               ∨ᵉ  middleᵉ   ∨ᵉ
               cᵉ -------->ᵉ dᵉ
               |           |
   bottom-leftᵉ |           | bottom-rightᵉ
               ∨ᵉ           ∨ᵉ
               eᵉ -------->ᵉ f.ᵉ
                  bottomᵉ
```

```agda
module _
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  where

  left-whisker-concat-vertical-concat-coherence-square-identificationsᵉ :
    {xᵉ aᵉ bᵉ cᵉ dᵉ eᵉ fᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ aᵉ) →
    (topᵉ : aᵉ ＝ᵉ bᵉ) (top-leftᵉ : aᵉ ＝ᵉ cᵉ) (top-rightᵉ : bᵉ ＝ᵉ dᵉ) (middleᵉ : cᵉ ＝ᵉ dᵉ)
    (bottom-leftᵉ : cᵉ ＝ᵉ eᵉ) (bottom-rightᵉ : dᵉ ＝ᵉ fᵉ) (bottomᵉ : eᵉ ＝ᵉ fᵉ)
    (tᵉ : coherence-square-identificationsᵉ topᵉ top-leftᵉ top-rightᵉ middleᵉ) →
    (bᵉ :
      coherence-square-identificationsᵉ middleᵉ bottom-leftᵉ bottom-rightᵉ bottomᵉ) →
    right-whisker-concatᵉ (assocᵉ pᵉ top-leftᵉ bottom-leftᵉ) bottomᵉ ∙ᵉ
    left-whisker-concat-coherence-square-identificationsᵉ pᵉ
      ( topᵉ)
      ( top-leftᵉ ∙ᵉ bottom-leftᵉ)
      ( top-rightᵉ ∙ᵉ bottom-rightᵉ)
      ( bottomᵉ)
      ( vertical-pasting-coherence-square-identificationsᵉ
        ( topᵉ)
        ( top-leftᵉ)
        ( top-rightᵉ)
        ( middleᵉ)
        ( bottom-leftᵉ)
        ( bottom-rightᵉ)
        ( bottomᵉ)
        ( tᵉ)
        ( bᵉ)) ＝ᵉ
    vertical-pasting-coherence-square-identificationsᵉ
      ( pᵉ ∙ᵉ topᵉ)
      ( pᵉ ∙ᵉ top-leftᵉ)
      ( top-rightᵉ)
      ( middleᵉ)
      ( bottom-leftᵉ)
      ( bottom-rightᵉ)
      ( bottomᵉ)
      ( left-whisker-concat-coherence-square-identificationsᵉ pᵉ
        ( topᵉ)
        ( top-leftᵉ)
        ( top-rightᵉ)
        ( middleᵉ)
        ( tᵉ))
      ( bᵉ)
  left-whisker-concat-vertical-concat-coherence-square-identificationsᵉ
    reflᵉ topᵉ top-leftᵉ top-rightᵉ middleᵉ bottom-leftᵉ bottom-rightᵉ bottomᵉ tᵉ bᵉ =
    reflᵉ
```

### Right whiskering horizontal pastings of commuting squares of identifications

Considerᵉ aᵉ commutingᵉ diagramᵉ ofᵉ identificationsᵉ ofᵉ theᵉ formᵉ

```text
            top-leftᵉ        top-rightᵉ
       aᵉ ------------->ᵉ cᵉ ------------->ᵉ eᵉ
       |                |                |
  leftᵉ |                | middleᵉ         | rightᵉ
       ∨ᵉ                ∨ᵉ                ∨ᵉ
       bᵉ ------------->ᵉ dᵉ ------------->ᵉ fᵉ
          bottom-leftᵉ      bottom-rightᵉ
```

andᵉ considerᵉ anᵉ identificationᵉ `qᵉ : fᵉ ＝ᵉ y`.ᵉ Thenᵉ theᵉ rightᵉ whiskeringᵉ ofᵉ theᵉ
horizontalᵉ pastingᵉ ofᵉ theᵉ squaresᵉ aboveᵉ isᵉ upᵉ to associativityᵉ theᵉ horizontalᵉ
pastingᵉ ofᵉ theᵉ squaresᵉ

```text
            top-leftᵉ           top-rightᵉ
       aᵉ ------------->ᵉ cᵉ ------------------>ᵉ eᵉ
       |                |                     |
  leftᵉ |                | middleᵉ              | rightᵉ ∙ᵉ qᵉ
       ∨ᵉ                ∨ᵉ                     ∨ᵉ
       bᵉ ------------->ᵉ dᵉ ------------------>ᵉ yᵉ
          bottom-leftᵉ      bottom-rightᵉ ∙ᵉ qᵉ
```

```agda
module _
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  where

  right-whisker-concat-horizontal-pasting-coherence-square-identificationsᵉ :
    {aᵉ bᵉ cᵉ dᵉ eᵉ fᵉ yᵉ : Aᵉ}
    (top-leftᵉ : aᵉ ＝ᵉ cᵉ) (top-rightᵉ : cᵉ ＝ᵉ eᵉ)
    (leftᵉ : aᵉ ＝ᵉ bᵉ) (middleᵉ : cᵉ ＝ᵉ dᵉ) (rightᵉ : eᵉ ＝ᵉ fᵉ)
    (bottom-leftᵉ : bᵉ ＝ᵉ dᵉ) (bottom-rightᵉ : dᵉ ＝ᵉ fᵉ)
    (lᵉ : coherence-square-identificationsᵉ top-leftᵉ leftᵉ middleᵉ bottom-leftᵉ) →
    (rᵉ : coherence-square-identificationsᵉ top-rightᵉ middleᵉ rightᵉ bottom-rightᵉ) →
    (qᵉ : fᵉ ＝ᵉ yᵉ) →
    right-whisker-concat-coherence-square-identificationsᵉ
      ( top-leftᵉ ∙ᵉ top-rightᵉ)
      ( leftᵉ)
      ( rightᵉ)
      ( bottom-leftᵉ ∙ᵉ bottom-rightᵉ)
      ( horizontal-pasting-coherence-square-identificationsᵉ
        ( top-leftᵉ)
        ( top-rightᵉ)
        ( leftᵉ)
        ( middleᵉ)
        ( rightᵉ)
        ( bottom-leftᵉ)
        ( bottom-rightᵉ)
        ( lᵉ)
        ( rᵉ))
      ( qᵉ) ＝ᵉ
    left-whisker-concatᵉ leftᵉ (assocᵉ bottom-leftᵉ bottom-rightᵉ qᵉ) ∙ᵉ
    horizontal-pasting-coherence-square-identificationsᵉ
      ( top-leftᵉ)
      ( top-rightᵉ)
      ( leftᵉ)
      ( middleᵉ)
      ( rightᵉ ∙ᵉ qᵉ)
      ( bottom-leftᵉ)
      ( bottom-rightᵉ ∙ᵉ qᵉ)
      ( lᵉ)
      ( right-whisker-concat-coherence-square-identificationsᵉ
        ( top-rightᵉ)
        ( middleᵉ)
        ( rightᵉ)
        ( bottom-rightᵉ)
        ( rᵉ)
        ( qᵉ))
  right-whisker-concat-horizontal-pasting-coherence-square-identificationsᵉ
    reflᵉ reflᵉ reflᵉ .reflᵉ .reflᵉ reflᵉ reflᵉ reflᵉ reflᵉ reflᵉ =
    reflᵉ
```

### Right whiskering vertical concatenations of squares with identifications

Considerᵉ twoᵉ squaresᵉ ofᵉ identificationsᵉ asᵉ in theᵉ diagramᵉ

```text
                  topᵉ
              aᵉ -------->ᵉ bᵉ
              |           |
     top-leftᵉ |           | top-rightᵉ
              ∨ᵉ  middleᵉ   ∨ᵉ
              cᵉ -------->ᵉ dᵉ
              |           |
  bottom-leftᵉ |           | bottom-rightᵉ
              ∨ᵉ           ∨ᵉ
              eᵉ -------->ᵉ fᵉ
                 bottomᵉ
```

andᵉ considerᵉ anᵉ identificationᵉ `qᵉ : fᵉ ＝ᵉ y`.ᵉ Thenᵉ theᵉ rightᵉ whiskeringᵉ ofᵉ theᵉ
verticalᵉ pastingᵉ ofᵉ theᵉ twoᵉ squaresᵉ aboveᵉ with `q`ᵉ isᵉ upᵉ to associativityᵉ theᵉ
verticalᵉ pastingᵉ ofᵉ theᵉ squaresᵉ

```text
                     topᵉ
              aᵉ ------------>ᵉ bᵉ
              |               |
     top-leftᵉ |               | top-rightᵉ
              ∨ᵉ    middleᵉ     ∨ᵉ
              cᵉ ------------>ᵉ dᵉ
              |               |
  bottom-leftᵉ |               | bottom-rightᵉ ∙ᵉ qᵉ
              ∨ᵉ               ∨ᵉ
              eᵉ ------------>ᵉ y.ᵉ
                 bottomᵉ ∙ᵉ qᵉ
```

```agda
module _
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  where

  right-whisker-concat-vertical-pasting-coherence-square-identificationsᵉ :
    {aᵉ bᵉ cᵉ dᵉ eᵉ fᵉ yᵉ : Aᵉ}
    (topᵉ : aᵉ ＝ᵉ bᵉ) (top-leftᵉ : aᵉ ＝ᵉ cᵉ) (top-rightᵉ : bᵉ ＝ᵉ dᵉ)
    (middleᵉ : cᵉ ＝ᵉ dᵉ)
    (bottom-leftᵉ : cᵉ ＝ᵉ eᵉ) (bottom-rightᵉ : dᵉ ＝ᵉ fᵉ) (bottomᵉ : eᵉ ＝ᵉ fᵉ)
    (tᵉ : coherence-square-identificationsᵉ topᵉ top-leftᵉ top-rightᵉ middleᵉ) →
    (bᵉ :
      coherence-square-identificationsᵉ middleᵉ bottom-leftᵉ bottom-rightᵉ bottomᵉ) →
    (qᵉ : fᵉ ＝ᵉ yᵉ) →
    right-whisker-concat-coherence-square-identificationsᵉ
      ( topᵉ)
      ( top-leftᵉ ∙ᵉ bottom-leftᵉ)
      ( top-rightᵉ ∙ᵉ bottom-rightᵉ)
      ( bottomᵉ)
      ( vertical-pasting-coherence-square-identificationsᵉ
        ( topᵉ)
        ( top-leftᵉ)
        ( top-rightᵉ)
        ( middleᵉ)
        ( bottom-leftᵉ)
        ( bottom-rightᵉ)
        ( bottomᵉ)
        ( tᵉ)
        ( bᵉ))
      ( qᵉ) ∙ᵉ
    left-whisker-concatᵉ topᵉ (assocᵉ top-rightᵉ bottom-rightᵉ qᵉ) ＝ᵉ
    vertical-pasting-coherence-square-identificationsᵉ
      ( topᵉ)
      ( top-leftᵉ)
      ( top-rightᵉ)
      ( middleᵉ)
      ( bottom-leftᵉ)
      ( bottom-rightᵉ ∙ᵉ qᵉ)
      ( bottomᵉ ∙ᵉ qᵉ)
      ( tᵉ)
      ( right-whisker-concat-coherence-square-identificationsᵉ
        ( middleᵉ)
        ( bottom-leftᵉ)
        ( bottom-rightᵉ)
        ( bottomᵉ)
        ( bᵉ)
        ( qᵉ))
  right-whisker-concat-vertical-pasting-coherence-square-identificationsᵉ
    reflᵉ reflᵉ .reflᵉ reflᵉ reflᵉ .reflᵉ reflᵉ reflᵉ reflᵉ reflᵉ =
    reflᵉ
```