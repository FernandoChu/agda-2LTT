# Commuting squares of homotopies

```agda
module foundation-core.commuting-squares-of-homotopiesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ

open import foundation-core.commuting-squares-of-identificationsᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.whiskering-homotopies-concatenationᵉ
```

</details>

## Idea

Aᵉ squareᵉ ofᵉ [homotopies](foundation-core.homotopies.mdᵉ)

```text
          topᵉ
      fᵉ ------>ᵉ gᵉ
      |         |
 leftᵉ |         | rightᵉ
      ∨ᵉ         ∨ᵉ
      hᵉ ------>ᵉ iᵉ
        bottomᵉ
```

isᵉ saidᵉ to beᵉ aᵉ {{#conceptᵉ "commutingᵉ square"ᵉ Disambiguation="homotopies"ᵉ}} ofᵉ
homotopiesᵉ ifᵉ thereᵉ isᵉ aᵉ homotopyᵉ `leftᵉ ∙hᵉ bottomᵉ ~ᵉ topᵉ ∙hᵉ rightᵉ `.ᵉ Suchᵉ aᵉ
homotopyᵉ isᵉ calledᵉ aᵉ
{{#conceptᵉ "coherence"ᵉ Disambiguation="commutingᵉ squareᵉ ofᵉ homotopies"ᵉ Agda=coherence-square-homotopiesᵉ}}
ofᵉ theᵉ square.ᵉ

## Definitions

### Commuting squares of homotopies

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {fᵉ gᵉ hᵉ iᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ}
  (topᵉ : fᵉ ~ᵉ gᵉ) (leftᵉ : fᵉ ~ᵉ hᵉ) (rightᵉ : gᵉ ~ᵉ iᵉ) (bottomᵉ : hᵉ ~ᵉ iᵉ)
  where

  coherence-square-homotopiesᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  coherence-square-homotopiesᵉ =
    leftᵉ ∙hᵉ bottomᵉ ~ᵉ topᵉ ∙hᵉ rightᵉ

  coherence-square-homotopies'ᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  coherence-square-homotopies'ᵉ =
    topᵉ ∙hᵉ rightᵉ ~ᵉ leftᵉ ∙hᵉ bottomᵉ
```

### Horizontally constant squares

{{#conceptᵉ "Horizontallyᵉ constantᵉ squares"ᵉ Disambiguation="homotopies"ᵉ Agda=horizontal-refl-coherence-square-homotopiesᵉ}}
areᵉ commutingᵉ squaresᵉ ofᵉ homotopiesᵉ ofᵉ theᵉ formᵉ

```text
       refl-htpyᵉ
    fᵉ ---------->ᵉ fᵉ
    |             |
  Hᵉ |             | Hᵉ
    ∨ᵉ             ∨ᵉ
    gᵉ ---------->ᵉ g.ᵉ
       refl-htpyᵉ
```

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {fᵉ gᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ} (Hᵉ : fᵉ ~ᵉ gᵉ)
  where

  horizontal-refl-coherence-square-homotopiesᵉ :
    coherence-square-homotopiesᵉ refl-htpyᵉ Hᵉ Hᵉ refl-htpyᵉ
  horizontal-refl-coherence-square-homotopiesᵉ xᵉ =
    horizontal-refl-coherence-square-identificationsᵉ (Hᵉ xᵉ)
```

### Vertically constant squares

{{#conceptᵉ "Verticallyᵉ constantᵉ squares"ᵉ Disambiguation="homotopies"ᵉ Agda=vertical-refl-coherence-square-homotopiesᵉ}}
areᵉ commutingᵉ squaresᵉ ofᵉ homotopiesᵉ ofᵉ theᵉ formᵉ

```text
                Hᵉ
            fᵉ ----->ᵉ gᵉ
            |        |
  refl-htpyᵉ |        | refl-htpyᵉ
            ∨ᵉ        ∨ᵉ
            fᵉ ----->ᵉ g.ᵉ
                Hᵉ
```

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {fᵉ gᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ} (Hᵉ : fᵉ ~ᵉ gᵉ)
  where

  vertical-refl-coherence-square-homotopiesᵉ :
    coherence-square-homotopiesᵉ Hᵉ refl-htpyᵉ refl-htpyᵉ Hᵉ
  vertical-refl-coherence-square-homotopiesᵉ xᵉ =
    vertical-refl-coherence-square-identificationsᵉ (Hᵉ xᵉ)
```

### Squares with refl on the top and bottom

Givenᵉ aᵉ homotopyᵉ `Hᵉ ~ᵉ H'`,ᵉ weᵉ canᵉ obtainᵉ aᵉ coherenceᵉ squareᵉ with `refl-htpy`ᵉ onᵉ
theᵉ topᵉ andᵉ bottom.ᵉ

```text
       refl-htpyᵉ
    fᵉ ---------->ᵉ fᵉ
    |             |
  Hᵉ |             | H'ᵉ
    ∨ᵉ             ∨ᵉ
    gᵉ ---------->ᵉ gᵉ
       refl-htpyᵉ
```

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {fᵉ gᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ}
  (Hᵉ H'ᵉ : fᵉ ~ᵉ gᵉ)
  where

  coherence-square-homotopies-horizontal-reflᵉ :
    Hᵉ ~ᵉ H'ᵉ →
    coherence-square-homotopiesᵉ
      ( refl-htpyᵉ)
      ( Hᵉ)
      ( H'ᵉ)
      ( refl-htpyᵉ)
  coherence-square-homotopies-horizontal-reflᵉ Kᵉ =
    right-unit-htpyᵉ ∙hᵉ Kᵉ
```

Conversely,ᵉ givenᵉ aᵉ coherenceᵉ squareᵉ asᵉ above,ᵉ weᵉ canᵉ obtainᵉ aᵉ homotopyᵉ
`Hᵉ ~ᵉ H'`.ᵉ

```agda
  inv-coherence-square-homotopies-horizontal-reflᵉ :
    coherence-square-homotopiesᵉ
      ( refl-htpyᵉ)
      ( Hᵉ)
      ( H'ᵉ)
      ( refl-htpyᵉ) →
    Hᵉ ~ᵉ H'ᵉ
  inv-coherence-square-homotopies-horizontal-reflᵉ Kᵉ =
    inv-htpy-right-unit-htpyᵉ ∙hᵉ Kᵉ
```

### Squares with `refl-htpy` on the left and right

Givenᵉ aᵉ homotopyᵉ `Hᵉ ~ᵉ H'`,ᵉ weᵉ canᵉ obtainᵉ aᵉ coherenceᵉ squareᵉ with `refl-htpy`ᵉ onᵉ
theᵉ leftᵉ andᵉ right.ᵉ

```text
                 H'ᵉ
            fᵉ ------>ᵉ gᵉ
            |         |
  refl-htpyᵉ |         | refl-htpyᵉ
            ∨ᵉ         ∨ᵉ
            fᵉ ------>ᵉ gᵉ
                 Hᵉ
```

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {fᵉ gᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ}
  (Hᵉ H'ᵉ : fᵉ ~ᵉ gᵉ)
  where

  coherence-square-homotopies-vertical-reflᵉ :
    Hᵉ ~ᵉ H'ᵉ →
    coherence-square-homotopiesᵉ
      ( H'ᵉ)
      ( refl-htpyᵉ)
      ( refl-htpyᵉ)
      ( Hᵉ)
  coherence-square-homotopies-vertical-reflᵉ Kᵉ =
    Kᵉ ∙hᵉ inv-htpyᵉ right-unit-htpyᵉ
```

Conversely,ᵉ givenᵉ aᵉ coherenceᵉ squareᵉ asᵉ above,ᵉ weᵉ canᵉ obtainᵉ aᵉ homotopyᵉ
`Hᵉ ~ᵉ H'`.ᵉ

```agda
  inv-coherence-square-homotopies-vertical-reflᵉ :
    coherence-square-homotopiesᵉ
      ( H'ᵉ)
      ( refl-htpyᵉ)
      ( refl-htpyᵉ)
      ( Hᵉ) →
    Hᵉ ~ᵉ H'ᵉ
  inv-coherence-square-homotopies-vertical-reflᵉ Kᵉ =
    Kᵉ ∙hᵉ right-unit-htpyᵉ
```

## Operations

### Inverting squares of homotopies horizontally

Givenᵉ aᵉ commutingᵉ squareᵉ ofᵉ homotopiesᵉ

```text
           topᵉ
       fᵉ ------->ᵉ gᵉ
       |          |
  leftᵉ |          | rightᵉ
       ∨ᵉ          ∨ᵉ
       hᵉ ------->ᵉ i,ᵉ
          bottomᵉ
```

theᵉ squareᵉ ofᵉ homotopiesᵉ

```text
              top⁻¹ᵉ
        gᵉ ------------>ᵉ fᵉ
        |               |
  rightᵉ |               | leftᵉ
        ∨ᵉ               ∨ᵉ
        iᵉ ------------>ᵉ hᵉ
             bottom⁻¹ᵉ
```

commutes.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {fᵉ gᵉ hᵉ iᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ}
  where

  horizontal-inv-coherence-square-homotopiesᵉ :
    (topᵉ : fᵉ ~ᵉ gᵉ) (leftᵉ : fᵉ ~ᵉ hᵉ) (rightᵉ : gᵉ ~ᵉ iᵉ) (bottomᵉ : hᵉ ~ᵉ iᵉ) →
    coherence-square-homotopiesᵉ topᵉ leftᵉ rightᵉ bottomᵉ →
    coherence-square-homotopiesᵉ (inv-htpyᵉ topᵉ) rightᵉ leftᵉ (inv-htpyᵉ bottomᵉ)
  horizontal-inv-coherence-square-homotopiesᵉ topᵉ leftᵉ rightᵉ bottomᵉ Hᵉ xᵉ =
    horizontal-inv-coherence-square-identificationsᵉ
      ( topᵉ xᵉ)
      ( leftᵉ xᵉ)
      ( rightᵉ xᵉ)
      ( bottomᵉ xᵉ)
      ( Hᵉ xᵉ)
```

### Inverting squares of homotopies vertically

Givenᵉ aᵉ commutingᵉ squareᵉ ofᵉ homotopiesᵉ

```text
           topᵉ
       fᵉ ------->ᵉ gᵉ
       |          |
  leftᵉ |          | rightᵉ
       ∨ᵉ          ∨ᵉ
       hᵉ ------->ᵉ i,ᵉ
          bottomᵉ
```

theᵉ squareᵉ ofᵉ homotopiesᵉ

```text
            bottomᵉ
         hᵉ ------->ᵉ iᵉ
         |          |
  left⁻¹ᵉ |          | right⁻¹ᵉ
         ∨ᵉ          ∨ᵉ
         fᵉ ------->ᵉ gᵉ
             topᵉ
```

commutes.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {fᵉ gᵉ hᵉ iᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ}
  where

  vertical-inv-coherence-square-homotopiesᵉ :
    (topᵉ : fᵉ ~ᵉ gᵉ) (leftᵉ : fᵉ ~ᵉ hᵉ) (rightᵉ : gᵉ ~ᵉ iᵉ) (bottomᵉ : hᵉ ~ᵉ iᵉ) →
    coherence-square-homotopiesᵉ topᵉ leftᵉ rightᵉ bottomᵉ →
    coherence-square-homotopiesᵉ bottomᵉ (inv-htpyᵉ leftᵉ) (inv-htpyᵉ rightᵉ) topᵉ
  vertical-inv-coherence-square-homotopiesᵉ topᵉ leftᵉ rightᵉ bottomᵉ Hᵉ xᵉ =
    vertical-inv-coherence-square-identificationsᵉ
      ( topᵉ xᵉ)
      ( leftᵉ xᵉ)
      ( rightᵉ xᵉ)
      ( bottomᵉ xᵉ)
      ( Hᵉ xᵉ)
```

### Functions acting on squares of homotopies

Givenᵉ aᵉ commutingᵉ squareᵉ ofᵉ homotopiesᵉ

```text
           topᵉ
       fᵉ ------->ᵉ gᵉ
       |          |
  leftᵉ |          | rightᵉ
       ∨ᵉ          ∨ᵉ
       hᵉ ------->ᵉ iᵉ
          bottomᵉ
```

in `(xᵉ : Aᵉ) → Bᵉ x`,ᵉ andᵉ givenᵉ aᵉ dependentᵉ mapᵉ `Fᵉ : {xᵉ : Aᵉ} → Bᵉ xᵉ → Cᵉ x`,ᵉ theᵉ
squareᵉ ofᵉ homotopiesᵉ

```text
                 Fᵉ ·lᵉ topᵉ
           fᵉ fᵉ ----------->ᵉ fᵉ gᵉ
            |                |
  Fᵉ ·lᵉ leftᵉ |                | Fᵉ ·lᵉ rightᵉ
            ∨ᵉ                ∨ᵉ
            hᵉ ------------->ᵉ iᵉ
               Fᵉ ·lᵉ bottomᵉ
```

commutes.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {Cᵉ : Aᵉ → UUᵉ l3ᵉ}
  {fᵉ gᵉ hᵉ iᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ}
  (Fᵉ : {xᵉ : Aᵉ} → Bᵉ xᵉ → Cᵉ xᵉ)
  where

  map-coherence-square-homotopiesᵉ :
    (topᵉ : fᵉ ~ᵉ gᵉ) (leftᵉ : fᵉ ~ᵉ hᵉ) (rightᵉ : gᵉ ~ᵉ iᵉ) (bottomᵉ : hᵉ ~ᵉ iᵉ) →
    coherence-square-homotopiesᵉ topᵉ leftᵉ rightᵉ bottomᵉ →
    coherence-square-homotopiesᵉ
      ( Fᵉ ·lᵉ topᵉ)
      ( Fᵉ ·lᵉ leftᵉ)
      ( Fᵉ ·lᵉ rightᵉ)
      ( Fᵉ ·lᵉ bottomᵉ)
  map-coherence-square-homotopiesᵉ topᵉ leftᵉ rightᵉ bottomᵉ Hᵉ xᵉ =
    map-coherence-square-identificationsᵉ
      ( Fᵉ)
      ( topᵉ xᵉ)
      ( leftᵉ xᵉ)
      ( rightᵉ xᵉ)
      ( bottomᵉ xᵉ)
      ( Hᵉ xᵉ)
```

Similarlyᵉ weᵉ mayᵉ whiskerᵉ itᵉ onᵉ theᵉ right.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : Bᵉ → UUᵉ l3ᵉ}
  {fᵉ gᵉ hᵉ iᵉ : (yᵉ : Bᵉ) → Cᵉ yᵉ}
  where

  right-whisker-comp-coherence-square-homotopiesᵉ :
    (topᵉ : fᵉ ~ᵉ gᵉ) (leftᵉ : fᵉ ~ᵉ hᵉ) (rightᵉ : gᵉ ~ᵉ iᵉ) (bottomᵉ : hᵉ ~ᵉ iᵉ) →
    (Fᵉ : Aᵉ → Bᵉ) →
    coherence-square-homotopiesᵉ topᵉ leftᵉ rightᵉ bottomᵉ →
    coherence-square-homotopiesᵉ
      ( topᵉ ·rᵉ Fᵉ)
      ( leftᵉ ·rᵉ Fᵉ)
      ( rightᵉ ·rᵉ Fᵉ)
      ( bottomᵉ ·rᵉ Fᵉ)
  right-whisker-comp-coherence-square-homotopiesᵉ topᵉ leftᵉ rightᵉ bottomᵉ Fᵉ αᵉ =
    αᵉ ·rᵉ Fᵉ
```

### Concatenating homotopies of edges and coherences of commuting squares of homotopies

Considerᵉ aᵉ commutingᵉ squareᵉ ofᵉ homotopiesᵉ andᵉ aᵉ homotopyᵉ ofᵉ oneᵉ ofᵉ theᵉ fourᵉ
sidesᵉ with anotherᵉ homotopy,ᵉ asᵉ forᵉ exampleᵉ in theᵉ diagramᵉ belowᵉ:

```text
             topᵉ
       aᵉ --------->ᵉ bᵉ
       |           | |
  leftᵉ |     rightᵉ |~|ᵉ right'ᵉ
       ∨ᵉ           ∨ᵉ ∨ᵉ
       cᵉ --------->ᵉ d.ᵉ
           bottomᵉ
```

Thenᵉ anyᵉ homotopyᵉ witnessingᵉ thatᵉ theᵉ squareᵉ commutesᵉ canᵉ beᵉ concatenatedᵉ with
theᵉ homotopyᵉ onᵉ theᵉ side,ᵉ to obtainᵉ aᵉ newᵉ commutingᵉ squareᵉ ofᵉ homotopies.ᵉ

**Note.**ᵉ Toᵉ avoidᵉ cyclicᵉ module dependenciesᵉ weᵉ willᵉ giveᵉ directᵉ proofsᵉ thatᵉ
concatenatingᵉ homotopiesᵉ ofᵉ edgesᵉ ofᵉ aᵉ squareᵉ with theᵉ coherenceᵉ ofᵉ itsᵉ
commutativityᵉ isᵉ anᵉ equivalence.ᵉ

#### Concatenating homotopies of the top edge with a coherence of a commuting square of homotopies

Considerᵉ aᵉ commutingᵉ diagramᵉ ofᵉ homotopiesᵉ

```text
           top'ᵉ
         ------->ᵉ
       fᵉ ------->ᵉ gᵉ
       |   topᵉ    |
  leftᵉ |          | rightᵉ
       ∨ᵉ          ∨ᵉ
       hᵉ ------->ᵉ i.ᵉ
          bottomᵉ
```

with aᵉ homotopyᵉ `topᵉ ~ᵉ top'`.ᵉ Thenᵉ weᵉ getᵉ mapsᵉ backᵉ andᵉ forthᵉ

```text
           topᵉ                             top'ᵉ
       fᵉ ------->ᵉ gᵉ                    fᵉ ------->ᵉ gᵉ
       |          |                    |          |
  leftᵉ |          | rightᵉ    ↔ᵉ    leftᵉ |          | rightᵉ
       ∨ᵉ          ∨ᵉ                    ∨ᵉ          ∨ᵉ
       hᵉ ------->ᵉ iᵉ                    hᵉ ------->ᵉ i.ᵉ
          bottomᵉ                          bottomᵉ
```

Weᵉ record thatᵉ thisᵉ constructionᵉ isᵉ anᵉ equivalenceᵉ in
[`foundation.commuting-squares-of-homotopies`](foundation.commuting-squares-of-homotopies.md).ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {fᵉ gᵉ hᵉ iᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ}
  (topᵉ : fᵉ ~ᵉ gᵉ) (leftᵉ : fᵉ ~ᵉ hᵉ) (rightᵉ : gᵉ ~ᵉ iᵉ) (bottomᵉ : hᵉ ~ᵉ iᵉ)
  {top'ᵉ : fᵉ ~ᵉ gᵉ} (sᵉ : topᵉ ~ᵉ top'ᵉ)
  where

  concat-top-homotopy-coherence-square-homotopiesᵉ :
    coherence-square-homotopiesᵉ topᵉ leftᵉ rightᵉ bottomᵉ →
    coherence-square-homotopiesᵉ top'ᵉ leftᵉ rightᵉ bottomᵉ
  concat-top-homotopy-coherence-square-homotopiesᵉ Hᵉ xᵉ =
    concat-top-identification-coherence-square-identificationsᵉ
      ( topᵉ xᵉ)
      ( leftᵉ xᵉ)
      ( rightᵉ xᵉ)
      ( bottomᵉ xᵉ)
      ( sᵉ xᵉ)
      ( Hᵉ xᵉ)

  inv-concat-top-homotopy-coherence-square-homotopiesᵉ :
    coherence-square-homotopiesᵉ top'ᵉ leftᵉ rightᵉ bottomᵉ →
    coherence-square-homotopiesᵉ topᵉ leftᵉ rightᵉ bottomᵉ
  inv-concat-top-homotopy-coherence-square-homotopiesᵉ Hᵉ xᵉ =
    inv-concat-top-identification-coherence-square-identificationsᵉ
      ( topᵉ xᵉ)
      ( leftᵉ xᵉ)
      ( rightᵉ xᵉ)
      ( bottomᵉ xᵉ)
      ( sᵉ xᵉ)
      ( Hᵉ xᵉ)
```

#### Concatenating homotopies of the left edge with a coherence of a commuting square of homotopies

Considerᵉ aᵉ commutingᵉ diagramᵉ ofᵉ homotopiesᵉ

```text
              topᵉ
         fᵉ ------->ᵉ gᵉ
        | |         |
  left'ᵉ | | leftᵉ    | rightᵉ
        ∨ᵉ ∨ᵉ         ∨ᵉ
         hᵉ ------->ᵉ i.ᵉ
            bottomᵉ
```

with aᵉ homotopyᵉ `leftᵉ ~ᵉ left'`.ᵉ Thenᵉ weᵉ getᵉ mapsᵉ backᵉ andᵉ forthᵉ

```text
           topᵉ                              topᵉ
       fᵉ ------->ᵉ gᵉ                     fᵉ ------->ᵉ gᵉ
       |          |                     |          |
  leftᵉ |          | rightᵉ    ↔ᵉ    left'ᵉ |          | rightᵉ
       ∨ᵉ          ∨ᵉ                     ∨ᵉ          ∨ᵉ
       hᵉ ------->ᵉ iᵉ                     hᵉ ------->ᵉ i.ᵉ
          bottomᵉ                           bottomᵉ
```

Weᵉ record thatᵉ thisᵉ constructionᵉ isᵉ anᵉ equivalenceᵉ in
[`foundation.commuting-squares-of-homotopies`](foundation.commuting-squares-of-homotopies.md).ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {fᵉ gᵉ hᵉ iᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ}
  (topᵉ : fᵉ ~ᵉ gᵉ) (leftᵉ : fᵉ ~ᵉ hᵉ) (rightᵉ : gᵉ ~ᵉ iᵉ) (bottomᵉ : hᵉ ~ᵉ iᵉ)
  {left'ᵉ : fᵉ ~ᵉ hᵉ} (sᵉ : leftᵉ ~ᵉ left'ᵉ)
  where

  concat-left-homotopy-coherence-square-homotopiesᵉ :
    coherence-square-homotopiesᵉ topᵉ leftᵉ rightᵉ bottomᵉ →
    coherence-square-homotopiesᵉ topᵉ left'ᵉ rightᵉ bottomᵉ
  concat-left-homotopy-coherence-square-homotopiesᵉ Hᵉ xᵉ =
    concat-left-identification-coherence-square-identificationsᵉ
      ( topᵉ xᵉ)
      ( leftᵉ xᵉ)
      ( rightᵉ xᵉ)
      ( bottomᵉ xᵉ)
      ( sᵉ xᵉ)
      ( Hᵉ xᵉ)

  inv-concat-left-homotopy-coherence-square-homotopiesᵉ :
    coherence-square-homotopiesᵉ topᵉ left'ᵉ rightᵉ bottomᵉ →
    coherence-square-homotopiesᵉ topᵉ leftᵉ rightᵉ bottomᵉ
  inv-concat-left-homotopy-coherence-square-homotopiesᵉ Hᵉ xᵉ =
    inv-concat-left-identification-coherence-square-identificationsᵉ
      ( topᵉ xᵉ)
      ( leftᵉ xᵉ)
      ( rightᵉ xᵉ)
      ( bottomᵉ xᵉ)
      ( sᵉ xᵉ)
      ( Hᵉ xᵉ)
```

#### Concatenating homotopies of the right edge with a coherence of a commuting square of homotopies

Considerᵉ aᵉ commutingᵉ diagramᵉ ofᵉ homotopiesᵉ

```text
            topᵉ
       fᵉ ------->ᵉ gᵉ
       |         | |
  leftᵉ |   rightᵉ | | right'ᵉ
       ∨ᵉ         ∨ᵉ ∨ᵉ
       hᵉ ------->ᵉ i.ᵉ
          bottomᵉ
```

with aᵉ homotopyᵉ `rightᵉ ~ᵉ right'`.ᵉ Thenᵉ weᵉ getᵉ mapsᵉ backᵉ andᵉ forthᵉ

```text
           topᵉ                             topᵉ
       fᵉ ------->ᵉ gᵉ                    fᵉ ------->ᵉ gᵉ
       |          |                    |          |
  leftᵉ |          | rightᵉ    ↔ᵉ    leftᵉ |          | right'ᵉ
       ∨ᵉ          ∨ᵉ                    ∨ᵉ          ∨ᵉ
       hᵉ ------->ᵉ iᵉ                    hᵉ ------->ᵉ i.ᵉ
          bottomᵉ                          bottomᵉ
```

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {fᵉ gᵉ hᵉ iᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ}
  (topᵉ : fᵉ ~ᵉ gᵉ) (leftᵉ : fᵉ ~ᵉ hᵉ) (rightᵉ : gᵉ ~ᵉ iᵉ) (bottomᵉ : hᵉ ~ᵉ iᵉ)
  {right'ᵉ : gᵉ ~ᵉ iᵉ} (sᵉ : rightᵉ ~ᵉ right'ᵉ)
  where

  concat-right-homotopy-coherence-square-homotopiesᵉ :
    coherence-square-homotopiesᵉ topᵉ leftᵉ rightᵉ bottomᵉ →
    coherence-square-homotopiesᵉ topᵉ leftᵉ right'ᵉ bottomᵉ
  concat-right-homotopy-coherence-square-homotopiesᵉ Hᵉ xᵉ =
    concat-right-identification-coherence-square-identificationsᵉ
      ( topᵉ xᵉ)
      ( leftᵉ xᵉ)
      ( rightᵉ xᵉ)
      ( bottomᵉ xᵉ)
      ( sᵉ xᵉ)
      ( Hᵉ xᵉ)

  inv-concat-right-homotopy-coherence-square-homotopiesᵉ :
    coherence-square-homotopiesᵉ topᵉ leftᵉ right'ᵉ bottomᵉ →
    coherence-square-homotopiesᵉ topᵉ leftᵉ rightᵉ bottomᵉ
  inv-concat-right-homotopy-coherence-square-homotopiesᵉ Hᵉ xᵉ =
    inv-concat-right-identification-coherence-square-identificationsᵉ
      ( topᵉ xᵉ)
      ( leftᵉ xᵉ)
      ( rightᵉ xᵉ)
      ( bottomᵉ xᵉ)
      ( sᵉ xᵉ)
      ( Hᵉ xᵉ)
```

Weᵉ record thatᵉ thisᵉ constructionᵉ isᵉ anᵉ equivalenceᵉ in
[`foundation.commuting-squares-of-homotopies`](foundation.commuting-squares-of-homotopies.md).ᵉ

#### Concatenating homotopies of the bottom edge with a coherence of a commuting square of homotopies

Considerᵉ aᵉ commutingᵉ diagramᵉ ofᵉ homotopiesᵉ

```text
            topᵉ
       fᵉ ------->ᵉ gᵉ
       |          |
  leftᵉ |          | rightᵉ
       ∨ᵉ  bottomᵉ  ∨ᵉ
       hᵉ ------->ᵉ i.ᵉ
         ------->ᵉ
          bottom'ᵉ
```

with aᵉ homotopyᵉ `bottomᵉ ~ᵉ bottom'`.ᵉ Thenᵉ weᵉ getᵉ mapsᵉ backᵉ andᵉ forthᵉ

```text
           topᵉ                             topᵉ
       fᵉ ------->ᵉ gᵉ                    fᵉ ------->ᵉ gᵉ
       |          |                    |          |
  leftᵉ |          | rightᵉ    ↔ᵉ    leftᵉ |          | rightᵉ
       ∨ᵉ          ∨ᵉ                    ∨ᵉ          ∨ᵉ
       hᵉ ------->ᵉ iᵉ                    hᵉ ------->ᵉ i.ᵉ
          bottomᵉ                          bottom'ᵉ
```

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {fᵉ gᵉ hᵉ iᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ}
  (topᵉ : fᵉ ~ᵉ gᵉ) (leftᵉ : fᵉ ~ᵉ hᵉ) (rightᵉ : gᵉ ~ᵉ iᵉ) (bottomᵉ : hᵉ ~ᵉ iᵉ)
  {bottom'ᵉ : hᵉ ~ᵉ iᵉ} (sᵉ : bottomᵉ ~ᵉ bottom'ᵉ)
  where

  concat-bottom-homotopy-coherence-square-homotopiesᵉ :
    coherence-square-homotopiesᵉ topᵉ leftᵉ rightᵉ bottomᵉ →
    coherence-square-homotopiesᵉ topᵉ leftᵉ rightᵉ bottom'ᵉ
  concat-bottom-homotopy-coherence-square-homotopiesᵉ Hᵉ xᵉ =
    concat-bottom-identification-coherence-square-identificationsᵉ
      ( topᵉ xᵉ)
      ( leftᵉ xᵉ)
      ( rightᵉ xᵉ)
      ( bottomᵉ xᵉ)
      ( sᵉ xᵉ)
      ( Hᵉ xᵉ)

  inv-concat-bottom-homotopy-coherence-square-homotopiesᵉ :
    coherence-square-homotopiesᵉ topᵉ leftᵉ rightᵉ bottom'ᵉ →
    coherence-square-homotopiesᵉ topᵉ leftᵉ rightᵉ bottomᵉ
  inv-concat-bottom-homotopy-coherence-square-homotopiesᵉ Hᵉ xᵉ =
    inv-concat-bottom-identification-coherence-square-identificationsᵉ
      ( topᵉ xᵉ)
      ( leftᵉ xᵉ)
      ( rightᵉ xᵉ)
      ( bottomᵉ xᵉ)
      ( sᵉ xᵉ)
      ( Hᵉ xᵉ)
```

Weᵉ record thatᵉ thisᵉ constructionᵉ isᵉ anᵉ equivalenceᵉ in
[`foundation.commuting-squares-of-homotopies`](foundation.commuting-squares-of-homotopies.md).ᵉ

### Whiskering and splicing coherences of commuting squares of homotopies with respect to concatenation of homotopies

Givenᵉ aᵉ commutingᵉ squareᵉ ofᵉ homotopiesᵉ

```text
           topᵉ
       fᵉ ------->ᵉ gᵉ
       |          |
  leftᵉ |          | rightᵉ
       ∨ᵉ          ∨ᵉ
       hᵉ ------->ᵉ i,ᵉ
          bottomᵉ
```

weᵉ mayᵉ considerᵉ fourᵉ waysᵉ ofᵉ attachingᵉ newᵉ homotopiesᵉ to itᵉ:

1.ᵉ Prependingᵉ `Hᵉ : uᵉ ~ᵉ f`ᵉ to theᵉ leftᵉ givesᵉ usᵉ aᵉ commutingᵉ squareᵉ

   ```text
                Hᵉ ∙hᵉ topᵉ
              uᵉ ------->ᵉ gᵉ
              |          |
    Hᵉ ∙hᵉ leftᵉ |          | rightᵉ
              ∨ᵉ          ∨ᵉ
              hᵉ ------->ᵉ i.ᵉ
                 bottomᵉ
   ```

   Moreᵉ precisely,ᵉ weᵉ haveᵉ anᵉ equivalenceᵉ

   ```text
     (leftᵉ ∙hᵉ bottomᵉ ~ᵉ topᵉ ∙hᵉ rightᵉ) ≃ᵉ ((Hᵉ ∙hᵉ leftᵉ) ∙hᵉ bottomᵉ ~ᵉ (Hᵉ ∙hᵉ topᵉ) ∙hᵉ right).ᵉ
   ```

2.ᵉ Appendingᵉ aᵉ homotopyᵉ `Hᵉ : iᵉ ~ᵉ u`ᵉ to theᵉ rightᵉ givesᵉ aᵉ commutingᵉ squareᵉ ofᵉ
   homotopiesᵉ

   ```text
                   topᵉ
           fᵉ ------------>ᵉ gᵉ
           |               |
      leftᵉ |               | rightᵉ ∙hᵉ Hᵉ
           ∨ᵉ               ∨ᵉ
           hᵉ ------------>ᵉ u.ᵉ
              bottomᵉ ∙hᵉ Hᵉ
   ```

   Moreᵉ precisely,ᵉ weᵉ haveᵉ anᵉ equivalenceᵉ

   ```text
     (leftᵉ ∙hᵉ bottomᵉ ~ᵉ topᵉ ∙hᵉ rightᵉ) ≃ᵉ (leftᵉ ∙hᵉ (bottomᵉ ∙hᵉ Hᵉ) ~ᵉ topᵉ ∙hᵉ (rightᵉ ∙hᵉ H)).ᵉ
   ```

3.ᵉ Splicingᵉ aᵉ homotopyᵉ `Hᵉ : hᵉ ~ᵉ u`ᵉ andᵉ itsᵉ inverseᵉ intoᵉ theᵉ middleᵉ givesᵉ aᵉ
   commutingᵉ squareᵉ ofᵉ homotopiesᵉ

   ```text
                      topᵉ
              fᵉ -------------->ᵉ gᵉ
              |                 |
    leftᵉ ∙hᵉ Hᵉ |                 | rightᵉ
              ∨ᵉ                 ∨ᵉ
              uᵉ -------------->ᵉ i.ᵉ
                 H⁻¹ᵉ ∙hᵉ bottomᵉ
   ```

   Moreᵉ precisely,ᵉ weᵉ haveᵉ anᵉ equivalenceᵉ

   ```text
     (leftᵉ ∙hᵉ bottomᵉ ~ᵉ topᵉ ∙hᵉ rightᵉ) ≃ᵉ ((leftᵉ ∙hᵉ Hᵉ) ∙hᵉ (H⁻¹ᵉ ∙hᵉ bottomᵉ) ~ᵉ topᵉ ∙hᵉ right).ᵉ
   ```

   Similarly,ᵉ weᵉ haveᵉ anᵉ equivalenceᵉ

   ```text
     (leftᵉ ∙hᵉ bottomᵉ ~ᵉ topᵉ ∙hᵉ rightᵉ) ≃ᵉ ((leftᵉ ∙hᵉ H⁻¹ᵉ) ∙hᵉ (Hᵉ ∙hᵉ bottomᵉ) ~ᵉ topᵉ ∙hᵉ right).ᵉ
   ```

4.ᵉ Splicingᵉ aᵉ homotopyᵉ `Hᵉ : gᵉ ~ᵉ u`ᵉ andᵉ itsᵉ inverseᵉ intoᵉ theᵉ middleᵉ givesᵉ aᵉ
   commutingᵉ squareᵉ ofᵉ homotopiesᵉ

   ```text
            topᵉ ∙hᵉ Hᵉ
          fᵉ -------->ᵉ uᵉ
          |           |
     leftᵉ |           | H⁻¹ᵉ ∙hᵉ rightᵉ
          ∨ᵉ           ∨ᵉ
          hᵉ -------->ᵉ i.ᵉ
             bottomᵉ
   ```

   Moreᵉ precisely,ᵉ weᵉ haveᵉ anᵉ equivalenceᵉ

   ```text
     (leftᵉ ∙hᵉ bottomᵉ ~ᵉ topᵉ ∙hᵉ rightᵉ) ≃ᵉ (leftᵉ ∙hᵉ bottomᵉ ~ᵉ (topᵉ ∙hᵉ Hᵉ) ∙hᵉ (H⁻¹ᵉ ∙hᵉ right)).ᵉ
   ```

   Similarly,ᵉ weᵉ haveᵉ anᵉ equivalenceᵉ

   ```text
     (leftᵉ ∙hᵉ bottomᵉ ~ᵉ topᵉ ∙hᵉ rightᵉ) ≃ᵉ (leftᵉ ∙hᵉ bottomᵉ ~ᵉ (topᵉ ∙hᵉ H⁻¹ᵉ) ∙hᵉ (Hᵉ ∙hᵉ right)).ᵉ
   ```

Theseᵉ operationsᵉ areᵉ usefulᵉ in proofsᵉ involvingᵉ homotopyᵉ algebra,ᵉ becauseᵉ takingᵉ
`equiv-right-whisker-concat-coherence-square-homotopies`ᵉ asᵉ anᵉ example,ᵉ itᵉ
providesᵉ usᵉ with twoᵉ mapsᵉ: theᵉ forwardᵉ directionᵉ statesᵉ
`(Hᵉ ∙hᵉ rᵉ ~ᵉ Kᵉ ∙hᵉ sᵉ) → (Hᵉ ∙hᵉ (rᵉ ∙hᵉ tᵉ)) ~ᵉ Kᵉ ∙hᵉ (sᵉ ∙hᵉ t))`,ᵉ whichᵉ allowsᵉ oneᵉ to
appendᵉ aᵉ homotopyᵉ withoutᵉ needingᵉ to reassociateᵉ onᵉ theᵉ right,ᵉ andᵉ theᵉ backwardsᵉ
directionᵉ converselyᵉ allowsᵉ oneᵉ to cancelᵉ outᵉ aᵉ homotopyᵉ in parentheses.ᵉ

#### Left whiskering coherences of commuting squares of homotopies

Forᵉ anyᵉ homotopyᵉ `Hᵉ : uᵉ ~ᵉ f`ᵉ weᵉ obtainᵉ mapsᵉ backᵉ andᵉ forthᵉ

```text
           topᵉ                                Hᵉ ∙hᵉ topᵉ
       fᵉ ------->ᵉ gᵉ                         uᵉ ------->ᵉ gᵉ
       |          |                         |          |
  leftᵉ |          | rightᵉ    ↔ᵉ    Hᵉ ∙hᵉ leftᵉ |          | rightᵉ
       ∨ᵉ          ∨ᵉ                         ∨ᵉ          ∨ᵉ
       hᵉ ------->ᵉ iᵉ                         hᵉ ------->ᵉ iᵉ
          bottomᵉ                               bottomᵉ
```

ofᵉ coherencesᵉ ofᵉ commutingᵉ squaresᵉ ofᵉ homotopies.ᵉ Weᵉ showᵉ in
[`foundation.commuting-squares-of-homotopies`](foundation.commuting-squares-of-homotopies.mdᵉ)
thatᵉ theseᵉ mapsᵉ areᵉ equivalences.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {fᵉ gᵉ hᵉ iᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ}
  where

  left-whisker-concat-coherence-square-homotopiesᵉ :
    {uᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ} (Hᵉ : uᵉ ~ᵉ fᵉ)
    (topᵉ : fᵉ ~ᵉ gᵉ) (leftᵉ : fᵉ ~ᵉ hᵉ) (rightᵉ : gᵉ ~ᵉ iᵉ) (bottomᵉ : hᵉ ~ᵉ iᵉ) →
    coherence-square-homotopiesᵉ topᵉ leftᵉ rightᵉ bottomᵉ →
    coherence-square-homotopiesᵉ (Hᵉ ∙hᵉ topᵉ) (Hᵉ ∙hᵉ leftᵉ) rightᵉ bottomᵉ
  left-whisker-concat-coherence-square-homotopiesᵉ
    Hᵉ topᵉ leftᵉ rightᵉ bottomᵉ cohᵉ xᵉ =
    left-whisker-concat-coherence-square-identificationsᵉ
      ( Hᵉ xᵉ)
      ( topᵉ xᵉ)
      ( leftᵉ xᵉ)
      ( rightᵉ xᵉ)
      ( bottomᵉ xᵉ)
      ( cohᵉ xᵉ)

  left-unwhisker-concat-coherence-square-homotopiesᵉ :
    {uᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ} (Hᵉ : uᵉ ~ᵉ fᵉ)
    (topᵉ : fᵉ ~ᵉ gᵉ) (leftᵉ : fᵉ ~ᵉ hᵉ) (rightᵉ : gᵉ ~ᵉ iᵉ) (bottomᵉ : hᵉ ~ᵉ iᵉ) →
    coherence-square-homotopiesᵉ (Hᵉ ∙hᵉ topᵉ) (Hᵉ ∙hᵉ leftᵉ) rightᵉ bottomᵉ →
    coherence-square-homotopiesᵉ topᵉ leftᵉ rightᵉ bottomᵉ
  left-unwhisker-concat-coherence-square-homotopiesᵉ
    Hᵉ topᵉ leftᵉ rightᵉ bottomᵉ cohᵉ xᵉ =
    left-unwhisker-concat-coherence-square-identificationsᵉ
      ( Hᵉ xᵉ)
      ( topᵉ xᵉ)
      ( leftᵉ xᵉ)
      ( rightᵉ xᵉ)
      ( bottomᵉ xᵉ)
      ( cohᵉ xᵉ)
```

#### Right whiskering coherences of commuting squares of homotopies

Forᵉ anyᵉ homotopyᵉ `Hᵉ : iᵉ ~ᵉ u`ᵉ weᵉ obtainᵉ mapsᵉ backᵉ andᵉ forthᵉ

```text
           topᵉ                                 topᵉ
       fᵉ ------->ᵉ gᵉ                     fᵉ ------------>ᵉ gᵉ
       |          |                     |               |
  leftᵉ |          | rightᵉ    ↔ᵉ     leftᵉ |               | rightᵉ ∙hᵉ Hᵉ
       ∨ᵉ          ∨ᵉ                     ∨ᵉ               ∨ᵉ
       hᵉ ------->ᵉ iᵉ                     hᵉ ------------>ᵉ iᵉ
          bottomᵉ                           bottomᵉ ∙hᵉ Hᵉ
```

ofᵉ coherencesᵉ ofᵉ commutingᵉ squaresᵉ ofᵉ homotopies.ᵉ Weᵉ showᵉ in
[`foundation.commuting-squares-of-homotopies`](foundation.commuting-squares-of-homotopies.mdᵉ)
thatᵉ theseᵉ mapsᵉ areᵉ equivalences.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {fᵉ gᵉ hᵉ iᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ}
  (topᵉ : fᵉ ~ᵉ gᵉ) (leftᵉ : fᵉ ~ᵉ hᵉ) (rightᵉ : gᵉ ~ᵉ iᵉ) (bottomᵉ : hᵉ ~ᵉ iᵉ)
  where

  right-whisker-concat-coherence-square-homotopiesᵉ :
    coherence-square-homotopiesᵉ topᵉ leftᵉ rightᵉ bottomᵉ →
    {uᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ} (Hᵉ : iᵉ ~ᵉ uᵉ) →
    coherence-square-homotopiesᵉ topᵉ leftᵉ (rightᵉ ∙hᵉ Hᵉ) (bottomᵉ ∙hᵉ Hᵉ)
  right-whisker-concat-coherence-square-homotopiesᵉ cohᵉ Hᵉ xᵉ =
    right-whisker-concat-coherence-square-identificationsᵉ
      ( topᵉ xᵉ)
      ( leftᵉ xᵉ)
      ( rightᵉ xᵉ)
      ( bottomᵉ xᵉ)
      ( cohᵉ xᵉ)
      ( Hᵉ xᵉ)

  right-unwhisker-cohernece-square-homotopiesᵉ :
    {uᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ} (Hᵉ : iᵉ ~ᵉ uᵉ) →
    coherence-square-homotopiesᵉ topᵉ leftᵉ (rightᵉ ∙hᵉ Hᵉ) (bottomᵉ ∙hᵉ Hᵉ) →
    coherence-square-homotopiesᵉ topᵉ leftᵉ rightᵉ bottomᵉ
  right-unwhisker-cohernece-square-homotopiesᵉ Hᵉ cohᵉ xᵉ =
    right-unwhisker-cohernece-square-identificationsᵉ
      ( topᵉ xᵉ)
      ( leftᵉ xᵉ)
      ( rightᵉ xᵉ)
      ( bottomᵉ xᵉ)
      ( Hᵉ xᵉ)
      ( cohᵉ xᵉ)
```

### Double whiskering of commuting squares of homotopies

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {fᵉ gᵉ hᵉ uᵉ vᵉ iᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ}
  where

  double-whisker-coherence-square-homotopiesᵉ :
    (pᵉ : fᵉ ~ᵉ gᵉ)
    (topᵉ : gᵉ ~ᵉ uᵉ) (leftᵉ : gᵉ ~ᵉ hᵉ) (rightᵉ : uᵉ ~ᵉ vᵉ) (bottomᵉ : hᵉ ~ᵉ vᵉ)
    (sᵉ : vᵉ ~ᵉ iᵉ) →
    coherence-square-homotopiesᵉ topᵉ leftᵉ rightᵉ bottomᵉ →
    coherence-square-homotopiesᵉ
      ( pᵉ ∙hᵉ topᵉ)
      ( pᵉ ∙hᵉ leftᵉ)
      ( rightᵉ ∙hᵉ sᵉ)
      ( bottomᵉ ∙hᵉ sᵉ)
  double-whisker-coherence-square-homotopiesᵉ pᵉ topᵉ leftᵉ rightᵉ bottomᵉ qᵉ Hᵉ =
    left-whisker-concat-coherence-square-homotopiesᵉ pᵉ topᵉ leftᵉ
      ( rightᵉ ∙hᵉ qᵉ)
      ( bottomᵉ ∙hᵉ qᵉ)
    ( right-whisker-concat-coherence-square-homotopiesᵉ
      ( topᵉ)
      ( leftᵉ)
      ( rightᵉ)
      ( bottomᵉ)
      ( Hᵉ)
      ( qᵉ))
```

#### Left splicing coherences of commuting squares of homotopies

Forᵉ anyᵉ inverseᵉ pairᵉ ofᵉ homotopiesᵉ `Hᵉ : gᵉ ~ᵉ u`ᵉ andᵉ `Kᵉ : uᵉ ~ᵉ g`ᵉ equippedᵉ with
`αᵉ : inv-htpyᵉ Hᵉ ~ᵉ K`ᵉ weᵉ obtainᵉ mapsᵉ backᵉ andᵉ forthᵉ

```text
           topᵉ                                    topᵉ
       fᵉ ------->ᵉ gᵉ                         fᵉ ----------->ᵉ gᵉ
       |          |                         |              |
  leftᵉ |          | rightᵉ    ↔ᵉ    leftᵉ ∙hᵉ Hᵉ |              | rightᵉ
       ∨ᵉ          ∨ᵉ                         ∨ᵉ              ∨ᵉ
       hᵉ ------->ᵉ iᵉ                         uᵉ ----------->ᵉ iᵉ
          bottomᵉ                               Kᵉ ∙hᵉ bottomᵉ
```

ofᵉ coherencesᵉ ofᵉ commutingᵉ squaresᵉ ofᵉ homotopies.ᵉ Weᵉ showᵉ in
[`foundation.commuting-squares-of-homotopies`](foundation.commuting-squares-of-homotopies.mdᵉ)
thatᵉ theseᵉ mapsᵉ areᵉ equivalences.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {fᵉ gᵉ hᵉ iᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ}
  (topᵉ : fᵉ ~ᵉ gᵉ) (leftᵉ : fᵉ ~ᵉ hᵉ) (rightᵉ : gᵉ ~ᵉ iᵉ) (bottomᵉ : hᵉ ~ᵉ iᵉ)
  where

  left-splice-coherence-square-homotopiesᵉ :
    {uᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ} (Hᵉ : hᵉ ~ᵉ uᵉ) (Kᵉ : uᵉ ~ᵉ hᵉ) (αᵉ : inv-htpyᵉ Hᵉ ~ᵉ Kᵉ) →
    coherence-square-homotopiesᵉ topᵉ leftᵉ rightᵉ bottomᵉ →
    coherence-square-homotopiesᵉ topᵉ (leftᵉ ∙hᵉ Hᵉ) rightᵉ (Kᵉ ∙hᵉ bottomᵉ)
  left-splice-coherence-square-homotopiesᵉ Hᵉ Kᵉ αᵉ cohᵉ xᵉ =
    left-splice-coherence-square-identificationsᵉ
      ( topᵉ xᵉ)
      ( leftᵉ xᵉ)
      ( rightᵉ xᵉ)
      ( bottomᵉ xᵉ)
      ( Hᵉ xᵉ)
      ( Kᵉ xᵉ)
      ( αᵉ xᵉ)
      ( cohᵉ xᵉ)

  left-unsplice-coherence-square-homotopiesᵉ :
    {uᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ} (Hᵉ : hᵉ ~ᵉ uᵉ) (Kᵉ : uᵉ ~ᵉ hᵉ) (αᵉ : inv-htpyᵉ Hᵉ ~ᵉ Kᵉ) →
    coherence-square-homotopiesᵉ topᵉ (leftᵉ ∙hᵉ Hᵉ) rightᵉ (Kᵉ ∙hᵉ bottomᵉ) →
    coherence-square-homotopiesᵉ topᵉ leftᵉ rightᵉ bottomᵉ
  left-unsplice-coherence-square-homotopiesᵉ Hᵉ Kᵉ αᵉ cohᵉ xᵉ =
    left-unsplice-coherence-square-identificationsᵉ
      ( topᵉ xᵉ)
      ( leftᵉ xᵉ)
      ( rightᵉ xᵉ)
      ( bottomᵉ xᵉ)
      ( Hᵉ xᵉ)
      ( Kᵉ xᵉ)
      ( αᵉ xᵉ)
      ( cohᵉ xᵉ)
```

#### Right splicing coherences of commuting squares of homotopies

Forᵉ anyᵉ inverseᵉ pairᵉ ofᵉ homotopiesᵉ `Hᵉ : gᵉ ~ᵉ u`ᵉ andᵉ `Kᵉ : uᵉ ~ᵉ g`ᵉ equippedᵉ with
`αᵉ : inv-htpyᵉ Hᵉ ~ᵉ K`ᵉ weᵉ obtainᵉ mapsᵉ backᵉ andᵉ forthᵉ

```text
           topᵉ                             topᵉ ∙hᵉ Hᵉ
       fᵉ ------->ᵉ gᵉ                     fᵉ -------->ᵉ uᵉ
       |          |                     |           |
  leftᵉ |          | rightᵉ    ↔ᵉ     leftᵉ |           | Kᵉ ∙hᵉ rightᵉ
       ∨ᵉ          ∨ᵉ                     ∨ᵉ           ∨ᵉ
       hᵉ ------->ᵉ iᵉ                     hᵉ -------->ᵉ iᵉ
          bottomᵉ                           bottomᵉ
```

ofᵉ coherencesᵉ ofᵉ commutingᵉ squaresᵉ ofᵉ homotopies.ᵉ Weᵉ showᵉ in
[`foundation.commuting-squares-of-homotopies`](foundation.commuting-squares-of-homotopies.mdᵉ)
thatᵉ theseᵉ mapsᵉ areᵉ equivalences.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {fᵉ gᵉ hᵉ iᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ}
  (topᵉ : fᵉ ~ᵉ gᵉ) (leftᵉ : fᵉ ~ᵉ hᵉ) (rightᵉ : gᵉ ~ᵉ iᵉ) (bottomᵉ : hᵉ ~ᵉ iᵉ)
  where

  right-splice-coherence-square-homotopiesᵉ :
    {uᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ} (Hᵉ : gᵉ ~ᵉ uᵉ) (Kᵉ : uᵉ ~ᵉ gᵉ) (αᵉ : inv-htpyᵉ Hᵉ ~ᵉ Kᵉ) →
    coherence-square-homotopiesᵉ topᵉ leftᵉ rightᵉ bottomᵉ →
    coherence-square-homotopiesᵉ (topᵉ ∙hᵉ Hᵉ) leftᵉ (inv-htpyᵉ Hᵉ ∙hᵉ rightᵉ) bottomᵉ
  right-splice-coherence-square-homotopiesᵉ Hᵉ Kᵉ αᵉ cohᵉ xᵉ =
    right-splice-coherence-square-identificationsᵉ
      ( topᵉ xᵉ)
      ( leftᵉ xᵉ)
      ( rightᵉ xᵉ)
      ( bottomᵉ xᵉ)
      ( Hᵉ xᵉ)
      ( Kᵉ xᵉ)
      ( αᵉ xᵉ)
      ( cohᵉ xᵉ)

  right-unsplice-coherence-square-homotopiesᵉ :
    {uᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ} (Hᵉ : gᵉ ~ᵉ uᵉ) (Kᵉ : uᵉ ~ᵉ gᵉ) (αᵉ : inv-htpyᵉ Hᵉ ~ᵉ Kᵉ) →
    coherence-square-homotopiesᵉ (topᵉ ∙hᵉ Hᵉ) leftᵉ (inv-htpyᵉ Hᵉ ∙hᵉ rightᵉ) bottomᵉ →
    coherence-square-homotopiesᵉ topᵉ leftᵉ rightᵉ bottomᵉ
  right-unsplice-coherence-square-homotopiesᵉ Hᵉ Kᵉ αᵉ cohᵉ xᵉ =
    right-unsplice-coherence-square-identificationsᵉ
      ( topᵉ xᵉ)
      ( leftᵉ xᵉ)
      ( rightᵉ xᵉ)
      ( bottomᵉ xᵉ)
      ( Hᵉ xᵉ)
      ( Kᵉ xᵉ)
      ( αᵉ xᵉ)
      ( cohᵉ xᵉ)
```

### Horizontally pasting squares of homotopies

Considerᵉ twoᵉ squaresᵉ ofᵉ homotopiesᵉ asᵉ in theᵉ diagramᵉ

```text
            top-leftᵉ         top-rightᵉ
       aᵉ ------------->ᵉ bᵉ ------------->ᵉ cᵉ
       |                |                |
  leftᵉ |                | middleᵉ         | rightᵉ
       ∨ᵉ                ∨ᵉ                ∨ᵉ
       dᵉ ------------->ᵉ eᵉ ------------->ᵉ fᵉ
          bottom-leftᵉ      bottom-rightᵉ
```

with `Hᵉ : leftᵉ ∙hᵉ bottom-leftᵉ ~ᵉ top-leftᵉ ∙hᵉ middle`ᵉ andᵉ
`Kᵉ : middleᵉ ∙hᵉ bottom-rightᵉ ~ᵉ top-rightᵉ ∙hᵉ right`.ᵉ Thenᵉ theᵉ outerᵉ squareᵉ
commutes.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {aᵉ bᵉ cᵉ dᵉ eᵉ fᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ}
  (top-leftᵉ : aᵉ ~ᵉ bᵉ) (top-rightᵉ : bᵉ ~ᵉ cᵉ)
  (leftᵉ : aᵉ ~ᵉ dᵉ) (middleᵉ : bᵉ ~ᵉ eᵉ) (rightᵉ : cᵉ ~ᵉ fᵉ)
  (bottom-leftᵉ : dᵉ ~ᵉ eᵉ) (bottom-rightᵉ : eᵉ ~ᵉ fᵉ)
  where

  horizontal-pasting-coherence-square-homotopiesᵉ :
    coherence-square-homotopiesᵉ top-leftᵉ leftᵉ middleᵉ bottom-leftᵉ →
    coherence-square-homotopiesᵉ top-rightᵉ middleᵉ rightᵉ bottom-rightᵉ →
    coherence-square-homotopiesᵉ
      (top-leftᵉ ∙hᵉ top-rightᵉ) leftᵉ rightᵉ (bottom-leftᵉ ∙hᵉ bottom-rightᵉ)
  horizontal-pasting-coherence-square-homotopiesᵉ Hᵉ Kᵉ xᵉ =
    horizontal-pasting-coherence-square-identificationsᵉ
      ( top-leftᵉ xᵉ)
      ( top-rightᵉ xᵉ)
      ( leftᵉ xᵉ)
      ( middleᵉ xᵉ)
      ( rightᵉ xᵉ)
      ( bottom-leftᵉ xᵉ)
      ( bottom-rightᵉ xᵉ)
      ( Hᵉ xᵉ)
      ( Kᵉ xᵉ)
```

### Vertically pasting squares of homotopies

Considerᵉ twoᵉ squaresᵉ ofᵉ homotopiesᵉ asᵉ in theᵉ diagramᵉ

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

with `Hᵉ : top-leftᵉ ∙hᵉ middleᵉ ~ᵉ topᵉ ∙hᵉ top-right`ᵉ andᵉ
`Kᵉ : bottom-leftᵉ ∙hᵉ bottomᵉ ~ᵉ middleᵉ ∙hᵉ bottom-right`.ᵉ Thenᵉ theᵉ outerᵉ squareᵉ
commutes.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {aᵉ bᵉ cᵉ dᵉ eᵉ fᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ}
  (topᵉ : aᵉ ~ᵉ bᵉ) (top-leftᵉ : aᵉ ~ᵉ cᵉ) (top-rightᵉ : bᵉ ~ᵉ dᵉ)
  (middleᵉ : cᵉ ~ᵉ dᵉ) (bottom-leftᵉ : cᵉ ~ᵉ eᵉ) (bottom-rightᵉ : dᵉ ~ᵉ fᵉ)
  (bottomᵉ : eᵉ ~ᵉ fᵉ)
  where

  vertical-pasting-coherence-square-homotopiesᵉ :
    coherence-square-homotopiesᵉ topᵉ top-leftᵉ top-rightᵉ middleᵉ →
    coherence-square-homotopiesᵉ middleᵉ bottom-leftᵉ bottom-rightᵉ bottomᵉ →
    coherence-square-homotopiesᵉ
      topᵉ (top-leftᵉ ∙hᵉ bottom-leftᵉ) (top-rightᵉ ∙hᵉ bottom-rightᵉ) bottomᵉ
  vertical-pasting-coherence-square-homotopiesᵉ Hᵉ Kᵉ xᵉ =
    vertical-pasting-coherence-square-identificationsᵉ
      ( topᵉ xᵉ)
      ( top-leftᵉ xᵉ)
      ( top-rightᵉ xᵉ)
      ( middleᵉ xᵉ)
      ( bottom-leftᵉ xᵉ)
      ( bottom-rightᵉ xᵉ)
      ( bottomᵉ xᵉ)
      ( Hᵉ xᵉ)
      ( Kᵉ xᵉ)
```

## Properties

### Left unit law for horizontal pasting of commuting squares of homotopies

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {fᵉ gᵉ hᵉ iᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ}
  where

  left-unit-law-horizontal-pasting-coherence-square-homotopiesᵉ :
    (topᵉ : fᵉ ~ᵉ gᵉ) (leftᵉ : fᵉ ~ᵉ hᵉ) (rightᵉ : gᵉ ~ᵉ iᵉ) (bottomᵉ : hᵉ ~ᵉ iᵉ) →
    (Hᵉ : coherence-square-homotopiesᵉ topᵉ leftᵉ rightᵉ bottomᵉ) →
    horizontal-pasting-coherence-square-homotopiesᵉ
      ( refl-htpyᵉ)
      ( topᵉ)
      ( leftᵉ)
      ( leftᵉ)
      ( rightᵉ)
      ( refl-htpyᵉ)
      ( bottomᵉ)
      ( horizontal-refl-coherence-square-homotopiesᵉ leftᵉ)
      ( Hᵉ) ~ᵉ
    Hᵉ
  left-unit-law-horizontal-pasting-coherence-square-homotopiesᵉ
    topᵉ leftᵉ rightᵉ bottomᵉ Hᵉ xᵉ =
    left-unit-law-horizontal-pasting-coherence-square-identificationsᵉ
      ( topᵉ xᵉ)
      ( leftᵉ xᵉ)
      ( rightᵉ xᵉ)
      ( bottomᵉ xᵉ)
      ( Hᵉ xᵉ)
```

### Right unit law for horizontal pasting of commuting squares of homotopies

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {fᵉ gᵉ hᵉ iᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ}
  where

  right-unit-law-horizontal-pasting-coherence-square-homotopiesᵉ :
    (topᵉ : fᵉ ~ᵉ gᵉ) (leftᵉ : fᵉ ~ᵉ hᵉ) (rightᵉ : gᵉ ~ᵉ iᵉ) (bottomᵉ : hᵉ ~ᵉ iᵉ) →
    (Hᵉ : coherence-square-homotopiesᵉ topᵉ leftᵉ rightᵉ bottomᵉ) →
    horizontal-pasting-coherence-square-homotopiesᵉ
      ( topᵉ)
      ( refl-htpyᵉ)
      ( leftᵉ)
      ( rightᵉ)
      ( rightᵉ)
      ( bottomᵉ)
      ( refl-htpyᵉ)
      ( Hᵉ)
      ( horizontal-refl-coherence-square-homotopiesᵉ rightᵉ) ∙hᵉ
    right-whisker-concat-htpyᵉ right-unit-htpyᵉ rightᵉ ~ᵉ
    left-whisker-concat-htpyᵉ leftᵉ right-unit-htpyᵉ ∙hᵉ Hᵉ
  right-unit-law-horizontal-pasting-coherence-square-homotopiesᵉ
    topᵉ leftᵉ rightᵉ bottomᵉ Hᵉ xᵉ =
    right-unit-law-horizontal-pasting-coherence-square-identificationsᵉ
      ( topᵉ xᵉ)
      ( leftᵉ xᵉ)
      ( rightᵉ xᵉ)
      ( bottomᵉ xᵉ)
      ( Hᵉ xᵉ)
```

### Left unit law for vertical pasting of commuting squares of homotopies

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {fᵉ gᵉ hᵉ iᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ}
  where

  left-unit-law-vertical-pasting-coherence-square-homotopiesᵉ :
    (topᵉ : fᵉ ~ᵉ gᵉ) (leftᵉ : fᵉ ~ᵉ hᵉ) (rightᵉ : gᵉ ~ᵉ iᵉ) (bottomᵉ : hᵉ ~ᵉ iᵉ) →
    (Hᵉ : coherence-square-homotopiesᵉ topᵉ leftᵉ rightᵉ bottomᵉ) →
    vertical-pasting-coherence-square-homotopiesᵉ
      ( topᵉ)
      ( refl-htpyᵉ)
      ( refl-htpyᵉ)
      ( topᵉ)
      ( leftᵉ)
      ( rightᵉ)
      ( bottomᵉ)
      ( vertical-refl-coherence-square-homotopiesᵉ topᵉ)
      ( Hᵉ) ~ᵉ
    Hᵉ
  left-unit-law-vertical-pasting-coherence-square-homotopiesᵉ
    topᵉ leftᵉ rightᵉ bottomᵉ Hᵉ xᵉ =
    left-unit-law-vertical-pasting-coherence-square-identificationsᵉ
      ( topᵉ xᵉ)
      ( leftᵉ xᵉ)
      ( rightᵉ xᵉ)
      ( bottomᵉ xᵉ)
      ( Hᵉ xᵉ)
```

### Right unit law for vertical pasting of commuting squares of homotopies

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {fᵉ gᵉ hᵉ iᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ}
  where

  right-unit-law-vertical-pasting-coherence-square-homotopiesᵉ :
    (topᵉ : fᵉ ~ᵉ gᵉ) (leftᵉ : fᵉ ~ᵉ hᵉ) (rightᵉ : gᵉ ~ᵉ iᵉ) (bottomᵉ : hᵉ ~ᵉ iᵉ) →
    (Hᵉ : coherence-square-homotopiesᵉ topᵉ leftᵉ rightᵉ bottomᵉ) →
    vertical-pasting-coherence-square-homotopiesᵉ
      ( topᵉ)
      ( leftᵉ)
      ( rightᵉ)
      ( bottomᵉ)
      ( refl-htpyᵉ)
      ( refl-htpyᵉ)
      ( bottomᵉ)
      ( Hᵉ)
      ( vertical-refl-coherence-square-homotopiesᵉ bottomᵉ) ∙hᵉ
    left-whisker-concat-htpyᵉ topᵉ right-unit-htpyᵉ ~ᵉ
    right-whisker-concat-htpyᵉ right-unit-htpyᵉ bottomᵉ ∙hᵉ Hᵉ
  right-unit-law-vertical-pasting-coherence-square-homotopiesᵉ
    topᵉ leftᵉ rightᵉ bottomᵉ Hᵉ xᵉ =
    right-unit-law-vertical-pasting-coherence-square-identificationsᵉ
      ( topᵉ xᵉ)
      ( leftᵉ xᵉ)
      ( rightᵉ xᵉ)
      ( bottomᵉ xᵉ)
      ( Hᵉ xᵉ)
```

### Computing the right whiskering of a vertically constant square with a homotopy

Considerᵉ theᵉ verticallyᵉ constantᵉ squareᵉ ofᵉ homotopiesᵉ

```text
           Hᵉ
       fᵉ ----->ᵉ gᵉ
       |        |
  reflᵉ |        | reflᵉ
       ∨ᵉ        ∨ᵉ
       fᵉ ----->ᵉ gᵉ
           Hᵉ
```

atᵉ aᵉ homotopyᵉ `Hᵉ : fᵉ ~ᵉ g`,ᵉ andᵉ considerᵉ aᵉ homotopyᵉ `Kᵉ : gᵉ ~ᵉ h`.ᵉ Thenᵉ theᵉ rightᵉ
whiskeringᵉ ofᵉ theᵉ aboveᵉ squareᵉ with `K`ᵉ isᵉ theᵉ commutingᵉ squareᵉ ofᵉ homotopiesᵉ

```text
            Hᵉ
       fᵉ ------->ᵉ gᵉ
       |          |
  reflᵉ |   reflᵉ   | Kᵉ
       ∨ᵉ          ∨ᵉ
       fᵉ ------->ᵉ hᵉ
          Hᵉ ∙hᵉ Kᵉ
```

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {fᵉ gᵉ hᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ}
  where

  right-whisker-concat-vertical-refl-coherence-square-homotopiesᵉ :
    (Hᵉ : fᵉ ~ᵉ gᵉ) (Kᵉ : gᵉ ~ᵉ hᵉ) →
    right-whisker-concat-coherence-square-homotopiesᵉ Hᵉ refl-htpyᵉ refl-htpyᵉ Hᵉ
      ( vertical-refl-coherence-square-homotopiesᵉ Hᵉ)
      ( Kᵉ) ~ᵉ
    refl-htpyᵉ
  right-whisker-concat-vertical-refl-coherence-square-homotopiesᵉ Hᵉ Kᵉ xᵉ =
    right-whisker-concat-vertical-refl-coherence-square-identificationsᵉ
      ( Hᵉ xᵉ)
      ( Kᵉ xᵉ)
```

### Computing the right whiskering of a horizontally constant square with a homotopy

Considerᵉ aᵉ horizontallyᵉ constantᵉ commutingᵉ squareᵉ ofᵉ homotopiesᵉ

```text
       refl-htpyᵉ
    fᵉ ---------->ᵉ fᵉ
    |             |
  Hᵉ |             | Hᵉ
    ∨ᵉ             ∨ᵉ
    gᵉ ---------->ᵉ gᵉ
       refl-htpyᵉ
```

atᵉ aᵉ homotopyᵉ `H`ᵉ andᵉ considerᵉ aᵉ homotopyᵉ `Kᵉ : gᵉ ~ᵉ h`.ᵉ Thenᵉ theᵉ rightᵉ whiskeringᵉ
ofᵉ theᵉ aboveᵉ squareᵉ with `K`ᵉ isᵉ theᵉ squareᵉ

```text
       refl-htpyᵉ
    fᵉ ---------->ᵉ fᵉ
    |             |
  Hᵉ |  refl-htpyᵉ  | Hᵉ ∙hᵉ Kᵉ
    ∨ᵉ             ∨ᵉ
    gᵉ ---------->ᵉ h.ᵉ
           Kᵉ
```

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {fᵉ gᵉ hᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ}
  where

  right-whisker-concat-horizontal-refl-coherence-square-homotopiesᵉ :
    (Hᵉ : fᵉ ~ᵉ gᵉ) (Kᵉ : gᵉ ~ᵉ hᵉ) →
    right-whisker-concat-coherence-square-homotopiesᵉ refl-htpyᵉ Hᵉ Hᵉ refl-htpyᵉ
      ( horizontal-refl-coherence-square-homotopiesᵉ Hᵉ)
      ( Kᵉ) ~ᵉ
    refl-htpyᵉ
  right-whisker-concat-horizontal-refl-coherence-square-homotopiesᵉ Hᵉ Kᵉ xᵉ =
    right-whisker-concat-horizontal-refl-coherence-square-identificationsᵉ
      ( Hᵉ xᵉ)
      ( Kᵉ xᵉ)
```

### Computing the left whiskering of a horizontally constant square with a homotopy

Considerᵉ aᵉ homotopyᵉ `Hᵉ : fᵉ ~ᵉ g`ᵉ andᵉ aᵉ horizontallyᵉ constantᵉ commutingᵉ squareᵉ ofᵉ
homotopiesᵉ

```text
       refl-htpyᵉ
    gᵉ ---------->ᵉ gᵉ
    |             |
  Kᵉ |             | Kᵉ
    ∨ᵉ             ∨ᵉ
    hᵉ ---------->ᵉ hᵉ
       refl-htpyᵉ
```

atᵉ aᵉ homotopyᵉ `Kᵉ : gᵉ ~ᵉ h`.ᵉ Theᵉ theᵉ leftᵉ whiskeringᵉ ofᵉ theᵉ aboveᵉ squareᵉ with `H`ᵉ
isᵉ theᵉ commutingᵉ squareᵉ

```text
                                    Kᵉ ∙hᵉ refl-htpyᵉ
         fᵉ ----------------------------------------------------------------->ᵉ gᵉ
         |                                                                    |
  Kᵉ ∙hᵉ Hᵉ | right-unit-htpyᵉ ∙hᵉ (right-whisker-concat-htpyᵉ right-unit-htpyᵉ H)⁻¹ᵉ | Hᵉ
         ∨ᵉ                                                                    ∨ᵉ
         hᵉ ----------------------------------------------------------------->ᵉ h.ᵉ
                                      refl-htpyᵉ
```

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {fᵉ gᵉ hᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ}
  where

  left-whisker-concat-horizontal-refl-coherence-square-homotopiesᵉ :
    (Hᵉ : fᵉ ~ᵉ gᵉ) (Kᵉ : gᵉ ~ᵉ hᵉ) →
    left-whisker-concat-coherence-square-homotopiesᵉ Hᵉ refl-htpyᵉ Kᵉ Kᵉ refl-htpyᵉ
      ( horizontal-refl-coherence-square-homotopiesᵉ Kᵉ) ∙hᵉ
    right-whisker-concat-htpyᵉ right-unit-htpyᵉ Kᵉ ~ᵉ
    right-unit-htpyᵉ
  left-whisker-concat-horizontal-refl-coherence-square-homotopiesᵉ Hᵉ Kᵉ xᵉ =
    left-whisker-concat-horizontal-refl-coherence-square-identificationsᵉ
      ( Hᵉ xᵉ)
      ( Kᵉ xᵉ)

  left-whisker-concat-horizontal-refl-coherence-square-homotopies'ᵉ :
    (Hᵉ : fᵉ ~ᵉ gᵉ) (Kᵉ : gᵉ ~ᵉ hᵉ) →
    left-whisker-concat-coherence-square-homotopiesᵉ Hᵉ refl-htpyᵉ Kᵉ Kᵉ refl-htpyᵉ
      ( horizontal-refl-coherence-square-homotopiesᵉ Kᵉ) ~ᵉ
    right-unit-htpyᵉ ∙hᵉ inv-htpyᵉ (right-whisker-concat-htpyᵉ right-unit-htpyᵉ Kᵉ)
  left-whisker-concat-horizontal-refl-coherence-square-homotopies'ᵉ Hᵉ Kᵉ xᵉ =
    left-whisker-concat-horizontal-refl-coherence-square-identifications'ᵉ
      ( Hᵉ xᵉ)
      ( Kᵉ xᵉ)
```

### Computing the left whiskering of a vertically constant square with a homotopy

Considerᵉ theᵉ verticallyᵉ constantᵉ squareᵉ ofᵉ homotopiesᵉ

```text
                Kᵉ
            gᵉ ----->ᵉ hᵉ
            |        |
  refl-htpyᵉ |        | refl-htpyᵉ
            ∨ᵉ        ∨ᵉ
            gᵉ ----->ᵉ hᵉ
                Kᵉ
```

atᵉ aᵉ homotopyᵉ `Kᵉ : gᵉ ~ᵉ h`ᵉ andᵉ considerᵉ aᵉ homotopyᵉ `Hᵉ : fᵉ ~ᵉ g`.ᵉ Thenᵉ theᵉ leftᵉ
whiskeringᵉ ofᵉ theᵉ aboveᵉ squareᵉ with `H`ᵉ isᵉ theᵉ squareᵉ

```text
                                            Hᵉ ∙hᵉ Kᵉ
                 fᵉ ---------------------------------------------------------->ᵉ hᵉ
                 |                                                             |
  Hᵉ ∙hᵉ refl-htpyᵉ | right-whisker-concat-htpyᵉ right-unit-htpyᵉ Kᵉ ∙hᵉ right-unit⁻¹ᵉ | refl-htpyᵉ
                 ∨ᵉ                                                             ∨ᵉ
                 gᵉ ---------------------------------------------------------->ᵉ h.ᵉ
                                              Kᵉ
```

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {fᵉ gᵉ hᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ}
  where

  left-whisker-concat-vertical-refl-coherence-square-homotopiesᵉ :
    (Hᵉ : fᵉ ~ᵉ gᵉ) (Kᵉ : gᵉ ~ᵉ hᵉ) →
    left-whisker-concat-coherence-square-homotopiesᵉ Hᵉ Kᵉ refl-htpyᵉ refl-htpyᵉ Kᵉ
      ( vertical-refl-coherence-square-homotopiesᵉ Kᵉ) ∙hᵉ
    right-unit-htpyᵉ ~ᵉ
    right-whisker-concat-htpyᵉ right-unit-htpyᵉ Kᵉ
  left-whisker-concat-vertical-refl-coherence-square-homotopiesᵉ Hᵉ Kᵉ xᵉ =
    left-whisker-concat-vertical-refl-coherence-square-identificationsᵉ
      ( Hᵉ xᵉ)
      ( Kᵉ xᵉ)

  left-whisker-concat-vertical-refl-coherence-square-homotopies'ᵉ :
    (Hᵉ : fᵉ ~ᵉ gᵉ) (Kᵉ : gᵉ ~ᵉ hᵉ) →
    left-whisker-concat-coherence-square-homotopiesᵉ Hᵉ Kᵉ refl-htpyᵉ refl-htpyᵉ Kᵉ
      ( vertical-refl-coherence-square-homotopiesᵉ Kᵉ) ~ᵉ
    right-whisker-concat-htpyᵉ right-unit-htpyᵉ Kᵉ ∙hᵉ inv-htpyᵉ right-unit-htpyᵉ
  left-whisker-concat-vertical-refl-coherence-square-homotopies'ᵉ Hᵉ Kᵉ xᵉ =
    left-whisker-concat-vertical-refl-coherence-square-identifications'ᵉ
      ( Hᵉ xᵉ)
      ( Kᵉ xᵉ)
```

### Left whiskering horizontal concatenations of squares with homotopies

Considerᵉ aᵉ commutingᵉ diagramᵉ ofᵉ homotopiesᵉ ofᵉ theᵉ formᵉ

```text
            top-leftᵉ        top-rightᵉ
       aᵉ ------------->ᵉ cᵉ ------------->ᵉ eᵉ
       |                |                |
  leftᵉ |                | middleᵉ         | rightᵉ
       ∨ᵉ                ∨ᵉ                ∨ᵉ
       bᵉ ------------->ᵉ dᵉ ------------->ᵉ fᵉ
          bottom-leftᵉ      bottom-rightᵉ
```

andᵉ considerᵉ aᵉ homotopyᵉ `Hᵉ : fᵉ ~ᵉ a`.ᵉ Thenᵉ theᵉ leftᵉ whiskeringᵉ ofᵉ `H`ᵉ andᵉ theᵉ
horizontalᵉ concatenationᵉ ofᵉ coherencesᵉ ofᵉ commutingᵉ squaresᵉ isᵉ upᵉ to
associativityᵉ theᵉ horizontalᵉ concatenationᵉ ofᵉ theᵉ squaresᵉ

```text
               Hᵉ ∙hᵉ top-leftᵉ      top-rightᵉ
            uᵉ ------------->ᵉ cᵉ ------------->ᵉ eᵉ
            |                |                |
  Hᵉ ∙hᵉ leftᵉ |                | middleᵉ         | rightᵉ
            ∨ᵉ                ∨ᵉ                ∨ᵉ
            bᵉ ------------->ᵉ dᵉ ------------->ᵉ fᵉ
               bottom-leftᵉ      bottom-rightᵉ
```

where theᵉ leftᵉ squareᵉ isᵉ theᵉ leftᵉ whiskeringᵉ ofᵉ `H`ᵉ andᵉ theᵉ originalᵉ leftᵉ
square.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  left-whisker-concat-horizontal-pasting-coherence-square-homotopiesᵉ :
    {uᵉ aᵉ bᵉ cᵉ dᵉ eᵉ fᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ} (Hᵉ : uᵉ ~ᵉ aᵉ)
    (top-leftᵉ : aᵉ ~ᵉ cᵉ) (top-rightᵉ : cᵉ ~ᵉ eᵉ)
    (leftᵉ : aᵉ ~ᵉ bᵉ) (middleᵉ : cᵉ ~ᵉ dᵉ) (rightᵉ : eᵉ ~ᵉ fᵉ)
    (bottom-leftᵉ : bᵉ ~ᵉ dᵉ) (bottom-rightᵉ : dᵉ ~ᵉ fᵉ)
    (lᵉ : coherence-square-homotopiesᵉ top-leftᵉ leftᵉ middleᵉ bottom-leftᵉ)
    (rᵉ : coherence-square-homotopiesᵉ top-rightᵉ middleᵉ rightᵉ bottom-rightᵉ) →
    left-whisker-concat-coherence-square-homotopiesᵉ Hᵉ
      ( top-leftᵉ ∙hᵉ top-rightᵉ)
      ( leftᵉ)
      ( rightᵉ)
      ( bottom-leftᵉ ∙hᵉ bottom-rightᵉ)
      ( horizontal-pasting-coherence-square-homotopiesᵉ
        ( top-leftᵉ)
        ( top-rightᵉ)
        ( leftᵉ)
        ( middleᵉ)
        ( rightᵉ)
        ( bottom-leftᵉ)
        ( bottom-rightᵉ)
        ( lᵉ)
        ( rᵉ)) ~ᵉ
    horizontal-pasting-coherence-square-homotopiesᵉ
      ( Hᵉ ∙hᵉ top-leftᵉ)
      ( top-rightᵉ)
      ( Hᵉ ∙hᵉ leftᵉ)
      ( middleᵉ)
      ( rightᵉ)
      ( bottom-leftᵉ)
      ( bottom-rightᵉ)
      ( left-whisker-concat-coherence-square-homotopiesᵉ Hᵉ
        ( top-leftᵉ)
        ( leftᵉ)
        ( middleᵉ)
        ( bottom-leftᵉ)
        ( lᵉ))
      ( rᵉ) ∙hᵉ
    right-whisker-concat-htpyᵉ
      ( assoc-htpyᵉ Hᵉ top-leftᵉ top-rightᵉ)
      ( rightᵉ)
  left-whisker-concat-horizontal-pasting-coherence-square-homotopiesᵉ
    Hᵉ top-leftᵉ top-rightᵉ leftᵉ middleᵉ rightᵉ bottom-leftᵉ bottom-rightᵉ lᵉ rᵉ xᵉ =
    left-whisker-concat-horizontal-pasting-coherence-square-identificationsᵉ
      ( Hᵉ xᵉ)
      ( top-leftᵉ xᵉ)
      ( top-rightᵉ xᵉ)
      ( leftᵉ xᵉ)
      ( middleᵉ xᵉ)
      ( rightᵉ xᵉ)
      ( bottom-leftᵉ xᵉ)
      ( bottom-rightᵉ xᵉ)
      ( lᵉ xᵉ)
      ( rᵉ xᵉ)
```

### Left whiskering vertical concatenations of squares with homotopies

Considerᵉ twoᵉ squaresᵉ ofᵉ homotopiesᵉ asᵉ in theᵉ diagramᵉ

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

andᵉ considerᵉ aᵉ homotopyᵉ `Hᵉ : fᵉ ~ᵉ a`.ᵉ Thenᵉ theᵉ leftᵉ whiskeringᵉ ofᵉ `H`ᵉ with theᵉ
verticalᵉ pastingᵉ ofᵉ theᵉ twoᵉ squaresᵉ aboveᵉ isᵉ upᵉ to associativityᵉ theᵉ verticalᵉ
pastingᵉ ofᵉ theᵉ squaresᵉ

```text
                  Hᵉ ∙hᵉ topᵉ
                uᵉ -------->ᵉ bᵉ
                |           |
  Hᵉ ∙hᵉ top-leftᵉ |           | top-rightᵉ
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
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  left-whisker-concat-vertical-concat-coherence-square-homotopiesᵉ :
    {uᵉ aᵉ bᵉ cᵉ dᵉ eᵉ fᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ} (Hᵉ : uᵉ ~ᵉ aᵉ) →
    (topᵉ : aᵉ ~ᵉ bᵉ) (top-leftᵉ : aᵉ ~ᵉ cᵉ) (top-rightᵉ : bᵉ ~ᵉ dᵉ) (middleᵉ : cᵉ ~ᵉ dᵉ)
    (bottom-leftᵉ : cᵉ ~ᵉ eᵉ) (bottom-rightᵉ : dᵉ ~ᵉ fᵉ) (bottomᵉ : eᵉ ~ᵉ fᵉ)
    (tᵉ : coherence-square-homotopiesᵉ topᵉ top-leftᵉ top-rightᵉ middleᵉ) →
    (bᵉ :
      coherence-square-homotopiesᵉ middleᵉ bottom-leftᵉ bottom-rightᵉ bottomᵉ) →
    right-whisker-concat-htpyᵉ (assoc-htpyᵉ Hᵉ top-leftᵉ bottom-leftᵉ) bottomᵉ ∙hᵉ
    left-whisker-concat-coherence-square-homotopiesᵉ Hᵉ
      ( topᵉ)
      ( top-leftᵉ ∙hᵉ bottom-leftᵉ)
      ( top-rightᵉ ∙hᵉ bottom-rightᵉ)
      ( bottomᵉ)
      ( vertical-pasting-coherence-square-homotopiesᵉ
        ( topᵉ)
        ( top-leftᵉ)
        ( top-rightᵉ)
        ( middleᵉ)
        ( bottom-leftᵉ)
        ( bottom-rightᵉ)
        ( bottomᵉ)
        ( tᵉ)
        ( bᵉ)) ~ᵉ
    vertical-pasting-coherence-square-homotopiesᵉ
      ( Hᵉ ∙hᵉ topᵉ)
      ( Hᵉ ∙hᵉ top-leftᵉ)
      ( top-rightᵉ)
      ( middleᵉ)
      ( bottom-leftᵉ)
      ( bottom-rightᵉ)
      ( bottomᵉ)
      ( left-whisker-concat-coherence-square-homotopiesᵉ Hᵉ
        ( topᵉ)
        ( top-leftᵉ)
        ( top-rightᵉ)
        ( middleᵉ)
        ( tᵉ))
      ( bᵉ)
  left-whisker-concat-vertical-concat-coherence-square-homotopiesᵉ
    Hᵉ topᵉ top-leftᵉ top-rightᵉ middleᵉ bottom-leftᵉ bottom-rightᵉ bottomᵉ tᵉ bᵉ xᵉ =
    left-whisker-concat-vertical-concat-coherence-square-identificationsᵉ
      ( Hᵉ xᵉ)
      ( topᵉ xᵉ)
      ( top-leftᵉ xᵉ)
      ( top-rightᵉ xᵉ)
      ( middleᵉ xᵉ)
      ( bottom-leftᵉ xᵉ)
      ( bottom-rightᵉ xᵉ)
      ( bottomᵉ xᵉ)
      ( tᵉ xᵉ)
      ( bᵉ xᵉ)
```

### Right whiskering horizontal pastings of commuting squares of homotopies

Considerᵉ aᵉ commutingᵉ diagramᵉ ofᵉ homotopiesᵉ ofᵉ theᵉ formᵉ

```text
            top-leftᵉ        top-rightᵉ
       aᵉ ------------->ᵉ cᵉ ------------->ᵉ eᵉ
       |                |                |
  leftᵉ |                | middleᵉ         | rightᵉ
       ∨ᵉ                ∨ᵉ                ∨ᵉ
       bᵉ ------------->ᵉ dᵉ ------------->ᵉ fᵉ
          bottom-leftᵉ      bottom-rightᵉ
```

andᵉ considerᵉ aᵉ homotopyᵉ `Kᵉ : fᵉ ~ᵉ g`.ᵉ Thenᵉ theᵉ rightᵉ whiskeringᵉ ofᵉ theᵉ horizontalᵉ
pastingᵉ ofᵉ theᵉ squaresᵉ aboveᵉ isᵉ upᵉ to associativityᵉ theᵉ horizontalᵉ pastingᵉ ofᵉ
theᵉ squaresᵉ

```text
            top-leftᵉ           top-rightᵉ
       aᵉ ------------->ᵉ cᵉ ------------------>ᵉ eᵉ
       |                |                     |
  leftᵉ |                | middleᵉ              | rightᵉ ∙hᵉ Kᵉ
       ∨ᵉ                ∨ᵉ                     ∨ᵉ
       bᵉ ------------->ᵉ dᵉ ------------------>ᵉ gᵉ
          bottom-leftᵉ      bottom-rightᵉ ∙hᵉ Kᵉ
```

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  right-whisker-concat-horizontal-pasting-coherence-square-homotopiesᵉ :
    {aᵉ bᵉ cᵉ dᵉ eᵉ fᵉ gᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ}
    (top-leftᵉ : aᵉ ~ᵉ cᵉ) (top-rightᵉ : cᵉ ~ᵉ eᵉ)
    (leftᵉ : aᵉ ~ᵉ bᵉ) (middleᵉ : cᵉ ~ᵉ dᵉ) (rightᵉ : eᵉ ~ᵉ fᵉ)
    (bottom-leftᵉ : bᵉ ~ᵉ dᵉ) (bottom-rightᵉ : dᵉ ~ᵉ fᵉ)
    (lᵉ : coherence-square-homotopiesᵉ top-leftᵉ leftᵉ middleᵉ bottom-leftᵉ) →
    (rᵉ : coherence-square-homotopiesᵉ top-rightᵉ middleᵉ rightᵉ bottom-rightᵉ) →
    (Kᵉ : fᵉ ~ᵉ gᵉ) →
    right-whisker-concat-coherence-square-homotopiesᵉ
      ( top-leftᵉ ∙hᵉ top-rightᵉ)
      ( leftᵉ)
      ( rightᵉ)
      ( bottom-leftᵉ ∙hᵉ bottom-rightᵉ)
      ( horizontal-pasting-coherence-square-homotopiesᵉ
        ( top-leftᵉ)
        ( top-rightᵉ)
        ( leftᵉ)
        ( middleᵉ)
        ( rightᵉ)
        ( bottom-leftᵉ)
        ( bottom-rightᵉ)
        ( lᵉ)
        ( rᵉ))
      ( Kᵉ) ~ᵉ
    left-whisker-concat-htpyᵉ leftᵉ (assoc-htpyᵉ bottom-leftᵉ bottom-rightᵉ Kᵉ) ∙hᵉ
    horizontal-pasting-coherence-square-homotopiesᵉ
      ( top-leftᵉ)
      ( top-rightᵉ)
      ( leftᵉ)
      ( middleᵉ)
      ( rightᵉ ∙hᵉ Kᵉ)
      ( bottom-leftᵉ)
      ( bottom-rightᵉ ∙hᵉ Kᵉ)
      ( lᵉ)
      ( right-whisker-concat-coherence-square-homotopiesᵉ
        ( top-rightᵉ)
        ( middleᵉ)
        ( rightᵉ)
        ( bottom-rightᵉ)
        ( rᵉ)
        ( Kᵉ))
  right-whisker-concat-horizontal-pasting-coherence-square-homotopiesᵉ
    top-leftᵉ top-rightᵉ leftᵉ middleᵉ rightᵉ bottom-leftᵉ bottom-rightᵉ lᵉ rᵉ Kᵉ xᵉ =
    right-whisker-concat-horizontal-pasting-coherence-square-identificationsᵉ
      ( top-leftᵉ xᵉ)
      ( top-rightᵉ xᵉ)
      ( leftᵉ xᵉ)
      ( middleᵉ xᵉ)
      ( rightᵉ xᵉ)
      ( bottom-leftᵉ xᵉ)
      ( bottom-rightᵉ xᵉ)
      ( lᵉ xᵉ)
      ( rᵉ xᵉ)
      ( Kᵉ xᵉ)
```

### Right whiskering vertical concatenations of squares with homotopies

Considerᵉ twoᵉ squaresᵉ ofᵉ homotopiesᵉ asᵉ in theᵉ diagramᵉ

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

andᵉ considerᵉ aᵉ homotopyᵉ `Kᵉ : fᵉ ~ᵉ g`.ᵉ Thenᵉ theᵉ rightᵉ whiskeringᵉ ofᵉ theᵉ verticalᵉ
pastingᵉ ofᵉ theᵉ twoᵉ squaresᵉ aboveᵉ with `K`ᵉ isᵉ upᵉ to associativityᵉ theᵉ verticalᵉ
pastingᵉ ofᵉ theᵉ squaresᵉ

```text
                     topᵉ
              aᵉ ------------>ᵉ bᵉ
              |               |
     top-leftᵉ |               | top-rightᵉ
              ∨ᵉ    middleᵉ     ∨ᵉ
              cᵉ ------------>ᵉ dᵉ
              |               |
  bottom-leftᵉ |               | bottom-rightᵉ ∙hᵉ Kᵉ
              ∨ᵉ               ∨ᵉ
              eᵉ ------------>ᵉ g.ᵉ
                 bottomᵉ ∙hᵉ Kᵉ
```

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  right-whisker-concat-vertical-pasting-coherence-square-homotopiesᵉ :
    {aᵉ bᵉ cᵉ dᵉ eᵉ fᵉ gᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ}
    (topᵉ : aᵉ ~ᵉ bᵉ) (top-leftᵉ : aᵉ ~ᵉ cᵉ) (top-rightᵉ : bᵉ ~ᵉ dᵉ)
    (middleᵉ : cᵉ ~ᵉ dᵉ)
    (bottom-leftᵉ : cᵉ ~ᵉ eᵉ) (bottom-rightᵉ : dᵉ ~ᵉ fᵉ) (bottomᵉ : eᵉ ~ᵉ fᵉ)
    (tᵉ : coherence-square-homotopiesᵉ topᵉ top-leftᵉ top-rightᵉ middleᵉ) →
    (bᵉ :
      coherence-square-homotopiesᵉ middleᵉ bottom-leftᵉ bottom-rightᵉ bottomᵉ) →
    (Kᵉ : fᵉ ~ᵉ gᵉ) →
    right-whisker-concat-coherence-square-homotopiesᵉ
      ( topᵉ)
      ( top-leftᵉ ∙hᵉ bottom-leftᵉ)
      ( top-rightᵉ ∙hᵉ bottom-rightᵉ)
      ( bottomᵉ)
      ( vertical-pasting-coherence-square-homotopiesᵉ
        ( topᵉ)
        ( top-leftᵉ)
        ( top-rightᵉ)
        ( middleᵉ)
        ( bottom-leftᵉ)
        ( bottom-rightᵉ)
        ( bottomᵉ)
        ( tᵉ)
        ( bᵉ))
      ( Kᵉ) ∙hᵉ
    left-whisker-concat-htpyᵉ topᵉ (assoc-htpyᵉ top-rightᵉ bottom-rightᵉ Kᵉ) ~ᵉ
    vertical-pasting-coherence-square-homotopiesᵉ
      ( topᵉ)
      ( top-leftᵉ)
      ( top-rightᵉ)
      ( middleᵉ)
      ( bottom-leftᵉ)
      ( bottom-rightᵉ ∙hᵉ Kᵉ)
      ( bottomᵉ ∙hᵉ Kᵉ)
      ( tᵉ)
      ( right-whisker-concat-coherence-square-homotopiesᵉ
        ( middleᵉ)
        ( bottom-leftᵉ)
        ( bottom-rightᵉ)
        ( bottomᵉ)
        ( bᵉ)
        ( Kᵉ))
  right-whisker-concat-vertical-pasting-coherence-square-homotopiesᵉ
    topᵉ top-leftᵉ top-rightᵉ middleᵉ bottom-leftᵉ bottom-rightᵉ bottomᵉ tᵉ bᵉ Kᵉ xᵉ =
    right-whisker-concat-vertical-pasting-coherence-square-identificationsᵉ
      ( topᵉ xᵉ)
      ( top-leftᵉ xᵉ)
      ( top-rightᵉ xᵉ)
      ( middleᵉ xᵉ)
      ( bottom-leftᵉ xᵉ)
      ( bottom-rightᵉ xᵉ)
      ( bottomᵉ xᵉ)
      ( tᵉ xᵉ)
      ( bᵉ xᵉ)
      ( Kᵉ xᵉ)
```