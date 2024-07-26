# Commuting squares of identifications

```agda
module foundation.commuting-squares-of-identificationsᵉ where

open import foundation-core.commuting-squares-of-identificationsᵉ public
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.path-algebraᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.equivalencesᵉ
open import foundation-core.identity-typesᵉ
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

  abstract
    is-equiv-concat-top-identification-coherence-square-identificationsᵉ :
      is-equivᵉ
        ( concat-top-identification-coherence-square-identificationsᵉ
            topᵉ leftᵉ rightᵉ bottomᵉ sᵉ)
    is-equiv-concat-top-identification-coherence-square-identificationsᵉ =
      is-equiv-is-invertibleᵉ
        ( inv-concat-top-identification-coherence-square-identificationsᵉ
            topᵉ leftᵉ rightᵉ bottomᵉ sᵉ)
        ( is-section-inv-concat-top-identification-coherence-square-identificationsᵉ
            topᵉ leftᵉ rightᵉ bottomᵉ sᵉ)
        ( is-retraction-inv-concat-top-identification-coherence-square-identificationsᵉ
            topᵉ leftᵉ rightᵉ bottomᵉ sᵉ)

  equiv-concat-top-identification-coherence-square-identificationsᵉ :
    coherence-square-identificationsᵉ topᵉ leftᵉ rightᵉ bottomᵉ ≃ᵉ
    coherence-square-identificationsᵉ top'ᵉ leftᵉ rightᵉ bottomᵉ
  pr1ᵉ equiv-concat-top-identification-coherence-square-identificationsᵉ =
    concat-top-identification-coherence-square-identificationsᵉ
      topᵉ leftᵉ rightᵉ bottomᵉ sᵉ
  pr2ᵉ equiv-concat-top-identification-coherence-square-identificationsᵉ =
    is-equiv-concat-top-identification-coherence-square-identificationsᵉ
```

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

  abstract
    is-equiv-concat-left-identification-coherence-square-identificationsᵉ :
      is-equivᵉ
        ( concat-left-identification-coherence-square-identificationsᵉ
            topᵉ leftᵉ rightᵉ bottomᵉ sᵉ)
    is-equiv-concat-left-identification-coherence-square-identificationsᵉ =
      is-equiv-is-invertibleᵉ
        ( inv-concat-left-identification-coherence-square-identificationsᵉ
            topᵉ leftᵉ rightᵉ bottomᵉ sᵉ)
        ( is-section-inv-concat-left-identification-coherence-square-identificationsᵉ
            topᵉ leftᵉ rightᵉ bottomᵉ sᵉ)
        ( is-retraction-inv-concat-left-identification-coherence-square-identificationsᵉ
            topᵉ leftᵉ rightᵉ bottomᵉ sᵉ)

  equiv-concat-left-identification-coherence-square-identificationsᵉ :
    coherence-square-identificationsᵉ topᵉ leftᵉ rightᵉ bottomᵉ ≃ᵉ
    coherence-square-identificationsᵉ topᵉ left'ᵉ rightᵉ bottomᵉ
  pr1ᵉ equiv-concat-left-identification-coherence-square-identificationsᵉ =
    concat-left-identification-coherence-square-identificationsᵉ
        topᵉ leftᵉ rightᵉ bottomᵉ sᵉ
  pr2ᵉ equiv-concat-left-identification-coherence-square-identificationsᵉ =
    is-equiv-concat-left-identification-coherence-square-identificationsᵉ
```

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

  abstract
    is-equiv-concat-right-identification-coherence-square-identificationsᵉ :
      is-equivᵉ
        ( concat-right-identification-coherence-square-identificationsᵉ
            topᵉ leftᵉ rightᵉ bottomᵉ sᵉ)
    is-equiv-concat-right-identification-coherence-square-identificationsᵉ =
      is-equiv-is-invertibleᵉ
        ( inv-concat-right-identification-coherence-square-identificationsᵉ
            topᵉ leftᵉ rightᵉ bottomᵉ sᵉ)
        ( is-section-inv-concat-right-identification-coherence-square-identificationsᵉ
            topᵉ leftᵉ rightᵉ bottomᵉ sᵉ)
        ( is-retraction-inv-concat-right-identification-coherence-square-identificationsᵉ
            topᵉ leftᵉ rightᵉ bottomᵉ sᵉ)

  equiv-concat-right-identification-coherence-square-identificationsᵉ :
    coherence-square-identificationsᵉ topᵉ leftᵉ rightᵉ bottomᵉ ≃ᵉ
    coherence-square-identificationsᵉ topᵉ leftᵉ right'ᵉ bottomᵉ
  pr1ᵉ equiv-concat-right-identification-coherence-square-identificationsᵉ =
    concat-right-identification-coherence-square-identificationsᵉ
      topᵉ leftᵉ rightᵉ bottomᵉ sᵉ
  pr2ᵉ equiv-concat-right-identification-coherence-square-identificationsᵉ =
    is-equiv-concat-right-identification-coherence-square-identificationsᵉ
```

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

  is-equiv-concat-bottom-identification-coherence-square-identificationsᵉ :
    is-equivᵉ
      ( concat-bottom-identification-coherence-square-identificationsᵉ
          topᵉ leftᵉ rightᵉ bottomᵉ sᵉ)
  is-equiv-concat-bottom-identification-coherence-square-identificationsᵉ =
    is-equiv-is-invertibleᵉ
      ( inv-concat-bottom-identification-coherence-square-identificationsᵉ
          topᵉ leftᵉ rightᵉ bottomᵉ sᵉ)
      ( is-section-inv-concat-bottom-identification-coherence-square-identificationsᵉ
          topᵉ leftᵉ rightᵉ bottomᵉ sᵉ)
      ( is-retraction-inv-concat-bottom-identification-coherence-square-identificationsᵉ
          topᵉ leftᵉ rightᵉ bottomᵉ sᵉ)

  equiv-concat-bottom-identification-coherence-square-identificationsᵉ :
    coherence-square-identificationsᵉ topᵉ leftᵉ rightᵉ bottomᵉ ≃ᵉ
    coherence-square-identificationsᵉ topᵉ leftᵉ rightᵉ bottom'ᵉ
  pr1ᵉ equiv-concat-bottom-identification-coherence-square-identificationsᵉ =
    concat-bottom-identification-coherence-square-identificationsᵉ
        topᵉ leftᵉ rightᵉ bottomᵉ sᵉ
  pr2ᵉ equiv-concat-bottom-identification-coherence-square-identificationsᵉ =
    is-equiv-concat-bottom-identification-coherence-square-identificationsᵉ
```

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

  equiv-left-whisker-concat-coherence-square-identificationsᵉ :
    (pᵉ : uᵉ ＝ᵉ xᵉ)
    (topᵉ : xᵉ ＝ᵉ yᵉ) (leftᵉ : xᵉ ＝ᵉ zᵉ) (rightᵉ : yᵉ ＝ᵉ wᵉ) (bottomᵉ : zᵉ ＝ᵉ wᵉ) →
    coherence-square-identificationsᵉ topᵉ leftᵉ rightᵉ bottomᵉ ≃ᵉ
    coherence-square-identificationsᵉ (pᵉ ∙ᵉ topᵉ) (pᵉ ∙ᵉ leftᵉ) rightᵉ bottomᵉ
  equiv-left-whisker-concat-coherence-square-identificationsᵉ
    reflᵉ topᵉ leftᵉ rightᵉ bottomᵉ =
    id-equivᵉ
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

  equiv-right-whisker-concat-coherence-square-identificationsᵉ :
    {uᵉ : Aᵉ} (pᵉ : wᵉ ＝ᵉ uᵉ) →
    coherence-square-identificationsᵉ topᵉ leftᵉ rightᵉ bottomᵉ ≃ᵉ
    coherence-square-identificationsᵉ topᵉ leftᵉ (rightᵉ ∙ᵉ pᵉ) (bottomᵉ ∙ᵉ pᵉ)
  equiv-right-whisker-concat-coherence-square-identificationsᵉ reflᵉ =
    ( equiv-concat-bottom-identification-coherence-square-identificationsᵉ
      ( topᵉ)
      ( leftᵉ)
      ( rightᵉ ∙ᵉ reflᵉ)
      ( bottomᵉ)
      ( invᵉ right-unitᵉ)) ∘eᵉ
    ( equiv-concat-right-identification-coherence-square-identificationsᵉ
      ( topᵉ)
      ( leftᵉ)
      ( rightᵉ)
      ( bottomᵉ)
      ( invᵉ right-unitᵉ))
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

  equiv-left-splice-coherence-square-identificationsᵉ :
    {uᵉ : Aᵉ} (pᵉ : zᵉ ＝ᵉ uᵉ) (qᵉ : uᵉ ＝ᵉ zᵉ) (αᵉ : invᵉ pᵉ ＝ᵉ qᵉ) →
    coherence-square-identificationsᵉ topᵉ leftᵉ rightᵉ bottomᵉ ≃ᵉ
    coherence-square-identificationsᵉ topᵉ (leftᵉ ∙ᵉ pᵉ) rightᵉ (qᵉ ∙ᵉ bottomᵉ)
  equiv-left-splice-coherence-square-identificationsᵉ reflᵉ .reflᵉ reflᵉ =
    equiv-concat-left-identification-coherence-square-identificationsᵉ
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

  equiv-right-splice-coherence-square-identificationsᵉ :
    {uᵉ : Aᵉ} (pᵉ : yᵉ ＝ᵉ uᵉ) (qᵉ : uᵉ ＝ᵉ yᵉ) (αᵉ : invᵉ pᵉ ＝ᵉ qᵉ) →
    coherence-square-identificationsᵉ topᵉ leftᵉ rightᵉ bottomᵉ ≃ᵉ
    coherence-square-identificationsᵉ (topᵉ ∙ᵉ pᵉ) leftᵉ (invᵉ pᵉ ∙ᵉ rightᵉ) bottomᵉ
  equiv-right-splice-coherence-square-identificationsᵉ reflᵉ .reflᵉ reflᵉ =
    equiv-concat-top-identification-coherence-square-identificationsᵉ
      ( topᵉ)
      ( leftᵉ)
      ( rightᵉ)
      ( bottomᵉ)
      ( invᵉ right-unitᵉ)
```

### Double whiskering of commuting squares of identifications

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {xᵉ yᵉ zᵉ uᵉ vᵉ wᵉ : Aᵉ}
  where

  equiv-double-whisker-coherence-square-identificationsᵉ :
    (pᵉ : xᵉ ＝ᵉ yᵉ)
    (topᵉ : yᵉ ＝ᵉ uᵉ) (leftᵉ : yᵉ ＝ᵉ zᵉ) (rightᵉ : uᵉ ＝ᵉ vᵉ) (bottomᵉ : zᵉ ＝ᵉ vᵉ)
    (sᵉ : vᵉ ＝ᵉ wᵉ) →
    coherence-square-identificationsᵉ topᵉ leftᵉ rightᵉ bottomᵉ ≃ᵉ
    coherence-square-identificationsᵉ
      ( pᵉ ∙ᵉ topᵉ)
      ( pᵉ ∙ᵉ leftᵉ)
      ( rightᵉ ∙ᵉ sᵉ)
      ( bottomᵉ ∙ᵉ sᵉ)
  equiv-double-whisker-coherence-square-identificationsᵉ
    pᵉ topᵉ leftᵉ rightᵉ bottomᵉ qᵉ =
    equiv-left-whisker-concat-coherence-square-identificationsᵉ pᵉ topᵉ leftᵉ
      ( rightᵉ ∙ᵉ qᵉ)
      ( bottomᵉ ∙ᵉ qᵉ) ∘eᵉ
    equiv-right-whisker-concat-coherence-square-identificationsᵉ
      ( topᵉ)
      ( leftᵉ)
      ( rightᵉ)
      ( bottomᵉ)
      ( qᵉ)
```

### Computing the pasting of squares with `refl` on opposite sides

Considerᵉ twoᵉ squaresᵉ ofᵉ identificationsᵉ asᵉ in theᵉ diagramᵉ

```text
                  reflᵉ
              aᵉ -------->ᵉ aᵉ
              |           |
     top-leftᵉ |           | top-rightᵉ
              ∨ᵉ   reflᵉ    ∨ᵉ
              bᵉ -------->ᵉ bᵉ
              |           |
  bottom-leftᵉ |           | bottom-rightᵉ
              ∨ᵉ           ∨ᵉ
              cᵉ -------->ᵉ cᵉ
                  reflᵉ
```

Thenᵉ theᵉ pastedᵉ squareᵉ canᵉ beᵉ computedᵉ in termsᵉ ofᵉ theᵉ horizontalᵉ concatenationᵉ
ofᵉ theᵉ fillerᵉ squaresᵉ

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {aᵉ bᵉ cᵉ : Aᵉ}
  where

  vertical-pasting-coherence-square-identifications-horizontal-reflᵉ :
    (top-leftᵉ : aᵉ ＝ᵉ bᵉ) (top-rightᵉ : aᵉ ＝ᵉ bᵉ)
    (bottom-leftᵉ : bᵉ ＝ᵉ cᵉ) (bottom-rightᵉ : bᵉ ＝ᵉ cᵉ)
    (αᵉ : top-leftᵉ ＝ᵉ top-rightᵉ) (βᵉ : bottom-leftᵉ ＝ᵉ bottom-rightᵉ) →
    ( inv-coherence-square-identifications-horizontal-reflᵉ
      ( top-leftᵉ ∙ᵉ bottom-leftᵉ)
      ( top-rightᵉ ∙ᵉ bottom-rightᵉ)
      ( vertical-pasting-coherence-square-identificationsᵉ
        ( reflᵉ)
        ( top-leftᵉ)
        ( top-rightᵉ)
        ( reflᵉ)
        ( bottom-leftᵉ)
        ( bottom-rightᵉ)
        ( reflᵉ)
        ( coherence-square-identifications-horizontal-reflᵉ
          ( top-leftᵉ)
          ( top-rightᵉ)
          ( αᵉ))
        ( coherence-square-identifications-horizontal-reflᵉ
          ( bottom-leftᵉ)
          ( bottom-rightᵉ)
          ( βᵉ)))) ＝ᵉ
      ( horizontal-concat-Id²ᵉ αᵉ βᵉ)
  vertical-pasting-coherence-square-identifications-horizontal-reflᵉ
    reflᵉ reflᵉ reflᵉ reflᵉ reflᵉ reflᵉ =
      reflᵉ

  vertical-pasting-inv-coherence-square-identifications-horizontal-reflᵉ :
    (top-leftᵉ : aᵉ ＝ᵉ bᵉ) (top-rightᵉ : aᵉ ＝ᵉ bᵉ)
    (bottom-leftᵉ : bᵉ ＝ᵉ cᵉ) (bottom-rightᵉ : bᵉ ＝ᵉ cᵉ)
    (αᵉ : coherence-square-identificationsᵉ reflᵉ top-leftᵉ top-rightᵉ reflᵉ)
    (βᵉ : coherence-square-identificationsᵉ reflᵉ bottom-leftᵉ bottom-rightᵉ reflᵉ) →
    ( inv-coherence-square-identifications-horizontal-reflᵉ
      ( top-leftᵉ ∙ᵉ bottom-leftᵉ)
      ( top-rightᵉ ∙ᵉ bottom-rightᵉ)
      ( vertical-pasting-coherence-square-identificationsᵉ
        ( reflᵉ)
        ( top-leftᵉ)
        ( top-rightᵉ)
        ( reflᵉ)
        ( bottom-leftᵉ)
        ( bottom-rightᵉ)
        ( reflᵉ)
        ( αᵉ)
        ( βᵉ))) ＝ᵉ
      ( horizontal-concat-Id²ᵉ
        ( inv-coherence-square-identifications-horizontal-reflᵉ
          ( top-leftᵉ)
          ( top-rightᵉ)
          ( αᵉ))
        ( inv-coherence-square-identifications-horizontal-reflᵉ
          ( bottom-leftᵉ)
          ( bottom-rightᵉ)
          ( βᵉ)))
  vertical-pasting-inv-coherence-square-identifications-horizontal-reflᵉ
    reflᵉ reflᵉ reflᵉ reflᵉ reflᵉ reflᵉ =
      reflᵉ
```