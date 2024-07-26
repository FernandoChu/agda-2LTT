# Commuting squares of homotopies

```agda
module foundation.commuting-squares-of-homotopiesᵉ where

open import foundation-core.commuting-squares-of-homotopiesᵉ public
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-squares-of-identificationsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.equivalencesᵉ
open import foundation-core.functoriality-dependent-function-typesᵉ
```

</details>

## Idea

Aᵉ squareᵉ ofᵉ [homotopies](foundation-core.identity-types.mdᵉ)

```text
           topᵉ
       fᵉ ------->ᵉ gᵉ
       |          |
  leftᵉ |          | rightᵉ
       ∨ᵉ          ∨ᵉ
       hᵉ ------->ᵉ iᵉ
          bottomᵉ
```

isᵉ saidᵉ to beᵉ aᵉ
{{#conceptᵉ "commutingᵉ square"ᵉ Disambiguation="homotopies"ᵉ Agda=coherence-square-homotopiesᵉ}}
ifᵉ thereᵉ isᵉ aᵉ homotopyᵉ `leftᵉ ∙hᵉ bottomᵉ ~ᵉ topᵉ ∙hᵉ right`.ᵉ Suchᵉ aᵉ homotopyᵉ isᵉ
calledᵉ aᵉ
{{#conceptᵉ "coherence"ᵉ Disambiguation="commutingᵉ squareᵉ ofᵉ homotopies"ᵉ Agda=coherence-square-homotopiesᵉ}}
ofᵉ theᵉ square.ᵉ

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

with aᵉ homotopyᵉ `topᵉ ~ᵉ top'`.ᵉ Thenᵉ weᵉ getᵉ anᵉ equivalenceᵉ

```text
           topᵉ                             top'ᵉ
       fᵉ ------->ᵉ gᵉ                    fᵉ ------->ᵉ gᵉ
       |          |                    |          |
  leftᵉ |          | rightᵉ    ≃ᵉ    leftᵉ |          | rightᵉ
       ∨ᵉ          ∨ᵉ                    ∨ᵉ          ∨ᵉ
       hᵉ ------->ᵉ iᵉ                    hᵉ ------->ᵉ i.ᵉ
          bottomᵉ                          bottomᵉ
```

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {fᵉ gᵉ hᵉ iᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ}
  (topᵉ : fᵉ ~ᵉ gᵉ) (leftᵉ : fᵉ ~ᵉ hᵉ) (rightᵉ : gᵉ ~ᵉ iᵉ) (bottomᵉ : hᵉ ~ᵉ iᵉ)
  {top'ᵉ : fᵉ ~ᵉ gᵉ} (sᵉ : topᵉ ~ᵉ top'ᵉ)
  where

  abstract
    is-equiv-concat-top-homotopy-coherence-square-homotopiesᵉ :
      is-equivᵉ
        ( concat-top-homotopy-coherence-square-homotopiesᵉ
            topᵉ leftᵉ rightᵉ bottomᵉ sᵉ)
    is-equiv-concat-top-homotopy-coherence-square-homotopiesᵉ =
      is-equiv-map-Π-is-fiberwise-equivᵉ
        ( λ xᵉ →
          is-equiv-concat-top-identification-coherence-square-identificationsᵉ
            ( topᵉ xᵉ) (leftᵉ xᵉ) (rightᵉ xᵉ) (bottomᵉ xᵉ) (sᵉ xᵉ))

  equiv-concat-top-homotopy-coherence-square-homotopiesᵉ :
    coherence-square-homotopiesᵉ topᵉ leftᵉ rightᵉ bottomᵉ ≃ᵉ
    coherence-square-homotopiesᵉ top'ᵉ leftᵉ rightᵉ bottomᵉ
  pr1ᵉ equiv-concat-top-homotopy-coherence-square-homotopiesᵉ =
    concat-top-homotopy-coherence-square-homotopiesᵉ topᵉ leftᵉ rightᵉ bottomᵉ sᵉ
  pr2ᵉ equiv-concat-top-homotopy-coherence-square-homotopiesᵉ =
    is-equiv-concat-top-homotopy-coherence-square-homotopiesᵉ
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

with aᵉ homotopyᵉ `leftᵉ ~ᵉ left'`.ᵉ Thenᵉ weᵉ getᵉ anᵉ equivalenceᵉ

```text
           topᵉ                              topᵉ
       fᵉ ------->ᵉ gᵉ                     fᵉ ------->ᵉ gᵉ
       |          |                     |          |
  leftᵉ |          | rightᵉ    ≃ᵉ    left'ᵉ |          | rightᵉ
       ∨ᵉ          ∨ᵉ                     ∨ᵉ          ∨ᵉ
       hᵉ ------->ᵉ iᵉ                     hᵉ ------->ᵉ i.ᵉ
          bottomᵉ                           bottomᵉ
```

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {fᵉ gᵉ hᵉ iᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ}
  (topᵉ : fᵉ ~ᵉ gᵉ) (leftᵉ : fᵉ ~ᵉ hᵉ) (rightᵉ : gᵉ ~ᵉ iᵉ) (bottomᵉ : hᵉ ~ᵉ iᵉ)
  {left'ᵉ : fᵉ ~ᵉ hᵉ} (sᵉ : leftᵉ ~ᵉ left'ᵉ)
  where

  abstract
    is-equiv-concat-left-homotopy-coherence-square-homotopiesᵉ :
      is-equivᵉ
        ( concat-left-homotopy-coherence-square-homotopiesᵉ
            topᵉ leftᵉ rightᵉ bottomᵉ sᵉ)
    is-equiv-concat-left-homotopy-coherence-square-homotopiesᵉ =
      is-equiv-map-Π-is-fiberwise-equivᵉ
        ( λ xᵉ →
          is-equiv-concat-left-identification-coherence-square-identificationsᵉ
            ( topᵉ xᵉ) (leftᵉ xᵉ) (rightᵉ xᵉ) (bottomᵉ xᵉ) (sᵉ xᵉ))

  equiv-concat-left-homotopy-coherence-square-homotopiesᵉ :
    coherence-square-homotopiesᵉ topᵉ leftᵉ rightᵉ bottomᵉ ≃ᵉ
    coherence-square-homotopiesᵉ topᵉ left'ᵉ rightᵉ bottomᵉ
  pr1ᵉ equiv-concat-left-homotopy-coherence-square-homotopiesᵉ =
    concat-left-homotopy-coherence-square-homotopiesᵉ topᵉ leftᵉ rightᵉ bottomᵉ sᵉ
  pr2ᵉ equiv-concat-left-homotopy-coherence-square-homotopiesᵉ =
    is-equiv-concat-left-homotopy-coherence-square-homotopiesᵉ
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

with aᵉ homotopyᵉ `rightᵉ ~ᵉ right'`.ᵉ Thenᵉ weᵉ getᵉ anᵉ equivalenceᵉ

```text
           topᵉ                             topᵉ
       fᵉ ------->ᵉ gᵉ                    fᵉ ------->ᵉ gᵉ
       |          |                    |          |
  leftᵉ |          | rightᵉ    ≃ᵉ    leftᵉ |          | right'ᵉ
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

  abstract
    is-equiv-concat-right-homotopy-coherence-square-homotopiesᵉ :
      is-equivᵉ
        ( concat-right-homotopy-coherence-square-homotopiesᵉ
            topᵉ leftᵉ rightᵉ bottomᵉ sᵉ)
    is-equiv-concat-right-homotopy-coherence-square-homotopiesᵉ =
      is-equiv-map-Π-is-fiberwise-equivᵉ
        ( λ xᵉ →
          is-equiv-concat-right-identification-coherence-square-identificationsᵉ
            ( topᵉ xᵉ) (leftᵉ xᵉ) (rightᵉ xᵉ) (bottomᵉ xᵉ) (sᵉ xᵉ))

  equiv-concat-right-homotopy-coherence-square-homotopiesᵉ :
    coherence-square-homotopiesᵉ topᵉ leftᵉ rightᵉ bottomᵉ ≃ᵉ
    coherence-square-homotopiesᵉ topᵉ leftᵉ right'ᵉ bottomᵉ
  pr1ᵉ equiv-concat-right-homotopy-coherence-square-homotopiesᵉ =
    concat-right-homotopy-coherence-square-homotopiesᵉ topᵉ leftᵉ rightᵉ bottomᵉ sᵉ
  pr2ᵉ equiv-concat-right-homotopy-coherence-square-homotopiesᵉ =
    is-equiv-concat-right-homotopy-coherence-square-homotopiesᵉ
```

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

with aᵉ homotopyᵉ `bottomᵉ ~ᵉ bottom'`.ᵉ Thenᵉ weᵉ getᵉ anᵉ equivalenceᵉ

```text
           topᵉ                             topᵉ
       fᵉ ------->ᵉ gᵉ                    fᵉ ------->ᵉ gᵉ
       |          |                    |          |
  leftᵉ |          | rightᵉ    ≃ᵉ    leftᵉ |          | rightᵉ
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

  is-equiv-concat-bottom-homotopy-coherence-square-homotopiesᵉ :
    is-equivᵉ
      ( concat-bottom-homotopy-coherence-square-homotopiesᵉ
          topᵉ leftᵉ rightᵉ bottomᵉ sᵉ)
  is-equiv-concat-bottom-homotopy-coherence-square-homotopiesᵉ =
      is-equiv-map-Π-is-fiberwise-equivᵉ
        ( λ xᵉ →
          is-equiv-concat-bottom-identification-coherence-square-identificationsᵉ
            ( topᵉ xᵉ) (leftᵉ xᵉ) (rightᵉ xᵉ) (bottomᵉ xᵉ) (sᵉ xᵉ))

  equiv-concat-bottom-homotopy-coherence-square-homotopiesᵉ :
    coherence-square-homotopiesᵉ topᵉ leftᵉ rightᵉ bottomᵉ ≃ᵉ
    coherence-square-homotopiesᵉ topᵉ leftᵉ rightᵉ bottom'ᵉ
  pr1ᵉ equiv-concat-bottom-homotopy-coherence-square-homotopiesᵉ =
    concat-bottom-homotopy-coherence-square-homotopiesᵉ topᵉ leftᵉ rightᵉ bottomᵉ sᵉ
  pr2ᵉ equiv-concat-bottom-homotopy-coherence-square-homotopiesᵉ =
    is-equiv-concat-bottom-homotopy-coherence-square-homotopiesᵉ
```

### Whiskering and splicing coherences of commuting squares of homotopies

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

1.ᵉ Prependingᵉ `pᵉ : uᵉ ~ᵉ f`ᵉ to theᵉ leftᵉ givesᵉ usᵉ aᵉ commutingᵉ squareᵉ

   ```text
                pᵉ ∙hᵉ topᵉ
              uᵉ ------->ᵉ gᵉ
              |          |
     pᵉ ∙hᵉ leftᵉ |          | rightᵉ
              ∨ᵉ          ∨ᵉ
              hᵉ ------->ᵉ i.ᵉ
                 bottomᵉ
   ```

   Moreᵉ precisely,ᵉ weᵉ haveᵉ anᵉ equivalenceᵉ

   ```text
     (leftᵉ ∙hᵉ bottomᵉ ~ᵉ topᵉ ∙hᵉ rightᵉ) ≃ᵉ ((pᵉ ∙hᵉ leftᵉ) ∙hᵉ bottomᵉ ~ᵉ (pᵉ ∙hᵉ topᵉ) ∙hᵉ right).ᵉ
   ```

2.ᵉ Appendingᵉ aᵉ homotopyᵉ `pᵉ : iᵉ ~ᵉ u`ᵉ to theᵉ rightᵉ givesᵉ aᵉ commutingᵉ squareᵉ ofᵉ
   homotopiesᵉ

   ```text
                   topᵉ
           fᵉ ------------>ᵉ gᵉ
           |               |
      leftᵉ |               | rightᵉ ∙hᵉ pᵉ
           ∨ᵉ               ∨ᵉ
           hᵉ ------------>ᵉ u.ᵉ
              bottomᵉ ∙hᵉ pᵉ
   ```

   Moreᵉ precisely,ᵉ weᵉ haveᵉ anᵉ equivalenceᵉ

   ```text
     (leftᵉ ∙hᵉ bottomᵉ ~ᵉ topᵉ ∙hᵉ rightᵉ) ≃ᵉ (leftᵉ ∙hᵉ (bottomᵉ ∙hᵉ pᵉ) ~ᵉ topᵉ ∙hᵉ (rightᵉ ∙hᵉ p)).ᵉ
   ```

3.ᵉ Splicingᵉ aᵉ homotopyᵉ `pᵉ : hᵉ ~ᵉ u`ᵉ andᵉ itsᵉ inverseᵉ intoᵉ theᵉ middleᵉ givesᵉ aᵉ
   commutingᵉ squareᵉ ofᵉ homotopiesᵉ

   ```text
                      topᵉ
              fᵉ -------------->ᵉ gᵉ
              |                 |
    leftᵉ ∙hᵉ pᵉ |                 | rightᵉ
              ∨ᵉ                 ∨ᵉ
              uᵉ -------------->ᵉ i.ᵉ
                 p⁻¹ᵉ ∙hᵉ bottomᵉ
   ```

   Moreᵉ precisely,ᵉ weᵉ haveᵉ anᵉ equivalenceᵉ

   ```text
     (leftᵉ ∙hᵉ bottomᵉ ~ᵉ topᵉ ∙hᵉ rightᵉ) ≃ᵉ ((leftᵉ ∙hᵉ pᵉ) ∙hᵉ (p⁻¹ᵉ ∙hᵉ bottomᵉ) ~ᵉ topᵉ ∙hᵉ right).ᵉ
   ```

   Similarly,ᵉ weᵉ haveᵉ anᵉ equivalenceᵉ

   ```text
     (leftᵉ ∙hᵉ bottomᵉ ~ᵉ topᵉ ∙hᵉ rightᵉ) ≃ᵉ ((leftᵉ ∙hᵉ p⁻¹ᵉ) ∙hᵉ (pᵉ ∙hᵉ bottomᵉ) ~ᵉ topᵉ ∙hᵉ right).ᵉ
   ```

4.ᵉ Splicingᵉ aᵉ homotopyᵉ `pᵉ : gᵉ ~ᵉ u`ᵉ andᵉ itsᵉ inverseᵉ intoᵉ theᵉ middleᵉ givesᵉ aᵉ
   commutingᵉ squareᵉ ofᵉ homotopiesᵉ

   ```text
             topᵉ ∙hᵉ pᵉ
          fᵉ -------->ᵉ uᵉ
          |           |
     leftᵉ |           | p⁻¹ᵉ ∙hᵉ rightᵉ
          ∨ᵉ           ∨ᵉ
          hᵉ -------->ᵉ i.ᵉ
             bottomᵉ
   ```

   Moreᵉ precisely,ᵉ weᵉ haveᵉ anᵉ equivalenceᵉ

   ```text
     (leftᵉ ∙hᵉ bottomᵉ ~ᵉ topᵉ ∙hᵉ rightᵉ) ≃ᵉ (leftᵉ ∙hᵉ bottomᵉ ~ᵉ (topᵉ ∙hᵉ pᵉ) ∙hᵉ (p⁻¹ᵉ ∙hᵉ right)).ᵉ
   ```

   Similarly,ᵉ weᵉ haveᵉ anᵉ equivalenceᵉ

   ```text
     (leftᵉ ∙hᵉ bottomᵉ ~ᵉ topᵉ ∙hᵉ rightᵉ) ≃ᵉ (leftᵉ ∙hᵉ bottomᵉ ~ᵉ (topᵉ ∙hᵉ p⁻¹ᵉ) ∙hᵉ (pᵉ ∙hᵉ right)).ᵉ
   ```

Theseᵉ operationsᵉ areᵉ usefulᵉ in proofsᵉ involvingᵉ homotopyᵉ algebra,ᵉ becauseᵉ takingᵉ
`equiv-right-whisker-concat-coherence-square-homotopies`ᵉ asᵉ anᵉ example,ᵉ itᵉ
providesᵉ usᵉ with twoᵉ mapsᵉ: theᵉ forwardᵉ directionᵉ statesᵉ
`(pᵉ ∙hᵉ rᵉ ~ᵉ qᵉ ∙hᵉ sᵉ) → (pᵉ ∙hᵉ (rᵉ ∙hᵉ tᵉ)) ~ᵉ qᵉ ∙hᵉ (sᵉ ∙hᵉ t))`,ᵉ whichᵉ allowsᵉ oneᵉ to
appendᵉ aᵉ homotopyᵉ withoutᵉ needingᵉ to reassociateᵉ onᵉ theᵉ right,ᵉ andᵉ theᵉ backwardsᵉ
directionᵉ converselyᵉ allowsᵉ oneᵉ to cancelᵉ outᵉ aᵉ homotopyᵉ in parentheses.ᵉ

#### Left whiskering coherences of commuting squares of homotopies

Forᵉ anyᵉ homotopyᵉ `pᵉ : uᵉ ~ᵉ f`ᵉ weᵉ obtainᵉ anᵉ equivalenceᵉ

```text
           topᵉ                                pᵉ ∙hᵉ topᵉ
       fᵉ ------->ᵉ gᵉ                         uᵉ ------->ᵉ gᵉ
       |          |                         |          |
  leftᵉ |          | rightᵉ    ≃ᵉ    pᵉ ∙hᵉ leftᵉ |          | rightᵉ
       ∨ᵉ          ∨ᵉ                         ∨ᵉ          ∨ᵉ
       hᵉ ------->ᵉ iᵉ                         hᵉ ------->ᵉ iᵉ
          bottomᵉ                               bottomᵉ
```

ofᵉ coherencesᵉ ofᵉ commutingᵉ squaresᵉ ofᵉ homotopies.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {fᵉ gᵉ hᵉ iᵉ uᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ}
  where

  equiv-left-whisker-concat-coherence-square-homotopiesᵉ :
    (pᵉ : uᵉ ~ᵉ fᵉ)
    (topᵉ : fᵉ ~ᵉ gᵉ) (leftᵉ : fᵉ ~ᵉ hᵉ) (rightᵉ : gᵉ ~ᵉ iᵉ) (bottomᵉ : hᵉ ~ᵉ iᵉ) →
    coherence-square-homotopiesᵉ topᵉ leftᵉ rightᵉ bottomᵉ ≃ᵉ
    coherence-square-homotopiesᵉ (pᵉ ∙hᵉ topᵉ) (pᵉ ∙hᵉ leftᵉ) rightᵉ bottomᵉ
  equiv-left-whisker-concat-coherence-square-homotopiesᵉ
    pᵉ topᵉ leftᵉ rightᵉ bottomᵉ =
    equiv-Π-equiv-familyᵉ
      ( λ xᵉ →
        equiv-left-whisker-concat-coherence-square-identificationsᵉ
          ( pᵉ xᵉ) (topᵉ xᵉ) (leftᵉ xᵉ) (rightᵉ xᵉ) (bottomᵉ xᵉ))
```

#### Right whiskering coherences of commuting squares of homotopies

Forᵉ anyᵉ homotopyᵉ `pᵉ : iᵉ ~ᵉ u`ᵉ weᵉ obtainᵉ anᵉ equivalenceᵉ

```text
           topᵉ                                 topᵉ
       fᵉ ------->ᵉ gᵉ                     fᵉ ------------>ᵉ gᵉ
       |          |                     |               |
  leftᵉ |          | rightᵉ    ≃ᵉ     leftᵉ |               | rightᵉ ∙hᵉ pᵉ
       ∨ᵉ          ∨ᵉ                     ∨ᵉ               ∨ᵉ
       hᵉ ------->ᵉ iᵉ                     hᵉ ------------>ᵉ iᵉ
          bottomᵉ                           bottomᵉ ∙hᵉ pᵉ
```

ofᵉ coherencesᵉ ofᵉ commutingᵉ squaresᵉ ofᵉ homotopies.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {fᵉ gᵉ hᵉ iᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ}
  (topᵉ : fᵉ ~ᵉ gᵉ) (leftᵉ : fᵉ ~ᵉ hᵉ) (rightᵉ : gᵉ ~ᵉ iᵉ) (bottomᵉ : hᵉ ~ᵉ iᵉ)
  where

  equiv-right-whisker-concat-coherence-square-homotopiesᵉ :
    {uᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ} (pᵉ : iᵉ ~ᵉ uᵉ) →
    coherence-square-homotopiesᵉ topᵉ leftᵉ rightᵉ bottomᵉ ≃ᵉ
    coherence-square-homotopiesᵉ topᵉ leftᵉ (rightᵉ ∙hᵉ pᵉ) (bottomᵉ ∙hᵉ pᵉ)
  equiv-right-whisker-concat-coherence-square-homotopiesᵉ pᵉ =
    equiv-Π-equiv-familyᵉ
      ( λ xᵉ →
        equiv-right-whisker-concat-coherence-square-identificationsᵉ
          ( topᵉ xᵉ) (leftᵉ xᵉ) (rightᵉ xᵉ) (bottomᵉ xᵉ) (pᵉ xᵉ))
```

#### Left splicing coherences of commuting squares of homotopies

Forᵉ anyᵉ inverseᵉ pairᵉ ofᵉ homotopiesᵉ `pᵉ : gᵉ ~ᵉ u`ᵉ andᵉ `qᵉ : uᵉ ~ᵉ g`ᵉ equippedᵉ with
`αᵉ : inv-htpyᵉ pᵉ ~ᵉ q`ᵉ weᵉ obtainᵉ anᵉ equivalenceᵉ

```text
           topᵉ                                    topᵉ
       fᵉ ------->ᵉ gᵉ                         fᵉ ----------->ᵉ gᵉ
       |          |                         |              |
  leftᵉ |          | rightᵉ    ≃ᵉ     leftᵉ ∙hᵉ pᵉ |              | rightᵉ
       ∨ᵉ          ∨ᵉ                         ∨ᵉ              ∨ᵉ
       hᵉ ------->ᵉ iᵉ                         uᵉ ----------->ᵉ iᵉ
          bottomᵉ                               qᵉ ∙hᵉ bottomᵉ
```

ofᵉ coherencesᵉ ofᵉ commutingᵉ squaresᵉ ofᵉ homotopies.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {fᵉ gᵉ hᵉ iᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ}
  (topᵉ : fᵉ ~ᵉ gᵉ) (leftᵉ : fᵉ ~ᵉ hᵉ) (rightᵉ : gᵉ ~ᵉ iᵉ) (bottomᵉ : hᵉ ~ᵉ iᵉ)
  where

  equiv-left-splice-coherence-square-homotopiesᵉ :
    {uᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ} (pᵉ : hᵉ ~ᵉ uᵉ) (qᵉ : uᵉ ~ᵉ hᵉ) (αᵉ : inv-htpyᵉ pᵉ ~ᵉ qᵉ) →
    coherence-square-homotopiesᵉ topᵉ leftᵉ rightᵉ bottomᵉ ≃ᵉ
    coherence-square-homotopiesᵉ topᵉ (leftᵉ ∙hᵉ pᵉ) rightᵉ (qᵉ ∙hᵉ bottomᵉ)
  equiv-left-splice-coherence-square-homotopiesᵉ pᵉ qᵉ αᵉ =
    equiv-Π-equiv-familyᵉ
      ( λ xᵉ →
        equiv-left-splice-coherence-square-identificationsᵉ
          ( topᵉ xᵉ) (leftᵉ xᵉ) (rightᵉ xᵉ) (bottomᵉ xᵉ) (pᵉ xᵉ) (qᵉ xᵉ) (αᵉ xᵉ))
```

#### Right splicing coherences of commuting squares of homotopies

Forᵉ anyᵉ inverseᵉ pairᵉ ofᵉ homotopiesᵉ `pᵉ : gᵉ ~ᵉ u`ᵉ andᵉ `qᵉ : uᵉ ~ᵉ g`ᵉ equippedᵉ with
`αᵉ : inv-htpyᵉ pᵉ ~ᵉ q`ᵉ weᵉ obtainᵉ anᵉ equivalenceᵉ

```text
           topᵉ                             topᵉ ∙hᵉ pᵉ
       fᵉ ------->ᵉ gᵉ                     fᵉ -------->ᵉ uᵉ
       |          |                     |           |
  leftᵉ |          | rightᵉ    ≃ᵉ     leftᵉ |           | qᵉ ∙hᵉ rightᵉ
       ∨ᵉ          ∨ᵉ                     ∨ᵉ           ∨ᵉ
       hᵉ ------->ᵉ iᵉ                     hᵉ -------->ᵉ iᵉ
          bottomᵉ                           bottomᵉ
```

ofᵉ coherencesᵉ ofᵉ commutingᵉ squaresᵉ ofᵉ homotopies.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {fᵉ gᵉ hᵉ iᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ}
  (topᵉ : fᵉ ~ᵉ gᵉ) (leftᵉ : fᵉ ~ᵉ hᵉ) (rightᵉ : gᵉ ~ᵉ iᵉ) (bottomᵉ : hᵉ ~ᵉ iᵉ)
  where

  equiv-right-splice-coherence-square-homotopiesᵉ :
    {uᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ} (pᵉ : gᵉ ~ᵉ uᵉ) (qᵉ : uᵉ ~ᵉ gᵉ) (αᵉ : inv-htpyᵉ pᵉ ~ᵉ qᵉ) →
    coherence-square-homotopiesᵉ topᵉ leftᵉ rightᵉ bottomᵉ ≃ᵉ
    coherence-square-homotopiesᵉ (topᵉ ∙hᵉ pᵉ) leftᵉ (inv-htpyᵉ pᵉ ∙hᵉ rightᵉ) bottomᵉ
  equiv-right-splice-coherence-square-homotopiesᵉ pᵉ qᵉ αᵉ =
    equiv-Π-equiv-familyᵉ
      ( λ xᵉ →
        equiv-right-splice-coherence-square-identificationsᵉ
          ( topᵉ xᵉ) (leftᵉ xᵉ) (rightᵉ xᵉ) (bottomᵉ xᵉ) (pᵉ xᵉ) (qᵉ xᵉ) (αᵉ xᵉ))
```

### Double whiskering of commuting squares of homotopies

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {fᵉ gᵉ hᵉ uᵉ vᵉ iᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ}
  where

  equiv-double-whisker-coherence-square-homotopiesᵉ :
    (pᵉ : fᵉ ~ᵉ gᵉ)
    (topᵉ : gᵉ ~ᵉ uᵉ) (leftᵉ : gᵉ ~ᵉ hᵉ) (rightᵉ : uᵉ ~ᵉ vᵉ) (bottomᵉ : hᵉ ~ᵉ vᵉ)
    (sᵉ : vᵉ ~ᵉ iᵉ) →
    coherence-square-homotopiesᵉ topᵉ leftᵉ rightᵉ bottomᵉ ≃ᵉ
    coherence-square-homotopiesᵉ
      ( pᵉ ∙hᵉ topᵉ)
      ( pᵉ ∙hᵉ leftᵉ)
      ( rightᵉ ∙hᵉ sᵉ)
      ( bottomᵉ ∙hᵉ sᵉ)
  equiv-double-whisker-coherence-square-homotopiesᵉ pᵉ topᵉ leftᵉ rightᵉ bottomᵉ qᵉ =
    equiv-Π-equiv-familyᵉ
      ( λ xᵉ →
        equiv-double-whisker-coherence-square-identificationsᵉ
          ( pᵉ xᵉ) (topᵉ xᵉ) (leftᵉ xᵉ) (rightᵉ xᵉ) (bottomᵉ xᵉ) (qᵉ xᵉ))
```

### Computing the pasting of two squares with `refl-htpy` on opposite sides

Considerᵉ twoᵉ squaresᵉ ofᵉ homotopiesᵉ asᵉ in theᵉ diagramᵉ

```text
                 refl-htpyᵉ
              aᵉ ---------->ᵉ aᵉ
              |             |
     top-leftᵉ |             | top-rightᵉ
              ∨ᵉ  refl-htpyᵉ  ∨ᵉ
              bᵉ ---------->ᵉ bᵉ
              |             |
  bottom-leftᵉ |             | bottom-rightᵉ
              ∨ᵉ             ∨ᵉ
              cᵉ ---------->ᵉ cᵉ
                 refl-htpyᵉ
```

Theᵉ resultᵉ ofᵉ verticallyᵉ pastingᵉ theseᵉ squaresᵉ canᵉ beᵉ computedᵉ in termsᵉ ofᵉ theᵉ
horizontalᵉ concatenationᵉ ofᵉ homotopies.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {aᵉ bᵉ cᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ}
  (top-leftᵉ : aᵉ ~ᵉ bᵉ) (top-rightᵉ : aᵉ ~ᵉ bᵉ)
  (bottom-leftᵉ : bᵉ ~ᵉ cᵉ) (bottom-rightᵉ : bᵉ ~ᵉ cᵉ)
  where

  vertical-pasting-coherence-square-homotopies-horizontal-reflᵉ :
    (Hᵉ : top-leftᵉ ~ᵉ top-rightᵉ) (Kᵉ : bottom-leftᵉ ~ᵉ bottom-rightᵉ) →
    ( inv-coherence-square-homotopies-horizontal-reflᵉ
      ( top-leftᵉ ∙hᵉ bottom-leftᵉ)
      ( top-rightᵉ ∙hᵉ bottom-rightᵉ)
      ( vertical-pasting-coherence-square-homotopiesᵉ
        ( refl-htpyᵉ)
        ( top-leftᵉ)
        ( top-rightᵉ)
        ( refl-htpyᵉ)
        ( bottom-leftᵉ)
        ( bottom-rightᵉ)
        ( refl-htpyᵉ)
        ( coherence-square-homotopies-horizontal-reflᵉ
          ( top-leftᵉ)
          ( top-rightᵉ)
          ( Hᵉ))
        ( coherence-square-homotopies-horizontal-reflᵉ
          ( bottom-leftᵉ)
          ( bottom-rightᵉ)
          ( Kᵉ)))) ~ᵉ
    ( horizontal-concat-htpy²ᵉ Hᵉ Kᵉ)
  vertical-pasting-coherence-square-homotopies-horizontal-reflᵉ Hᵉ Kᵉ xᵉ =
    vertical-pasting-coherence-square-identifications-horizontal-reflᵉ
      ( top-leftᵉ xᵉ)
      ( top-rightᵉ xᵉ)
      ( bottom-leftᵉ xᵉ)
      ( bottom-rightᵉ xᵉ)
      ( Hᵉ xᵉ)
      ( Kᵉ xᵉ)

  vertical-pasting-inv-coherence-square-homotopies-horizontal-reflᵉ :
    (Hᵉ : coherence-square-homotopiesᵉ
      ( refl-htpyᵉ)
      ( top-leftᵉ)
      ( top-rightᵉ)
      ( refl-htpyᵉ))
    (Kᵉ : coherence-square-homotopiesᵉ
      ( refl-htpyᵉ)
      ( bottom-leftᵉ)
      ( bottom-rightᵉ)
      ( refl-htpyᵉ)) →
    ( inv-coherence-square-homotopies-horizontal-reflᵉ
      ( top-leftᵉ ∙hᵉ bottom-leftᵉ)
      ( top-rightᵉ ∙hᵉ bottom-rightᵉ)
      ( vertical-pasting-coherence-square-homotopiesᵉ
        ( refl-htpyᵉ)
        ( top-leftᵉ)
        ( top-rightᵉ)
        ( refl-htpyᵉ)
        ( bottom-leftᵉ)
        ( bottom-rightᵉ)
        ( refl-htpyᵉ)
        ( Hᵉ)
        ( Kᵉ))) ~ᵉ
    ( horizontal-concat-htpy²ᵉ
      ( inv-coherence-square-homotopies-horizontal-reflᵉ
        ( top-leftᵉ)
        ( top-rightᵉ)
        ( Hᵉ))
      ( inv-coherence-square-homotopies-horizontal-reflᵉ
        ( bottom-leftᵉ)
        ( bottom-rightᵉ)
        ( Kᵉ)))
  vertical-pasting-inv-coherence-square-homotopies-horizontal-reflᵉ Hᵉ Kᵉ xᵉ =
    vertical-pasting-inv-coherence-square-identifications-horizontal-reflᵉ
      ( top-leftᵉ xᵉ)
      ( top-rightᵉ xᵉ)
      ( bottom-leftᵉ xᵉ)
      ( bottom-rightᵉ xᵉ)
      ( Hᵉ xᵉ)
      ( Kᵉ xᵉ)
```