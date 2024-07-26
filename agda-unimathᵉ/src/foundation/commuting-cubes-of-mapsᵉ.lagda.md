# Commuting cubes of maps

```agda
module foundation.commuting-cubes-of-mapsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.commuting-hexagons-of-identificationsᵉ
open import foundation.commuting-squares-of-mapsᵉ
open import foundation.cones-over-cospan-diagramsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.homotopiesᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ

open import foundation-core.function-typesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.precomposition-functionsᵉ
open import foundation-core.whiskering-identifications-concatenationᵉ
```

</details>

## Idea

Weᵉ specifyᵉ theᵉ typeᵉ ofᵉ theᵉ homotopyᵉ witnessingᵉ thatᵉ aᵉ cubeᵉ commutes.ᵉ Imagineᵉ
thatᵉ theᵉ cubeᵉ isᵉ presentedᵉ asᵉ aᵉ latticeᵉ

```text
            A'ᵉ
          /ᵉ | \ᵉ
         /ᵉ  |  \ᵉ
        /ᵉ   |   \ᵉ
       B'ᵉ   Aᵉ    C'ᵉ
       |\ᵉ /ᵉ   \ᵉ /|ᵉ
       | \ᵉ     /ᵉ |
       |/ᵉ \ᵉ   /ᵉ \|ᵉ
       Bᵉ    D'ᵉ   Cᵉ
        \ᵉ   |   /ᵉ
         \ᵉ  |  /ᵉ
          \ᵉ | /ᵉ
            Dᵉ
```

with allᵉ mapsᵉ pointingᵉ in theᵉ downwardsᵉ direction.ᵉ Presentedᵉ in thisᵉ way,ᵉ aᵉ cubeᵉ
ofᵉ mapsᵉ hasᵉ aᵉ topᵉ face,ᵉ aᵉ back-leftᵉ face,ᵉ aᵉ back-rightᵉ face,ᵉ aᵉ front-leftᵉ face,ᵉ
aᵉ front-rightᵉ face,ᵉ andᵉ aᵉ bottomᵉ face,ᵉ allᵉ ofᵉ whichᵉ areᵉ homotopies.ᵉ Anᵉ elementᵉ
ofᵉ typeᵉ `coherence-cube-maps`ᵉ isᵉ aᵉ homotopyᵉ fillingᵉ theᵉ cube.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l1'ᵉ l2'ᵉ l3'ᵉ l4'ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} {Dᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Aᵉ → Cᵉ) (hᵉ : Bᵉ → Dᵉ) (kᵉ : Cᵉ → Dᵉ)
  {A'ᵉ : UUᵉ l1'ᵉ} {B'ᵉ : UUᵉ l2'ᵉ} {C'ᵉ : UUᵉ l3'ᵉ} {D'ᵉ : UUᵉ l4'ᵉ}
  (f'ᵉ : A'ᵉ → B'ᵉ) (g'ᵉ : A'ᵉ → C'ᵉ) (h'ᵉ : B'ᵉ → D'ᵉ) (k'ᵉ : C'ᵉ → D'ᵉ)
  (hAᵉ : A'ᵉ → Aᵉ) (hBᵉ : B'ᵉ → Bᵉ) (hCᵉ : C'ᵉ → Cᵉ) (hDᵉ : D'ᵉ → Dᵉ)
  where

  coherence-cube-mapsᵉ :
    (topᵉ : (h'ᵉ ∘ᵉ f'ᵉ) ~ᵉ (k'ᵉ ∘ᵉ g'ᵉ))
    (back-leftᵉ : (fᵉ ∘ᵉ hAᵉ) ~ᵉ (hBᵉ ∘ᵉ f'ᵉ))
    (back-rightᵉ : (gᵉ ∘ᵉ hAᵉ) ~ᵉ (hCᵉ ∘ᵉ g'ᵉ))
    (front-leftᵉ : (hᵉ ∘ᵉ hBᵉ) ~ᵉ (hDᵉ ∘ᵉ h'ᵉ))
    (front-rightᵉ : (kᵉ ∘ᵉ hCᵉ) ~ᵉ (hDᵉ ∘ᵉ k'ᵉ))
    (bottomᵉ : (hᵉ ∘ᵉ fᵉ) ~ᵉ (kᵉ ∘ᵉ gᵉ)) →
    UUᵉ (l4ᵉ ⊔ l1'ᵉ)
  coherence-cube-mapsᵉ topᵉ back-leftᵉ back-rightᵉ front-leftᵉ front-rightᵉ bottomᵉ =
    (a'ᵉ : A'ᵉ) →
    coherence-hexagonᵉ
      ( apᵉ hᵉ (back-leftᵉ a'ᵉ))
      ( front-leftᵉ (f'ᵉ a'ᵉ))
      ( apᵉ hDᵉ (topᵉ a'ᵉ))
      ( bottomᵉ (hAᵉ a'ᵉ))
      ( apᵉ kᵉ (back-rightᵉ a'ᵉ))
      ( front-rightᵉ (g'ᵉ a'ᵉ))
```

### Symmetries of commuting cubes

Theᵉ symmetryᵉ groupᵉ D₃ᵉ actsᵉ onᵉ aᵉ cube.ᵉ However,ᵉ theᵉ coherenceᵉ fillingᵉ aᵉ cubeᵉ
needsᵉ to beᵉ modifiedᵉ to showᵉ thatᵉ theᵉ rotated/reflectedᵉ cubeᵉ againᵉ commutes.ᵉ Inᵉ
theᵉ followingᵉ definitionsᵉ weᵉ provideᵉ theᵉ homotopiesᵉ witnessingᵉ thatᵉ theᵉ
rotated/reflectedᵉ cubesᵉ againᵉ commute.ᵉ

Noteᵉ: althoughᵉ in principleᵉ itᵉ oughtᵉ to beᵉ enoughᵉ to showᵉ thisᵉ forᵉ theᵉ
generatorsᵉ ofᵉ theᵉ symmetryᵉ groupᵉ D₃,ᵉ in practiceᵉ itᵉ isᵉ moreᵉ straightforwardᵉ to
justᵉ do theᵉ workᵉ forᵉ eachᵉ ofᵉ theᵉ symmetriesᵉ separately.ᵉ Oneᵉ reasonᵉ isᵉ thatᵉ someᵉ
ofᵉ theᵉ homotopiesᵉ witnessingᵉ thatᵉ theᵉ facesᵉ commuteᵉ willᵉ beᵉ invertedᵉ asᵉ theᵉ
resultᵉ ofᵉ anᵉ applicationᵉ ofᵉ aᵉ symmetry.ᵉ Invertingᵉ aᵉ homotopyᵉ twiceᵉ resultsᵉ in aᵉ
newᵉ homotopyᵉ thatᵉ isᵉ onlyᵉ homotopicᵉ to theᵉ originalᵉ homotopy.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l1'ᵉ l2'ᵉ l3'ᵉ l4'ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} {Dᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Aᵉ → Cᵉ) (hᵉ : Bᵉ → Dᵉ) (kᵉ : Cᵉ → Dᵉ)
  {A'ᵉ : UUᵉ l1'ᵉ} {B'ᵉ : UUᵉ l2'ᵉ} {C'ᵉ : UUᵉ l3'ᵉ} {D'ᵉ : UUᵉ l4'ᵉ}
  (f'ᵉ : A'ᵉ → B'ᵉ) (g'ᵉ : A'ᵉ → C'ᵉ) (h'ᵉ : B'ᵉ → D'ᵉ) (k'ᵉ : C'ᵉ → D'ᵉ)
  (hAᵉ : A'ᵉ → Aᵉ) (hBᵉ : B'ᵉ → Bᵉ) (hCᵉ : C'ᵉ → Cᵉ) (hDᵉ : D'ᵉ → Dᵉ)
  (topᵉ : coherence-square-mapsᵉ g'ᵉ f'ᵉ k'ᵉ h'ᵉ)
  (back-leftᵉ : coherence-square-mapsᵉ f'ᵉ hAᵉ hBᵉ fᵉ)
  (back-rightᵉ : coherence-square-mapsᵉ g'ᵉ hAᵉ hCᵉ gᵉ)
  (front-leftᵉ : coherence-square-mapsᵉ h'ᵉ hBᵉ hDᵉ hᵉ)
  (front-rightᵉ : coherence-square-mapsᵉ k'ᵉ hCᵉ hDᵉ kᵉ)
  (bottomᵉ : coherence-square-mapsᵉ gᵉ fᵉ kᵉ hᵉ)
  (cᵉ :
    coherence-cube-mapsᵉ
      fᵉ gᵉ hᵉ kᵉ f'ᵉ g'ᵉ h'ᵉ k'ᵉ hAᵉ hBᵉ hCᵉ hDᵉ
      topᵉ back-leftᵉ back-rightᵉ front-leftᵉ front-rightᵉ bottomᵉ)
  where

  coherence-cube-maps-rotate-120ᵉ :
    coherence-cube-mapsᵉ hCᵉ k'ᵉ kᵉ hDᵉ hAᵉ f'ᵉ fᵉ hBᵉ g'ᵉ gᵉ h'ᵉ hᵉ
      ( back-leftᵉ)
      ( inv-htpyᵉ back-rightᵉ)
      ( inv-htpyᵉ topᵉ)
      ( inv-htpyᵉ bottomᵉ)
      ( inv-htpyᵉ front-leftᵉ)
      ( front-rightᵉ)
  coherence-cube-maps-rotate-120ᵉ a'ᵉ =
    ( right-whisker-concatᵉ
      ( right-whisker-concatᵉ
        ( ap-invᵉ kᵉ (back-rightᵉ a'ᵉ))
        ( invᵉ (bottomᵉ (hAᵉ a'ᵉ))))
      ( apᵉ hᵉ (back-leftᵉ a'ᵉ))) ∙ᵉ
    ( ( hexagon-rotate-120ᵉ
        ( apᵉ hᵉ (back-leftᵉ a'ᵉ))
        ( front-leftᵉ (f'ᵉ a'ᵉ))
        ( apᵉ hDᵉ (topᵉ a'ᵉ))
        ( bottomᵉ (hAᵉ a'ᵉ))
        ( apᵉ kᵉ (back-rightᵉ a'ᵉ))
        ( front-rightᵉ (g'ᵉ a'ᵉ))
        ( cᵉ a'ᵉ)) ∙ᵉ
      ( invᵉ
        ( left-whisker-concatᵉ
          ( front-rightᵉ (g'ᵉ a'ᵉ))
          ( right-whisker-concatᵉ
            ( ap-invᵉ hDᵉ (topᵉ a'ᵉ))
            ( invᵉ (front-leftᵉ (f'ᵉ a'ᵉ)))))))

  coherence-cube-maps-rotate-240ᵉ :
    coherence-cube-mapsᵉ h'ᵉ hBᵉ hDᵉ hᵉ g'ᵉ hAᵉ hCᵉ gᵉ f'ᵉ k'ᵉ fᵉ kᵉ
      ( inv-htpyᵉ back-rightᵉ)
      ( topᵉ)
      ( inv-htpyᵉ back-leftᵉ)
      ( inv-htpyᵉ front-rightᵉ)
      ( bottomᵉ)
      ( inv-htpyᵉ front-leftᵉ)
  coherence-cube-maps-rotate-240ᵉ a'ᵉ =
    ( left-whisker-concatᵉ _ (ap-invᵉ kᵉ (back-rightᵉ a'ᵉ))) ∙ᵉ
    ( ( hexagon-rotate-240ᵉ
        ( apᵉ hᵉ (back-leftᵉ a'ᵉ))
        ( front-leftᵉ (f'ᵉ a'ᵉ))
        ( apᵉ hDᵉ (topᵉ a'ᵉ))
        ( bottomᵉ (hAᵉ a'ᵉ))
        ( apᵉ kᵉ (back-rightᵉ a'ᵉ))
        ( front-rightᵉ (g'ᵉ a'ᵉ))
        ( cᵉ a'ᵉ)) ∙ᵉ
      ( invᵉ
        ( left-whisker-concatᵉ
          ( invᵉ (front-leftᵉ (f'ᵉ a'ᵉ)))
          ( right-whisker-concatᵉ (ap-invᵉ hᵉ (back-leftᵉ a'ᵉ)) _))))

  coherence-cube-maps-mirror-Aᵉ :
    coherence-cube-mapsᵉ gᵉ fᵉ kᵉ hᵉ g'ᵉ f'ᵉ k'ᵉ h'ᵉ hAᵉ hCᵉ hBᵉ hDᵉ
      ( inv-htpyᵉ topᵉ)
      ( back-rightᵉ)
      ( back-leftᵉ)
      ( front-rightᵉ)
      ( front-leftᵉ)
      ( inv-htpyᵉ bottomᵉ)
  coherence-cube-maps-mirror-Aᵉ a'ᵉ =
    ( left-whisker-concatᵉ _ (ap-invᵉ hDᵉ (topᵉ a'ᵉ))) ∙ᵉ
    ( hexagon-mirror-Aᵉ
      ( apᵉ hᵉ (back-leftᵉ a'ᵉ))
      ( front-leftᵉ (f'ᵉ a'ᵉ))
      ( apᵉ hDᵉ (topᵉ a'ᵉ))
      ( bottomᵉ (hAᵉ a'ᵉ))
      ( apᵉ kᵉ (back-rightᵉ a'ᵉ))
      ( front-rightᵉ (g'ᵉ a'ᵉ))
      ( cᵉ a'ᵉ))

  coherence-cube-maps-mirror-Bᵉ :
    coherence-cube-mapsᵉ hBᵉ h'ᵉ hᵉ hDᵉ hAᵉ g'ᵉ gᵉ hCᵉ f'ᵉ fᵉ k'ᵉ kᵉ
      ( back-rightᵉ)
      ( inv-htpyᵉ back-leftᵉ)
      ( topᵉ)
      ( bottomᵉ)
      ( inv-htpyᵉ front-rightᵉ)
      ( front-leftᵉ)
  coherence-cube-maps-mirror-Bᵉ a'ᵉ =
    ( right-whisker-concatᵉ
      ( right-whisker-concatᵉ (ap-invᵉ hᵉ (back-leftᵉ a'ᵉ)) _)
      ( apᵉ kᵉ (back-rightᵉ a'ᵉ))) ∙ᵉ
    ( hexagon-mirror-Bᵉ
      ( apᵉ hᵉ (back-leftᵉ a'ᵉ))
      ( front-leftᵉ (f'ᵉ a'ᵉ))
      ( apᵉ hDᵉ (topᵉ a'ᵉ))
      ( bottomᵉ (hAᵉ a'ᵉ))
      ( apᵉ kᵉ (back-rightᵉ a'ᵉ))
      ( front-rightᵉ (g'ᵉ a'ᵉ))
      ( cᵉ a'ᵉ))

  coherence-cube-maps-mirror-Cᵉ :
    coherence-cube-mapsᵉ k'ᵉ hCᵉ hDᵉ kᵉ f'ᵉ hAᵉ hBᵉ fᵉ g'ᵉ h'ᵉ gᵉ hᵉ
      ( inv-htpyᵉ back-leftᵉ)
      ( inv-htpyᵉ topᵉ)
      ( inv-htpyᵉ back-rightᵉ)
      ( inv-htpyᵉ front-leftᵉ)
      ( inv-htpyᵉ bottomᵉ)
      ( inv-htpyᵉ front-rightᵉ)
  coherence-cube-maps-mirror-Cᵉ a'ᵉ =
    ( apᵉ
      ( λ tᵉ → (tᵉ ∙ᵉ invᵉ (front-leftᵉ (f'ᵉ a'ᵉ))) ∙ᵉ (apᵉ hᵉ (invᵉ (back-leftᵉ a'ᵉ))))
      ( ap-invᵉ hDᵉ (topᵉ a'ᵉ))) ∙ᵉ
    ( ( left-whisker-concatᵉ _ (ap-invᵉ hᵉ (back-leftᵉ a'ᵉ))) ∙ᵉ
      ( ( hexagon-mirror-Cᵉ
          ( apᵉ hᵉ (back-leftᵉ a'ᵉ))
          ( front-leftᵉ (f'ᵉ a'ᵉ))
          ( apᵉ hDᵉ (topᵉ a'ᵉ))
          ( bottomᵉ (hAᵉ a'ᵉ))
          ( apᵉ kᵉ (back-rightᵉ a'ᵉ))
          ( front-rightᵉ (g'ᵉ a'ᵉ))
          ( cᵉ a'ᵉ)) ∙ᵉ
        ( invᵉ
          ( left-whisker-concatᵉ
            ( invᵉ (front-rightᵉ (g'ᵉ a'ᵉ)))
            ( right-whisker-concatᵉ (ap-invᵉ kᵉ (back-rightᵉ a'ᵉ)) _)))))
```

### Rectangles in commuting cubes

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l1'ᵉ l2'ᵉ l3'ᵉ l4'ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} {Dᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Aᵉ → Cᵉ) (hᵉ : Bᵉ → Dᵉ) (kᵉ : Cᵉ → Dᵉ)
  {A'ᵉ : UUᵉ l1'ᵉ} {B'ᵉ : UUᵉ l2'ᵉ} {C'ᵉ : UUᵉ l3'ᵉ} {D'ᵉ : UUᵉ l4'ᵉ}
  (f'ᵉ : A'ᵉ → B'ᵉ) (g'ᵉ : A'ᵉ → C'ᵉ) (h'ᵉ : B'ᵉ → D'ᵉ) (k'ᵉ : C'ᵉ → D'ᵉ)
  (hAᵉ : A'ᵉ → Aᵉ) (hBᵉ : B'ᵉ → Bᵉ) (hCᵉ : C'ᵉ → Cᵉ) (hDᵉ : D'ᵉ → Dᵉ)
  (topᵉ : coherence-square-mapsᵉ g'ᵉ f'ᵉ k'ᵉ h'ᵉ)
  (back-leftᵉ : coherence-square-mapsᵉ f'ᵉ hAᵉ hBᵉ fᵉ)
  (back-rightᵉ : coherence-square-mapsᵉ g'ᵉ hAᵉ hCᵉ gᵉ)
  (front-leftᵉ : coherence-square-mapsᵉ h'ᵉ hBᵉ hDᵉ hᵉ)
  (front-rightᵉ : coherence-square-mapsᵉ k'ᵉ hCᵉ hDᵉ kᵉ)
  (bottomᵉ : coherence-square-mapsᵉ gᵉ fᵉ kᵉ hᵉ)
  where

  rectangle-left-cubeᵉ :
    ((hᵉ ∘ᵉ fᵉ) ∘ᵉ hAᵉ) ~ᵉ (hDᵉ ∘ᵉ (h'ᵉ ∘ᵉ f'ᵉ))
  rectangle-left-cubeᵉ =
    pasting-horizontal-coherence-square-mapsᵉ
      f'ᵉ h'ᵉ hAᵉ hBᵉ hDᵉ fᵉ hᵉ back-leftᵉ front-leftᵉ

  rectangle-right-cubeᵉ :
    ((kᵉ ∘ᵉ gᵉ) ∘ᵉ hAᵉ) ~ᵉ (hDᵉ ∘ᵉ (k'ᵉ ∘ᵉ g'ᵉ))
  rectangle-right-cubeᵉ =
    pasting-horizontal-coherence-square-mapsᵉ
      g'ᵉ k'ᵉ hAᵉ hCᵉ hDᵉ gᵉ kᵉ back-rightᵉ front-rightᵉ

  coherence-htpy-parallel-cone-rectangle-left-rectangle-right-cubeᵉ :
    (cᵉ : coherence-cube-mapsᵉ fᵉ gᵉ hᵉ kᵉ f'ᵉ g'ᵉ h'ᵉ k'ᵉ hAᵉ hBᵉ hCᵉ hDᵉ
      topᵉ back-leftᵉ back-rightᵉ front-leftᵉ front-rightᵉ bottomᵉ) →
    coherence-htpy-parallel-coneᵉ
      ( bottomᵉ)
      ( refl-htpy'ᵉ hDᵉ)
      ( hAᵉ ,ᵉ h'ᵉ ∘ᵉ f'ᵉ ,ᵉ rectangle-left-cubeᵉ)
      ( hAᵉ ,ᵉ k'ᵉ ∘ᵉ g'ᵉ ,ᵉ rectangle-right-cubeᵉ)
      ( refl-htpy'ᵉ hAᵉ)
      ( topᵉ)
  coherence-htpy-parallel-cone-rectangle-left-rectangle-right-cubeᵉ cᵉ =
    ( λ a'ᵉ → left-whisker-concatᵉ (rectangle-left-cubeᵉ a'ᵉ) right-unitᵉ) ∙hᵉ
    ( cᵉ)

  rectangle-top-front-left-cubeᵉ :
    ((hᵉ ∘ᵉ hBᵉ) ∘ᵉ f'ᵉ) ~ᵉ ((hDᵉ ∘ᵉ k'ᵉ) ∘ᵉ g'ᵉ)
  rectangle-top-front-left-cubeᵉ =
    ( front-leftᵉ ·rᵉ f'ᵉ) ∙hᵉ (hDᵉ ·lᵉ topᵉ)

  rectangle-back-right-bottom-cubeᵉ :
    ((hᵉ ∘ᵉ fᵉ) ∘ᵉ hAᵉ) ~ᵉ ((kᵉ ∘ᵉ hCᵉ) ∘ᵉ g'ᵉ)
  rectangle-back-right-bottom-cubeᵉ =
    ( bottomᵉ ·rᵉ hAᵉ) ∙hᵉ (kᵉ ·lᵉ back-rightᵉ)

  rectangle-top-front-right-cubeᵉ :
    ((hDᵉ ∘ᵉ h'ᵉ) ∘ᵉ f'ᵉ) ~ᵉ ((kᵉ ∘ᵉ hCᵉ) ∘ᵉ g'ᵉ)
  rectangle-top-front-right-cubeᵉ =
    (hDᵉ ·lᵉ topᵉ) ∙hᵉ (inv-htpyᵉ (front-rightᵉ) ·rᵉ g'ᵉ)

  rectangle-back-left-bottom-cubeᵉ :
    ((hᵉ ∘ᵉ hBᵉ) ∘ᵉ f'ᵉ) ~ᵉ ((kᵉ ∘ᵉ gᵉ) ∘ᵉ hAᵉ)
  rectangle-back-left-bottom-cubeᵉ =
    (hᵉ ·lᵉ (inv-htpyᵉ back-leftᵉ)) ∙hᵉ (bottomᵉ ·rᵉ hAᵉ)
```

Inᵉ analogyᵉ to theᵉ coherenceᵉ
`coherence-htpy-parallel-cone-rectangle-left-rectangle-right-cube`ᵉ weᵉ alsoᵉ
expectᵉ to beᵉ ableᵉ to constructᵉ aᵉ coherenceᵉ

```text
  coherence-htpy-parallel-cone-rectangle-top-fl-rectangle-br-bot-cubeᵉ :
    (cᵉ : coherence-cube-mapsᵉ fᵉ gᵉ hᵉ kᵉ f'ᵉ g'ᵉ h'ᵉ k'ᵉ hAᵉ hBᵉ hCᵉ hDᵉ
      topᵉ back-leftᵉ back-rightᵉ front-leftᵉ front-rightᵉ bottomᵉ) →
    coherence-htpy-parallel-coneᵉ
      ( inv-htpyᵉ front-rightᵉ)
      ( refl-htpy'ᵉ hᵉ)
      ( g'ᵉ ,ᵉ hBᵉ ∘ᵉ f'ᵉ ,ᵉ inv-htpyᵉ (rectangle-top-front-left-cubeᵉ))
      ( g'ᵉ ,ᵉ fᵉ ∘ᵉ hAᵉ ,ᵉ inv-htpyᵉ (rectangle-back-right-bottom-cubeᵉ))
      ( refl-htpy'ᵉ g'ᵉ)
      ( inv-htpyᵉ back-leftᵉ)
```

### Any coherence of commuting cubes induces a coherence of parallel cones

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l1'ᵉ l2'ᵉ l3'ᵉ l4'ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} {Dᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Aᵉ → Cᵉ) (hᵉ : Bᵉ → Dᵉ) (kᵉ : Cᵉ → Dᵉ)
  {A'ᵉ : UUᵉ l1'ᵉ} {B'ᵉ : UUᵉ l2'ᵉ} {C'ᵉ : UUᵉ l3'ᵉ} {D'ᵉ : UUᵉ l4'ᵉ}
  (f'ᵉ : A'ᵉ → B'ᵉ) (g'ᵉ : A'ᵉ → C'ᵉ) (h'ᵉ : B'ᵉ → D'ᵉ) (k'ᵉ : C'ᵉ → D'ᵉ)
  (hAᵉ : A'ᵉ → Aᵉ) (hBᵉ : B'ᵉ → Bᵉ) (hCᵉ : C'ᵉ → Cᵉ) (hDᵉ : D'ᵉ → Dᵉ)
  (topᵉ : coherence-square-mapsᵉ g'ᵉ f'ᵉ k'ᵉ h'ᵉ)
  (back-leftᵉ : coherence-square-mapsᵉ f'ᵉ hAᵉ hBᵉ fᵉ)
  (back-rightᵉ : coherence-square-mapsᵉ g'ᵉ hAᵉ hCᵉ gᵉ)
  (front-leftᵉ : coherence-square-mapsᵉ h'ᵉ hBᵉ hDᵉ hᵉ)
  (front-rightᵉ : coherence-square-mapsᵉ k'ᵉ hCᵉ hDᵉ kᵉ)
  (bottomᵉ : coherence-square-mapsᵉ gᵉ fᵉ kᵉ hᵉ)
  where

  coherence-htpy-parallel-cone-coherence-cube-mapsᵉ :
    ( cᵉ :
      coherence-cube-mapsᵉ
        fᵉ gᵉ hᵉ kᵉ f'ᵉ g'ᵉ h'ᵉ k'ᵉ hAᵉ hBᵉ hCᵉ hDᵉ
        topᵉ back-leftᵉ back-rightᵉ front-leftᵉ front-rightᵉ bottomᵉ) →
    coherence-htpy-parallel-coneᵉ
      ( front-leftᵉ)
      ( refl-htpy'ᵉ kᵉ)
      ( ( f'ᵉ) ,ᵉ
        ( gᵉ ∘ᵉ hAᵉ) ,ᵉ
        ( rectangle-back-left-bottom-cubeᵉ
          fᵉ gᵉ hᵉ kᵉ f'ᵉ g'ᵉ h'ᵉ k'ᵉ hAᵉ hBᵉ hCᵉ hDᵉ
          topᵉ back-leftᵉ back-rightᵉ front-leftᵉ front-rightᵉ bottomᵉ))
      ( ( f'ᵉ) ,ᵉ
        ( hCᵉ ∘ᵉ g'ᵉ) ,ᵉ
        ( rectangle-top-front-right-cubeᵉ
          fᵉ gᵉ hᵉ kᵉ f'ᵉ g'ᵉ h'ᵉ k'ᵉ hAᵉ hBᵉ hCᵉ hDᵉ
          topᵉ back-leftᵉ back-rightᵉ front-leftᵉ front-rightᵉ bottomᵉ))
      ( refl-htpy'ᵉ f'ᵉ)
      ( back-rightᵉ)
  coherence-htpy-parallel-cone-coherence-cube-mapsᵉ cᵉ =
    ( assoc-htpyᵉ
      ( hᵉ ·lᵉ (inv-htpyᵉ back-leftᵉ))
      ( bottomᵉ ·rᵉ hAᵉ)
      ( (kᵉ ·lᵉ back-rightᵉ) ∙hᵉ (refl-htpy'ᵉ (kᵉ ∘ᵉ (hCᵉ ∘ᵉ g'ᵉ))))) ∙hᵉ
    ( ( ap-concat-htpy'ᵉ
        ( _)
        ( left-whisker-inv-htpyᵉ hᵉ back-leftᵉ)) ∙hᵉ
      ( inv-htpy-left-transpose-htpy-concatᵉ (hᵉ ·lᵉ back-leftᵉ) _ _
        ( ( (inv-htpy-assoc-htpyᵉ (hᵉ ·lᵉ back-leftᵉ) (front-leftᵉ ·rᵉ f'ᵉ) _) ∙hᵉ
            ( ( inv-htpy-assoc-htpyᵉ
                ( (hᵉ ·lᵉ back-leftᵉ) ∙hᵉ (front-leftᵉ ·rᵉ f'ᵉ))
                ( hDᵉ ·lᵉ topᵉ)
                ( (inv-htpyᵉ front-rightᵉ) ·rᵉ g'ᵉ)) ∙hᵉ
              ( inv-htpy-right-transpose-htpy-concatᵉ _ (front-rightᵉ ·rᵉ g'ᵉ) _
                ( (assoc-htpyᵉ (bottomᵉ ·rᵉ hAᵉ) _ _) ∙hᵉ (inv-htpyᵉ cᵉ))))) ∙hᵉ
          ( ap-concat-htpyᵉ (bottomᵉ ·rᵉ hAᵉ) inv-htpy-right-unit-htpyᵉ))))
```

### Commuting cubes of maps induce commuting cubes of precomposition maps

```agda
module _
  { l1ᵉ l2ᵉ l3ᵉ l4ᵉ l1'ᵉ l2'ᵉ l3'ᵉ l4'ᵉ l5ᵉ : Level}
  { Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} {Dᵉ : UUᵉ l4ᵉ}
  ( fᵉ : Aᵉ → Bᵉ) (gᵉ : Aᵉ → Cᵉ) (hᵉ : Bᵉ → Dᵉ) (kᵉ : Cᵉ → Dᵉ)
  { A'ᵉ : UUᵉ l1'ᵉ} {B'ᵉ : UUᵉ l2'ᵉ} {C'ᵉ : UUᵉ l3'ᵉ} {D'ᵉ : UUᵉ l4'ᵉ}
  ( f'ᵉ : A'ᵉ → B'ᵉ) (g'ᵉ : A'ᵉ → C'ᵉ) (h'ᵉ : B'ᵉ → D'ᵉ) (k'ᵉ : C'ᵉ → D'ᵉ)
  ( hAᵉ : A'ᵉ → Aᵉ) (hBᵉ : B'ᵉ → Bᵉ) (hCᵉ : C'ᵉ → Cᵉ) (hDᵉ : D'ᵉ → Dᵉ)
  ( topᵉ : coherence-square-mapsᵉ g'ᵉ f'ᵉ k'ᵉ h'ᵉ)
  ( back-leftᵉ : coherence-square-mapsᵉ f'ᵉ hAᵉ hBᵉ fᵉ)
  ( back-rightᵉ : coherence-square-mapsᵉ g'ᵉ hAᵉ hCᵉ gᵉ)
  ( front-leftᵉ : coherence-square-mapsᵉ h'ᵉ hBᵉ hDᵉ hᵉ)
  ( front-rightᵉ : coherence-square-mapsᵉ k'ᵉ hCᵉ hDᵉ kᵉ)
  ( bottomᵉ : coherence-square-mapsᵉ gᵉ fᵉ kᵉ hᵉ)
  where

  precomp-coherence-cube-mapsᵉ :
    coherence-cube-mapsᵉ fᵉ gᵉ hᵉ kᵉ f'ᵉ g'ᵉ h'ᵉ k'ᵉ hAᵉ hBᵉ hCᵉ hDᵉ
      ( topᵉ)
      ( back-leftᵉ)
      ( back-rightᵉ)
      ( front-leftᵉ)
      ( front-rightᵉ)
      ( bottomᵉ) →
    ( Wᵉ : UUᵉ l5ᵉ) →
    coherence-cube-mapsᵉ
      ( precompᵉ h'ᵉ Wᵉ)
      ( precompᵉ k'ᵉ Wᵉ)
      ( precompᵉ f'ᵉ Wᵉ)
      ( precompᵉ g'ᵉ Wᵉ)
      ( precompᵉ hᵉ Wᵉ)
      ( precompᵉ kᵉ Wᵉ)
      ( precompᵉ fᵉ Wᵉ)
      ( precompᵉ gᵉ Wᵉ)
      ( precompᵉ hDᵉ Wᵉ)
      ( precompᵉ hBᵉ Wᵉ)
      ( precompᵉ hCᵉ Wᵉ)
      ( precompᵉ hAᵉ Wᵉ)
      ( precomp-coherence-square-mapsᵉ gᵉ fᵉ kᵉ hᵉ bottomᵉ Wᵉ)
      ( precomp-coherence-square-mapsᵉ hBᵉ h'ᵉ hᵉ hDᵉ (inv-htpyᵉ front-leftᵉ) Wᵉ)
      ( precomp-coherence-square-mapsᵉ hCᵉ k'ᵉ kᵉ hDᵉ (inv-htpyᵉ front-rightᵉ) Wᵉ)
      ( precomp-coherence-square-mapsᵉ hAᵉ f'ᵉ fᵉ hBᵉ (inv-htpyᵉ back-leftᵉ) Wᵉ)
      ( precomp-coherence-square-mapsᵉ hAᵉ g'ᵉ gᵉ hCᵉ (inv-htpyᵉ back-rightᵉ) Wᵉ)
      ( precomp-coherence-square-mapsᵉ g'ᵉ f'ᵉ k'ᵉ h'ᵉ topᵉ Wᵉ)
  precomp-coherence-cube-mapsᵉ cᵉ Wᵉ =
    homotopy-reasoningᵉ
      ( (precompᵉ f'ᵉ Wᵉ) ·lᵉ precomp-front-left-invᵉ) ∙hᵉ
      ( precomp-back-left-invᵉ ·rᵉ (precompᵉ hᵉ Wᵉ)) ∙hᵉ
      ( (precompᵉ hAᵉ Wᵉ) ·lᵉ precomp-bottomᵉ)
      ~ᵉ ( precomp-front-left-inv-whisker-f'ᵉ) ∙hᵉ
        ( precomp-h-whisker-back-left-invᵉ) ∙hᵉ
        ( precomp-bottom-whisker-hAᵉ)
        byᵉ
        inv-htpyᵉ
          ( horizontal-concat-htpy²ᵉ
            ( horizontal-concat-htpy²ᵉ
              ( distributive-precomp-right-whisker-comp-coherence-square-mapsᵉ
                ( Wᵉ)
                ( hBᵉ)
                ( h'ᵉ)
                ( hᵉ)
                ( hDᵉ)
                ( inv-htpyᵉ front-leftᵉ)
                ( f'ᵉ))
              ( distributive-precomp-left-whisker-comp-coherence-square-mapsᵉ
                ( Wᵉ)
                ( hAᵉ)
                ( f'ᵉ)
                ( fᵉ)
                ( hBᵉ)
                ( inv-htpyᵉ back-leftᵉ)
                ( hᵉ)))
            ( distributive-precomp-right-whisker-comp-coherence-square-mapsᵉ
              ( Wᵉ)
              ( gᵉ)
              ( fᵉ)
              ( kᵉ)
              ( hᵉ)
              ( bottomᵉ)
              ( hAᵉ)))
      ~ᵉ precomp-coherence-square-mapsᵉ hAᵉ
          ( h'ᵉ ∘ᵉ f'ᵉ)
          ( kᵉ ∘ᵉ gᵉ)
          ( hDᵉ)
          ( ( inv-htpyᵉ front-leftᵉ ·rᵉ f'ᵉ) ∙hᵉ
            ( hᵉ ·lᵉ inv-htpyᵉ back-leftᵉ) ∙hᵉ
            ( bottomᵉ ·rᵉ hAᵉ))
          ( Wᵉ)
        byᵉ
        inv-htpyᵉ
          ( distributive-precomp-coherence-square-left-map-triangle-coherence-triangle-mapsᵉ
            ( Wᵉ)
            ( hAᵉ)
            ( h'ᵉ ∘ᵉ f'ᵉ)
            ( kᵉ ∘ᵉ gᵉ)
            ( hDᵉ)
            ( hᵉ ·lᵉ inv-htpyᵉ back-leftᵉ)
            ( inv-htpyᵉ front-leftᵉ ·rᵉ f'ᵉ)
            ( bottomᵉ ·rᵉ hAᵉ))
      ~ᵉ precomp-coherence-square-mapsᵉ hAᵉ
          ( h'ᵉ ∘ᵉ f'ᵉ)
          ( kᵉ ∘ᵉ gᵉ)
          ( hDᵉ)
          ( ( hDᵉ ·lᵉ topᵉ) ∙hᵉ
            ( ( inv-htpyᵉ front-rightᵉ ·rᵉ g'ᵉ) ∙hᵉ
              ( kᵉ ·lᵉ inv-htpyᵉ back-rightᵉ)))
          ( Wᵉ)
        byᵉ
        ( λ xᵉ →
          apᵉ
            ( λ squareᵉ →
              precomp-coherence-square-mapsᵉ hAᵉ (h'ᵉ ∘ᵉ f'ᵉ) (kᵉ ∘ᵉ gᵉ) hDᵉ squareᵉ Wᵉ xᵉ)
            ( eq-htpyᵉ
              ( λ a'ᵉ →
                inv-hexagonᵉ
                  ( apᵉ hDᵉ (topᵉ a'ᵉ))
                  ( invᵉ (front-rightᵉ (g'ᵉ a'ᵉ)))
                  ( apᵉ kᵉ (invᵉ (back-rightᵉ a'ᵉ)))
                  ( invᵉ (front-leftᵉ (f'ᵉ a'ᵉ)))
                  ( apᵉ hᵉ (invᵉ (back-leftᵉ a'ᵉ)))
                  ( bottomᵉ (hAᵉ a'ᵉ))
                  ( coherence-cube-maps-rotate-240ᵉ fᵉ gᵉ hᵉ kᵉ f'ᵉ g'ᵉ h'ᵉ k'ᵉ hAᵉ hBᵉ hCᵉ
                    ( hDᵉ)
                    ( topᵉ)
                    ( back-leftᵉ)
                    ( back-rightᵉ)
                    ( front-leftᵉ)
                    ( front-rightᵉ)
                    ( bottomᵉ)
                    ( cᵉ)
                    ( a'ᵉ)))))
      ~ᵉ ( precomp-hD-whisker-topᵉ) ∙hᵉ
        ( ( precomp-front-right-inv-whisker-g'ᵉ) ∙hᵉ
          ( precomp-k-whisker-back-right-invᵉ))
        byᵉ
        distributive-precomp-coherence-square-left-map-triangle-coherence-triangle-maps'ᵉ
          ( Wᵉ)
          ( hAᵉ)
          ( h'ᵉ ∘ᵉ f'ᵉ)
          ( kᵉ ∘ᵉ gᵉ)
          ( hDᵉ)
          ( inv-htpyᵉ front-rightᵉ ·rᵉ g'ᵉ)
          ( hDᵉ ·lᵉ topᵉ)
          ( kᵉ ·lᵉ inv-htpyᵉ back-rightᵉ)
      ~ᵉ ( precomp-topᵉ ·rᵉ (precompᵉ hDᵉ Wᵉ)) ∙hᵉ
        ( ( (precompᵉ g'ᵉ Wᵉ) ·lᵉ precomp-front-right-invᵉ) ∙hᵉ
          ( precomp-back-right-invᵉ ·rᵉ (precompᵉ kᵉ Wᵉ)))
        byᵉ
        horizontal-concat-htpy²ᵉ
          ( distributive-precomp-left-whisker-comp-coherence-square-mapsᵉ Wᵉ
            ( g'ᵉ)
            ( f'ᵉ)
            ( k'ᵉ)
            ( h'ᵉ)
            ( topᵉ)
            ( hDᵉ))
          ( horizontal-concat-htpy²ᵉ
            ( distributive-precomp-right-whisker-comp-coherence-square-mapsᵉ
              ( Wᵉ)
              ( hCᵉ)
              ( k'ᵉ)
              ( kᵉ)
              ( hDᵉ)
              ( inv-htpyᵉ front-rightᵉ)
              ( g'ᵉ))
            ( distributive-precomp-left-whisker-comp-coherence-square-mapsᵉ Wᵉ hAᵉ
              ( g'ᵉ)
              ( gᵉ)
              ( hCᵉ)
              ( inv-htpyᵉ back-rightᵉ)
              ( kᵉ)))
    where
    precomp-topᵉ :
      coherence-square-mapsᵉ
        ( precompᵉ k'ᵉ Wᵉ)
        ( precompᵉ h'ᵉ Wᵉ)
        ( precompᵉ g'ᵉ Wᵉ)
        ( precompᵉ f'ᵉ Wᵉ)
    precomp-topᵉ = precomp-coherence-square-mapsᵉ g'ᵉ f'ᵉ k'ᵉ h'ᵉ topᵉ Wᵉ
    precomp-back-left-invᵉ :
      coherence-square-mapsᵉ
        ( precompᵉ fᵉ Wᵉ)
        ( precompᵉ hBᵉ Wᵉ)
        ( precompᵉ hAᵉ Wᵉ)
        ( precompᵉ f'ᵉ Wᵉ)
    precomp-back-left-invᵉ =
      precomp-coherence-square-mapsᵉ hAᵉ f'ᵉ fᵉ hBᵉ (inv-htpyᵉ back-leftᵉ) Wᵉ
    precomp-back-right-invᵉ :
      coherence-square-mapsᵉ
        ( precompᵉ gᵉ Wᵉ)
        ( precompᵉ hCᵉ Wᵉ)
        ( precompᵉ hAᵉ Wᵉ)
        ( precompᵉ g'ᵉ Wᵉ)
    precomp-back-right-invᵉ =
      precomp-coherence-square-mapsᵉ hAᵉ g'ᵉ gᵉ hCᵉ (inv-htpyᵉ back-rightᵉ) Wᵉ
    precomp-front-left-invᵉ :
      coherence-square-mapsᵉ
        ( precompᵉ hᵉ Wᵉ)
        ( precompᵉ hDᵉ Wᵉ)
        ( precompᵉ hBᵉ Wᵉ)
        ( precompᵉ h'ᵉ Wᵉ)
    precomp-front-left-invᵉ =
      precomp-coherence-square-mapsᵉ hBᵉ h'ᵉ hᵉ hDᵉ (inv-htpyᵉ front-leftᵉ) Wᵉ
    precomp-front-right-invᵉ :
      coherence-square-mapsᵉ
        ( precompᵉ kᵉ Wᵉ)
        ( precompᵉ hDᵉ Wᵉ)
        ( precompᵉ hCᵉ Wᵉ)
        ( precompᵉ k'ᵉ Wᵉ)
    precomp-front-right-invᵉ =
      precomp-coherence-square-mapsᵉ hCᵉ k'ᵉ kᵉ hDᵉ (inv-htpyᵉ front-rightᵉ) Wᵉ
    precomp-bottomᵉ :
      coherence-square-mapsᵉ
        ( precompᵉ kᵉ Wᵉ)
        ( precompᵉ hᵉ Wᵉ)
        ( precompᵉ gᵉ Wᵉ)
        ( precompᵉ fᵉ Wᵉ)
    precomp-bottomᵉ = precomp-coherence-square-mapsᵉ gᵉ fᵉ kᵉ hᵉ bottomᵉ Wᵉ
    precomp-front-left-inv-whisker-f'ᵉ :
      coherence-square-mapsᵉ
        ( precompᵉ hᵉ Wᵉ)
        ( precompᵉ hDᵉ Wᵉ)
        ( precompᵉ f'ᵉ Wᵉ ∘ᵉ precompᵉ hBᵉ Wᵉ)
        ( precompᵉ f'ᵉ Wᵉ ∘ᵉ precompᵉ h'ᵉ Wᵉ)
    precomp-front-left-inv-whisker-f'ᵉ =
      precomp-coherence-square-mapsᵉ
        ( hBᵉ ∘ᵉ f'ᵉ)
        ( h'ᵉ ∘ᵉ f'ᵉ)
        ( hᵉ)
        ( hDᵉ)
        ( inv-htpyᵉ front-leftᵉ ·rᵉ f'ᵉ)
        ( Wᵉ)
    precomp-h-whisker-back-left-invᵉ :
      coherence-square-mapsᵉ
        ( precompᵉ fᵉ Wᵉ ∘ᵉ precompᵉ hᵉ Wᵉ)
        ( precompᵉ hBᵉ Wᵉ ∘ᵉ precompᵉ hᵉ Wᵉ)
        ( precompᵉ hAᵉ Wᵉ)
        ( precompᵉ f'ᵉ Wᵉ)
    precomp-h-whisker-back-left-invᵉ =
      precomp-coherence-square-mapsᵉ hAᵉ f'ᵉ
        ( hᵉ ∘ᵉ fᵉ)
        ( hᵉ ∘ᵉ hBᵉ)
        ( hᵉ ·lᵉ inv-htpyᵉ back-leftᵉ)
        ( Wᵉ)
    precomp-bottom-whisker-hAᵉ :
      coherence-square-mapsᵉ
        ( precompᵉ kᵉ Wᵉ)
        ( precompᵉ hᵉ Wᵉ)
        ( precompᵉ hAᵉ Wᵉ ∘ᵉ precompᵉ gᵉ Wᵉ)
        ( precompᵉ hAᵉ Wᵉ ∘ᵉ precompᵉ fᵉ Wᵉ)
    precomp-bottom-whisker-hAᵉ =
      precomp-coherence-square-mapsᵉ
        ( gᵉ ∘ᵉ hAᵉ)
        ( fᵉ ∘ᵉ hAᵉ)
        ( kᵉ)
        ( hᵉ)
        ( bottomᵉ ·rᵉ hAᵉ)
        ( Wᵉ)
    precomp-hD-whisker-topᵉ :
      coherence-square-mapsᵉ
        ( precompᵉ k'ᵉ Wᵉ ∘ᵉ precompᵉ hDᵉ Wᵉ)
        ( precompᵉ h'ᵉ Wᵉ ∘ᵉ precompᵉ hDᵉ Wᵉ)
        ( precompᵉ g'ᵉ Wᵉ)
        ( precompᵉ f'ᵉ Wᵉ)
    precomp-hD-whisker-topᵉ =
      precomp-coherence-square-mapsᵉ g'ᵉ f'ᵉ
        ( hDᵉ ∘ᵉ k'ᵉ)
        ( hDᵉ ∘ᵉ h'ᵉ)
        ( hDᵉ ·lᵉ topᵉ)
        ( Wᵉ)
    precomp-front-right-inv-whisker-g'ᵉ :
      coherence-square-mapsᵉ
        ( precompᵉ kᵉ Wᵉ)
        ( precompᵉ hDᵉ Wᵉ)
        ( precompᵉ g'ᵉ Wᵉ ∘ᵉ precompᵉ hCᵉ Wᵉ)
        ( precompᵉ g'ᵉ Wᵉ ∘ᵉ precompᵉ k'ᵉ Wᵉ)
    precomp-front-right-inv-whisker-g'ᵉ =
      precomp-coherence-square-mapsᵉ
        ( hCᵉ ∘ᵉ g'ᵉ)
        ( k'ᵉ ∘ᵉ g'ᵉ)
        ( kᵉ)
        ( hDᵉ)
        ( inv-htpyᵉ front-rightᵉ ·rᵉ g'ᵉ)
        ( Wᵉ)
    precomp-k-whisker-back-right-invᵉ :
      coherence-square-mapsᵉ
        ( precompᵉ gᵉ Wᵉ ∘ᵉ precompᵉ kᵉ Wᵉ)
        ( precompᵉ hCᵉ Wᵉ ∘ᵉ precompᵉ kᵉ Wᵉ)
        ( precompᵉ hAᵉ Wᵉ)
        ( precompᵉ g'ᵉ Wᵉ)
    precomp-k-whisker-back-right-invᵉ =
      precomp-coherence-square-mapsᵉ hAᵉ g'ᵉ
        ( kᵉ ∘ᵉ gᵉ)
        ( kᵉ ∘ᵉ hCᵉ)
        ( kᵉ ·lᵉ inv-htpyᵉ back-rightᵉ)
        ( Wᵉ)
```