# Commuting prisms of maps

```agda
module foundation-core.commuting-prisms-of-mapsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.commuting-pentagons-of-identificationsᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ
open import foundation.whiskering-identifications-concatenationᵉ

open import foundation-core.commuting-squares-of-mapsᵉ
open import foundation-core.commuting-triangles-of-mapsᵉ
open import foundation-core.homotopiesᵉ
```

</details>

## Idea

Considerᵉ anᵉ arrangmentᵉ ofᵉ mapsᵉ composableᵉ intoᵉ aᵉ diagramᵉ asᵉ followsᵉ:

```text
          hAᵉ
    Aᵉ --------->ᵉ A'ᵉ
    |\ᵉ           |\ᵉ
    | \ᵉ hᵉ   ⇗ᵉ    | \ᵉ h'ᵉ
    |  \ᵉ      f'ᵉ |  \ᵉ
    |   ∨ᵉ        |   ∨ᵉ
  fᵉ | ⇐ᵉ Bᵉ ------ᵉ | ->ᵉ B'ᵉ
    |   /ᵉ   hBᵉ   | ⇐ᵉ /ᵉ
    |  /ᵉ gᵉ       |  /ᵉ g'ᵉ
    | /ᵉ     ⇗ᵉ    | /ᵉ
    ∨∨ᵉ           ∨∨ᵉ
    Cᵉ --------->ᵉ C'ᵉ ,ᵉ
          hCᵉ
```

andᵉ [homotopies](foundation-core.homotopies.mdᵉ) fillingᵉ itsᵉ faces.ᵉ Thenᵉ aᵉ
{{#conceptᵉ "horizontalᵉ commutingᵉ prismᵉ ofᵉ maps"ᵉ Agda=horizontal-coherence-prism-mapsᵉ}}
isᵉ aᵉ homotopyᵉ fillingᵉ theᵉ shape.ᵉ Inᵉ otherᵉ words,ᵉ weᵉ mayᵉ chooseᵉ twoᵉ homotopiesᵉ
fromᵉ theᵉ compositionᵉ `hCᵉ ∘ᵉ gᵉ ∘ᵉ h`ᵉ to `f'ᵉ ∘ᵉ hA`,ᵉ namelyᵉ followingᵉ 1ᵉ) theᵉ leftᵉ
[triangle](foundation-core.commuting-triangles-of-maps.mdᵉ) andᵉ thenᵉ theᵉ frontᵉ
[square](foundation-core.commuting-squares-of-maps.md),ᵉ orᵉ 2ᵉ) theᵉ twoᵉ backᵉ
squaresᵉ andᵉ thenᵉ theᵉ rightᵉ triangle;ᵉ theᵉ prismᵉ isᵉ thenᵉ aᵉ homotopyᵉ betweenᵉ theseᵉ
twoᵉ homotopies.ᵉ Inᵉ thisᵉ way,ᵉ aᵉ commutingᵉ prismᵉ mayᵉ beᵉ viewedᵉ asᵉ aᵉ homotopyᵉ
betweenᵉ aᵉ pastingᵉ ofᵉ squaresᵉ andᵉ theirᵉ compositeᵉ —ᵉ thatᵉ isᵉ theᵉ motivationᵉ forᵉ
havingᵉ theᵉ trianglesᵉ goᵉ theᵉ unconventionalᵉ way,ᵉ fromᵉ theᵉ compositionᵉ to theᵉ
composite.ᵉ

Weᵉ mayᵉ alsoᵉ arrangeᵉ theᵉ mapsᵉ intoᵉ aᵉ moreᵉ verticalᵉ shape,ᵉ likeᵉ soᵉ:

```text
          Bᵉ
      hᵉ  ∧|ᵉ \ᵉ  gᵉ
       /ᵉ  |   \ᵉ
     /ᵉ  fᵉ | ⇑ᵉ   ∨ᵉ
    Aᵉ --------->ᵉ Cᵉ
    |     | hBᵉ   |
    | ⇗ᵉ   ∨ᵉ   ⇗ᵉ  |
 hAᵉ |     B'ᵉ     | hCᵉ
    | h'ᵉ ∧ᵉ  \ᵉ g'ᵉ |
    |  /ᵉ  ⇑ᵉ   \ᵉ  |
    ∨/ᵉ          ∨∨ᵉ
    A'ᵉ -------->ᵉ C'ᵉ .ᵉ
          f'ᵉ
```

Then,ᵉ givenᵉ homotopiesᵉ forᵉ theᵉ faces,ᵉ weᵉ callᵉ aᵉ homotopyᵉ fillingᵉ thisᵉ shapeᵉ aᵉ
{{#conceptᵉ "verticalᵉ commutingᵉ prismᵉ ofᵉ maps"ᵉ Agda=vertical-coherence-prism-mapsᵉ Agda=vertical-coherence-prism-maps'}}.ᵉ
Thisᵉ rotationᵉ ofᵉ aᵉ prismᵉ mayᵉ beᵉ viewedᵉ asᵉ aᵉ homotopyᵉ betweenᵉ twoᵉ trianglesᵉ with
differentᵉ butᵉ relatedᵉ sides.ᵉ

Itᵉ remainsᵉ to beᵉ formalizedᵉ thatᵉ theᵉ typeᵉ ofᵉ verticalᵉ prismsᵉ isᵉ
[equivalent](foundation-core.equivalences.mdᵉ) to theᵉ typeᵉ ofᵉ horizontalᵉ prisms.ᵉ

## Definitions

### Horizontal commuting prisms of maps

```agda
module _
  { l1ᵉ l2ᵉ l3ᵉ l1'ᵉ l2'ᵉ l3'ᵉ : Level}
  { Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ}
  { A'ᵉ : UUᵉ l1'ᵉ} {B'ᵉ : UUᵉ l2'ᵉ} {C'ᵉ : UUᵉ l3'ᵉ}
  ( hAᵉ : Aᵉ → A'ᵉ) (hᵉ : Aᵉ → Bᵉ) (h'ᵉ : A'ᵉ → B'ᵉ)
  ( hBᵉ : Bᵉ → B'ᵉ) (gᵉ : Bᵉ → Cᵉ) (g'ᵉ : B'ᵉ → C'ᵉ)
  ( hCᵉ : Cᵉ → C'ᵉ) (fᵉ : Aᵉ → Cᵉ) (f'ᵉ : A'ᵉ → C'ᵉ)
  ( leftᵉ : coherence-triangle-maps'ᵉ fᵉ gᵉ hᵉ)
  ( sq-topᵉ : coherence-square-mapsᵉ hAᵉ hᵉ h'ᵉ hBᵉ)
  ( sq-bottomᵉ : coherence-square-mapsᵉ hBᵉ gᵉ g'ᵉ hCᵉ)
  ( sq-frontᵉ : coherence-square-mapsᵉ hAᵉ fᵉ f'ᵉ hCᵉ)
  ( rightᵉ : coherence-triangle-maps'ᵉ f'ᵉ g'ᵉ h'ᵉ)
  where

  horizontal-coherence-prism-mapsᵉ : UUᵉ (l1ᵉ ⊔ l3'ᵉ)
  horizontal-coherence-prism-mapsᵉ =
    ( ( hCᵉ ·lᵉ leftᵉ) ∙hᵉ sq-frontᵉ) ~ᵉ
    ( ( pasting-vertical-coherence-square-mapsᵉ hAᵉ hᵉ h'ᵉ hBᵉ gᵉ g'ᵉ hCᵉ
        ( sq-topᵉ)
        ( sq-bottomᵉ)) ∙hᵉ
      ( rightᵉ ·rᵉ hAᵉ))
```

### Vertical commuting prisms of maps

Becauseᵉ triangularᵉ prismsᵉ areᵉ lessᵉ symmetricᵉ than,ᵉ say,ᵉ cubes,ᵉ weᵉ haveᵉ moreᵉ thanᵉ
oneᵉ naturalᵉ formulationᵉ forᵉ where to drawᵉ theᵉ "seams"ᵉ forᵉ theᵉ filler.ᵉ Here,ᵉ weᵉ
presentᵉ twoᵉ choices,ᵉ andᵉ showᵉ thatᵉ theyᵉ areᵉ equivalentᵉ in
[`foundation.commuting-prisms-of-maps`](foundation.commuting-prisms-of-maps.md).ᵉ

```agda
module _
  { l1ᵉ l2ᵉ l3ᵉ l1'ᵉ l2'ᵉ l3'ᵉ : Level}
  { Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ}
  ( fᵉ : Aᵉ → Cᵉ) (gᵉ : Bᵉ → Cᵉ) (hᵉ : Aᵉ → Bᵉ)
  { A'ᵉ : UUᵉ l1'ᵉ} {B'ᵉ : UUᵉ l2'ᵉ} {C'ᵉ : UUᵉ l3'ᵉ}
  ( f'ᵉ : A'ᵉ → C'ᵉ) (g'ᵉ : B'ᵉ → C'ᵉ) (h'ᵉ : A'ᵉ → B'ᵉ)
  ( hAᵉ : Aᵉ → A'ᵉ) (hBᵉ : Bᵉ → B'ᵉ) (hCᵉ : Cᵉ → C'ᵉ)
  where

  module _
    ( topᵉ : coherence-triangle-mapsᵉ fᵉ gᵉ hᵉ)
    ( frontᵉ : coherence-square-mapsᵉ fᵉ hAᵉ hCᵉ f'ᵉ)
    ( rightᵉ : coherence-square-mapsᵉ gᵉ hBᵉ hCᵉ g'ᵉ)
    ( leftᵉ : coherence-square-mapsᵉ hᵉ hAᵉ hBᵉ h'ᵉ)
    ( bottomᵉ : coherence-triangle-mapsᵉ f'ᵉ g'ᵉ h'ᵉ)
    where

    vertical-coherence-prism-mapsᵉ : UUᵉ (l1ᵉ ⊔ l3'ᵉ)
    vertical-coherence-prism-mapsᵉ =
      ( ( bottomᵉ ·rᵉ hAᵉ) ∙hᵉ
        ( pasting-horizontal-coherence-square-mapsᵉ hᵉ gᵉ hAᵉ hBᵉ hCᵉ h'ᵉ g'ᵉ
          ( leftᵉ)
          ( rightᵉ))) ~ᵉ
      ( frontᵉ ∙hᵉ (hCᵉ ·lᵉ topᵉ))

  module _
    ( topᵉ : coherence-triangle-mapsᵉ fᵉ gᵉ hᵉ)
    ( inv-frontᵉ : coherence-square-maps'ᵉ fᵉ hAᵉ hCᵉ f'ᵉ)
    ( inv-rightᵉ : coherence-square-maps'ᵉ gᵉ hBᵉ hCᵉ g'ᵉ)
    ( leftᵉ : coherence-square-mapsᵉ hᵉ hAᵉ hBᵉ h'ᵉ)
    ( bottomᵉ : coherence-triangle-mapsᵉ f'ᵉ g'ᵉ h'ᵉ)
    where

    vertical-coherence-prism-maps'ᵉ : UUᵉ (l1ᵉ ⊔ l3'ᵉ)
    vertical-coherence-prism-maps'ᵉ =
      ( inv-frontᵉ ∙hᵉ ((bottomᵉ ·rᵉ hAᵉ) ∙hᵉ (g'ᵉ ·lᵉ leftᵉ))) ~ᵉ
      ( (hCᵉ ·lᵉ topᵉ) ∙hᵉ (inv-rightᵉ ·rᵉ hᵉ))

  module _
    ( topᵉ : coherence-triangle-mapsᵉ fᵉ gᵉ hᵉ)
    ( inv-frontᵉ : coherence-square-maps'ᵉ fᵉ hAᵉ hCᵉ f'ᵉ)
    ( inv-rightᵉ : coherence-square-maps'ᵉ gᵉ hBᵉ hCᵉ g'ᵉ)
    ( inv-leftᵉ : coherence-square-maps'ᵉ hᵉ hAᵉ hBᵉ h'ᵉ)
    ( bottomᵉ : coherence-triangle-mapsᵉ f'ᵉ g'ᵉ h'ᵉ)
    where

    vertical-coherence-prism-inv-squares-mapsᵉ : UUᵉ (l1ᵉ ⊔ l3'ᵉ)
    vertical-coherence-prism-inv-squares-mapsᵉ =
      ( inv-frontᵉ ∙hᵉ (bottomᵉ ·rᵉ hAᵉ)) ~ᵉ
      ( (hCᵉ ·lᵉ topᵉ) ∙hᵉ ((inv-rightᵉ ·rᵉ hᵉ) ∙hᵉ (g'ᵉ ·lᵉ inv-leftᵉ)))

  module _
    ( inv-topᵉ : coherence-triangle-maps'ᵉ fᵉ gᵉ hᵉ)
    ( frontᵉ : coherence-square-mapsᵉ fᵉ hAᵉ hCᵉ f'ᵉ)
    ( rightᵉ : coherence-square-mapsᵉ gᵉ hBᵉ hCᵉ g'ᵉ)
    ( leftᵉ : coherence-square-mapsᵉ hᵉ hAᵉ hBᵉ h'ᵉ)
    ( inv-bottomᵉ : coherence-triangle-maps'ᵉ f'ᵉ g'ᵉ h'ᵉ)
    where

    vertical-coherence-prism-inv-triangles-mapsᵉ : UUᵉ (l1ᵉ ⊔ l3'ᵉ)
    vertical-coherence-prism-inv-triangles-mapsᵉ =
      ( (g'ᵉ ·lᵉ leftᵉ) ∙hᵉ (rightᵉ ·rᵉ hᵉ) ∙hᵉ (hCᵉ ·lᵉ inv-topᵉ)) ~ᵉ
      ( (inv-bottomᵉ ·rᵉ hAᵉ) ∙hᵉ frontᵉ)

  module _
    ( inv-topᵉ : coherence-triangle-maps'ᵉ fᵉ gᵉ hᵉ)
    ( inv-frontᵉ : coherence-square-maps'ᵉ fᵉ hAᵉ hCᵉ f'ᵉ)
    ( inv-rightᵉ : coherence-square-maps'ᵉ gᵉ hBᵉ hCᵉ g'ᵉ)
    ( inv-leftᵉ : coherence-square-maps'ᵉ hᵉ hAᵉ hBᵉ h'ᵉ)
    ( inv-bottomᵉ : coherence-triangle-maps'ᵉ f'ᵉ g'ᵉ h'ᵉ)
    where

    vertical-coherence-prism-inv-boundary-mapsᵉ : UUᵉ (l1ᵉ ⊔ l3'ᵉ)
    vertical-coherence-prism-inv-boundary-mapsᵉ =
      ( (inv-rightᵉ ·rᵉ hᵉ) ∙hᵉ (g'ᵉ ·lᵉ inv-leftᵉ) ∙hᵉ (inv-bottomᵉ ·rᵉ hAᵉ)) ~ᵉ
      ( (hCᵉ ·lᵉ inv-topᵉ) ∙hᵉ inv-frontᵉ)
```

## Translations between coherences of prisms of maps

Ourᵉ differentᵉ formulationsᵉ ofᵉ commutingᵉ prismsᵉ ofᵉ mapsᵉ areᵉ ofᵉ courseᵉ allᵉ
equivalent,ᵉ althoughᵉ thisᵉ remainsᵉ to beᵉ formalized.ᵉ Below,ᵉ weᵉ record variousᵉ
translationsᵉ betweenᵉ them.ᵉ

```agda
module _
  { l1ᵉ l2ᵉ l3ᵉ l1'ᵉ l2'ᵉ l3'ᵉ : Level}
  { Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ}
  ( fᵉ : Aᵉ → Cᵉ) (gᵉ : Bᵉ → Cᵉ) (hᵉ : Aᵉ → Bᵉ)
  { A'ᵉ : UUᵉ l1'ᵉ} {B'ᵉ : UUᵉ l2'ᵉ} {C'ᵉ : UUᵉ l3'ᵉ}
  ( f'ᵉ : A'ᵉ → C'ᵉ) (g'ᵉ : B'ᵉ → C'ᵉ) (h'ᵉ : A'ᵉ → B'ᵉ)
  ( hAᵉ : Aᵉ → A'ᵉ) (hBᵉ : Bᵉ → B'ᵉ) (hCᵉ : Cᵉ → C'ᵉ)
  where

  module _
    ( topᵉ : coherence-triangle-mapsᵉ fᵉ gᵉ hᵉ)
    ( inv-frontᵉ : coherence-square-maps'ᵉ fᵉ hAᵉ hCᵉ f'ᵉ)
    ( inv-rightᵉ : coherence-square-maps'ᵉ gᵉ hBᵉ hCᵉ g'ᵉ)
    ( inv-leftᵉ : coherence-square-maps'ᵉ hᵉ hAᵉ hBᵉ h'ᵉ)
    ( bottomᵉ : coherence-triangle-mapsᵉ f'ᵉ g'ᵉ h'ᵉ)
    where

    vertical-coherence-prism-maps-vertical-coherence-prism-inv-squares-mapsᵉ :
      vertical-coherence-prism-inv-squares-mapsᵉ fᵉ gᵉ hᵉ f'ᵉ g'ᵉ h'ᵉ hAᵉ hBᵉ hCᵉ
        ( topᵉ)
        ( inv-frontᵉ)
        ( inv-rightᵉ)
        ( inv-leftᵉ)
        ( bottomᵉ) →
      vertical-coherence-prism-mapsᵉ fᵉ gᵉ hᵉ f'ᵉ g'ᵉ h'ᵉ hAᵉ hBᵉ hCᵉ
        ( topᵉ)
        ( inv-htpyᵉ inv-frontᵉ)
        ( inv-htpyᵉ inv-rightᵉ)
        ( inv-htpyᵉ inv-leftᵉ)
        ( bottomᵉ)
    vertical-coherence-prism-maps-vertical-coherence-prism-inv-squares-mapsᵉ Hᵉ =
      ( ap-concat-htpyᵉ
        ( bottomᵉ ·rᵉ hAᵉ)
        ( ( ap-concat-htpy'ᵉ
            ( inv-htpyᵉ inv-rightᵉ ·rᵉ hᵉ)
            ( left-whisker-inv-htpyᵉ g'ᵉ inv-leftᵉ)) ∙hᵉ
          ( inv-htpy-distributive-inv-concat-htpyᵉ
            ( inv-rightᵉ ·rᵉ hᵉ)
            ( g'ᵉ ·lᵉ inv-leftᵉ)))) ∙hᵉ
      ( inv-htpy-right-transpose-htpy-concatᵉ
        ( inv-htpyᵉ inv-frontᵉ ∙hᵉ (hCᵉ ·lᵉ topᵉ))
        ( inv-rightᵉ ·rᵉ hᵉ ∙hᵉ (g'ᵉ ·lᵉ inv-leftᵉ))
        ( bottomᵉ ·rᵉ hAᵉ)
        ( ( assoc-htpyᵉ
            ( inv-htpyᵉ inv-frontᵉ)
            ( hCᵉ ·lᵉ topᵉ)
            ( inv-rightᵉ ·rᵉ hᵉ ∙hᵉ (g'ᵉ ·lᵉ inv-leftᵉ))) ∙hᵉ
          ( inv-htpy-left-transpose-htpy-concatᵉ
            ( inv-frontᵉ)
            ( bottomᵉ ·rᵉ hAᵉ)
            ( (hCᵉ ·lᵉ topᵉ) ∙hᵉ (inv-rightᵉ ·rᵉ hᵉ ∙hᵉ (g'ᵉ ·lᵉ inv-leftᵉ)))
            ( Hᵉ))))

  module _
    ( topᵉ : coherence-triangle-mapsᵉ fᵉ gᵉ hᵉ)
    ( inv-frontᵉ : coherence-square-mapsᵉ fᵉ hAᵉ hCᵉ f'ᵉ)
    ( inv-rightᵉ : coherence-square-mapsᵉ gᵉ hBᵉ hCᵉ g'ᵉ)
    ( inv-leftᵉ : coherence-square-mapsᵉ hᵉ hAᵉ hBᵉ h'ᵉ)
    ( bottomᵉ : coherence-triangle-mapsᵉ f'ᵉ g'ᵉ h'ᵉ)
    where

    vertical-coherence-prism-inv-squares-maps-vertical-coherence-prism-mapsᵉ :
      vertical-coherence-prism-mapsᵉ fᵉ gᵉ hᵉ f'ᵉ g'ᵉ h'ᵉ hAᵉ hBᵉ hCᵉ
        ( topᵉ)
        ( inv-frontᵉ)
        ( inv-rightᵉ)
        ( inv-leftᵉ)
        ( bottomᵉ) →
      vertical-coherence-prism-inv-squares-mapsᵉ fᵉ gᵉ hᵉ f'ᵉ g'ᵉ h'ᵉ hAᵉ hBᵉ hCᵉ
        ( topᵉ)
        ( inv-htpyᵉ inv-frontᵉ)
        ( inv-htpyᵉ inv-rightᵉ)
        ( inv-htpyᵉ inv-leftᵉ)
        ( bottomᵉ)
    vertical-coherence-prism-inv-squares-maps-vertical-coherence-prism-mapsᵉ
      Hᵉ aᵉ =
      ( reflect-top-left-coherence-pentagon-identificationsᵉ
        ( bottomᵉ (hAᵉ aᵉ))
        ( inv-frontᵉ aᵉ)
        ( apᵉ g'ᵉ (inv-leftᵉ aᵉ))
        ( apᵉ hCᵉ (topᵉ aᵉ))
        ( inv-rightᵉ (hᵉ aᵉ))
        ( invᵉ
          ( ( assocᵉ (bottomᵉ (hAᵉ aᵉ)) (apᵉ g'ᵉ (inv-leftᵉ aᵉ)) (inv-rightᵉ (hᵉ aᵉ))) ∙ᵉ
            ( Hᵉ aᵉ)))) ∙ᵉ
      ( left-whisker-concatᵉ
        ( apᵉ hCᵉ (topᵉ aᵉ) ∙ᵉ invᵉ (inv-rightᵉ (hᵉ aᵉ)))
        ( invᵉ (ap-invᵉ g'ᵉ (inv-leftᵉ aᵉ)))) ∙ᵉ
      ( assocᵉ
        ( apᵉ hCᵉ (topᵉ aᵉ))
        ( invᵉ (inv-rightᵉ (hᵉ aᵉ)))
        ( apᵉ g'ᵉ (invᵉ (inv-leftᵉ aᵉ))))

  module _
    ( inv-topᵉ : coherence-triangle-maps'ᵉ fᵉ gᵉ hᵉ)
    ( inv-frontᵉ : coherence-square-maps'ᵉ fᵉ hAᵉ hCᵉ f'ᵉ)
    ( inv-rightᵉ : coherence-square-maps'ᵉ gᵉ hBᵉ hCᵉ g'ᵉ)
    ( inv-leftᵉ : coherence-square-maps'ᵉ hᵉ hAᵉ hBᵉ h'ᵉ)
    ( inv-bottomᵉ : coherence-triangle-maps'ᵉ f'ᵉ g'ᵉ h'ᵉ)
    where

    vertical-coherence-prism-inv-triangles-maps-vertical-coherence-prism-inv-boundary-mapsᵉ :
      vertical-coherence-prism-inv-boundary-mapsᵉ fᵉ gᵉ hᵉ f'ᵉ g'ᵉ h'ᵉ hAᵉ hBᵉ hCᵉ
        ( inv-topᵉ)
        ( inv-frontᵉ)
        ( inv-rightᵉ)
        ( inv-leftᵉ)
        ( inv-bottomᵉ) →
      vertical-coherence-prism-inv-triangles-mapsᵉ fᵉ gᵉ hᵉ f'ᵉ g'ᵉ h'ᵉ hAᵉ hBᵉ hCᵉ
        ( inv-topᵉ)
        ( inv-htpyᵉ inv-frontᵉ)
        ( inv-htpyᵉ inv-rightᵉ)
        ( inv-htpyᵉ inv-leftᵉ)
        ( inv-bottomᵉ)
    vertical-coherence-prism-inv-triangles-maps-vertical-coherence-prism-inv-boundary-mapsᵉ
      Hᵉ =
      ( ap-concat-htpy'ᵉ
        ( hCᵉ ·lᵉ inv-topᵉ)
        ( ( ap-concat-htpy'ᵉ
            ( inv-htpyᵉ inv-rightᵉ ·rᵉ hᵉ)
            ( left-whisker-inv-htpyᵉ g'ᵉ inv-leftᵉ)) ∙hᵉ
          ( inv-htpy-distributive-inv-concat-htpyᵉ
            ( inv-rightᵉ ·rᵉ hᵉ)
            ( g'ᵉ ·lᵉ inv-leftᵉ)))) ∙hᵉ
      ( right-transpose-htpy-concatᵉ
        ( ( inv-htpyᵉ (inv-rightᵉ ·rᵉ hᵉ ∙hᵉ (g'ᵉ ·lᵉ inv-leftᵉ))) ∙hᵉ (hCᵉ ·lᵉ inv-topᵉ))
        ( inv-frontᵉ)
        ( inv-bottomᵉ ·rᵉ hAᵉ)
        ( ( assoc-htpyᵉ
            ( inv-htpyᵉ (inv-rightᵉ ·rᵉ hᵉ ∙hᵉ (g'ᵉ ·lᵉ inv-leftᵉ)))
            ( hCᵉ ·lᵉ inv-topᵉ)
            ( inv-frontᵉ)) ∙hᵉ
          ( inv-htpy-left-transpose-htpy-concatᵉ
            ( inv-rightᵉ ·rᵉ hᵉ ∙hᵉ (g'ᵉ ·lᵉ inv-leftᵉ))
            ( inv-bottomᵉ ·rᵉ hAᵉ)
            ( (hCᵉ ·lᵉ inv-topᵉ) ∙hᵉ inv-frontᵉ)
            ( Hᵉ))))
```