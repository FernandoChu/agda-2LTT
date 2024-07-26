# Commuting squares of maps

```agda
module foundation.commuting-squares-of-mapsᵉ where

open import foundation-core.commuting-squares-of-mapsᵉ public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functionsᵉ
open import foundation.action-on-identifications-functionsᵉ
open import foundation.commuting-triangles-of-homotopiesᵉ
open import foundation.commuting-triangles-of-mapsᵉ
open import foundation.function-extensionalityᵉ
open import foundation.homotopy-algebraᵉ
open import foundation.postcomposition-functionsᵉ
open import foundation.precomposition-functionsᵉ
open import foundation.transposition-identifications-along-equivalencesᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-higher-homotopies-compositionᵉ
open import foundation.whiskering-homotopies-compositionᵉ

open import foundation-core.commuting-prisms-of-mapsᵉ
open import foundation-core.commuting-squares-of-homotopiesᵉ
open import foundation-core.commuting-squares-of-identificationsᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.whiskering-identifications-concatenationᵉ
```

</details>

## Definitions

### Commuting squares of maps induce commuting squares of precomposition maps

Everyᵉ commutingᵉ squareᵉ

```text
            topᵉ
       Aᵉ -------->ᵉ Xᵉ
       |           |
  leftᵉ |           | rightᵉ
       ∨ᵉ           ∨ᵉ
       Bᵉ -------->ᵉ Yᵉ
          bottomᵉ
```

inducesᵉ aᵉ commutingᵉ squareᵉ ofᵉ
[precompositionᵉ functions](foundation-core.precomposition-functions.mdᵉ)

```text
                         precompᵉ rightᵉ Sᵉ
                (Aᵉ → Sᵉ) ----------------->ᵉ (Xᵉ → Sᵉ)
                   |                           |
  precompᵉ bottomᵉ Sᵉ |                           | precompᵉ topᵉ Sᵉ
                   ∨ᵉ                           ∨ᵉ
                (Bᵉ → Sᵉ) ------------------>ᵉ (Yᵉ → S).ᵉ
                          precompᵉ leftᵉ Sᵉ
```

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (topᵉ : Aᵉ → Xᵉ) (leftᵉ : Aᵉ → Bᵉ) (rightᵉ : Xᵉ → Yᵉ) (bottomᵉ : Bᵉ → Yᵉ)
  where

  precomp-coherence-square-mapsᵉ :
    coherence-square-mapsᵉ topᵉ leftᵉ rightᵉ bottomᵉ →
    (Sᵉ : UUᵉ l5ᵉ) →
    coherence-square-mapsᵉ
      ( precompᵉ rightᵉ Sᵉ)
      ( precompᵉ bottomᵉ Sᵉ)
      ( precompᵉ topᵉ Sᵉ)
      ( precompᵉ leftᵉ Sᵉ)
  precomp-coherence-square-mapsᵉ = htpy-precompᵉ

  precomp-coherence-square-maps'ᵉ :
    coherence-square-maps'ᵉ topᵉ leftᵉ rightᵉ bottomᵉ →
    (Sᵉ : UUᵉ l5ᵉ) →
    coherence-square-maps'ᵉ
      ( precompᵉ rightᵉ Sᵉ)
      ( precompᵉ bottomᵉ Sᵉ)
      ( precompᵉ topᵉ Sᵉ)
      ( precompᵉ leftᵉ Sᵉ)
  precomp-coherence-square-maps'ᵉ = htpy-precompᵉ
```

### Commuting squares of maps induce commuting squares of postcomposition maps

Everyᵉ commutingᵉ squareᵉ

```text
            topᵉ
       Aᵉ -------->ᵉ Xᵉ
       |           |
  leftᵉ |           | rightᵉ
       ∨ᵉ           ∨ᵉ
       Bᵉ -------->ᵉ Yᵉ
          bottomᵉ
```

inducesᵉ aᵉ commutingᵉ squareᵉ ofᵉ
[postcompositionᵉ functions](foundation-core.postcomposition-functions.mdᵉ)

```text
                        postcompᵉ Sᵉ topᵉ
              (Sᵉ → Aᵉ) ------------------>ᵉ (Sᵉ → Xᵉ)
                 |                           |
 postcompᵉ Sᵉ leftᵉ |                           | postcompᵉ Sᵉ rightᵉ
                 ∨ᵉ                           ∨ᵉ
              (Sᵉ → Bᵉ) ------------------>ᵉ (Sᵉ → Y).ᵉ
                       postcompᵉ Sᵉ bottomᵉ
```

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (topᵉ : Aᵉ → Xᵉ) (leftᵉ : Aᵉ → Bᵉ) (rightᵉ : Xᵉ → Yᵉ) (bottomᵉ : Bᵉ → Yᵉ)
  where

  postcomp-coherence-square-mapsᵉ :
    (Sᵉ : UUᵉ l5ᵉ) →
    coherence-square-mapsᵉ topᵉ leftᵉ rightᵉ bottomᵉ →
    coherence-square-mapsᵉ
      ( postcompᵉ Sᵉ topᵉ)
      ( postcompᵉ Sᵉ leftᵉ)
      ( postcompᵉ Sᵉ rightᵉ)
      ( postcompᵉ Sᵉ bottomᵉ)
  postcomp-coherence-square-mapsᵉ Sᵉ = htpy-postcompᵉ Sᵉ

  postcomp-coherence-square-maps'ᵉ :
    (Sᵉ : UUᵉ l5ᵉ) →
    coherence-square-maps'ᵉ topᵉ leftᵉ rightᵉ bottomᵉ →
    coherence-square-maps'ᵉ
      ( postcompᵉ Sᵉ topᵉ)
      ( postcompᵉ Sᵉ leftᵉ)
      ( postcompᵉ Sᵉ rightᵉ)
      ( postcompᵉ Sᵉ bottomᵉ)
  postcomp-coherence-square-maps'ᵉ Sᵉ = htpy-postcompᵉ Sᵉ
```

## Properties

### Taking vertical inversions of squares is an inverse operation

Verticalᵉ compositionᵉ ofᵉ aᵉ squareᵉ with theᵉ squareᵉ obtainedᵉ byᵉ invertingᵉ theᵉ
verticalᵉ mapsᵉ fitsᵉ intoᵉ aᵉ [prism](foundation.commuting-prisms-of-maps.mdᵉ) with
theᵉ reflexivityᵉ square.ᵉ

Theᵉ analogousᵉ resultᵉ forᵉ horizontalᵉ compositionᵉ remainsᵉ to beᵉ formalized.ᵉ

```agda
module _
  { l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  ( topᵉ : Aᵉ → Xᵉ) (leftᵉ : Aᵉ ≃ᵉ Bᵉ) (rightᵉ : Xᵉ ≃ᵉ Yᵉ) (bottomᵉ : Bᵉ → Yᵉ)
  where

  left-inverse-law-pasting-vertical-coherence-square-mapsᵉ :
    ( Hᵉ : coherence-square-mapsᵉ topᵉ (map-equivᵉ leftᵉ) (map-equivᵉ rightᵉ) bottomᵉ) →
    horizontal-coherence-prism-mapsᵉ
      ( topᵉ)
      ( map-equivᵉ leftᵉ)
      ( map-equivᵉ rightᵉ)
      ( bottomᵉ)
      ( map-inv-equivᵉ leftᵉ)
      ( map-inv-equivᵉ rightᵉ)
      ( topᵉ)
      ( idᵉ)
      ( idᵉ)
      ( is-retraction-map-inv-equivᵉ leftᵉ)
      ( Hᵉ)
      ( vertical-inv-equiv-coherence-square-mapsᵉ topᵉ leftᵉ rightᵉ bottomᵉ Hᵉ)
      ( refl-htpyᵉ)
      ( is-retraction-map-inv-equivᵉ rightᵉ)
  left-inverse-law-pasting-vertical-coherence-square-mapsᵉ Hᵉ aᵉ =
    ( right-unitᵉ) ∙ᵉ
    ( invᵉ
      ( ( apᵉ
          ( λ qᵉ →
            ( qᵉ ∙ᵉ apᵉ (map-inv-equivᵉ rightᵉ) (Hᵉ aᵉ)) ∙ᵉ
            ( is-retraction-map-inv-equivᵉ rightᵉ (topᵉ aᵉ)))
          ( triangle-eq-transpose-equiv-concatᵉ
            ( rightᵉ)
            ( invᵉ (Hᵉ (map-inv-equivᵉ leftᵉ (map-equivᵉ leftᵉ aᵉ))))
            ( apᵉ bottomᵉ (is-section-map-inv-equivᵉ leftᵉ (map-equivᵉ leftᵉ aᵉ))))) ∙ᵉ
        ( assocᵉ
          ( ( map-eq-transpose-equivᵉ
              ( rightᵉ)
              ( invᵉ (Hᵉ (map-inv-equivᵉ leftᵉ (map-equivᵉ leftᵉ aᵉ))))) ∙ᵉ
            ( apᵉ
              ( map-inv-equivᵉ rightᵉ)
              ( apᵉ bottomᵉ (is-section-map-inv-equivᵉ leftᵉ (map-equivᵉ leftᵉ aᵉ)))))
          ( apᵉ (map-inv-equivᵉ rightᵉ) (Hᵉ aᵉ))
          ( is-retraction-map-inv-equivᵉ rightᵉ (topᵉ aᵉ))) ∙ᵉ
        ( left-whisker-concat-coherence-square-identificationsᵉ
          ( map-eq-transpose-equivᵉ
            ( rightᵉ)
            ( invᵉ (Hᵉ (map-inv-equivᵉ leftᵉ (map-equivᵉ leftᵉ aᵉ)))))
          ( _)
          ( _)
          ( _)
          ( _)
          ( invᵉ
            ( vertical-pasting-coherence-square-identificationsᵉ
              ( apᵉ
                ( map-inv-equivᵉ rightᵉ)
                ( apᵉ
                  ( bottomᵉ)
                  ( is-section-map-inv-equivᵉ leftᵉ (map-equivᵉ leftᵉ aᵉ))))
              ( apᵉ
                ( map-inv-equivᵉ rightᵉ)
                ( Hᵉ (map-inv-equivᵉ leftᵉ (map-equivᵉ leftᵉ aᵉ))))
              ( apᵉ (map-inv-equivᵉ rightᵉ) (Hᵉ aᵉ))
              ( apᵉ
                ( map-inv-equivᵉ rightᵉ)
                ( apᵉ
                  ( map-equivᵉ rightᵉ ∘ᵉ topᵉ)
                  ( is-retraction-map-inv-equivᵉ leftᵉ aᵉ)))
              ( is-retraction-map-inv-equivᵉ rightᵉ
                ( topᵉ (map-inv-equivᵉ leftᵉ (map-equivᵉ leftᵉ aᵉ))))
              ( is-retraction-map-inv-equivᵉ rightᵉ (topᵉ aᵉ))
              ( apᵉ topᵉ (is-retraction-map-inv-equivᵉ leftᵉ aᵉ))
              ( concat-top-identification-coherence-square-identificationsᵉ
                ( _)
                ( apᵉ
                  ( map-inv-equivᵉ rightᵉ)
                  ( Hᵉ (map-inv-equivᵉ leftᵉ (map-equivᵉ leftᵉ aᵉ))))
                ( _)
                ( _)
                ( invᵉ
                  ( apᵉ
                    ( apᵉ (map-inv-equivᵉ rightᵉ))
                    ( ( left-whisker-comp²ᵉ
                        ( bottomᵉ)
                        ( coherence-map-inv-equivᵉ leftᵉ)
                        ( aᵉ)) ∙ᵉ
                      ( invᵉ
                        ( ap-compᵉ
                          ( bottomᵉ)
                          ( map-equivᵉ leftᵉ)
                          ( is-retraction-map-inv-equivᵉ leftᵉ aᵉ))))))
                ( map-coherence-square-identificationsᵉ
                  ( map-inv-equivᵉ rightᵉ)
                  ( apᵉ
                    ( bottomᵉ ∘ᵉ map-equivᵉ leftᵉ)
                    ( is-retraction-map-inv-equivᵉ leftᵉ aᵉ))
                  ( Hᵉ (map-inv-equivᵉ leftᵉ (map-equivᵉ leftᵉ aᵉ)))
                  ( Hᵉ aᵉ)
                  ( apᵉ
                    ( map-equivᵉ rightᵉ ∘ᵉ topᵉ)
                    ( is-retraction-map-inv-equivᵉ leftᵉ aᵉ))
                  ( nat-htpyᵉ Hᵉ (is-retraction-map-inv-equivᵉ leftᵉ aᵉ))))
              ( concat-top-identification-coherence-square-identificationsᵉ _ _ _
                ( apᵉ topᵉ (is-retraction-map-inv-equivᵉ leftᵉ aᵉ))
                ( ap-compᵉ
                  ( map-inv-equivᵉ rightᵉ)
                  ( map-equivᵉ rightᵉ ∘ᵉ topᵉ)
                  ( is-retraction-map-inv-equivᵉ leftᵉ aᵉ))
                ( nat-htpyᵉ
                  ( is-retraction-map-inv-equivᵉ rightᵉ ·rᵉ topᵉ)
                  ( is-retraction-map-inv-equivᵉ leftᵉ aᵉ)))))) ∙ᵉ
        ( right-whisker-concatᵉ
          ( right-inverse-eq-transpose-equivᵉ
            ( rightᵉ)
            ( Hᵉ (map-inv-equivᵉ leftᵉ (map-equivᵉ leftᵉ aᵉ))))
          ( apᵉ topᵉ (is-retraction-map-inv-equivᵉ leftᵉ aᵉ)))))

  right-inverse-law-pasting-vertical-coherence-square-mapsᵉ :
    ( Hᵉ : coherence-square-mapsᵉ topᵉ (map-equivᵉ leftᵉ) (map-equivᵉ rightᵉ) bottomᵉ) →
    horizontal-coherence-prism-mapsᵉ
      ( bottomᵉ)
      ( map-inv-equivᵉ leftᵉ)
      ( map-inv-equivᵉ rightᵉ)
      ( topᵉ)
      ( map-equivᵉ leftᵉ)
      ( map-equivᵉ rightᵉ)
      ( bottomᵉ)
      ( idᵉ)
      ( idᵉ)
      ( is-section-map-inv-equivᵉ leftᵉ)
      ( vertical-inv-equiv-coherence-square-mapsᵉ topᵉ leftᵉ rightᵉ bottomᵉ Hᵉ)
      ( Hᵉ)
      ( refl-htpyᵉ)
      ( is-section-map-inv-equivᵉ rightᵉ)
  right-inverse-law-pasting-vertical-coherence-square-mapsᵉ Hᵉ aᵉ =
    ( right-unitᵉ) ∙ᵉ
    ( invᵉ
      ( ( assocᵉ
          ( Hᵉ (map-inv-equivᵉ leftᵉ aᵉ))
          ( apᵉ
            ( map-equivᵉ rightᵉ)
            ( vertical-inv-equiv-coherence-square-mapsᵉ topᵉ leftᵉ rightᵉ bottomᵉ
              ( Hᵉ)
              ( aᵉ)))
          ( is-section-map-inv-equivᵉ rightᵉ (bottomᵉ aᵉ))) ∙ᵉ
        ( left-whisker-concatᵉ
          ( Hᵉ (map-inv-equivᵉ leftᵉ aᵉ))
          ( triangle-eq-transpose-equivᵉ
            ( rightᵉ)
            ( ( invᵉ (Hᵉ (map-inv-equivᵉ leftᵉ aᵉ))) ∙ᵉ
              ( apᵉ bottomᵉ (is-section-map-inv-equivᵉ leftᵉ aᵉ))))) ∙ᵉ
        ( is-section-inv-concatᵉ
          ( Hᵉ (map-inv-equivᵉ leftᵉ aᵉ))
          ( apᵉ bottomᵉ (is-section-map-inv-equivᵉ leftᵉ aᵉ)))))
```

### Associativity of vertical pasting

Theᵉ proofᵉ ofᵉ associativityᵉ ofᵉ horizontalᵉ pastingᵉ mayᵉ beᵉ foundᵉ in
[`foundation-core.commuting-squares-of-maps`](foundation-core.commuting-squares-of-maps.md).ᵉ

```agda
module _
  { l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ l7ᵉ l8ᵉ : Level}
  { Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} {Dᵉ : UUᵉ l4ᵉ}
  { Xᵉ : UUᵉ l5ᵉ} {Yᵉ : UUᵉ l6ᵉ} {Zᵉ : UUᵉ l7ᵉ} {Wᵉ : UUᵉ l8ᵉ}
  ( topᵉ : Aᵉ → Xᵉ) (top-leftᵉ : Aᵉ → Bᵉ) (top-rightᵉ : Xᵉ → Yᵉ)
  ( mid-topᵉ : Bᵉ → Yᵉ) (mid-leftᵉ : Bᵉ → Cᵉ) (mid-rightᵉ : Yᵉ → Zᵉ) (mid-bottomᵉ : Cᵉ → Zᵉ)
  ( bottom-leftᵉ : Cᵉ → Dᵉ) (bottom-rightᵉ : Zᵉ → Wᵉ) (bottomᵉ : Dᵉ → Wᵉ)
  ( sq-topᵉ : coherence-square-mapsᵉ topᵉ top-leftᵉ top-rightᵉ mid-topᵉ)
  ( sq-midᵉ : coherence-square-mapsᵉ mid-topᵉ mid-leftᵉ mid-rightᵉ mid-bottomᵉ)
  ( sq-bottomᵉ :
      coherence-square-mapsᵉ mid-bottomᵉ bottom-leftᵉ bottom-rightᵉ bottomᵉ)
  where

  assoc-pasting-vertical-coherence-square-mapsᵉ :
    pasting-vertical-coherence-square-mapsᵉ
      ( topᵉ)
      ( mid-leftᵉ ∘ᵉ top-leftᵉ)
      ( mid-rightᵉ ∘ᵉ top-rightᵉ)
      ( mid-bottomᵉ)
      ( bottom-leftᵉ)
      ( bottom-rightᵉ)
      ( bottomᵉ)
      ( pasting-vertical-coherence-square-mapsᵉ
        ( topᵉ)
        ( top-leftᵉ)
        ( top-rightᵉ)
        ( mid-topᵉ)
        ( mid-leftᵉ)
        ( mid-rightᵉ)
        ( mid-bottomᵉ)
        ( sq-topᵉ)
        ( sq-midᵉ))
      ( sq-bottomᵉ) ~ᵉ
    pasting-vertical-coherence-square-mapsᵉ
      ( topᵉ)
      ( top-leftᵉ)
      ( top-rightᵉ)
      ( mid-topᵉ)
      ( bottom-leftᵉ ∘ᵉ mid-leftᵉ)
      ( bottom-rightᵉ ∘ᵉ mid-rightᵉ)
      ( bottomᵉ)
      ( sq-topᵉ)
      ( pasting-vertical-coherence-square-mapsᵉ
        ( mid-topᵉ)
        ( mid-leftᵉ)
        ( mid-rightᵉ)
        ( mid-bottomᵉ)
        ( bottom-leftᵉ)
        ( bottom-rightᵉ)
        ( bottomᵉ)
        ( sq-midᵉ)
        ( sq-bottomᵉ))
  assoc-pasting-vertical-coherence-square-mapsᵉ =
    ( ap-concat-htpyᵉ
      ( sq-bottomᵉ ·rᵉ mid-leftᵉ ·rᵉ top-leftᵉ)
      ( ( distributive-left-whisker-comp-concatᵉ
          ( bottom-rightᵉ)
          ( sq-midᵉ ·rᵉ top-leftᵉ)
          ( mid-rightᵉ ·lᵉ sq-topᵉ)) ∙hᵉ
        ( ap-concat-htpyᵉ
          ( bottom-rightᵉ ·lᵉ (sq-midᵉ ·rᵉ top-leftᵉ))
          ( preserves-comp-left-whisker-compᵉ
            ( bottom-rightᵉ)
            ( mid-rightᵉ)
            ( sq-topᵉ))))) ∙hᵉ
    ( inv-htpy-assoc-htpyᵉ
      ( sq-bottomᵉ ·rᵉ mid-leftᵉ ·rᵉ top-leftᵉ)
      ( bottom-rightᵉ ·lᵉ (sq-midᵉ ·rᵉ top-leftᵉ))
      ( ( bottom-rightᵉ ∘ᵉ mid-rightᵉ) ·lᵉ sq-topᵉ))
```

### Naturality of commuting squares of maps with respect to identifications

Similarlyᵉ to theᵉ naturalityᵉ squareᵉ ofᵉ homotopiesᵉ andᵉ
[identifications](foundation-core.identity-types.md),ᵉ weᵉ haveᵉ aᵉ naturalityᵉ
squareᵉ ofᵉ coherenceᵉ squaresᵉ ofᵉ mapsᵉ andᵉ identificationsᵉ:

```text
            apᵉ fᵉ (apᵉ gᵉ pᵉ)
   fᵉ (gᵉ xᵉ) --------------->ᵉ fᵉ (gᵉ yᵉ)
      |                       |
  Hᵉ xᵉ |                       | Hᵉ yᵉ
      ∨ᵉ                       ∨ᵉ
   hᵉ (kᵉ xᵉ) --------------->ᵉ hᵉ (kᵉ yᵉ)
            apᵉ hᵉ (apᵉ kᵉ pᵉ)           .ᵉ
```

```agda
module _
  { l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} {Dᵉ : UUᵉ l4ᵉ}
  ( topᵉ : Aᵉ → Bᵉ) (leftᵉ : Aᵉ → Cᵉ) (rightᵉ : Bᵉ → Dᵉ) (bottomᵉ : Cᵉ → Dᵉ)
  ( Hᵉ : coherence-square-mapsᵉ topᵉ leftᵉ rightᵉ bottomᵉ)
  where

  nat-coherence-square-mapsᵉ :
    { xᵉ yᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) →
    coherence-square-identificationsᵉ
      ( apᵉ bottomᵉ (apᵉ leftᵉ pᵉ))
      ( Hᵉ xᵉ)
      ( Hᵉ yᵉ)
      ( apᵉ rightᵉ (apᵉ topᵉ pᵉ))
  nat-coherence-square-mapsᵉ reflᵉ = right-unitᵉ
```

Asᵉ aᵉ corollary,ᵉ wheneverᵉ weᵉ haveᵉ twoᵉ coherenceᵉ squaresᵉ touchingᵉ atᵉ aᵉ vertexᵉ:

```text
  Aᵉ ----->ᵉ Bᵉ
  |        |
  |   Hᵉ ⇗ᵉ  |
  ∨ᵉ        ∨ᵉ
  Cᵉ ----->ᵉ Dᵉ ----->ᵉ Xᵉ
           |        |
           |   Kᵉ ⇗ᵉ  |
           ∨ᵉ        ∨ᵉ
           Yᵉ ----->ᵉ Zᵉ ,ᵉ
```

thereᵉ isᵉ aᵉ homotopyᵉ betweenᵉ firstᵉ applyingᵉ `H`,ᵉ thenᵉ `K`,ᵉ andᵉ firstᵉ applyingᵉ
`K`,ᵉ thenᵉ `H`.ᵉ

```agda
module _
  { l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ l7ᵉ : Level}
  { Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} {Dᵉ : UUᵉ l4ᵉ}
  { Xᵉ : UUᵉ l5ᵉ} {Yᵉ : UUᵉ l6ᵉ} {Zᵉ : UUᵉ l7ᵉ}
  ( topᵉ : Aᵉ → Bᵉ) (leftᵉ : Aᵉ → Cᵉ) (mid-topᵉ : Bᵉ → Dᵉ) (mid-leftᵉ : Cᵉ → Dᵉ)
  ( mid-rightᵉ : Dᵉ → Xᵉ) (mid-bottomᵉ : Dᵉ → Yᵉ) (rightᵉ : Xᵉ → Zᵉ) (bottomᵉ : Yᵉ → Zᵉ)
  ( Hᵉ : coherence-square-mapsᵉ topᵉ leftᵉ mid-topᵉ mid-leftᵉ)
  ( Kᵉ : coherence-square-mapsᵉ mid-rightᵉ mid-bottomᵉ rightᵉ bottomᵉ)
  where

  swap-nat-coherence-square-mapsᵉ :
    coherence-square-homotopiesᵉ
      ( bottomᵉ ·lᵉ mid-bottomᵉ ·lᵉ Hᵉ)
      ( Kᵉ ·rᵉ mid-leftᵉ ·rᵉ leftᵉ)
      ( Kᵉ ·rᵉ mid-topᵉ ·rᵉ topᵉ)
      ( rightᵉ ·lᵉ mid-rightᵉ ·lᵉ Hᵉ)
  swap-nat-coherence-square-mapsᵉ xᵉ =
    nat-coherence-square-mapsᵉ mid-rightᵉ mid-bottomᵉ rightᵉ bottomᵉ Kᵉ (Hᵉ xᵉ)
```

### Commutativity of horizontal and vertical pasting

Givenᵉ aᵉ squareᵉ ofᵉ commutingᵉ squares,ᵉ likeᵉ soᵉ:

```text
  Aᵉ ----->ᵉ Bᵉ ----->ᵉ Cᵉ
  |        |        |
  |    ⇗ᵉ   |    ⇗ᵉ   |
  ∨ᵉ        ∨ᵉ        ∨ᵉ
  Xᵉ ----->ᵉ Yᵉ ----->ᵉ Zᵉ
  |        |        |
  |    ⇗ᵉ   |    ⇗ᵉ   |
  ∨ᵉ        ∨ᵉ        ∨ᵉ
  Mᵉ ----->ᵉ Nᵉ ----->ᵉ Oᵉ ,ᵉ
```

weᵉ haveᵉ twoᵉ choicesᵉ forᵉ obtainingᵉ theᵉ outerᵉ commutingᵉ squareᵉ —ᵉ eitherᵉ byᵉ firstᵉ
verticallyᵉ composingᵉ theᵉ smallerᵉ squares,ᵉ andᵉ thenᵉ horizontallyᵉ composingᵉ theᵉ
newlyᵉ createdᵉ rectangles,ᵉ orᵉ byᵉ firstᵉ horizontallyᵉ composingᵉ theᵉ squares,ᵉ andᵉ
thenᵉ verticallyᵉ composingᵉ theᵉ rectangles.ᵉ

Theᵉ followingᵉ lemmaᵉ statesᵉ thatᵉ theᵉ bigᵉ squaresᵉ obtainedᵉ byᵉ theseᵉ twoᵉ
compositionsᵉ areᵉ againᵉ homotopic.ᵉ Diagrammatically,ᵉ weᵉ haveᵉ

```text
 Hᵉ | Kᵉ   Hᵉ | Kᵉ
 -----ᵉ ~ᵉ --|--ᵉ
 Lᵉ | Tᵉ   Lᵉ | Tᵉ .ᵉ
```

```agda
module _
  { l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ l7ᵉ l8ᵉ l9ᵉ : Level}
  { Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} {Xᵉ : UUᵉ l4ᵉ} {Yᵉ : UUᵉ l5ᵉ} {Zᵉ : UUᵉ l6ᵉ}
  { Mᵉ : UUᵉ l7ᵉ} {Nᵉ : UUᵉ l8ᵉ} {Oᵉ : UUᵉ l9ᵉ}
  ( top-leftᵉ : Aᵉ → Bᵉ) (top-rightᵉ : Bᵉ → Cᵉ)
  ( left-topᵉ : Aᵉ → Xᵉ) (mid-topᵉ : Bᵉ → Yᵉ) (right-topᵉ : Cᵉ → Zᵉ)
  ( mid-leftᵉ : Xᵉ → Yᵉ) (mid-rightᵉ : Yᵉ → Zᵉ)
  ( left-bottomᵉ : Xᵉ → Mᵉ) (mid-bottomᵉ : Yᵉ → Nᵉ) (right-bottomᵉ : Zᵉ → Oᵉ)
  ( bottom-leftᵉ : Mᵉ → Nᵉ) (bottom-rightᵉ : Nᵉ → Oᵉ)
  ( sq-left-topᵉ : coherence-square-mapsᵉ top-leftᵉ left-topᵉ mid-topᵉ mid-leftᵉ)
  ( sq-right-topᵉ : coherence-square-mapsᵉ top-rightᵉ mid-topᵉ right-topᵉ mid-rightᵉ)
  ( sq-left-bottomᵉ :
      coherence-square-mapsᵉ mid-leftᵉ left-bottomᵉ mid-bottomᵉ bottom-leftᵉ)
  ( sq-right-bottomᵉ :
      coherence-square-mapsᵉ mid-rightᵉ mid-bottomᵉ right-bottomᵉ bottom-rightᵉ)
  where

  commutative-pasting-vertical-pasting-horizontal-coherence-square-mapsᵉ :
    ( pasting-horizontal-coherence-square-mapsᵉ
      ( top-leftᵉ)
      ( top-rightᵉ)
      ( left-bottomᵉ ∘ᵉ left-topᵉ)
      ( mid-bottomᵉ ∘ᵉ mid-topᵉ)
      ( right-bottomᵉ ∘ᵉ right-topᵉ)
      ( bottom-leftᵉ)
      ( bottom-rightᵉ)
      ( pasting-vertical-coherence-square-mapsᵉ
        ( top-leftᵉ)
        ( left-topᵉ)
        ( mid-topᵉ)
        ( mid-leftᵉ)
        ( left-bottomᵉ)
        ( mid-bottomᵉ)
        ( bottom-leftᵉ)
        ( sq-left-topᵉ)
        ( sq-left-bottomᵉ))
      ( pasting-vertical-coherence-square-mapsᵉ
        ( top-rightᵉ)
        ( mid-topᵉ)
        ( right-topᵉ)
        ( mid-rightᵉ)
        ( mid-bottomᵉ)
        ( right-bottomᵉ)
        ( bottom-rightᵉ)
        ( sq-right-topᵉ)
        ( sq-right-bottomᵉ))) ~ᵉ
    ( pasting-vertical-coherence-square-mapsᵉ
      ( top-rightᵉ ∘ᵉ top-leftᵉ)
      ( left-topᵉ)
      ( right-topᵉ)
      ( mid-rightᵉ ∘ᵉ mid-leftᵉ)
      ( left-bottomᵉ)
      ( right-bottomᵉ)
      ( bottom-rightᵉ ∘ᵉ bottom-leftᵉ)
      ( pasting-horizontal-coherence-square-mapsᵉ
        ( top-leftᵉ)
        ( top-rightᵉ)
        ( left-topᵉ)
        ( mid-topᵉ)
        ( right-topᵉ)
        ( mid-leftᵉ)
        ( mid-rightᵉ)
        ( sq-left-topᵉ)
        ( sq-right-topᵉ))
      ( pasting-horizontal-coherence-square-mapsᵉ
        ( mid-leftᵉ)
        ( mid-rightᵉ)
        ( left-bottomᵉ)
        ( mid-bottomᵉ)
        ( right-bottomᵉ)
        ( bottom-leftᵉ)
        ( bottom-rightᵉ)
        ( sq-left-bottomᵉ)
        ( sq-right-bottomᵉ)))
  commutative-pasting-vertical-pasting-horizontal-coherence-square-mapsᵉ =
    ( ap-concat-htpy'ᵉ _
      ( distributive-left-whisker-comp-concatᵉ
        ( bottom-rightᵉ)
        ( sq-left-bottomᵉ ·rᵉ left-topᵉ)
        ( mid-bottomᵉ ·lᵉ sq-left-topᵉ)) ∙hᵉ
      ( double-whisker-coherence-square-homotopiesᵉ
        ( bottom-rightᵉ ·lᵉ sq-left-bottomᵉ ·rᵉ left-topᵉ)
        ( sq-right-bottomᵉ ·rᵉ mid-leftᵉ ·rᵉ left-topᵉ)
        ( bottom-rightᵉ ·lᵉ mid-bottomᵉ ·lᵉ sq-left-topᵉ)
        ( right-bottomᵉ ·lᵉ mid-rightᵉ ·lᵉ sq-left-topᵉ)
        ( sq-right-bottomᵉ ·rᵉ mid-topᵉ ·rᵉ top-leftᵉ)
        ( right-bottomᵉ ·lᵉ sq-right-topᵉ ·rᵉ top-leftᵉ)
        ( inv-htpyᵉ
          ( swap-nat-coherence-square-mapsᵉ
            ( top-leftᵉ)
            ( left-topᵉ)
            ( mid-topᵉ)
            ( mid-leftᵉ)
            ( mid-rightᵉ)
            ( mid-bottomᵉ)
            ( right-bottomᵉ)
            ( bottom-rightᵉ)
            ( sq-left-topᵉ)
            ( sq-right-bottomᵉ))))) ∙hᵉ
      ( ap-concat-htpyᵉ _
        ( inv-htpyᵉ
          ( distributive-left-whisker-comp-concatᵉ
            ( right-bottomᵉ)
            ( mid-rightᵉ ·lᵉ sq-left-topᵉ)
            ( sq-right-topᵉ ·rᵉ top-leftᵉ))))
```

### Distributivity of pasting squares and transposing by precomposition

Givenᵉ twoᵉ commutingᵉ squaresᵉ whichᵉ canᵉ beᵉ composedᵉ horizontallyᵉ (vertically),ᵉ weᵉ
knowᵉ thatᵉ composingᵉ themᵉ andᵉ thenᵉ transposingᵉ themᵉ byᵉ precompositionᵉ givesᵉ aᵉ
homotopyᵉ thatᵉ isᵉ homotopicᵉ to firstᵉ transposingᵉ theᵉ squaresᵉ andᵉ thenᵉ composingᵉ
them.ᵉ

```text
          tlᵉ       trᵉ                trᵉ ∘ᵉ tlᵉ
      Aᵉ ----->ᵉ Bᵉ ----->ᵉ Cᵉ         Aᵉ -------->ᵉ Cᵉ
      |        |        |         |           |
    lᵉ |   Hᵉ  mᵉ |   Kᵉ    | rᵉ  ↦ᵉ  lᵉ |   Hᵉ | Kᵉ   | rᵉ
      ∨ᵉ        ∨ᵉ        ∨ᵉ         ∨ᵉ           ∨ᵉ
      Xᵉ ----->ᵉ Yᵉ ----->ᵉ Zᵉ         Xᵉ -------->ᵉ Zᵉ
          blᵉ       brᵉ                brᵉ ∘ᵉ blᵉ

               ↧ᵉ                        ↧ᵉ

             -ᵉ ∘ᵉ rᵉ
        W^Zᵉ ------>ᵉ W^Cᵉ
         |           |
  -ᵉ ∘ᵉ brᵉ |    W^Kᵉ    | -ᵉ ∘ᵉ trᵉ        W^(Hᵉ | Kᵉ)
         ∨ᵉ   -ᵉ ∘ᵉ mᵉ   ∨ᵉ                  ~ᵉ
        W^Yᵉ ------>ᵉ W^Bᵉ       ↦ᵉ
         |           |                 W^Kᵉ
  -ᵉ ∘ᵉ blᵉ |    W^Hᵉ    | -ᵉ ∘ᵉ tlᵉ          ---ᵉ
         ∨ᵉ           ∨ᵉ                 W^Hᵉ
        W^Xᵉ ------>ᵉ W^Aᵉ
             -ᵉ ∘ᵉ lᵉ
```

```agda
module _
  { l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ l7ᵉ : Level}
  { Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} {Xᵉ : UUᵉ l4ᵉ} {Yᵉ : UUᵉ l5ᵉ} {Zᵉ : UUᵉ l6ᵉ}
  ( Wᵉ : UUᵉ l7ᵉ)
  where

  distributive-precomp-pasting-horizontal-coherence-square-mapsᵉ :
    ( top-leftᵉ : Aᵉ → Bᵉ) (top-rightᵉ : Bᵉ → Cᵉ)
    ( leftᵉ : Aᵉ → Xᵉ) (middleᵉ : Bᵉ → Yᵉ) (rightᵉ : Cᵉ → Zᵉ)
    ( bottom-leftᵉ : Xᵉ → Yᵉ) (bottom-rightᵉ : Yᵉ → Zᵉ) →
    ( Hᵉ : coherence-square-mapsᵉ top-leftᵉ leftᵉ middleᵉ bottom-leftᵉ) →
    ( Kᵉ : coherence-square-mapsᵉ top-rightᵉ middleᵉ rightᵉ bottom-rightᵉ) →
    precomp-coherence-square-mapsᵉ
      ( top-rightᵉ ∘ᵉ top-leftᵉ)
      ( leftᵉ)
      ( rightᵉ)
      ( bottom-rightᵉ ∘ᵉ bottom-leftᵉ)
      ( pasting-horizontal-coherence-square-mapsᵉ
        ( top-leftᵉ)
        ( top-rightᵉ)
        ( leftᵉ)
        ( middleᵉ)
        ( rightᵉ)
        ( bottom-leftᵉ)
        ( bottom-rightᵉ)
        ( Hᵉ)
        ( Kᵉ))
      ( Wᵉ) ~ᵉ
    pasting-vertical-coherence-square-mapsᵉ
      ( precompᵉ rightᵉ Wᵉ)
      ( precompᵉ bottom-rightᵉ Wᵉ)
      ( precompᵉ top-rightᵉ Wᵉ)
      ( precompᵉ middleᵉ Wᵉ)
      ( precompᵉ bottom-leftᵉ Wᵉ)
      ( precompᵉ top-leftᵉ Wᵉ)
      ( precompᵉ leftᵉ Wᵉ)
      ( precomp-coherence-square-mapsᵉ
        ( top-rightᵉ)
        ( middleᵉ)
        ( rightᵉ)
        ( bottom-rightᵉ)
        ( Kᵉ)
        ( Wᵉ))
      ( precomp-coherence-square-mapsᵉ
        ( top-leftᵉ)
        ( leftᵉ)
        ( middleᵉ)
        ( bottom-leftᵉ)
        ( Hᵉ)
        ( Wᵉ))
  distributive-precomp-pasting-horizontal-coherence-square-mapsᵉ
    ( top-leftᵉ)
    ( top-rightᵉ)
    ( leftᵉ)
    ( middleᵉ)
    ( rightᵉ)
    ( bottom-leftᵉ)
    ( bottom-rightᵉ)
    ( Hᵉ)
    ( Kᵉ)
    ( hᵉ) =
    equational-reasoningᵉ
      eq-htpyᵉ
        ( hᵉ ·lᵉ ((bottom-rightᵉ ·lᵉ Hᵉ) ∙hᵉ (Kᵉ ·rᵉ top-leftᵉ)))
      ＝ᵉ eq-htpyᵉ
          ( (hᵉ ·lᵉ (bottom-rightᵉ ·lᵉ Hᵉ)) ∙hᵉ ((hᵉ ·lᵉ Kᵉ) ·rᵉ top-leftᵉ))
        byᵉ
        apᵉ
          ( eq-htpyᵉ)
          ( eq-htpyᵉ
            ( distributive-left-whisker-comp-concatᵉ
              ( hᵉ)
              ( bottom-rightᵉ ·lᵉ Hᵉ)
              ( Kᵉ ·rᵉ top-leftᵉ)))
      ＝ᵉ eq-htpyᵉ
          ( hᵉ ·lᵉ (bottom-rightᵉ ·lᵉ Hᵉ)) ∙ᵉ
        eq-htpyᵉ
          ( (hᵉ ·lᵉ Kᵉ) ·rᵉ top-leftᵉ)
        byᵉ
        eq-htpy-concat-htpyᵉ
          ( hᵉ ·lᵉ (bottom-rightᵉ ·lᵉ Hᵉ))
          ( (hᵉ ·lᵉ Kᵉ) ·rᵉ top-leftᵉ)
      ＝ᵉ eq-htpyᵉ
          ( (hᵉ ∘ᵉ bottom-rightᵉ) ·lᵉ Hᵉ) ∙ᵉ
          apᵉ
            ( precompᵉ top-leftᵉ Wᵉ)
            ( htpy-precompᵉ Kᵉ Wᵉ hᵉ)
        byᵉ
        ap-binaryᵉ
          ( λ Lᵉ qᵉ → eq-htpyᵉ Lᵉ ∙ᵉ qᵉ)
          ( eq-htpyᵉ (preserves-comp-left-whisker-compᵉ hᵉ bottom-rightᵉ Hᵉ))
          ( invᵉ (compute-eq-htpy-ap-precompᵉ top-leftᵉ (hᵉ ·lᵉ Kᵉ)))

  distributive-precomp-pasting-vertical-coherence-square-mapsᵉ :
    ( topᵉ : Aᵉ → Xᵉ) (left-topᵉ : Aᵉ → Bᵉ) (right-topᵉ : Xᵉ → Yᵉ) (middleᵉ : Bᵉ → Yᵉ) →
    ( left-bottomᵉ : Bᵉ → Cᵉ) (right-bottomᵉ : Yᵉ → Zᵉ) (bottomᵉ : Cᵉ → Zᵉ) →
    ( Hᵉ : coherence-square-mapsᵉ topᵉ left-topᵉ right-topᵉ middleᵉ) →
    ( Kᵉ : coherence-square-mapsᵉ middleᵉ left-bottomᵉ right-bottomᵉ bottomᵉ) →
    precomp-coherence-square-mapsᵉ
      ( topᵉ)
      ( left-bottomᵉ ∘ᵉ left-topᵉ)
      ( right-bottomᵉ ∘ᵉ right-topᵉ)
      ( bottomᵉ)
      ( pasting-vertical-coherence-square-mapsᵉ
        ( topᵉ)
        ( left-topᵉ)
        ( right-topᵉ)
        ( middleᵉ)
        ( left-bottomᵉ)
        ( right-bottomᵉ)
        ( bottomᵉ)
        ( Hᵉ)
        ( Kᵉ))
      ( Wᵉ) ~ᵉ
    pasting-horizontal-coherence-square-mapsᵉ
      ( precompᵉ right-bottomᵉ Wᵉ)
      ( precompᵉ right-topᵉ Wᵉ)
      ( precompᵉ bottomᵉ Wᵉ)
      ( precompᵉ middleᵉ Wᵉ)
      ( precompᵉ topᵉ Wᵉ)
      ( precompᵉ left-bottomᵉ Wᵉ)
      ( precompᵉ left-topᵉ Wᵉ)
      ( precomp-coherence-square-mapsᵉ
        ( middleᵉ)
        ( left-bottomᵉ)
        ( right-bottomᵉ)
        ( bottomᵉ)
        ( Kᵉ)
        ( Wᵉ))
      ( precomp-coherence-square-mapsᵉ
        ( topᵉ)
        ( left-topᵉ)
        ( right-topᵉ)
        ( middleᵉ)
        ( Hᵉ)
        ( Wᵉ))
  distributive-precomp-pasting-vertical-coherence-square-mapsᵉ
    ( topᵉ)
    ( left-topᵉ)
    ( right-topᵉ)
    ( middleᵉ)
    ( left-bottomᵉ)
    ( right-bottomᵉ)
    ( bottomᵉ)
    ( Hᵉ)
    ( Kᵉ)
    ( hᵉ) =
    equational-reasoningᵉ
      eq-htpyᵉ
        (hᵉ ·lᵉ ((Kᵉ ·rᵉ left-topᵉ) ∙hᵉ (right-bottomᵉ ·lᵉ Hᵉ)))
      ＝ᵉ eq-htpyᵉ
          ( ((hᵉ ·lᵉ Kᵉ) ·rᵉ left-topᵉ) ∙hᵉ (hᵉ ·lᵉ (right-bottomᵉ ·lᵉ Hᵉ)))
        byᵉ
        apᵉ
          ( eq-htpyᵉ)
          ( eq-htpyᵉ
            ( distributive-left-whisker-comp-concatᵉ
            ( hᵉ)
            ( Kᵉ ·rᵉ left-topᵉ)
            ( right-bottomᵉ ·lᵉ Hᵉ)))
      ＝ᵉ eq-htpyᵉ
          ( (hᵉ ·lᵉ Kᵉ) ·rᵉ left-topᵉ) ∙ᵉ
        eq-htpyᵉ
          ( hᵉ ·lᵉ (right-bottomᵉ ·lᵉ Hᵉ))
        byᵉ
        eq-htpy-concat-htpyᵉ
          ( (hᵉ ·lᵉ Kᵉ) ·rᵉ left-topᵉ)
          ( hᵉ ·lᵉ (right-bottomᵉ ·lᵉ Hᵉ))
      ＝ᵉ apᵉ
          ( precompᵉ left-topᵉ Wᵉ)
          ( htpy-precompᵉ Kᵉ Wᵉ hᵉ) ∙ᵉ
        eq-htpyᵉ
          ( (hᵉ ∘ᵉ right-bottomᵉ) ·lᵉ Hᵉ)
        byᵉ
        ap-binaryᵉ
          ( λ pᵉ Lᵉ → pᵉ ∙ᵉ eq-htpyᵉ Lᵉ)
          ( invᵉ (compute-eq-htpy-ap-precompᵉ left-topᵉ (hᵉ ·lᵉ Kᵉ)))
          ( eq-htpyᵉ (preserves-comp-left-whisker-compᵉ hᵉ right-bottomᵉ Hᵉ))
```

### Transposing by precomposition of whiskered squares

Takingᵉ aᵉ squareᵉ ofᵉ theᵉ formᵉ

```text
      fᵉ        topᵉ
  Xᵉ ----->ᵉ Aᵉ ----->ᵉ Bᵉ
           |        |
      leftᵉ |   Hᵉ    | rightᵉ
           ∨ᵉ        ∨ᵉ
           Cᵉ ----->ᵉ Dᵉ
             bottomᵉ
```

andᵉ transposingᵉ itᵉ byᵉ precompositionᵉ resultsᵉ in theᵉ squareᵉ

```text
  W^Dᵉ ----->ᵉ W^Bᵉ
   |          |
   |   W^Hᵉ    |
   ∨ᵉ          ∨ᵉ  -ᵉ ∘ᵉ fᵉ
  W^Cᵉ ----->ᵉ W^Aᵉ ----->ᵉ W^Xᵉ
```

Thisᵉ factᵉ canᵉ beᵉ writtenᵉ asᵉ distributionᵉ ofᵉ rightᵉ whiskeringᵉ overᵉ transpositionᵉ:
`W^(Hᵉ ·rᵉ fᵉ) = W^fᵉ ·lᵉ W^H`.ᵉ

```agda
module _
  { l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level}
  { Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} {Dᵉ : UUᵉ l4ᵉ} {Xᵉ : UUᵉ l5ᵉ} (Wᵉ : UUᵉ l6ᵉ)
  ( topᵉ : Aᵉ → Bᵉ) (leftᵉ : Aᵉ → Cᵉ) (rightᵉ : Bᵉ → Dᵉ) (bottomᵉ : Cᵉ → Dᵉ)
  ( Hᵉ : coherence-square-mapsᵉ topᵉ leftᵉ rightᵉ bottomᵉ)
  where

  distributive-precomp-right-whisker-comp-coherence-square-mapsᵉ :
    ( fᵉ : Xᵉ → Aᵉ) →
    precomp-coherence-square-mapsᵉ
      ( topᵉ ∘ᵉ fᵉ)
      ( leftᵉ ∘ᵉ fᵉ)
      ( rightᵉ)
      ( bottomᵉ)
      ( Hᵉ ·rᵉ fᵉ)
      ( Wᵉ) ~ᵉ
    ( ( precompᵉ fᵉ Wᵉ) ·lᵉ
      ( precomp-coherence-square-mapsᵉ topᵉ leftᵉ rightᵉ bottomᵉ Hᵉ Wᵉ))
  distributive-precomp-right-whisker-comp-coherence-square-mapsᵉ fᵉ gᵉ =
    invᵉ (compute-eq-htpy-ap-precompᵉ fᵉ (gᵉ ·lᵉ Hᵉ))
```

Similarly,ᵉ weᵉ canᵉ calculateᵉ transpositionsᵉ ofᵉ left-whiskeredᵉ squaresᵉ with theᵉ
formulaᵉ `W^(fᵉ ·lᵉ Hᵉ) = W^Hᵉ ·rᵉ W^f`.ᵉ

```agda
  distributive-precomp-left-whisker-comp-coherence-square-mapsᵉ :
    ( fᵉ : Dᵉ → Xᵉ) →
    precomp-coherence-square-mapsᵉ
      ( topᵉ)
      ( leftᵉ)
      ( fᵉ ∘ᵉ rightᵉ)
      ( fᵉ ∘ᵉ bottomᵉ)
      ( fᵉ ·lᵉ Hᵉ)
      ( Wᵉ) ~ᵉ
    ( ( precomp-coherence-square-mapsᵉ topᵉ leftᵉ rightᵉ bottomᵉ Hᵉ Wᵉ) ·rᵉ
      ( precompᵉ fᵉ Wᵉ))
  distributive-precomp-left-whisker-comp-coherence-square-mapsᵉ fᵉ gᵉ =
    apᵉ eq-htpyᵉ (eq-htpyᵉ (λ aᵉ → invᵉ (ap-compᵉ gᵉ fᵉ (Hᵉ aᵉ))))
```

### The square of function spaces induced by a composition of triangles is homotopic to the composition of induced triangles of function spaces

```agda
module _
  { l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level}
  { Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ} (Wᵉ : UUᵉ l5ᵉ)
  ( topᵉ : Aᵉ → Xᵉ) (leftᵉ : Aᵉ → Bᵉ) (rightᵉ : Xᵉ → Yᵉ) (bottomᵉ : Bᵉ → Yᵉ)
  where

  distributive-precomp-coherence-square-left-map-triangle-coherence-triangle-mapsᵉ :
    { diagonal-leftᵉ diagonal-rightᵉ : Aᵉ → Yᵉ} →
    ( Lᵉ : diagonal-leftᵉ ~ᵉ diagonal-rightᵉ) →
    ( Hᵉ : coherence-triangle-maps'ᵉ diagonal-leftᵉ bottomᵉ leftᵉ) →
    ( Kᵉ : coherence-triangle-mapsᵉ diagonal-rightᵉ rightᵉ topᵉ) →
    ( precomp-coherence-square-mapsᵉ
      ( topᵉ)
      ( leftᵉ)
      ( rightᵉ)
      ( bottomᵉ)
      ( horizontal-pasting-htpy-coherence-triangle-mapsᵉ
        ( topᵉ)
        ( leftᵉ)
        ( rightᵉ)
        ( bottomᵉ)
        ( Lᵉ)
        ( Hᵉ)
        ( Kᵉ))
      ( Wᵉ)) ~ᵉ
    ( horizontal-pasting-htpy-coherence-triangle-mapsᵉ
      ( precompᵉ rightᵉ Wᵉ)
      ( precompᵉ bottomᵉ Wᵉ)
      ( precompᵉ topᵉ Wᵉ)
      ( precompᵉ leftᵉ Wᵉ)
      ( htpy-precompᵉ Lᵉ Wᵉ)
      ( precomp-coherence-triangle-maps'ᵉ diagonal-leftᵉ bottomᵉ leftᵉ Hᵉ Wᵉ)
      ( precomp-coherence-triangle-mapsᵉ diagonal-rightᵉ rightᵉ topᵉ Kᵉ Wᵉ))
  distributive-precomp-coherence-square-left-map-triangle-coherence-triangle-mapsᵉ
    { diagonal-rightᵉ = diagonal-rightᵉ}
    ( Lᵉ)
    ( Hᵉ)
    ( Kᵉ)
    ( hᵉ) =
    ( compute-concat-htpy-precompᵉ (Hᵉ ∙hᵉ Lᵉ) Kᵉ Wᵉ hᵉ) ∙ᵉ
    ( right-whisker-concatᵉ
      ( compute-concat-htpy-precompᵉ Hᵉ Lᵉ Wᵉ hᵉ)
      ( precomp-coherence-triangle-mapsᵉ diagonal-rightᵉ rightᵉ topᵉ Kᵉ Wᵉ hᵉ))

  distributive-precomp-coherence-square-left-map-triangle-coherence-triangle-maps'ᵉ :
    { diagonal-leftᵉ diagonal-rightᵉ : Aᵉ → Yᵉ} →
    ( Lᵉ : diagonal-leftᵉ ~ᵉ diagonal-rightᵉ) →
    ( Hᵉ : coherence-triangle-maps'ᵉ diagonal-leftᵉ bottomᵉ leftᵉ) →
    ( Kᵉ : coherence-triangle-mapsᵉ diagonal-rightᵉ rightᵉ topᵉ) →
    ( precomp-coherence-square-mapsᵉ
      ( topᵉ)
      ( leftᵉ)
      ( rightᵉ)
      ( bottomᵉ)
      ( horizontal-pasting-htpy-coherence-triangle-maps'ᵉ
        ( topᵉ)
        ( leftᵉ)
        ( rightᵉ)
        ( bottomᵉ)
        ( Lᵉ)
        ( Hᵉ)
        ( Kᵉ))
      ( Wᵉ)) ~ᵉ
    ( horizontal-pasting-htpy-coherence-triangle-maps'ᵉ
      ( precompᵉ rightᵉ Wᵉ)
      ( precompᵉ bottomᵉ Wᵉ)
      ( precompᵉ topᵉ Wᵉ)
      ( precompᵉ leftᵉ Wᵉ)
      ( htpy-precompᵉ Lᵉ Wᵉ)
      ( precomp-coherence-triangle-maps'ᵉ diagonal-leftᵉ bottomᵉ leftᵉ Hᵉ Wᵉ)
      ( precomp-coherence-triangle-mapsᵉ diagonal-rightᵉ rightᵉ topᵉ Kᵉ Wᵉ))
  distributive-precomp-coherence-square-left-map-triangle-coherence-triangle-maps'ᵉ
    { diagonal-leftᵉ = diagonal-leftᵉ}
    ( Lᵉ)
    ( Hᵉ)
    ( Kᵉ)
    ( hᵉ) =
    ( compute-concat-htpy-precompᵉ Hᵉ (Lᵉ ∙hᵉ Kᵉ) Wᵉ hᵉ) ∙ᵉ
    ( left-whisker-concatᵉ
      ( precomp-coherence-triangle-maps'ᵉ diagonal-leftᵉ bottomᵉ leftᵉ Hᵉ Wᵉ hᵉ)
      ( compute-concat-htpy-precompᵉ Lᵉ Kᵉ Wᵉ hᵉ))

  distributive-precomp-coherence-square-comp-coherence-triangles-mapsᵉ :
    ( diagonalᵉ : Aᵉ → Yᵉ) →
    ( Hᵉ : coherence-triangle-maps'ᵉ diagonalᵉ bottomᵉ leftᵉ) →
    ( Kᵉ : coherence-triangle-mapsᵉ diagonalᵉ rightᵉ topᵉ) →
    ( precomp-coherence-square-mapsᵉ
      ( topᵉ)
      ( leftᵉ)
      ( rightᵉ)
      ( bottomᵉ)
      ( horizontal-pasting-coherence-triangle-mapsᵉ
        ( topᵉ)
        ( leftᵉ)
        ( rightᵉ)
        ( bottomᵉ)
        ( diagonalᵉ)
        ( Hᵉ)
        ( Kᵉ))
      ( Wᵉ)) ~ᵉ
    ( horizontal-pasting-coherence-triangle-mapsᵉ
      ( precompᵉ rightᵉ Wᵉ)
      ( precompᵉ bottomᵉ Wᵉ)
      ( precompᵉ topᵉ Wᵉ)
      ( precompᵉ leftᵉ Wᵉ)
      ( precompᵉ diagonalᵉ Wᵉ)
      ( precomp-coherence-triangle-maps'ᵉ diagonalᵉ bottomᵉ leftᵉ Hᵉ Wᵉ)
      ( precomp-coherence-triangle-mapsᵉ diagonalᵉ rightᵉ topᵉ Kᵉ Wᵉ))
  distributive-precomp-coherence-square-comp-coherence-triangles-mapsᵉ
    ( diagonalᵉ)
    ( Hᵉ)
    ( Kᵉ)
    ( hᵉ) =
    compute-concat-htpy-precompᵉ Hᵉ Kᵉ Wᵉ hᵉ
```

### Collapsing inner squares in pasted squares composed of triangles

Considerᵉ twoᵉ commutingᵉ squares,ᵉ composedᵉ in totalᵉ ofᵉ fourᵉ commutingᵉ triangles,ᵉ
whichᵉ takeᵉ theᵉ followingᵉ formᵉ:

```text
           topᵉ
     Aᵉ ----------->ᵉ Cᵉ
     |             ∧|ᵉ
     |           /ᵉ  |
     |     blᵉ  /ᵉ    |
  tlᵉ |       /ᵉ      | trᵉ
     |     /ᵉ        |
     |   /ᵉ          |
     ∨ᵉ /ᵉ    midᵉ     ∨ᵉ
     Bᵉ ----------->ᵉ Yᵉ
     |             ∧|ᵉ
     |           /ᵉ  |
     |     trᵉ  /ᵉ    |
  blᵉ |       /ᵉ      | brᵉ
     |     /ᵉ        |
     |   /ᵉ          |
     ∨ᵉ /ᵉ            ∨ᵉ
     Cᵉ ----------->ᵉ Zᵉ .ᵉ
          bottomᵉ
```

Noteᵉ thatᵉ theᵉ bottom-leftᵉ vertexᵉ isᵉ theᵉ sameᵉ asᵉ theᵉ top-rightᵉ vertex,ᵉ andᵉ theᵉ
diagonalsᵉ areᵉ notᵉ arbitrary.ᵉ

Ifᵉ theᵉ squareᵉ thatᵉ arisesᵉ in theᵉ middle,ᵉ

```text
        blᵉ
     Bᵉ ---->ᵉ Cᵉ
     |       |
  blᵉ |       | trᵉ
     ∨ᵉ       ∨ᵉ
     Cᵉ ---->ᵉ Yᵉ ,ᵉ
        trᵉ
```

isᵉ homotopicᵉ to theᵉ reflexiveᵉ homotopyᵉ `refl-htpyᵉ : trᵉ ∘ᵉ blᵉ ~ᵉ trᵉ ∘ᵉ bl`,ᵉ thenᵉ theᵉ
wholeᵉ rectangleᵉ collapsesᵉ (isᵉ homotopicᵉ) to theᵉ
[horizontalᵉ composition](foundation.homotopy-algebra.mdᵉ)

```text
                         Yᵉ
                        ∧ᵉ \ᵉ
                  trᵉ  /ᵉ     \ᵉ  brᵉ
                    /ᵉ         \ᵉ
        topᵉ       /ᵉ             ∨ᵉ
  Aᵉ ----------->ᵉ Cᵉ ----------->ᵉ Zᵉ .ᵉ
   \ᵉ             ∧ᵉ    bottomᵉ
     \ᵉ         /ᵉ
   tlᵉ  \ᵉ     /ᵉ  blᵉ
         ∨ᵉ /ᵉ
          Bᵉ
```

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ}
  {Yᵉ : UUᵉ l4ᵉ} {Zᵉ : UUᵉ l5ᵉ}
  (topᵉ : Aᵉ → Cᵉ) (top-leftᵉ : Aᵉ → Bᵉ) (top-rightᵉ : Cᵉ → Yᵉ)
  (midᵉ : Bᵉ → Yᵉ)
  (bottom-leftᵉ : Bᵉ → Cᵉ) (bottom-rightᵉ : Yᵉ → Zᵉ) (bottomᵉ : Cᵉ → Zᵉ)
  (top-left-triangleᵉ : coherence-triangle-maps'ᵉ topᵉ bottom-leftᵉ top-leftᵉ)
  (top-right-triangleᵉ : coherence-triangle-mapsᵉ midᵉ top-rightᵉ bottom-leftᵉ)
  (bottom-left-triangleᵉ : coherence-triangle-maps'ᵉ midᵉ top-rightᵉ bottom-leftᵉ)
  (bottom-right-triangleᵉ :
    coherence-triangle-mapsᵉ bottomᵉ bottom-rightᵉ top-rightᵉ)
  where

  pasting-coherence-squares-collapse-triangles'ᵉ :
    bottom-left-triangleᵉ ∙hᵉ top-right-triangleᵉ ~ᵉ refl-htpyᵉ →
    pasting-vertical-coherence-square-mapsᵉ
      ( topᵉ)
      ( top-leftᵉ)
      ( top-rightᵉ)
      ( midᵉ)
      ( bottom-leftᵉ)
      ( bottom-rightᵉ)
      ( bottomᵉ)
      ( horizontal-pasting-up-diagonal-coherence-triangle-mapsᵉ
        ( topᵉ)
        ( top-leftᵉ)
        ( top-rightᵉ)
        ( midᵉ)
        ( top-left-triangleᵉ)
        ( top-right-triangleᵉ))
      ( horizontal-pasting-up-diagonal-coherence-triangle-mapsᵉ
        ( midᵉ)
        ( bottom-leftᵉ)
        ( bottom-rightᵉ)
        ( bottomᵉ)
        ( bottom-left-triangleᵉ)
        ( bottom-right-triangleᵉ)) ~ᵉ
    horizontal-concat-htpy'ᵉ
      ( bottom-right-triangleᵉ)
      ( top-left-triangleᵉ)
  pasting-coherence-squares-collapse-triangles'ᵉ Hᵉ =
    left-whisker-concat-coherence-square-homotopiesᵉ
      ( bottom-right-triangleᵉ ·rᵉ bottom-leftᵉ ·rᵉ top-leftᵉ)
      ( refl-htpyᵉ)
      ( _)
      ( _)
      ( _)
      ( ( inv-htpyᵉ
          ( distributive-left-whisker-comp-concatᵉ
            ( bottom-rightᵉ)
            ( bottom-left-triangleᵉ ·rᵉ top-leftᵉ)
            ( ( top-right-triangleᵉ ·rᵉ top-leftᵉ) ∙hᵉ
              ( top-rightᵉ ·lᵉ top-left-triangleᵉ)))) ∙hᵉ
        ( left-whisker-comp²ᵉ
          ( bottom-rightᵉ)
          ( inv-htpyᵉ
            ( right-whisker-concat-coherence-triangle-homotopiesᵉ
              ( refl-htpyᵉ)
              ( top-right-triangleᵉ ·rᵉ top-leftᵉ)
              ( bottom-left-triangleᵉ ·rᵉ top-leftᵉ)
              ( inv-htpyᵉ Hᵉ ·rᵉ top-leftᵉ)
              ( top-rightᵉ ·lᵉ top-left-triangleᵉ)))) ∙hᵉ
        ( preserves-comp-left-whisker-compᵉ
          ( bottom-rightᵉ)
          ( top-rightᵉ)
          ( top-left-triangleᵉ))) ∙hᵉ
    ( ap-concat-htpy'ᵉ
      ( (bottom-rightᵉ ∘ᵉ top-rightᵉ) ·lᵉ top-left-triangleᵉ)
      ( right-unit-htpyᵉ))

  pasting-coherence-squares-collapse-trianglesᵉ :
    bottom-left-triangleᵉ ∙hᵉ top-right-triangleᵉ ~ᵉ refl-htpyᵉ →
    pasting-vertical-coherence-square-mapsᵉ
      ( topᵉ)
      ( top-leftᵉ)
      ( top-rightᵉ)
      ( midᵉ)
      ( bottom-leftᵉ)
      ( bottom-rightᵉ)
      ( bottomᵉ)
      ( horizontal-pasting-up-diagonal-coherence-triangle-mapsᵉ
        ( topᵉ)
        ( top-leftᵉ)
        ( top-rightᵉ)
        ( midᵉ)
        ( top-left-triangleᵉ)
        ( top-right-triangleᵉ))
      ( horizontal-pasting-up-diagonal-coherence-triangle-mapsᵉ
        ( midᵉ)
        ( bottom-leftᵉ)
        ( bottom-rightᵉ)
        ( bottomᵉ)
        ( bottom-left-triangleᵉ)
        ( bottom-right-triangleᵉ)) ~ᵉ
    horizontal-concat-htpyᵉ
      ( bottom-right-triangleᵉ)
      ( top-left-triangleᵉ)
  pasting-coherence-squares-collapse-trianglesᵉ Hᵉ =
    ( pasting-coherence-squares-collapse-triangles'ᵉ Hᵉ) ∙hᵉ
    ( coh-horizontal-concat-htpyᵉ
      ( bottom-right-triangleᵉ)
      ( top-left-triangleᵉ))
```