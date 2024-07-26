# The universal property of coequalizers

```agda
module synthetic-homotopy-theory.universal-property-coequalizersᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-cubes-of-mapsᵉ
open import foundation.commuting-squares-of-mapsᵉ
open import foundation.contractible-mapsᵉ
open import foundation.contractible-typesᵉ
open import foundation.coproduct-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.double-arrowsᵉ
open import foundation.equivalencesᵉ
open import foundation.equivalences-double-arrowsᵉ
open import foundation.fibers-of-mapsᵉ
open import foundation.functoriality-coproduct-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.universe-levelsᵉ

open import synthetic-homotopy-theory.cocones-under-spansᵉ
open import synthetic-homotopy-theory.coforksᵉ
open import synthetic-homotopy-theory.equivalences-coforks-under-equivalences-double-arrowsᵉ
open import synthetic-homotopy-theory.universal-property-pushoutsᵉ
```

</details>

## Idea

Givenᵉ aᵉ [doubleᵉ arrow](foundation.double-arrows.mdᵉ) `f,ᵉ gᵉ : Aᵉ → B`,ᵉ considerᵉ aᵉ
[cofork](synthetic-homotopy-theory.coforks.mdᵉ) `eᵉ : Bᵉ → X`ᵉ with vertexᵉ `X`.ᵉ Theᵉ
**universalᵉ propertyᵉ ofᵉ coequalizers**ᵉ isᵉ theᵉ statementᵉ thatᵉ theᵉ coforkᵉ
postcompositionᵉ mapᵉ

```text
cofork-mapᵉ : (Xᵉ → Yᵉ) → coforkᵉ Yᵉ
```

isᵉ anᵉ [equivalence](foundation.equivalences.md).ᵉ

## Definitions

### The universal property of coequalizers

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (aᵉ : double-arrowᵉ l1ᵉ l2ᵉ) {Xᵉ : UUᵉ l3ᵉ}
  (eᵉ : coforkᵉ aᵉ Xᵉ)
  where

  universal-property-coequalizerᵉ : UUωᵉ
  universal-property-coequalizerᵉ =
    {lᵉ : Level} (Yᵉ : UUᵉ lᵉ) → is-equivᵉ (cofork-mapᵉ aᵉ eᵉ {Yᵉ = Yᵉ})

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (aᵉ : double-arrowᵉ l1ᵉ l2ᵉ) {Xᵉ : UUᵉ l3ᵉ}
  (eᵉ : coforkᵉ aᵉ Xᵉ) {Yᵉ : UUᵉ l4ᵉ}
  (up-coequalizerᵉ : universal-property-coequalizerᵉ aᵉ eᵉ)
  where

  map-universal-property-coequalizerᵉ : coforkᵉ aᵉ Yᵉ → (Xᵉ → Yᵉ)
  map-universal-property-coequalizerᵉ = map-inv-is-equivᵉ (up-coequalizerᵉ Yᵉ)
```

## Properties

### The mediating map obtained by the universal property is unique

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (aᵉ : double-arrowᵉ l1ᵉ l2ᵉ) {Xᵉ : UUᵉ l3ᵉ}
  (eᵉ : coforkᵉ aᵉ Xᵉ) {Yᵉ : UUᵉ l4ᵉ}
  (up-coequalizerᵉ : universal-property-coequalizerᵉ aᵉ eᵉ)
  (e'ᵉ : coforkᵉ aᵉ Yᵉ)
  where

  htpy-cofork-map-universal-property-coequalizerᵉ :
    htpy-coforkᵉ aᵉ
      ( cofork-mapᵉ aᵉ eᵉ
        ( map-universal-property-coequalizerᵉ aᵉ eᵉ up-coequalizerᵉ e'ᵉ))
      ( e'ᵉ)
  htpy-cofork-map-universal-property-coequalizerᵉ =
    htpy-cofork-eqᵉ aᵉ
      ( cofork-mapᵉ aᵉ eᵉ
        ( map-universal-property-coequalizerᵉ aᵉ eᵉ up-coequalizerᵉ e'ᵉ))
      ( e'ᵉ)
      ( is-section-map-inv-is-equivᵉ (up-coequalizerᵉ Yᵉ) e'ᵉ)

  abstract
    uniqueness-map-universal-property-coequalizerᵉ :
      is-contrᵉ (Σᵉ (Xᵉ → Yᵉ) (λ hᵉ → htpy-coforkᵉ aᵉ (cofork-mapᵉ aᵉ eᵉ hᵉ) e'ᵉ))
    uniqueness-map-universal-property-coequalizerᵉ =
      is-contr-is-equiv'ᵉ
        ( fiberᵉ (cofork-mapᵉ aᵉ eᵉ) e'ᵉ)
        ( totᵉ (λ hᵉ → htpy-cofork-eqᵉ aᵉ (cofork-mapᵉ aᵉ eᵉ hᵉ) e'ᵉ))
        ( is-equiv-tot-is-fiberwise-equivᵉ
          ( λ hᵉ → is-equiv-htpy-cofork-eqᵉ aᵉ (cofork-mapᵉ aᵉ eᵉ hᵉ) e'ᵉ))
        ( is-contr-map-is-equivᵉ (up-coequalizerᵉ Yᵉ) e'ᵉ)
```

### A cofork has the universal property of coequalizers if and only if the corresponding cocone has the universal property of pushouts

Asᵉ mentionedᵉ in [`coforks`](synthetic-homotopy-theory.coforks.md),ᵉ coforksᵉ canᵉ
beᵉ thoughtᵉ ofᵉ asᵉ specialᵉ casesᵉ ofᵉ coconesᵉ underᵉ spans.ᵉ Thisᵉ theoremᵉ makesᵉ itᵉ
moreᵉ precise,ᵉ assertingᵉ thatᵉ underᵉ thisᵉ mapping,ᵉ
[coequalizers](synthetic-homotopy-theory.coequalizers.mdᵉ) correspondᵉ to
[pushouts](synthetic-homotopy-theory.pushouts.md).ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (aᵉ : double-arrowᵉ l1ᵉ l2ᵉ) {Xᵉ : UUᵉ l3ᵉ}
  (eᵉ : coforkᵉ aᵉ Xᵉ)
  where

  universal-property-coequalizer-universal-property-pushoutᵉ :
    universal-property-pushoutᵉ
      ( vertical-map-span-cocone-coforkᵉ aᵉ)
      ( horizontal-map-span-cocone-coforkᵉ aᵉ)
      ( cocone-codiagonal-coforkᵉ aᵉ eᵉ) →
      universal-property-coequalizerᵉ aᵉ eᵉ
  universal-property-coequalizer-universal-property-pushoutᵉ up-pushoutᵉ Yᵉ =
    is-equiv-left-map-triangleᵉ
      ( cofork-mapᵉ aᵉ eᵉ)
      ( cofork-cocone-codiagonalᵉ aᵉ)
      ( cocone-mapᵉ
        ( vertical-map-span-cocone-coforkᵉ aᵉ)
        ( horizontal-map-span-cocone-coforkᵉ aᵉ)
        ( cocone-codiagonal-coforkᵉ aᵉ eᵉ))
      ( triangle-cofork-coconeᵉ aᵉ eᵉ)
      ( up-pushoutᵉ Yᵉ)
      ( is-equiv-cofork-cocone-codiagonalᵉ aᵉ)

  universal-property-pushout-universal-property-coequalizerᵉ :
    universal-property-coequalizerᵉ aᵉ eᵉ →
    universal-property-pushoutᵉ
      ( vertical-map-span-cocone-coforkᵉ aᵉ)
      ( horizontal-map-span-cocone-coforkᵉ aᵉ)
      ( cocone-codiagonal-coforkᵉ aᵉ eᵉ)
  universal-property-pushout-universal-property-coequalizerᵉ up-coequalizerᵉ Yᵉ =
    is-equiv-top-map-triangleᵉ
      ( cofork-mapᵉ aᵉ eᵉ)
      ( cofork-cocone-codiagonalᵉ aᵉ)
      ( cocone-mapᵉ
        ( vertical-map-span-cocone-coforkᵉ aᵉ)
        ( horizontal-map-span-cocone-coforkᵉ aᵉ)
        ( cocone-codiagonal-coforkᵉ aᵉ eᵉ))
      ( triangle-cofork-coconeᵉ aᵉ eᵉ)
      ( is-equiv-cofork-cocone-codiagonalᵉ aᵉ)
      ( up-coequalizerᵉ Yᵉ)
```

### In an equivalence of coforks, one cofork is a coequalizer if and only if the other is

Inᵉ otherᵉ words,ᵉ givenᵉ twoᵉ coforksᵉ connectedᵉ verticallyᵉ with equivalences,ᵉ asᵉ in
theᵉ followingᵉ diagramᵉ:

Givenᵉ anᵉ
[equivalenceᵉ ofᵉ coforks](synthetic-homotopy-theory.equivalences-coforks-under-equivalences-double-arrows.mdᵉ)
betweenᵉ coforksᵉ `c`ᵉ andᵉ `c'`ᵉ

```text
           ≃ᵉ
     Aᵉ -------->ᵉ A'ᵉ
    | |         | |
  fᵉ | | gᵉ    f'ᵉ | | g'ᵉ
    | |         | |
    ∨ᵉ ∨ᵉ         ∨ᵉ ∨ᵉ
     Bᵉ -------->ᵉ B'ᵉ
     |     ≃ᵉ     |
   cᵉ |           | c'ᵉ
     |           |
     ∨ᵉ           ∨ᵉ
     Xᵉ -------->ᵉ Yᵉ ,ᵉ
           ≃ᵉ
```

weᵉ haveᵉ thatᵉ theᵉ leftᵉ coforkᵉ isᵉ aᵉ coequalizerᵉ ifᵉ andᵉ onlyᵉ ifᵉ theᵉ rightᵉ coforkᵉ isᵉ
aᵉ coequalizer.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level}
  {aᵉ : double-arrowᵉ l1ᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} (cᵉ : coforkᵉ aᵉ Xᵉ)
  {a'ᵉ : double-arrowᵉ l4ᵉ l5ᵉ} {Yᵉ : UUᵉ l6ᵉ} (c'ᵉ : coforkᵉ a'ᵉ Yᵉ)
  (eᵉ : equiv-double-arrowᵉ aᵉ a'ᵉ) (e'ᵉ : equiv-cofork-equiv-double-arrowᵉ cᵉ c'ᵉ eᵉ)
  where

  universal-property-coequalizer-equiv-cofork-equiv-double-arrowᵉ :
    universal-property-coequalizerᵉ a'ᵉ c'ᵉ →
    universal-property-coequalizerᵉ aᵉ cᵉ
  universal-property-coequalizer-equiv-cofork-equiv-double-arrowᵉ up-c'ᵉ =
    universal-property-coequalizer-universal-property-pushoutᵉ aᵉ cᵉ
      ( universal-property-pushout-top-universal-property-pushout-bottom-cube-is-equivᵉ
        ( vertical-map-span-cocone-coforkᵉ a'ᵉ)
        ( horizontal-map-span-cocone-coforkᵉ a'ᵉ)
        ( horizontal-map-cocone-coforkᵉ a'ᵉ c'ᵉ)
        ( vertical-map-cocone-coforkᵉ a'ᵉ c'ᵉ)
        ( vertical-map-span-cocone-coforkᵉ aᵉ)
        ( horizontal-map-span-cocone-coforkᵉ aᵉ)
        ( horizontal-map-cocone-coforkᵉ aᵉ cᵉ)
        ( vertical-map-cocone-coforkᵉ aᵉ cᵉ)
        ( spanning-map-hom-span-diagram-cofork-hom-double-arrowᵉ aᵉ a'ᵉ
          ( hom-equiv-double-arrowᵉ aᵉ a'ᵉ eᵉ))
        ( domain-map-equiv-double-arrowᵉ aᵉ a'ᵉ eᵉ)
        ( codomain-map-equiv-double-arrowᵉ aᵉ a'ᵉ eᵉ)
        ( map-equiv-cofork-equiv-double-arrowᵉ cᵉ c'ᵉ eᵉ e'ᵉ)
        ( coherence-square-cocone-coforkᵉ aᵉ cᵉ)
        ( inv-htpyᵉ
          ( left-square-hom-span-diagram-cofork-hom-double-arrowᵉ aᵉ a'ᵉ
            ( hom-equiv-double-arrowᵉ aᵉ a'ᵉ eᵉ)))
        ( inv-htpyᵉ
          ( right-square-hom-span-diagram-cofork-hom-double-arrowᵉ aᵉ a'ᵉ
            ( hom-equiv-double-arrowᵉ aᵉ a'ᵉ eᵉ)))
        ( inv-htpyᵉ
          ( pasting-vertical-coherence-square-mapsᵉ
            ( domain-map-equiv-double-arrowᵉ aᵉ a'ᵉ eᵉ)
            ( left-map-double-arrowᵉ aᵉ)
            ( left-map-double-arrowᵉ a'ᵉ)
            ( codomain-map-equiv-double-arrowᵉ aᵉ a'ᵉ eᵉ)
            ( map-coforkᵉ aᵉ cᵉ)
            ( map-coforkᵉ a'ᵉ c'ᵉ)
            ( map-equiv-cofork-equiv-double-arrowᵉ cᵉ c'ᵉ eᵉ e'ᵉ)
            ( left-square-equiv-double-arrowᵉ aᵉ a'ᵉ eᵉ)
            ( coh-map-cofork-equiv-cofork-equiv-double-arrowᵉ cᵉ c'ᵉ eᵉ e'ᵉ)))
        ( inv-htpyᵉ (coh-map-cofork-equiv-cofork-equiv-double-arrowᵉ cᵉ c'ᵉ eᵉ e'ᵉ))
        ( coherence-square-cocone-coforkᵉ a'ᵉ c'ᵉ)
        ( coherence-cube-maps-rotate-120ᵉ
          ( horizontal-map-cocone-coforkᵉ aᵉ cᵉ)
          ( domain-map-equiv-double-arrowᵉ aᵉ a'ᵉ eᵉ)
          ( map-equiv-cofork-equiv-double-arrowᵉ cᵉ c'ᵉ eᵉ e'ᵉ)
          ( horizontal-map-cocone-coforkᵉ a'ᵉ c'ᵉ)
          ( horizontal-map-span-cocone-coforkᵉ aᵉ)
          ( spanning-map-hom-span-diagram-cofork-hom-double-arrowᵉ aᵉ a'ᵉ
            ( hom-equiv-double-arrowᵉ aᵉ a'ᵉ eᵉ))
          ( codomain-map-equiv-double-arrowᵉ aᵉ a'ᵉ eᵉ)
          ( horizontal-map-span-cocone-coforkᵉ a'ᵉ)
          ( vertical-map-span-cocone-coforkᵉ aᵉ)
          ( vertical-map-cocone-coforkᵉ aᵉ cᵉ)
          ( vertical-map-span-cocone-coforkᵉ a'ᵉ)
          ( vertical-map-cocone-coforkᵉ a'ᵉ c'ᵉ)
          ( right-square-hom-span-diagram-cofork-hom-double-arrowᵉ aᵉ a'ᵉ
            ( hom-equiv-double-arrowᵉ aᵉ a'ᵉ eᵉ))
          ( coherence-square-cocone-coforkᵉ aᵉ cᵉ)
          ( left-square-hom-span-diagram-cofork-hom-double-arrowᵉ aᵉ a'ᵉ
            ( hom-equiv-double-arrowᵉ aᵉ a'ᵉ eᵉ))
          ( coh-map-cofork-equiv-cofork-equiv-double-arrowᵉ cᵉ c'ᵉ eᵉ e'ᵉ)
          ( coherence-square-cocone-coforkᵉ a'ᵉ c'ᵉ)
          ( pasting-vertical-coherence-square-mapsᵉ
            ( domain-map-equiv-double-arrowᵉ aᵉ a'ᵉ eᵉ)
            ( left-map-double-arrowᵉ aᵉ)
            ( left-map-double-arrowᵉ a'ᵉ)
            ( codomain-map-equiv-double-arrowᵉ aᵉ a'ᵉ eᵉ)
            ( map-coforkᵉ aᵉ cᵉ)
            ( map-coforkᵉ a'ᵉ c'ᵉ)
            ( map-equiv-cofork-equiv-double-arrowᵉ cᵉ c'ᵉ eᵉ e'ᵉ)
            ( left-square-equiv-double-arrowᵉ aᵉ a'ᵉ eᵉ)
            ( coh-map-cofork-equiv-cofork-equiv-double-arrowᵉ cᵉ c'ᵉ eᵉ e'ᵉ))
          ( inv-htpyᵉ
            ( ind-coproductᵉ _
              ( right-unit-htpyᵉ)
              ( coh-equiv-cofork-equiv-double-arrowᵉ cᵉ c'ᵉ eᵉ e'ᵉ))))
        ( is-equiv-map-coproductᵉ
          ( is-equiv-domain-map-equiv-double-arrowᵉ aᵉ a'ᵉ eᵉ)
          ( is-equiv-domain-map-equiv-double-arrowᵉ aᵉ a'ᵉ eᵉ))
        ( is-equiv-domain-map-equiv-double-arrowᵉ aᵉ a'ᵉ eᵉ)
        ( is-equiv-codomain-map-equiv-double-arrowᵉ aᵉ a'ᵉ eᵉ)
        ( is-equiv-map-equiv-cofork-equiv-double-arrowᵉ cᵉ c'ᵉ eᵉ e'ᵉ)
        ( universal-property-pushout-universal-property-coequalizerᵉ a'ᵉ c'ᵉ
          ( up-c'ᵉ)))

  universal-property-coequalizer-equiv-cofork-equiv-double-arrow'ᵉ :
    universal-property-coequalizerᵉ aᵉ cᵉ →
    universal-property-coequalizerᵉ a'ᵉ c'ᵉ
  universal-property-coequalizer-equiv-cofork-equiv-double-arrow'ᵉ up-cᵉ =
    universal-property-coequalizer-universal-property-pushoutᵉ a'ᵉ c'ᵉ
      ( universal-property-pushout-bottom-universal-property-pushout-top-cube-is-equivᵉ
        ( vertical-map-span-cocone-coforkᵉ a'ᵉ)
        ( horizontal-map-span-cocone-coforkᵉ a'ᵉ)
        ( horizontal-map-cocone-coforkᵉ a'ᵉ c'ᵉ)
        ( vertical-map-cocone-coforkᵉ a'ᵉ c'ᵉ)
        ( vertical-map-span-cocone-coforkᵉ aᵉ)
        ( horizontal-map-span-cocone-coforkᵉ aᵉ)
        ( horizontal-map-cocone-coforkᵉ aᵉ cᵉ)
        ( vertical-map-cocone-coforkᵉ aᵉ cᵉ)
        ( spanning-map-hom-span-diagram-cofork-hom-double-arrowᵉ aᵉ a'ᵉ
          ( hom-equiv-double-arrowᵉ aᵉ a'ᵉ eᵉ))
        ( domain-map-equiv-double-arrowᵉ aᵉ a'ᵉ eᵉ)
        ( codomain-map-equiv-double-arrowᵉ aᵉ a'ᵉ eᵉ)
        ( map-equiv-cofork-equiv-double-arrowᵉ cᵉ c'ᵉ eᵉ e'ᵉ)
        ( coherence-square-cocone-coforkᵉ aᵉ cᵉ)
        ( inv-htpyᵉ
          ( left-square-hom-span-diagram-cofork-hom-double-arrowᵉ aᵉ a'ᵉ
            ( hom-equiv-double-arrowᵉ aᵉ a'ᵉ eᵉ)))
        ( inv-htpyᵉ
          ( right-square-hom-span-diagram-cofork-hom-double-arrowᵉ aᵉ a'ᵉ
            ( hom-equiv-double-arrowᵉ aᵉ a'ᵉ eᵉ)))
        ( inv-htpyᵉ
          ( pasting-vertical-coherence-square-mapsᵉ
            ( domain-map-equiv-double-arrowᵉ aᵉ a'ᵉ eᵉ)
            ( left-map-double-arrowᵉ aᵉ)
            ( left-map-double-arrowᵉ a'ᵉ)
            ( codomain-map-equiv-double-arrowᵉ aᵉ a'ᵉ eᵉ)
            ( map-coforkᵉ aᵉ cᵉ)
            ( map-coforkᵉ a'ᵉ c'ᵉ)
            ( map-equiv-cofork-equiv-double-arrowᵉ cᵉ c'ᵉ eᵉ e'ᵉ)
            ( left-square-equiv-double-arrowᵉ aᵉ a'ᵉ eᵉ)
            ( coh-map-cofork-equiv-cofork-equiv-double-arrowᵉ cᵉ c'ᵉ eᵉ e'ᵉ)))
        ( inv-htpyᵉ (coh-map-cofork-equiv-cofork-equiv-double-arrowᵉ cᵉ c'ᵉ eᵉ e'ᵉ))
        ( coherence-square-cocone-coforkᵉ a'ᵉ c'ᵉ)
        ( coherence-cube-maps-rotate-120ᵉ
          ( horizontal-map-cocone-coforkᵉ aᵉ cᵉ)
          ( domain-map-equiv-double-arrowᵉ aᵉ a'ᵉ eᵉ)
          ( map-equiv-cofork-equiv-double-arrowᵉ cᵉ c'ᵉ eᵉ e'ᵉ)
          ( horizontal-map-cocone-coforkᵉ a'ᵉ c'ᵉ)
          ( horizontal-map-span-cocone-coforkᵉ aᵉ)
          ( spanning-map-hom-span-diagram-cofork-hom-double-arrowᵉ aᵉ a'ᵉ
            ( hom-equiv-double-arrowᵉ aᵉ a'ᵉ eᵉ))
          ( codomain-map-equiv-double-arrowᵉ aᵉ a'ᵉ eᵉ)
          ( horizontal-map-span-cocone-coforkᵉ a'ᵉ)
          ( vertical-map-span-cocone-coforkᵉ aᵉ)
          ( vertical-map-cocone-coforkᵉ aᵉ cᵉ)
          ( vertical-map-span-cocone-coforkᵉ a'ᵉ)
          ( vertical-map-cocone-coforkᵉ a'ᵉ c'ᵉ)
          ( right-square-hom-span-diagram-cofork-hom-double-arrowᵉ aᵉ a'ᵉ
            ( hom-equiv-double-arrowᵉ aᵉ a'ᵉ eᵉ))
          ( coherence-square-cocone-coforkᵉ aᵉ cᵉ)
          ( left-square-hom-span-diagram-cofork-hom-double-arrowᵉ aᵉ a'ᵉ
            ( hom-equiv-double-arrowᵉ aᵉ a'ᵉ eᵉ))
          ( coh-map-cofork-equiv-cofork-equiv-double-arrowᵉ cᵉ c'ᵉ eᵉ e'ᵉ)
          ( coherence-square-cocone-coforkᵉ a'ᵉ c'ᵉ)
          ( pasting-vertical-coherence-square-mapsᵉ
            ( domain-map-equiv-double-arrowᵉ aᵉ a'ᵉ eᵉ)
            ( left-map-double-arrowᵉ aᵉ)
            ( left-map-double-arrowᵉ a'ᵉ)
            ( codomain-map-equiv-double-arrowᵉ aᵉ a'ᵉ eᵉ)
            ( map-coforkᵉ aᵉ cᵉ)
            ( map-coforkᵉ a'ᵉ c'ᵉ)
            ( map-equiv-cofork-equiv-double-arrowᵉ cᵉ c'ᵉ eᵉ e'ᵉ)
            ( left-square-equiv-double-arrowᵉ aᵉ a'ᵉ eᵉ)
            ( coh-map-cofork-equiv-cofork-equiv-double-arrowᵉ cᵉ c'ᵉ eᵉ e'ᵉ))
          ( inv-htpyᵉ
            ( ind-coproductᵉ _
              ( right-unit-htpyᵉ)
              ( coh-equiv-cofork-equiv-double-arrowᵉ cᵉ c'ᵉ eᵉ e'ᵉ))))
        ( is-equiv-map-coproductᵉ
          ( is-equiv-domain-map-equiv-double-arrowᵉ aᵉ a'ᵉ eᵉ)
          ( is-equiv-domain-map-equiv-double-arrowᵉ aᵉ a'ᵉ eᵉ))
        ( is-equiv-domain-map-equiv-double-arrowᵉ aᵉ a'ᵉ eᵉ)
        ( is-equiv-codomain-map-equiv-double-arrowᵉ aᵉ a'ᵉ eᵉ)
        ( is-equiv-map-equiv-cofork-equiv-double-arrowᵉ cᵉ c'ᵉ eᵉ e'ᵉ)
        ( universal-property-pushout-universal-property-coequalizerᵉ aᵉ cᵉ up-cᵉ))
```