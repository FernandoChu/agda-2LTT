# The flattening lemma for coequalizers

```agda
module synthetic-homotopy-theory.flattening-lemma-coequalizersᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.coproduct-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.double-arrowsᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.type-arithmetic-coproduct-typesᵉ
open import foundation.universe-levelsᵉ

open import synthetic-homotopy-theory.coforksᵉ
open import synthetic-homotopy-theory.dependent-universal-property-coequalizersᵉ
open import synthetic-homotopy-theory.flattening-lemma-pushoutsᵉ
open import synthetic-homotopy-theory.universal-property-coequalizersᵉ
open import synthetic-homotopy-theory.universal-property-pushoutsᵉ
```

</details>

## Idea

Theᵉ
{{#conceptᵉ "flatteningᵉ lemma"ᵉ Disambiguation="coequalizers"ᵉ Agda=flattening-lemma-coequalizerᵉ}}
forᵉ [coequalizers](synthetic-homotopy-theory.coequalizers.mdᵉ) statesᵉ thatᵉ
coequalizersᵉ commuteᵉ with
[dependentᵉ pairᵉ types](foundation.dependent-pair-types.md).ᵉ Moreᵉ precisely,ᵉ
givenᵉ aᵉ coequalizerᵉ

```text
     gᵉ
   ----->ᵉ     eᵉ
 Aᵉ ----->ᵉ Bᵉ ----->ᵉ Xᵉ
     fᵉ
```

with homotopyᵉ `Hᵉ : eᵉ ∘ᵉ fᵉ ~ᵉ eᵉ ∘ᵉ g`,ᵉ andᵉ aᵉ typeᵉ familyᵉ `Pᵉ : Xᵉ → 𝓤`ᵉ overᵉ `X`,ᵉ theᵉ
coforkᵉ

```text
                  ----->ᵉ
 Σᵉ (aᵉ : Aᵉ) P(efaᵉ) ----->ᵉ Σᵉ (bᵉ : Bᵉ) P(ebᵉ) --->ᵉ Σᵉ (xᵉ : Xᵉ) P(xᵉ)
```

isᵉ againᵉ aᵉ coequalizer.ᵉ

## Definitions

### The statement of the flattening lemma for coequalizers

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (aᵉ : double-arrowᵉ l1ᵉ l2ᵉ) {Xᵉ : UUᵉ l3ᵉ}
  (Pᵉ : Xᵉ → UUᵉ l4ᵉ) (eᵉ : coforkᵉ aᵉ Xᵉ)
  where

  left-map-double-arrow-flattening-lemma-coequalizerᵉ :
    Σᵉ (domain-double-arrowᵉ aᵉ) (Pᵉ ∘ᵉ map-coforkᵉ aᵉ eᵉ ∘ᵉ left-map-double-arrowᵉ aᵉ) →
    Σᵉ (codomain-double-arrowᵉ aᵉ) (Pᵉ ∘ᵉ map-coforkᵉ aᵉ eᵉ)
  left-map-double-arrow-flattening-lemma-coequalizerᵉ =
    map-Σ-map-baseᵉ
      ( left-map-double-arrowᵉ aᵉ)
      ( Pᵉ ∘ᵉ map-coforkᵉ aᵉ eᵉ)

  right-map-double-arrow-flattening-lemma-coequalizerᵉ :
    Σᵉ (domain-double-arrowᵉ aᵉ) (Pᵉ ∘ᵉ map-coforkᵉ aᵉ eᵉ ∘ᵉ left-map-double-arrowᵉ aᵉ) →
    Σᵉ (codomain-double-arrowᵉ aᵉ) (Pᵉ ∘ᵉ map-coforkᵉ aᵉ eᵉ)
  right-map-double-arrow-flattening-lemma-coequalizerᵉ =
    map-Σᵉ
      ( Pᵉ ∘ᵉ map-coforkᵉ aᵉ eᵉ)
      ( right-map-double-arrowᵉ aᵉ)
      ( λ xᵉ → trᵉ Pᵉ (coh-coforkᵉ aᵉ eᵉ xᵉ))

  double-arrow-flattening-lemma-coequalizerᵉ : double-arrowᵉ (l1ᵉ ⊔ l4ᵉ) (l2ᵉ ⊔ l4ᵉ)
  double-arrow-flattening-lemma-coequalizerᵉ =
    make-double-arrowᵉ
      ( left-map-double-arrow-flattening-lemma-coequalizerᵉ)
      ( right-map-double-arrow-flattening-lemma-coequalizerᵉ)

  cofork-flattening-lemma-coequalizerᵉ :
    coforkᵉ double-arrow-flattening-lemma-coequalizerᵉ (Σᵉ Xᵉ Pᵉ)
  pr1ᵉ cofork-flattening-lemma-coequalizerᵉ = map-Σ-map-baseᵉ (map-coforkᵉ aᵉ eᵉ) Pᵉ
  pr2ᵉ cofork-flattening-lemma-coequalizerᵉ =
    coherence-square-maps-map-Σ-map-baseᵉ Pᵉ
      ( right-map-double-arrowᵉ aᵉ)
      ( left-map-double-arrowᵉ aᵉ)
      ( map-coforkᵉ aᵉ eᵉ)
      ( map-coforkᵉ aᵉ eᵉ)
      ( coh-coforkᵉ aᵉ eᵉ)

  flattening-lemma-coequalizer-statementᵉ : UUωᵉ
  flattening-lemma-coequalizer-statementᵉ =
    universal-property-coequalizerᵉ aᵉ eᵉ →
    universal-property-coequalizerᵉ
      ( double-arrow-flattening-lemma-coequalizerᵉ)
      ( cofork-flattening-lemma-coequalizerᵉ)
```

## Properties

### Proof of the flattening lemma for coequalizers

Toᵉ showᵉ thatᵉ theᵉ coforkᵉ ofᵉ totalᵉ spacesᵉ isᵉ aᵉ coequalizer,ᵉ itᵉ
[sufficesᵉ to show](synthetic-homotopy-theory.universal-property-coequalizers.mdᵉ)
thatᵉ theᵉ inducedᵉ coconeᵉ isᵉ aᵉ pushout.ᵉ Thisᵉ isᵉ accomplishedᵉ byᵉ constructingᵉ aᵉ
[commutingᵉ cube](foundation.commuting-cubes-of-maps.mdᵉ) where theᵉ bottomᵉ isᵉ thisᵉ
cocone,ᵉ andᵉ theᵉ topᵉ isᵉ theᵉ coconeᵉ ofᵉ totalᵉ spacesᵉ forᵉ theᵉ coconeᵉ inducedᵉ byᵉ theᵉ
cofork.ᵉ

Assumingᵉ thatᵉ theᵉ givenᵉ coforkᵉ isᵉ aᵉ coequalizer,ᵉ weᵉ getᵉ thatᵉ itsᵉ inducedᵉ coconeᵉ
isᵉ aᵉ pushout,ᵉ soᵉ byᵉ theᵉ
[flatteningᵉ lemmaᵉ forᵉ pushouts](synthetic-homotopy-theory.flattening-lemma-pushouts.md),ᵉ
theᵉ topᵉ squareᵉ isᵉ aᵉ pushoutᵉ asᵉ well.ᵉ Theᵉ verticalᵉ mapsᵉ ofᵉ theᵉ cubeᵉ areᵉ
[equivalences](foundation.equivalences.md),ᵉ soᵉ itᵉ followsᵉ thatᵉ theᵉ bottomᵉ squareᵉ
isᵉ aᵉ pushout.ᵉ

```agda
module _
  { l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (aᵉ : double-arrowᵉ l1ᵉ l2ᵉ) {Xᵉ : UUᵉ l3ᵉ}
  ( Pᵉ : Xᵉ → UUᵉ l4ᵉ) (eᵉ : coforkᵉ aᵉ Xᵉ)
  where

  abstract
    flattening-lemma-coequalizerᵉ : flattening-lemma-coequalizer-statementᵉ aᵉ Pᵉ eᵉ
    flattening-lemma-coequalizerᵉ up-eᵉ =
      universal-property-coequalizer-universal-property-pushoutᵉ
        ( double-arrow-flattening-lemma-coequalizerᵉ aᵉ Pᵉ eᵉ)
        ( cofork-flattening-lemma-coequalizerᵉ aᵉ Pᵉ eᵉ)
        ( universal-property-pushout-bottom-universal-property-pushout-top-cube-is-equivᵉ
          ( vertical-map-span-cocone-coforkᵉ
            ( double-arrow-flattening-lemma-coequalizerᵉ aᵉ Pᵉ eᵉ))
          ( horizontal-map-span-cocone-coforkᵉ
            ( double-arrow-flattening-lemma-coequalizerᵉ aᵉ Pᵉ eᵉ))
          ( horizontal-map-cocone-flattening-pushoutᵉ Pᵉ
            ( vertical-map-span-cocone-coforkᵉ aᵉ)
            ( horizontal-map-span-cocone-coforkᵉ aᵉ)
            ( cocone-codiagonal-coforkᵉ aᵉ eᵉ))
          ( vertical-map-cocone-flattening-pushoutᵉ Pᵉ
            ( vertical-map-span-cocone-coforkᵉ aᵉ)
            ( horizontal-map-span-cocone-coforkᵉ aᵉ)
            ( cocone-codiagonal-coforkᵉ aᵉ eᵉ))
          ( vertical-map-span-flattening-pushoutᵉ Pᵉ
            ( vertical-map-span-cocone-coforkᵉ aᵉ)
            ( horizontal-map-span-cocone-coforkᵉ aᵉ)
            ( cocone-codiagonal-coforkᵉ aᵉ eᵉ))
          ( horizontal-map-span-flattening-pushoutᵉ Pᵉ
            ( vertical-map-span-cocone-coforkᵉ aᵉ)
            ( horizontal-map-span-cocone-coforkᵉ aᵉ)
            ( cocone-codiagonal-coforkᵉ aᵉ eᵉ))
          ( horizontal-map-cocone-flattening-pushoutᵉ Pᵉ
            ( vertical-map-span-cocone-coforkᵉ aᵉ)
            ( horizontal-map-span-cocone-coforkᵉ aᵉ)
            ( cocone-codiagonal-coforkᵉ aᵉ eᵉ))
          ( vertical-map-cocone-flattening-pushoutᵉ Pᵉ
            ( vertical-map-span-cocone-coforkᵉ aᵉ)
            ( horizontal-map-span-cocone-coforkᵉ aᵉ)
            ( cocone-codiagonal-coforkᵉ aᵉ eᵉ))
          ( map-equivᵉ
            ( right-distributive-Σ-coproductᵉ
              ( domain-double-arrowᵉ aᵉ)
              ( domain-double-arrowᵉ aᵉ)
              ( ( Pᵉ) ∘ᵉ
                ( horizontal-map-cocone-coforkᵉ aᵉ eᵉ) ∘ᵉ
                ( vertical-map-span-cocone-coforkᵉ aᵉ))))
          ( idᵉ)
          ( idᵉ)
          ( idᵉ)
          ( coherence-square-cocone-flattening-pushoutᵉ Pᵉ
            ( vertical-map-span-cocone-coforkᵉ aᵉ)
            ( horizontal-map-span-cocone-coforkᵉ aᵉ)
            ( cocone-codiagonal-coforkᵉ aᵉ eᵉ))
          ( ind-Σᵉ (ind-coproductᵉ _ (ev-pairᵉ refl-htpyᵉ) (ev-pairᵉ refl-htpyᵉ)))
          ( ind-Σᵉ (ind-coproductᵉ _ (ev-pairᵉ refl-htpyᵉ) (ev-pairᵉ refl-htpyᵉ)))
          ( refl-htpyᵉ)
          ( refl-htpyᵉ)
          ( coherence-square-cocone-coforkᵉ
            ( double-arrow-flattening-lemma-coequalizerᵉ aᵉ Pᵉ eᵉ)
            ( cofork-flattening-lemma-coequalizerᵉ aᵉ Pᵉ eᵉ))
          ( ind-Σᵉ
            ( ind-coproductᵉ _
              ( ev-pairᵉ refl-htpyᵉ)
              ( ev-pairᵉ (λ tᵉ → ap-idᵉ _ ∙ᵉ invᵉ right-unitᵉ))))
          ( is-equiv-map-equivᵉ
            ( right-distributive-Σ-coproductᵉ
              ( domain-double-arrowᵉ aᵉ)
              ( domain-double-arrowᵉ aᵉ)
              ( ( Pᵉ) ∘ᵉ
                ( horizontal-map-cocone-coforkᵉ aᵉ eᵉ) ∘ᵉ
                ( vertical-map-span-cocone-coforkᵉ aᵉ))))
          ( is-equiv-idᵉ)
          ( is-equiv-idᵉ)
          ( is-equiv-idᵉ)
          ( flattening-lemma-pushoutᵉ Pᵉ
            ( vertical-map-span-cocone-coforkᵉ aᵉ)
            ( horizontal-map-span-cocone-coforkᵉ aᵉ)
            ( cocone-codiagonal-coforkᵉ aᵉ eᵉ)
            ( universal-property-pushout-universal-property-coequalizerᵉ aᵉ eᵉ
              ( up-eᵉ))))
```