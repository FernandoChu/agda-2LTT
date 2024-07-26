# The flattening lemma for pushouts

```agda
module synthetic-homotopy-theory.flattening-lemma-pushoutsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.commuting-cubes-of-mapsᵉ
open import foundation.commuting-squares-of-mapsᵉ
open import foundation.commuting-triangles-of-mapsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equality-dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-dependent-function-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.span-diagramsᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.universal-property-dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import synthetic-homotopy-theory.cocones-under-spansᵉ
open import synthetic-homotopy-theory.dependent-cocones-under-spansᵉ
open import synthetic-homotopy-theory.dependent-universal-property-pushoutsᵉ
open import synthetic-homotopy-theory.descent-data-pushoutsᵉ
open import synthetic-homotopy-theory.equivalences-descent-data-pushoutsᵉ
open import synthetic-homotopy-theory.universal-property-pushoutsᵉ
```

</details>

## Idea

Theᵉ **flatteningᵉ lemma**ᵉ forᵉ [pushouts](synthetic-homotopy-theory.pushouts.mdᵉ)
statesᵉ thatᵉ pushoutsᵉ commuteᵉ with
[dependentᵉ pairᵉ types](foundation.dependent-pair-types.md).ᵉ Moreᵉ precisely,ᵉ
givenᵉ aᵉ pushoutᵉ squareᵉ

```text
      gᵉ
  Sᵉ ----->ᵉ Bᵉ
  |        |
 f|ᵉ        | jᵉ
  ∨ᵉ      ⌜ᵉ ∨ᵉ
  Aᵉ ----->ᵉ Xᵉ
      iᵉ
```

with homotopyᵉ `Hᵉ : iᵉ ∘ᵉ fᵉ ~ᵉ jᵉ ∘ᵉ g`,ᵉ andᵉ forᵉ anyᵉ typeᵉ familyᵉ `P`ᵉ overᵉ `X`,ᵉ theᵉ
commutingᵉ squareᵉ

```text
  Σᵉ (sᵉ : S),ᵉ P(if(sᵉ)) --->ᵉ Σᵉ (sᵉ : S),ᵉ P(jg(sᵉ)) --->ᵉ Σᵉ (bᵉ : B),ᵉ P(j(bᵉ))
           |                                                 |
           |                                                 |
           ∨ᵉ                                               ⌜ᵉ ∨ᵉ
  Σᵉ (aᵉ : A),ᵉ P(i(aᵉ)) ----------------------------->ᵉ Σᵉ (xᵉ : X),ᵉ P(xᵉ)
```

isᵉ againᵉ aᵉ pushoutᵉ square.ᵉ

## Definitions

### The statement of the flattening lemma for pushouts

```agda
module _
  { l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level} {Sᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ}
  { Xᵉ : UUᵉ l4ᵉ} (Pᵉ : Xᵉ → UUᵉ l5ᵉ)
  ( fᵉ : Sᵉ → Aᵉ) (gᵉ : Sᵉ → Bᵉ) (cᵉ : coconeᵉ fᵉ gᵉ Xᵉ)
  where

  vertical-map-span-flattening-pushoutᵉ :
    Σᵉ Sᵉ (Pᵉ ∘ᵉ horizontal-map-coconeᵉ fᵉ gᵉ cᵉ ∘ᵉ fᵉ) →
    Σᵉ Aᵉ (Pᵉ ∘ᵉ horizontal-map-coconeᵉ fᵉ gᵉ cᵉ)
  vertical-map-span-flattening-pushoutᵉ =
    map-Σ-map-baseᵉ fᵉ (Pᵉ ∘ᵉ horizontal-map-coconeᵉ fᵉ gᵉ cᵉ)

  horizontal-map-span-flattening-pushoutᵉ :
    Σᵉ Sᵉ (Pᵉ ∘ᵉ horizontal-map-coconeᵉ fᵉ gᵉ cᵉ ∘ᵉ fᵉ) →
    Σᵉ Bᵉ (Pᵉ ∘ᵉ vertical-map-coconeᵉ fᵉ gᵉ cᵉ)
  horizontal-map-span-flattening-pushoutᵉ =
    map-Σᵉ
      ( Pᵉ ∘ᵉ vertical-map-coconeᵉ fᵉ gᵉ cᵉ)
      ( gᵉ)
      ( λ sᵉ → trᵉ Pᵉ (coherence-square-coconeᵉ fᵉ gᵉ cᵉ sᵉ))

  horizontal-map-cocone-flattening-pushoutᵉ :
    Σᵉ Aᵉ (Pᵉ ∘ᵉ horizontal-map-coconeᵉ fᵉ gᵉ cᵉ) → Σᵉ Xᵉ Pᵉ
  horizontal-map-cocone-flattening-pushoutᵉ =
    map-Σ-map-baseᵉ (horizontal-map-coconeᵉ fᵉ gᵉ cᵉ) Pᵉ

  vertical-map-cocone-flattening-pushoutᵉ :
    Σᵉ Bᵉ (Pᵉ ∘ᵉ vertical-map-coconeᵉ fᵉ gᵉ cᵉ) → Σᵉ Xᵉ Pᵉ
  vertical-map-cocone-flattening-pushoutᵉ =
    map-Σ-map-baseᵉ (vertical-map-coconeᵉ fᵉ gᵉ cᵉ) Pᵉ

  coherence-square-cocone-flattening-pushoutᵉ :
    coherence-square-mapsᵉ
      ( horizontal-map-span-flattening-pushoutᵉ)
      ( vertical-map-span-flattening-pushoutᵉ)
      ( vertical-map-cocone-flattening-pushoutᵉ)
      ( horizontal-map-cocone-flattening-pushoutᵉ)
  coherence-square-cocone-flattening-pushoutᵉ =
    coherence-square-maps-map-Σ-map-baseᵉ Pᵉ gᵉ fᵉ
      ( vertical-map-coconeᵉ fᵉ gᵉ cᵉ)
      ( horizontal-map-coconeᵉ fᵉ gᵉ cᵉ)
      ( coherence-square-coconeᵉ fᵉ gᵉ cᵉ)

  cocone-flattening-pushoutᵉ :
    coconeᵉ
      ( vertical-map-span-flattening-pushoutᵉ)
      ( horizontal-map-span-flattening-pushoutᵉ)
      ( Σᵉ Xᵉ Pᵉ)
  pr1ᵉ cocone-flattening-pushoutᵉ =
    horizontal-map-cocone-flattening-pushoutᵉ
  pr1ᵉ (pr2ᵉ cocone-flattening-pushoutᵉ) =
    vertical-map-cocone-flattening-pushoutᵉ
  pr2ᵉ (pr2ᵉ cocone-flattening-pushoutᵉ) =
    coherence-square-cocone-flattening-pushoutᵉ

  flattening-lemma-pushout-statementᵉ : UUωᵉ
  flattening-lemma-pushout-statementᵉ =
    universal-property-pushoutᵉ fᵉ gᵉ cᵉ →
    universal-property-pushoutᵉ
      ( vertical-map-span-flattening-pushoutᵉ)
      ( horizontal-map-span-flattening-pushoutᵉ)
      ( cocone-flattening-pushoutᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level} {𝒮ᵉ : span-diagramᵉ l1ᵉ l2ᵉ l3ᵉ}
  {Xᵉ : UUᵉ l4ᵉ} (cᵉ : cocone-span-diagramᵉ 𝒮ᵉ Xᵉ)
  (Pᵉ : Xᵉ → UUᵉ l5ᵉ)
  where

  span-diagram-flattening-pushoutᵉ : span-diagramᵉ (l1ᵉ ⊔ l5ᵉ) (l2ᵉ ⊔ l5ᵉ) (l3ᵉ ⊔ l5ᵉ)
  span-diagram-flattening-pushoutᵉ =
    make-span-diagramᵉ
      ( vertical-map-span-flattening-pushoutᵉ Pᵉ _ _ cᵉ)
      ( horizontal-map-span-flattening-pushoutᵉ Pᵉ _ _ cᵉ)
```

### The statement of the flattening lemma for pushouts, phrased using descent data

Theᵉ aboveᵉ statementᵉ ofᵉ theᵉ flatteningᵉ lemmaᵉ worksᵉ with aᵉ providedᵉ typeᵉ familyᵉ
overᵉ theᵉ pushout.ᵉ Weᵉ canᵉ insteadᵉ acceptᵉ aᵉ definitionᵉ ofᵉ thisᵉ familyᵉ viaᵉ descentᵉ
data forᵉ theᵉ pushout.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {𝒮ᵉ : span-diagramᵉ l1ᵉ l2ᵉ l3ᵉ}
  (Pᵉ : descent-data-pushoutᵉ 𝒮ᵉ l4ᵉ)
  where

  vertical-map-span-flattening-descent-data-pushoutᵉ :
    Σᵉ ( spanning-type-span-diagramᵉ 𝒮ᵉ)
      ( λ sᵉ → pr1ᵉ Pᵉ (left-map-span-diagramᵉ 𝒮ᵉ sᵉ)) →
    Σᵉ ( domain-span-diagramᵉ 𝒮ᵉ) (pr1ᵉ Pᵉ)
  vertical-map-span-flattening-descent-data-pushoutᵉ =
    map-Σ-map-baseᵉ
      ( left-map-span-diagramᵉ 𝒮ᵉ)
      ( pr1ᵉ Pᵉ)

  horizontal-map-span-flattening-descent-data-pushoutᵉ :
    Σᵉ ( spanning-type-span-diagramᵉ 𝒮ᵉ)
      ( λ sᵉ → pr1ᵉ Pᵉ (left-map-span-diagramᵉ 𝒮ᵉ sᵉ)) →
    Σᵉ ( codomain-span-diagramᵉ 𝒮ᵉ) (pr1ᵉ (pr2ᵉ Pᵉ))
  horizontal-map-span-flattening-descent-data-pushoutᵉ =
    map-Σᵉ
      ( pr1ᵉ (pr2ᵉ Pᵉ))
      ( right-map-span-diagramᵉ 𝒮ᵉ)
      ( λ sᵉ → map-equivᵉ (pr2ᵉ (pr2ᵉ Pᵉ) sᵉ))

  span-diagram-flattening-descent-data-pushoutᵉ :
    span-diagramᵉ (l1ᵉ ⊔ l4ᵉ) (l2ᵉ ⊔ l4ᵉ) (l3ᵉ ⊔ l4ᵉ)
  span-diagram-flattening-descent-data-pushoutᵉ =
    make-span-diagramᵉ
      ( vertical-map-span-flattening-descent-data-pushoutᵉ)
      ( horizontal-map-span-flattening-descent-data-pushoutᵉ)

module _
  { l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level} {Sᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ} {Xᵉ : UUᵉ l4ᵉ}
  ( fᵉ : Sᵉ → Aᵉ) (gᵉ : Sᵉ → Bᵉ) (cᵉ : coconeᵉ fᵉ gᵉ Xᵉ)
  ( Pᵉ : descent-data-pushoutᵉ (make-span-diagramᵉ fᵉ gᵉ) l5ᵉ)
  ( Qᵉ : Xᵉ → UUᵉ l5ᵉ)
  ( eᵉ :
    equiv-descent-data-pushoutᵉ Pᵉ (descent-data-family-cocone-span-diagramᵉ cᵉ Qᵉ))
  where

  horizontal-map-cocone-flattening-descent-data-pushoutᵉ :
    Σᵉ Aᵉ (pr1ᵉ Pᵉ) → Σᵉ Xᵉ Qᵉ
  horizontal-map-cocone-flattening-descent-data-pushoutᵉ =
    map-Σᵉ Qᵉ
      ( horizontal-map-coconeᵉ fᵉ gᵉ cᵉ)
      ( λ aᵉ → map-equivᵉ (pr1ᵉ eᵉ aᵉ))

  vertical-map-cocone-flattening-descent-data-pushoutᵉ :
    Σᵉ Bᵉ (pr1ᵉ (pr2ᵉ Pᵉ)) → Σᵉ Xᵉ Qᵉ
  vertical-map-cocone-flattening-descent-data-pushoutᵉ =
    map-Σᵉ Qᵉ
      ( vertical-map-coconeᵉ fᵉ gᵉ cᵉ)
      ( λ bᵉ → map-equivᵉ (pr1ᵉ (pr2ᵉ eᵉ) bᵉ))

  coherence-square-cocone-flattening-descent-data-pushoutᵉ :
    coherence-square-mapsᵉ
      ( horizontal-map-span-flattening-descent-data-pushoutᵉ Pᵉ)
      ( vertical-map-span-flattening-descent-data-pushoutᵉ Pᵉ)
      ( vertical-map-cocone-flattening-descent-data-pushoutᵉ)
      ( horizontal-map-cocone-flattening-descent-data-pushoutᵉ)
  coherence-square-cocone-flattening-descent-data-pushoutᵉ =
    htpy-map-Σᵉ Qᵉ
      ( coherence-square-coconeᵉ fᵉ gᵉ cᵉ)
      ( λ sᵉ → map-equivᵉ (pr1ᵉ eᵉ (fᵉ sᵉ)))
      ( λ sᵉ → inv-htpyᵉ (pr2ᵉ (pr2ᵉ eᵉ) sᵉ))

  cocone-flattening-descent-data-pushoutᵉ :
    coconeᵉ
      ( vertical-map-span-flattening-descent-data-pushoutᵉ Pᵉ)
      ( horizontal-map-span-flattening-descent-data-pushoutᵉ Pᵉ)
      ( Σᵉ Xᵉ Qᵉ)
  pr1ᵉ cocone-flattening-descent-data-pushoutᵉ =
    horizontal-map-cocone-flattening-descent-data-pushoutᵉ
  pr1ᵉ (pr2ᵉ cocone-flattening-descent-data-pushoutᵉ) =
    vertical-map-cocone-flattening-descent-data-pushoutᵉ
  pr2ᵉ (pr2ᵉ cocone-flattening-descent-data-pushoutᵉ) =
    coherence-square-cocone-flattening-descent-data-pushoutᵉ

  flattening-lemma-descent-data-pushout-statementᵉ : UUωᵉ
  flattening-lemma-descent-data-pushout-statementᵉ =
    universal-property-pushoutᵉ fᵉ gᵉ cᵉ →
    universal-property-pushoutᵉ
      ( vertical-map-span-flattening-descent-data-pushoutᵉ Pᵉ)
      ( horizontal-map-span-flattening-descent-data-pushoutᵉ Pᵉ)
      ( cocone-flattening-descent-data-pushoutᵉ)
```

## Properties

### Proof of the flattening lemma for pushouts

Theᵉ proofᵉ usesᵉ theᵉ theoremᵉ thatᵉ mapsᵉ fromᵉ sigmaᵉ typesᵉ areᵉ equivalentᵉ to
dependentᵉ mapsᵉ overᵉ theᵉ indexᵉ type,ᵉ forᵉ whichᵉ weᵉ canᵉ invokeᵉ theᵉ dependentᵉ
universalᵉ propertyᵉ ofᵉ theᵉ indexingᵉ pushout.ᵉ

```agda
module _
  { l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level} {Sᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ}
  { Xᵉ : UUᵉ l4ᵉ} (Pᵉ : Xᵉ → UUᵉ l5ᵉ)
  ( fᵉ : Sᵉ → Aᵉ) (gᵉ : Sᵉ → Bᵉ) (cᵉ : coconeᵉ fᵉ gᵉ Xᵉ)
  where

  cocone-map-flattening-pushoutᵉ :
    { lᵉ : Level} (Yᵉ : UUᵉ lᵉ) →
    ( Σᵉ Xᵉ Pᵉ → Yᵉ) →
    coconeᵉ
      ( vertical-map-span-flattening-pushoutᵉ Pᵉ fᵉ gᵉ cᵉ)
      ( horizontal-map-span-flattening-pushoutᵉ Pᵉ fᵉ gᵉ cᵉ)
      ( Yᵉ)
  cocone-map-flattening-pushoutᵉ Yᵉ =
    cocone-mapᵉ
      ( vertical-map-span-flattening-pushoutᵉ Pᵉ fᵉ gᵉ cᵉ)
      ( horizontal-map-span-flattening-pushoutᵉ Pᵉ fᵉ gᵉ cᵉ)
      ( cocone-flattening-pushoutᵉ Pᵉ fᵉ gᵉ cᵉ)

  comparison-dependent-cocone-ind-Σ-coconeᵉ :
    { lᵉ : Level} (Yᵉ : UUᵉ lᵉ) →
    Σᵉ ( (aᵉ : Aᵉ) → Pᵉ (horizontal-map-coconeᵉ fᵉ gᵉ cᵉ aᵉ) → Yᵉ)
      ( λ kᵉ →
        Σᵉ ( (bᵉ : Bᵉ) → Pᵉ (vertical-map-coconeᵉ fᵉ gᵉ cᵉ bᵉ) → Yᵉ)
          ( λ lᵉ →
            ( sᵉ : Sᵉ) (tᵉ : Pᵉ (horizontal-map-coconeᵉ fᵉ gᵉ cᵉ (fᵉ sᵉ))) →
            ( kᵉ (fᵉ sᵉ) tᵉ) ＝ᵉ
            ( lᵉ (gᵉ sᵉ) (trᵉ Pᵉ (coherence-square-coconeᵉ fᵉ gᵉ cᵉ sᵉ) tᵉ)))) ≃ᵉ
    dependent-coconeᵉ fᵉ gᵉ cᵉ (λ xᵉ → Pᵉ xᵉ → Yᵉ)
  comparison-dependent-cocone-ind-Σ-coconeᵉ Yᵉ =
    equiv-totᵉ
      ( λ kᵉ →
        equiv-totᵉ
          ( λ lᵉ →
            equiv-Π-equiv-familyᵉ
              ( equiv-htpy-dependent-function-dependent-identification-function-typeᵉ
                ( Yᵉ)
                ( coherence-square-coconeᵉ fᵉ gᵉ cᵉ)
                ( kᵉ ∘ᵉ fᵉ)
                ( lᵉ ∘ᵉ gᵉ))))

  triangle-comparison-dependent-cocone-ind-Σ-coconeᵉ :
    { lᵉ : Level} (Yᵉ : UUᵉ lᵉ) →
    coherence-triangle-mapsᵉ
      ( dependent-cocone-mapᵉ fᵉ gᵉ cᵉ (λ xᵉ → Pᵉ xᵉ → Yᵉ))
      ( map-equivᵉ (comparison-dependent-cocone-ind-Σ-coconeᵉ Yᵉ))
      ( map-equivᵉ equiv-ev-pair³ᵉ ∘ᵉ cocone-map-flattening-pushoutᵉ Yᵉ ∘ᵉ ind-Σᵉ)
  triangle-comparison-dependent-cocone-ind-Σ-coconeᵉ Yᵉ hᵉ =
    eq-pair-eq-fiberᵉ
      ( eq-pair-eq-fiberᵉ
        ( eq-htpyᵉ
          ( inv-htpyᵉ
            ( compute-equiv-htpy-dependent-function-dependent-identification-function-typeᵉ
              ( Yᵉ)
              ( coherence-square-coconeᵉ fᵉ gᵉ cᵉ)
              ( hᵉ)))))
  abstract
    flattening-lemma-pushoutᵉ :
      flattening-lemma-pushout-statementᵉ Pᵉ fᵉ gᵉ cᵉ
    flattening-lemma-pushoutᵉ up-cᵉ Yᵉ =
      is-equiv-left-factorᵉ
        ( cocone-map-flattening-pushoutᵉ Yᵉ)
        ( ind-Σᵉ)
        ( is-equiv-right-factorᵉ
          ( map-equivᵉ equiv-ev-pair³ᵉ)
          ( cocone-map-flattening-pushoutᵉ Yᵉ ∘ᵉ ind-Σᵉ)
          ( is-equiv-map-equivᵉ equiv-ev-pair³ᵉ)
          ( is-equiv-top-map-triangleᵉ
            ( dependent-cocone-mapᵉ fᵉ gᵉ cᵉ (λ xᵉ → Pᵉ xᵉ → Yᵉ))
            ( map-equivᵉ (comparison-dependent-cocone-ind-Σ-coconeᵉ Yᵉ))
            ( ( map-equivᵉ equiv-ev-pair³ᵉ) ∘ᵉ
              ( cocone-map-flattening-pushoutᵉ Yᵉ) ∘ᵉ
              ( ind-Σᵉ))
            ( triangle-comparison-dependent-cocone-ind-Σ-coconeᵉ Yᵉ)
            ( is-equiv-map-equivᵉ (comparison-dependent-cocone-ind-Σ-coconeᵉ Yᵉ))
            ( dependent-universal-property-universal-property-pushoutᵉ _ _ _ up-cᵉ
              ( λ xᵉ → Pᵉ xᵉ → Yᵉ))))
        ( is-equiv-ind-Σᵉ)
```

### Proof of the descent data statement of the flattening lemma

Theᵉ proofᵉ isᵉ carriedᵉ outᵉ byᵉ constructingᵉ aᵉ commutingᵉ cube,ᵉ whichᵉ hasᵉ
equivalencesᵉ forᵉ verticalᵉ maps,ᵉ theᵉ `cocone-flattening-pushout`ᵉ squareᵉ forᵉ theᵉ
bottom,ᵉ andᵉ theᵉ `cocone-flattening-descent-data-pushout`ᵉ squareᵉ forᵉ theᵉ top.ᵉ

Theᵉ bottomᵉ isᵉ aᵉ pushoutᵉ byᵉ theᵉ aboveᵉ flatteningᵉ lemma,ᵉ whichᵉ impliesᵉ thatᵉ theᵉ
topᵉ isᵉ alsoᵉ aᵉ pushout.ᵉ

Theᵉ otherᵉ partsᵉ ofᵉ theᵉ cubeᵉ areᵉ definedᵉ naturally,ᵉ andᵉ comeᵉ fromᵉ theᵉ followingᵉ
mapᵉ ofᵉ spansᵉ:

```text
  Σᵉ (aᵉ : Aᵉ) (PAᵉ aᵉ) <-------ᵉ Σᵉ (sᵉ : Sᵉ) (PAᵉ (fᵉ sᵉ)) ----->ᵉ Σᵉ (bᵉ : Bᵉ) (PBᵉ bᵉ)
         |                           |                         |
         |                           |                         |
         ∨ᵉ                           ∨ᵉ                         ∨ᵉ
Σᵉ (aᵉ : Aᵉ) (Pᵉ (iᵉ aᵉ)) <----ᵉ Σᵉ (sᵉ : Sᵉ) (Pᵉ (iᵉ (fᵉ sᵉ))) --->ᵉ Σᵉ (bᵉ : Bᵉ) (Pᵉ (jᵉ bᵉ))
```

where theᵉ verticalᵉ mapsᵉ areᵉ equivalencesᵉ givenᵉ fiberwiseᵉ byᵉ theᵉ equivalenceᵉ ofᵉ
descentᵉ data.ᵉ

```agda
module _
  { l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level} {Sᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ} {Xᵉ : UUᵉ l4ᵉ}
  ( fᵉ : Sᵉ → Aᵉ) (gᵉ : Sᵉ → Bᵉ) (cᵉ : coconeᵉ fᵉ gᵉ Xᵉ)
  ( Pᵉ : descent-data-pushoutᵉ (make-span-diagramᵉ fᵉ gᵉ) l5ᵉ)
  ( Qᵉ : Xᵉ → UUᵉ l5ᵉ)
  ( eᵉ :
    equiv-descent-data-pushoutᵉ Pᵉ (descent-data-family-cocone-span-diagramᵉ cᵉ Qᵉ))
  where

  coherence-cube-flattening-lemma-descent-data-pushoutᵉ :
    coherence-cube-mapsᵉ
      ( vertical-map-span-flattening-pushoutᵉ Qᵉ fᵉ gᵉ cᵉ)
      ( horizontal-map-span-flattening-pushoutᵉ Qᵉ fᵉ gᵉ cᵉ)
      ( horizontal-map-cocone-flattening-pushoutᵉ Qᵉ fᵉ gᵉ cᵉ)
      ( vertical-map-cocone-flattening-pushoutᵉ Qᵉ fᵉ gᵉ cᵉ)
      ( vertical-map-span-flattening-descent-data-pushoutᵉ Pᵉ)
      ( horizontal-map-span-flattening-descent-data-pushoutᵉ Pᵉ)
      ( horizontal-map-cocone-flattening-descent-data-pushoutᵉ fᵉ gᵉ cᵉ Pᵉ Qᵉ eᵉ)
      ( vertical-map-cocone-flattening-descent-data-pushoutᵉ fᵉ gᵉ cᵉ Pᵉ Qᵉ eᵉ)
      ( totᵉ (λ sᵉ → map-equivᵉ (pr1ᵉ eᵉ (fᵉ sᵉ))))
      ( totᵉ (λ aᵉ → map-equivᵉ (pr1ᵉ eᵉ aᵉ)))
      ( totᵉ (λ bᵉ → map-equivᵉ (pr1ᵉ (pr2ᵉ eᵉ) bᵉ)))
      ( idᵉ)
      ( coherence-square-cocone-flattening-descent-data-pushoutᵉ fᵉ gᵉ cᵉ Pᵉ Qᵉ eᵉ)
      ( refl-htpyᵉ)
      ( htpy-map-Σᵉ
        ( Qᵉ ∘ᵉ vertical-map-coconeᵉ fᵉ gᵉ cᵉ)
        ( refl-htpyᵉ)
        ( λ sᵉ →
          trᵉ Qᵉ (coherence-square-coconeᵉ fᵉ gᵉ cᵉ sᵉ) ∘ᵉ (map-equivᵉ (pr1ᵉ eᵉ (fᵉ sᵉ))))
        ( λ sᵉ → inv-htpyᵉ (pr2ᵉ (pr2ᵉ eᵉ) sᵉ)))
      ( refl-htpyᵉ)
      ( refl-htpyᵉ)
      ( coherence-square-cocone-flattening-pushoutᵉ Qᵉ fᵉ gᵉ cᵉ)
  coherence-cube-flattening-lemma-descent-data-pushoutᵉ (sᵉ ,ᵉ tᵉ) =
    ( ap-idᵉ
      ( coherence-square-cocone-flattening-descent-data-pushoutᵉ fᵉ gᵉ cᵉ Pᵉ Qᵉ eᵉ
        ( sᵉ ,ᵉ tᵉ))) ∙ᵉ
    ( triangle-eq-pair-Σᵉ Qᵉ
      ( coherence-square-coconeᵉ fᵉ gᵉ cᵉ sᵉ)
      ( invᵉ (pr2ᵉ (pr2ᵉ eᵉ) sᵉ tᵉ))) ∙ᵉ
    ( apᵉ
      ( eq-pair-Σᵉ (coherence-square-coconeᵉ fᵉ gᵉ cᵉ sᵉ) reflᵉ ∙ᵉ_)
      ( invᵉ
        ( ( right-unitᵉ) ∙ᵉ
          ( compute-ap-map-Σ-map-base-eq-pair-Σᵉ
            ( vertical-map-coconeᵉ fᵉ gᵉ cᵉ)
            ( Qᵉ)
            ( reflᵉ)
            ( invᵉ (pr2ᵉ (pr2ᵉ eᵉ) sᵉ tᵉ))))))

  abstract
    flattening-lemma-descent-data-pushoutᵉ :
      flattening-lemma-descent-data-pushout-statementᵉ fᵉ gᵉ cᵉ Pᵉ Qᵉ eᵉ
    flattening-lemma-descent-data-pushoutᵉ up-cᵉ =
      universal-property-pushout-top-universal-property-pushout-bottom-cube-is-equivᵉ
        ( vertical-map-span-flattening-pushoutᵉ Qᵉ fᵉ gᵉ cᵉ)
        ( horizontal-map-span-flattening-pushoutᵉ Qᵉ fᵉ gᵉ cᵉ)
        ( horizontal-map-cocone-flattening-pushoutᵉ Qᵉ fᵉ gᵉ cᵉ)
        ( vertical-map-cocone-flattening-pushoutᵉ Qᵉ fᵉ gᵉ cᵉ)
        ( vertical-map-span-flattening-descent-data-pushoutᵉ Pᵉ)
        ( horizontal-map-span-flattening-descent-data-pushoutᵉ Pᵉ)
        ( horizontal-map-cocone-flattening-descent-data-pushoutᵉ fᵉ gᵉ cᵉ Pᵉ Qᵉ eᵉ)
        ( vertical-map-cocone-flattening-descent-data-pushoutᵉ fᵉ gᵉ cᵉ Pᵉ Qᵉ eᵉ)
        ( totᵉ (λ sᵉ → map-equivᵉ (pr1ᵉ eᵉ (fᵉ sᵉ))))
        ( totᵉ (λ aᵉ → map-equivᵉ (pr1ᵉ eᵉ aᵉ)))
        ( totᵉ (λ bᵉ → map-equivᵉ (pr1ᵉ (pr2ᵉ eᵉ) bᵉ)))
        ( idᵉ)
        ( coherence-square-cocone-flattening-descent-data-pushoutᵉ fᵉ gᵉ cᵉ Pᵉ Qᵉ eᵉ)
        ( refl-htpyᵉ)
        ( htpy-map-Σᵉ
          ( Qᵉ ∘ᵉ vertical-map-coconeᵉ fᵉ gᵉ cᵉ)
          ( refl-htpyᵉ)
          ( λ sᵉ →
            trᵉ Qᵉ (coherence-square-coconeᵉ fᵉ gᵉ cᵉ sᵉ) ∘ᵉ (map-equivᵉ (pr1ᵉ eᵉ (fᵉ sᵉ))))
          ( λ sᵉ → inv-htpyᵉ (pr2ᵉ (pr2ᵉ eᵉ) sᵉ)))
        ( refl-htpyᵉ)
        ( refl-htpyᵉ)
        ( coherence-square-cocone-flattening-pushoutᵉ Qᵉ fᵉ gᵉ cᵉ)
        ( coherence-cube-flattening-lemma-descent-data-pushoutᵉ)
        ( is-equiv-tot-is-fiberwise-equivᵉ
          ( λ sᵉ → is-equiv-map-equivᵉ (pr1ᵉ eᵉ (fᵉ sᵉ))))
        ( is-equiv-tot-is-fiberwise-equivᵉ
          ( λ aᵉ → is-equiv-map-equivᵉ (pr1ᵉ eᵉ aᵉ)))
        ( is-equiv-tot-is-fiberwise-equivᵉ
          ( λ bᵉ → is-equiv-map-equivᵉ (pr1ᵉ (pr2ᵉ eᵉ) bᵉ)))
        ( is-equiv-idᵉ)
        ( flattening-lemma-pushoutᵉ Qᵉ fᵉ gᵉ cᵉ up-cᵉ)
```