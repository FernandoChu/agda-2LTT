# Pullbacks

```agda
module foundation.pullbacksᵉ where

open import foundation-core.pullbacksᵉ public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.commuting-cubes-of-mapsᵉ
open import foundation.cones-over-cospan-diagramsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.dependent-sums-pullbacksᵉ
open import foundation.descent-equivalencesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.functoriality-coproduct-typesᵉ
open import foundation.functoriality-function-typesᵉ
open import foundation.standard-pullbacksᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ

open import foundation-core.cartesian-product-typesᵉ
open import foundation-core.constant-mapsᵉ
open import foundation-core.contractible-typesᵉ
open import foundation-core.diagonal-maps-cartesian-products-of-typesᵉ
open import foundation-core.equality-dependent-pair-typesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.functoriality-dependent-function-typesᵉ
open import foundation-core.functoriality-dependent-pair-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.postcomposition-functionsᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.retractionsᵉ
open import foundation-core.sectionsᵉ
open import foundation-core.torsorial-type-familiesᵉ
open import foundation-core.transport-along-identificationsᵉ
open import foundation-core.whiskering-identifications-concatenationᵉ
```

</details>

## Idea

Considerᵉ aᵉ [cone](foundation.cones-over-cospan-diagrams.mdᵉ) overᵉ aᵉ
[cospanᵉ diagramᵉ ofᵉ types](foundation.cospan-diagrams.mdᵉ) `fᵉ : Aᵉ ->ᵉ Xᵉ <-ᵉ Bᵉ : g,`ᵉ

```text
  Cᵉ ------>ᵉ Bᵉ
  |         |
  |         | gᵉ
  ∨ᵉ         ∨ᵉ
  Aᵉ ------>ᵉ X.ᵉ
       fᵉ
```

weᵉ wantᵉ to poseᵉ theᵉ questionᵉ ofᵉ whetherᵉ thisᵉ coneᵉ isᵉ aᵉ
{{#conceptᵉ "pullbackᵉ cone"ᵉ Disambiguation="types"ᵉ Agda=is-pullback}}.ᵉ Althoughᵉ
thisᵉ conceptᵉ isᵉ capturedᵉ byᵉ
[theᵉ universalᵉ propertyᵉ ofᵉ theᵉ pullback](foundation-core.universal-property-pullbacks.md),ᵉ
thisᵉ isᵉ aᵉ largeᵉ proposition,ᵉ whichᵉ isᵉ notᵉ suitableᵉ forᵉ allᵉ purposes.ᵉ Therefore,ᵉ
asᵉ ourᵉ mainᵉ definitionᵉ ofᵉ aᵉ pullbackᵉ coneᵉ weᵉ considerᵉ theᵉ
{{#conceptᵉ "smallᵉ predicateᵉ ofᵉ beingᵉ aᵉ pullback"ᵉ Agda=is-pullbackᵉ}}: givenᵉ theᵉ
existenceᵉ ofᵉ theᵉ [standardᵉ pullbackᵉ type](foundation.standard-pullbacks.mdᵉ)
`Aᵉ ×_Xᵉ B`,ᵉ aᵉ coneᵉ isᵉ aᵉ _pullbackᵉ_ ifᵉ theᵉ gapᵉ mapᵉ intoᵉ theᵉ standardᵉ pullbackᵉ isᵉ
anᵉ [equivalence](foundation-core.equivalences.md).ᵉ

## Properties

### Being a pullback is a property

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Cᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ)
  where

  is-prop-is-pullbackᵉ : (cᵉ : coneᵉ fᵉ gᵉ Cᵉ) → is-propᵉ (is-pullbackᵉ fᵉ gᵉ cᵉ)
  is-prop-is-pullbackᵉ cᵉ = is-property-is-equivᵉ (gapᵉ fᵉ gᵉ cᵉ)

  is-pullback-Propᵉ : (cᵉ : coneᵉ fᵉ gᵉ Cᵉ) → Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  pr1ᵉ (is-pullback-Propᵉ cᵉ) = is-pullbackᵉ fᵉ gᵉ cᵉ
  pr2ᵉ (is-pullback-Propᵉ cᵉ) = is-prop-is-pullbackᵉ cᵉ
```

### In a commuting cube where the front faces are pullbacks, either back face is a pullback iff the other back face is

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l1'ᵉ l2'ᵉ l3'ᵉ l4'ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} {Dᵉ : UUᵉ l4ᵉ}
  {fᵉ : Aᵉ → Bᵉ} {gᵉ : Aᵉ → Cᵉ} {hᵉ : Bᵉ → Dᵉ} {kᵉ : Cᵉ → Dᵉ}
  {A'ᵉ : UUᵉ l1'ᵉ} {B'ᵉ : UUᵉ l2'ᵉ} {C'ᵉ : UUᵉ l3'ᵉ} {D'ᵉ : UUᵉ l4'ᵉ}
  {f'ᵉ : A'ᵉ → B'ᵉ} {g'ᵉ : A'ᵉ → C'ᵉ} {h'ᵉ : B'ᵉ → D'ᵉ} {k'ᵉ : C'ᵉ → D'ᵉ}
  {hAᵉ : A'ᵉ → Aᵉ} {hBᵉ : B'ᵉ → Bᵉ} {hCᵉ : C'ᵉ → Cᵉ} {hDᵉ : D'ᵉ → Dᵉ}
  (topᵉ : h'ᵉ ∘ᵉ f'ᵉ ~ᵉ k'ᵉ ∘ᵉ g'ᵉ)
  (back-leftᵉ : fᵉ ∘ᵉ hAᵉ ~ᵉ hBᵉ ∘ᵉ f'ᵉ)
  (back-rightᵉ : gᵉ ∘ᵉ hAᵉ ~ᵉ hCᵉ ∘ᵉ g'ᵉ)
  (front-leftᵉ : hᵉ ∘ᵉ hBᵉ ~ᵉ hDᵉ ∘ᵉ h'ᵉ)
  (front-rightᵉ : kᵉ ∘ᵉ hCᵉ ~ᵉ hDᵉ ∘ᵉ k'ᵉ)
  (bottomᵉ : hᵉ ∘ᵉ fᵉ ~ᵉ kᵉ ∘ᵉ gᵉ)
  (cᵉ :
    coherence-cube-mapsᵉ
      fᵉ gᵉ hᵉ kᵉ f'ᵉ g'ᵉ h'ᵉ k'ᵉ hAᵉ hBᵉ hCᵉ hDᵉ
      topᵉ back-leftᵉ back-rightᵉ front-leftᵉ front-rightᵉ bottomᵉ)
  where

  is-pullback-back-left-is-pullback-back-right-cubeᵉ :
    is-pullbackᵉ hᵉ hDᵉ (hBᵉ ,ᵉ h'ᵉ ,ᵉ front-leftᵉ) →
    is-pullbackᵉ kᵉ hDᵉ (hCᵉ ,ᵉ k'ᵉ ,ᵉ front-rightᵉ) →
    is-pullbackᵉ gᵉ hCᵉ (hAᵉ ,ᵉ g'ᵉ ,ᵉ back-rightᵉ) →
    is-pullbackᵉ fᵉ hBᵉ (hAᵉ ,ᵉ f'ᵉ ,ᵉ back-leftᵉ)
  is-pullback-back-left-is-pullback-back-right-cubeᵉ
    is-pb-front-leftᵉ is-pb-front-rightᵉ is-pb-back-rightᵉ =
    is-pullback-left-square-is-pullback-rectangleᵉ fᵉ hᵉ hDᵉ
      ( hBᵉ ,ᵉ h'ᵉ ,ᵉ front-leftᵉ)
      ( hAᵉ ,ᵉ f'ᵉ ,ᵉ back-leftᵉ)
      ( is-pb-front-leftᵉ)
      ( is-pullback-htpyᵉ
        ( bottomᵉ)
        ( refl-htpyᵉ)
        ( tripleᵉ
          ( hAᵉ)
          ( k'ᵉ ∘ᵉ g'ᵉ)
          ( rectangle-right-cubeᵉ
            fᵉ gᵉ hᵉ kᵉ f'ᵉ g'ᵉ h'ᵉ k'ᵉ hAᵉ hBᵉ hCᵉ hDᵉ
            topᵉ back-leftᵉ back-rightᵉ front-leftᵉ front-rightᵉ bottomᵉ))
        ( tripleᵉ
          ( refl-htpyᵉ)
          ( topᵉ)
          ( coherence-htpy-parallel-cone-rectangle-left-rectangle-right-cubeᵉ
            fᵉ gᵉ hᵉ kᵉ f'ᵉ g'ᵉ h'ᵉ k'ᵉ hAᵉ hBᵉ hCᵉ hDᵉ
            topᵉ back-leftᵉ back-rightᵉ front-leftᵉ front-rightᵉ bottomᵉ cᵉ))
        ( is-pullback-rectangle-is-pullback-left-squareᵉ gᵉ kᵉ hDᵉ
          ( hCᵉ ,ᵉ k'ᵉ ,ᵉ front-rightᵉ)
          ( hAᵉ ,ᵉ g'ᵉ ,ᵉ back-rightᵉ)
          ( is-pb-front-rightᵉ)
          ( is-pb-back-rightᵉ)))

  is-pullback-back-right-is-pullback-back-left-cubeᵉ :
    is-pullbackᵉ hᵉ hDᵉ (hBᵉ ,ᵉ h'ᵉ ,ᵉ front-leftᵉ) →
    is-pullbackᵉ kᵉ hDᵉ (hCᵉ ,ᵉ k'ᵉ ,ᵉ front-rightᵉ) →
    is-pullbackᵉ fᵉ hBᵉ (hAᵉ ,ᵉ f'ᵉ ,ᵉ back-leftᵉ) →
    is-pullbackᵉ gᵉ hCᵉ (hAᵉ ,ᵉ g'ᵉ ,ᵉ back-rightᵉ)
  is-pullback-back-right-is-pullback-back-left-cubeᵉ
    is-pb-front-leftᵉ is-pb-front-rightᵉ is-pb-back-leftᵉ =
    is-pullback-left-square-is-pullback-rectangleᵉ gᵉ kᵉ hDᵉ
      ( hCᵉ ,ᵉ k'ᵉ ,ᵉ front-rightᵉ)
      ( hAᵉ ,ᵉ g'ᵉ ,ᵉ back-rightᵉ)
      ( is-pb-front-rightᵉ)
      ( is-pullback-htpy'ᵉ
        ( bottomᵉ)
        ( refl-htpyᵉ)
        ( tripleᵉ
          ( hAᵉ)
          ( h'ᵉ ∘ᵉ f'ᵉ)
          ( rectangle-left-cubeᵉ
            fᵉ gᵉ hᵉ kᵉ f'ᵉ g'ᵉ h'ᵉ k'ᵉ hAᵉ hBᵉ hCᵉ hDᵉ
            topᵉ back-leftᵉ back-rightᵉ front-leftᵉ front-rightᵉ bottomᵉ))
        ( tripleᵉ
          ( refl-htpyᵉ)
          ( topᵉ)
          ( coherence-htpy-parallel-cone-rectangle-left-rectangle-right-cubeᵉ
            fᵉ gᵉ hᵉ kᵉ f'ᵉ g'ᵉ h'ᵉ k'ᵉ hAᵉ hBᵉ hCᵉ hDᵉ
            topᵉ back-leftᵉ back-rightᵉ front-leftᵉ front-rightᵉ bottomᵉ cᵉ))
        ( is-pullback-rectangle-is-pullback-left-squareᵉ fᵉ hᵉ hDᵉ
          ( hBᵉ ,ᵉ h'ᵉ ,ᵉ front-leftᵉ)
          ( hAᵉ ,ᵉ f'ᵉ ,ᵉ back-leftᵉ)
          ( is-pb-front-leftᵉ)
          ( is-pb-back-leftᵉ)))
```

### In a commuting cube where the vertical maps are equivalences, the bottom square is a pullback if and only if the top square is a pullback

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l1'ᵉ l2'ᵉ l3'ᵉ l4'ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} {Dᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Aᵉ → Cᵉ) (hᵉ : Bᵉ → Dᵉ) (kᵉ : Cᵉ → Dᵉ)
  {A'ᵉ : UUᵉ l1'ᵉ} {B'ᵉ : UUᵉ l2'ᵉ} {C'ᵉ : UUᵉ l3'ᵉ} {D'ᵉ : UUᵉ l4'ᵉ}
  (f'ᵉ : A'ᵉ → B'ᵉ) (g'ᵉ : A'ᵉ → C'ᵉ) (h'ᵉ : B'ᵉ → D'ᵉ) (k'ᵉ : C'ᵉ → D'ᵉ)
  (hAᵉ : A'ᵉ → Aᵉ) (hBᵉ : B'ᵉ → Bᵉ) (hCᵉ : C'ᵉ → Cᵉ) (hDᵉ : D'ᵉ → Dᵉ)
  (topᵉ : h'ᵉ ∘ᵉ f'ᵉ ~ᵉ k'ᵉ ∘ᵉ g'ᵉ)
  (back-leftᵉ : fᵉ ∘ᵉ hAᵉ ~ᵉ hBᵉ ∘ᵉ f'ᵉ)
  (back-rightᵉ : gᵉ ∘ᵉ hAᵉ ~ᵉ hCᵉ ∘ᵉ g'ᵉ)
  (front-leftᵉ : hᵉ ∘ᵉ hBᵉ ~ᵉ hDᵉ ∘ᵉ h'ᵉ)
  (front-rightᵉ : kᵉ ∘ᵉ hCᵉ ~ᵉ hDᵉ ∘ᵉ k'ᵉ)
  (bottomᵉ : hᵉ ∘ᵉ fᵉ ~ᵉ kᵉ ∘ᵉ gᵉ)
  (cᵉ :
    coherence-cube-mapsᵉ
      fᵉ gᵉ hᵉ kᵉ f'ᵉ g'ᵉ h'ᵉ k'ᵉ hAᵉ hBᵉ hCᵉ hDᵉ
      topᵉ back-leftᵉ back-rightᵉ front-leftᵉ front-rightᵉ bottomᵉ)
  where

  is-pullback-bottom-is-pullback-top-cube-is-equivᵉ :
    is-equivᵉ hAᵉ → is-equivᵉ hBᵉ → is-equivᵉ hCᵉ → is-equivᵉ hDᵉ →
    is-pullbackᵉ h'ᵉ k'ᵉ (f'ᵉ ,ᵉ g'ᵉ ,ᵉ topᵉ) →
    is-pullbackᵉ hᵉ kᵉ (fᵉ ,ᵉ gᵉ ,ᵉ bottomᵉ)
  is-pullback-bottom-is-pullback-top-cube-is-equivᵉ
    is-equiv-hAᵉ is-equiv-hBᵉ is-equiv-hCᵉ is-equiv-hDᵉ is-pb-topᵉ =
    descent-is-equivᵉ hBᵉ hᵉ kᵉ
      ( fᵉ ,ᵉ gᵉ ,ᵉ bottomᵉ)
      ( f'ᵉ ,ᵉ hAᵉ ,ᵉ inv-htpyᵉ (back-leftᵉ))
      ( is-equiv-hBᵉ)
      ( is-equiv-hAᵉ)
      ( is-pullback-htpyᵉ
        ( front-leftᵉ)
        ( refl-htpy'ᵉ kᵉ)
        ( tripleᵉ
          ( f'ᵉ)
          ( hCᵉ ∘ᵉ g'ᵉ)
          ( rectangle-top-front-right-cubeᵉ
            fᵉ gᵉ hᵉ kᵉ f'ᵉ g'ᵉ h'ᵉ k'ᵉ hAᵉ hBᵉ hCᵉ hDᵉ
            topᵉ back-leftᵉ back-rightᵉ front-leftᵉ front-rightᵉ bottomᵉ))
        ( tripleᵉ
          ( refl-htpy'ᵉ f'ᵉ)
          ( back-rightᵉ)
          ( coherence-htpy-parallel-cone-coherence-cube-mapsᵉ
            fᵉ gᵉ hᵉ kᵉ f'ᵉ g'ᵉ h'ᵉ k'ᵉ hAᵉ hBᵉ hCᵉ hDᵉ
            topᵉ back-leftᵉ back-rightᵉ front-leftᵉ front-rightᵉ bottomᵉ cᵉ))
        ( is-pullback-rectangle-is-pullback-left-squareᵉ
          ( h'ᵉ)
          ( hDᵉ)
          ( kᵉ)
          ( k'ᵉ ,ᵉ hCᵉ ,ᵉ inv-htpyᵉ front-rightᵉ)
          ( f'ᵉ ,ᵉ g'ᵉ ,ᵉ topᵉ)
          ( is-pullback-is-equiv-horizontal-mapsᵉ hDᵉ kᵉ
            ( k'ᵉ ,ᵉ hCᵉ ,ᵉ inv-htpyᵉ front-rightᵉ)
            ( is-equiv-hDᵉ)
            ( is-equiv-hCᵉ))
          ( is-pb-topᵉ)))

  is-pullback-top-is-pullback-bottom-cube-is-equivᵉ :
    is-equivᵉ hAᵉ → is-equivᵉ hBᵉ → is-equivᵉ hCᵉ → is-equivᵉ hDᵉ →
    is-pullbackᵉ hᵉ kᵉ (fᵉ ,ᵉ gᵉ ,ᵉ bottomᵉ) →
    is-pullbackᵉ h'ᵉ k'ᵉ (f'ᵉ ,ᵉ g'ᵉ ,ᵉ topᵉ)
  is-pullback-top-is-pullback-bottom-cube-is-equivᵉ
    is-equiv-hAᵉ is-equiv-hBᵉ is-equiv-hCᵉ is-equiv-hDᵉ is-pb-bottomᵉ =
    is-pullback-top-square-is-pullback-rectangleᵉ hᵉ hDᵉ k'ᵉ
      ( hBᵉ ,ᵉ h'ᵉ ,ᵉ front-leftᵉ)
      ( f'ᵉ ,ᵉ g'ᵉ ,ᵉ topᵉ)
      ( is-pullback-is-equiv-vertical-mapsᵉ hᵉ hDᵉ
        ( hBᵉ ,ᵉ h'ᵉ ,ᵉ front-leftᵉ)
        is-equiv-hDᵉ is-equiv-hBᵉ)
      ( is-pullback-htpy'ᵉ refl-htpyᵉ front-rightᵉ
        ( pasting-vertical-coneᵉ hᵉ kᵉ hCᵉ
          ( fᵉ ,ᵉ gᵉ ,ᵉ bottomᵉ)
          ( hAᵉ ,ᵉ g'ᵉ ,ᵉ back-rightᵉ))
        ( tripleᵉ
          ( back-leftᵉ)
          ( refl-htpyᵉ)
          ( ( assoc-htpyᵉ
              ( bottomᵉ ·rᵉ hAᵉ)
              ( kᵉ ·lᵉ back-rightᵉ)
              ( front-rightᵉ ·rᵉ g'ᵉ)) ∙hᵉ
            ( inv-htpyᵉ cᵉ) ∙hᵉ
            ( assoc-htpyᵉ (hᵉ ·lᵉ back-leftᵉ) (front-leftᵉ ·rᵉ f'ᵉ) (hDᵉ ·lᵉ topᵉ)) ∙hᵉ
            ( ap-concat-htpy'ᵉ
              ( (front-leftᵉ ·rᵉ f'ᵉ) ∙hᵉ (hDᵉ ·lᵉ topᵉ))
              ( inv-htpy-right-unit-htpyᵉ {Hᵉ = hᵉ ·lᵉ back-leftᵉ}))))
        ( is-pullback-rectangle-is-pullback-top-squareᵉ hᵉ kᵉ hCᵉ
          ( fᵉ ,ᵉ gᵉ ,ᵉ bottomᵉ)
          ( hAᵉ ,ᵉ g'ᵉ ,ᵉ back-rightᵉ)
          ( is-pb-bottomᵉ)
          ( is-pullback-is-equiv-vertical-mapsᵉ gᵉ hCᵉ
            ( hAᵉ ,ᵉ g'ᵉ ,ᵉ back-rightᵉ)
            is-equiv-hCᵉ is-equiv-hAᵉ)))
```

### In a commuting cube where the maps from back-right to front-left are equivalences, the back-right square is a pullback if and only if the front-left square is a pullback

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l1'ᵉ l2'ᵉ l3'ᵉ l4'ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} {Dᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Aᵉ → Cᵉ) (hᵉ : Bᵉ → Dᵉ) (kᵉ : Cᵉ → Dᵉ)
  {A'ᵉ : UUᵉ l1'ᵉ} {B'ᵉ : UUᵉ l2'ᵉ} {C'ᵉ : UUᵉ l3'ᵉ} {D'ᵉ : UUᵉ l4'ᵉ}
  (f'ᵉ : A'ᵉ → B'ᵉ) (g'ᵉ : A'ᵉ → C'ᵉ) (h'ᵉ : B'ᵉ → D'ᵉ) (k'ᵉ : C'ᵉ → D'ᵉ)
  (hAᵉ : A'ᵉ → Aᵉ) (hBᵉ : B'ᵉ → Bᵉ) (hCᵉ : C'ᵉ → Cᵉ) (hDᵉ : D'ᵉ → Dᵉ)
  (topᵉ : h'ᵉ ∘ᵉ f'ᵉ ~ᵉ k'ᵉ ∘ᵉ g'ᵉ)
  (back-leftᵉ : fᵉ ∘ᵉ hAᵉ ~ᵉ hBᵉ ∘ᵉ f'ᵉ)
  (back-rightᵉ : gᵉ ∘ᵉ hAᵉ ~ᵉ hCᵉ ∘ᵉ g'ᵉ)
  (front-leftᵉ : hᵉ ∘ᵉ hBᵉ ~ᵉ hDᵉ ∘ᵉ h'ᵉ)
  (front-rightᵉ : kᵉ ∘ᵉ hCᵉ ~ᵉ hDᵉ ∘ᵉ k'ᵉ)
  (bottomᵉ : hᵉ ∘ᵉ fᵉ ~ᵉ kᵉ ∘ᵉ gᵉ)
  (cᵉ :
    coherence-cube-mapsᵉ
      fᵉ gᵉ hᵉ kᵉ f'ᵉ g'ᵉ h'ᵉ k'ᵉ hAᵉ hBᵉ hCᵉ hDᵉ
      topᵉ back-leftᵉ back-rightᵉ front-leftᵉ front-rightᵉ bottomᵉ)
  where

  is-pullback-front-left-is-pullback-back-right-cube-is-equivᵉ :
    is-equivᵉ f'ᵉ → is-equivᵉ fᵉ → is-equivᵉ k'ᵉ → is-equivᵉ kᵉ →
    is-pullbackᵉ gᵉ hCᵉ (hAᵉ ,ᵉ g'ᵉ ,ᵉ back-rightᵉ) →
    is-pullbackᵉ hᵉ hDᵉ (hBᵉ ,ᵉ h'ᵉ ,ᵉ front-leftᵉ)
  is-pullback-front-left-is-pullback-back-right-cube-is-equivᵉ
    is-equiv-f'ᵉ is-equiv-fᵉ is-equiv-k'ᵉ is-equiv-kᵉ is-pb-back-rightᵉ =
    is-pullback-bottom-is-pullback-top-cube-is-equivᵉ
      hBᵉ h'ᵉ hᵉ hDᵉ hAᵉ g'ᵉ gᵉ hCᵉ f'ᵉ fᵉ k'ᵉ kᵉ
      back-rightᵉ (inv-htpyᵉ back-leftᵉ) topᵉ bottomᵉ (inv-htpyᵉ front-rightᵉ)
      ( front-leftᵉ)
      ( coherence-cube-maps-mirror-Bᵉ fᵉ gᵉ hᵉ kᵉ f'ᵉ g'ᵉ h'ᵉ k'ᵉ hAᵉ hBᵉ hCᵉ hDᵉ topᵉ
        back-leftᵉ back-rightᵉ front-leftᵉ front-rightᵉ bottomᵉ cᵉ)
      is-equiv-f'ᵉ is-equiv-fᵉ is-equiv-k'ᵉ is-equiv-kᵉ is-pb-back-rightᵉ

  is-pullback-front-right-is-pullback-back-left-cube-is-equivᵉ :
    is-equivᵉ g'ᵉ → is-equivᵉ h'ᵉ → is-equivᵉ gᵉ → is-equivᵉ hᵉ →
    is-pullbackᵉ fᵉ hBᵉ (hAᵉ ,ᵉ f'ᵉ ,ᵉ back-leftᵉ) →
    is-pullbackᵉ kᵉ hDᵉ (hCᵉ ,ᵉ k'ᵉ ,ᵉ front-rightᵉ)
  is-pullback-front-right-is-pullback-back-left-cube-is-equivᵉ
    is-equiv-g'ᵉ is-equiv-h'ᵉ is-equiv-gᵉ is-equiv-hᵉ is-pb-back-leftᵉ =
    is-pullback-bottom-is-pullback-top-cube-is-equivᵉ
      hCᵉ k'ᵉ kᵉ hDᵉ hAᵉ f'ᵉ fᵉ hBᵉ g'ᵉ gᵉ h'ᵉ hᵉ
      back-leftᵉ (inv-htpyᵉ back-rightᵉ) (inv-htpyᵉ topᵉ)
      ( inv-htpyᵉ bottomᵉ) (inv-htpyᵉ front-leftᵉ) front-rightᵉ
      ( coherence-cube-maps-rotate-120ᵉ fᵉ gᵉ hᵉ kᵉ f'ᵉ g'ᵉ h'ᵉ k'ᵉ hAᵉ hBᵉ hCᵉ hDᵉ
        topᵉ back-leftᵉ back-rightᵉ front-leftᵉ front-rightᵉ bottomᵉ cᵉ)
      is-equiv-g'ᵉ is-equiv-gᵉ is-equiv-h'ᵉ is-equiv-hᵉ is-pb-back-leftᵉ
```

### Identity types commute with pullbacks

Givenᵉ aᵉ pullbackᵉ squareᵉ

```text
         f'ᵉ
    Cᵉ ------->ᵉ Bᵉ
    | ⌟ᵉ        |
  g'|ᵉ          | gᵉ
    ∨ᵉ          ∨ᵉ
    Aᵉ ------->ᵉ Xᵉ
         fᵉ
```

andᵉ twoᵉ elementsᵉ `u`ᵉ andᵉ `v`ᵉ ofᵉ `C`,ᵉ thenᵉ theᵉ inducedᵉ squareᵉ

```text
                apᵉ f'ᵉ
     (uᵉ ＝ᵉ vᵉ) -------->ᵉ (f'ᵉ uᵉ ＝ᵉ f'ᵉ vᵉ)
        |                     |
  apᵉ g'ᵉ |                     |
        ∨ᵉ                     ∨ᵉ
  (g'ᵉ uᵉ ＝ᵉ g'ᵉ vᵉ) ->ᵉ (fᵉ (g'ᵉ uᵉ) ＝ᵉ gᵉ (f'ᵉ vᵉ))
```

isᵉ alsoᵉ aᵉ pullback.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Cᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Xᵉ) (gᵉ : Bᵉ → Xᵉ) (cᵉ : coneᵉ fᵉ gᵉ Cᵉ)
  where

  cone-apᵉ :
    (uᵉ vᵉ : Cᵉ) →
    coneᵉ
      ( λ (αᵉ : vertical-map-coneᵉ fᵉ gᵉ cᵉ uᵉ ＝ᵉ vertical-map-coneᵉ fᵉ gᵉ cᵉ vᵉ) →
        apᵉ fᵉ αᵉ ∙ᵉ coherence-square-coneᵉ fᵉ gᵉ cᵉ vᵉ)
      ( λ (βᵉ : horizontal-map-coneᵉ fᵉ gᵉ cᵉ uᵉ ＝ᵉ horizontal-map-coneᵉ fᵉ gᵉ cᵉ vᵉ) →
        coherence-square-coneᵉ fᵉ gᵉ cᵉ uᵉ ∙ᵉ apᵉ gᵉ βᵉ)
      ( uᵉ ＝ᵉ vᵉ)
  pr1ᵉ (cone-apᵉ uᵉ vᵉ) = apᵉ (vertical-map-coneᵉ fᵉ gᵉ cᵉ)
  pr1ᵉ (pr2ᵉ (cone-apᵉ uᵉ vᵉ)) = apᵉ (horizontal-map-coneᵉ fᵉ gᵉ cᵉ)
  pr2ᵉ (pr2ᵉ (cone-apᵉ uᵉ vᵉ)) γᵉ =
    ( right-whisker-concatᵉ
      ( invᵉ (ap-compᵉ fᵉ (vertical-map-coneᵉ fᵉ gᵉ cᵉ) γᵉ))
      ( coherence-square-coneᵉ fᵉ gᵉ cᵉ vᵉ)) ∙ᵉ
    ( ( inv-nat-htpyᵉ (coherence-square-coneᵉ fᵉ gᵉ cᵉ) γᵉ) ∙ᵉ
      ( left-whisker-concatᵉ
        ( coherence-square-coneᵉ fᵉ gᵉ cᵉ uᵉ)
        ( ap-compᵉ gᵉ (horizontal-map-coneᵉ fᵉ gᵉ cᵉ) γᵉ)))

  cone-ap'ᵉ :
    (uᵉ vᵉ : Cᵉ) →
    coneᵉ
      ( λ (αᵉ : vertical-map-coneᵉ fᵉ gᵉ cᵉ uᵉ ＝ᵉ vertical-map-coneᵉ fᵉ gᵉ cᵉ vᵉ) →
        trᵉ
          ( fᵉ (vertical-map-coneᵉ fᵉ gᵉ cᵉ uᵉ) ＝ᵉ_)
          ( coherence-square-coneᵉ fᵉ gᵉ cᵉ vᵉ)
          ( apᵉ fᵉ αᵉ))
      ( λ (βᵉ : horizontal-map-coneᵉ fᵉ gᵉ cᵉ uᵉ ＝ᵉ horizontal-map-coneᵉ fᵉ gᵉ cᵉ vᵉ) →
        coherence-square-coneᵉ fᵉ gᵉ cᵉ uᵉ ∙ᵉ apᵉ gᵉ βᵉ)
      ( uᵉ ＝ᵉ vᵉ)
  pr1ᵉ (cone-ap'ᵉ uᵉ vᵉ) = apᵉ (vertical-map-coneᵉ fᵉ gᵉ cᵉ)
  pr1ᵉ (pr2ᵉ (cone-ap'ᵉ uᵉ vᵉ)) = apᵉ (horizontal-map-coneᵉ fᵉ gᵉ cᵉ)
  pr2ᵉ (pr2ᵉ (cone-ap'ᵉ uᵉ vᵉ)) γᵉ =
    ( tr-Id-rightᵉ
      ( coherence-square-coneᵉ fᵉ gᵉ cᵉ vᵉ)
      ( apᵉ fᵉ (apᵉ (vertical-map-coneᵉ fᵉ gᵉ cᵉ) γᵉ))) ∙ᵉ
    ( ( right-whisker-concatᵉ
        ( invᵉ (ap-compᵉ fᵉ (vertical-map-coneᵉ fᵉ gᵉ cᵉ) γᵉ))
        ( coherence-square-coneᵉ fᵉ gᵉ cᵉ vᵉ)) ∙ᵉ
      ( ( inv-nat-htpyᵉ (coherence-square-coneᵉ fᵉ gᵉ cᵉ) γᵉ) ∙ᵉ
        ( left-whisker-concatᵉ
          ( coherence-square-coneᵉ fᵉ gᵉ cᵉ uᵉ)
          ( ap-compᵉ gᵉ (horizontal-map-coneᵉ fᵉ gᵉ cᵉ) γᵉ))))

  abstract
    is-pullback-cone-apᵉ :
      is-pullbackᵉ fᵉ gᵉ cᵉ →
      (uᵉ vᵉ : Cᵉ) →
      is-pullbackᵉ
        ( λ (αᵉ : vertical-map-coneᵉ fᵉ gᵉ cᵉ uᵉ ＝ᵉ vertical-map-coneᵉ fᵉ gᵉ cᵉ vᵉ) →
          apᵉ fᵉ αᵉ ∙ᵉ coherence-square-coneᵉ fᵉ gᵉ cᵉ vᵉ)
        ( λ (βᵉ : horizontal-map-coneᵉ fᵉ gᵉ cᵉ uᵉ ＝ᵉ horizontal-map-coneᵉ fᵉ gᵉ cᵉ vᵉ) →
          coherence-square-coneᵉ fᵉ gᵉ cᵉ uᵉ ∙ᵉ apᵉ gᵉ βᵉ)
        ( cone-apᵉ uᵉ vᵉ)
    is-pullback-cone-apᵉ is-pb-cᵉ uᵉ vᵉ =
      is-pullback-htpy'ᵉ
        ( λ αᵉ → tr-Id-rightᵉ (coherence-square-coneᵉ fᵉ gᵉ cᵉ vᵉ) (apᵉ fᵉ αᵉ))
        ( refl-htpyᵉ)
        ( cone-ap'ᵉ uᵉ vᵉ)
        ( refl-htpyᵉ ,ᵉ refl-htpyᵉ ,ᵉ right-unit-htpyᵉ)
        ( is-pullback-family-is-pullback-totᵉ
          ( fᵉ (vertical-map-coneᵉ fᵉ gᵉ cᵉ uᵉ) ＝ᵉ_)
          ( λ aᵉ → apᵉ fᵉ {xᵉ = vertical-map-coneᵉ fᵉ gᵉ cᵉ uᵉ} {yᵉ = aᵉ})
          ( λ bᵉ βᵉ → coherence-square-coneᵉ fᵉ gᵉ cᵉ uᵉ ∙ᵉ apᵉ gᵉ βᵉ)
          ( cᵉ)
          ( cone-ap'ᵉ uᵉ)
          ( is-pb-cᵉ)
          ( is-pullback-is-equiv-vertical-mapsᵉ
            ( map-Σᵉ _ fᵉ (λ aᵉ αᵉ → apᵉ fᵉ αᵉ))
            ( map-Σᵉ _ gᵉ (λ bᵉ βᵉ → coherence-square-coneᵉ fᵉ gᵉ cᵉ uᵉ ∙ᵉ apᵉ gᵉ βᵉ))
            ( tot-cone-cone-familyᵉ
              ( fᵉ (vertical-map-coneᵉ fᵉ gᵉ cᵉ uᵉ) ＝ᵉ_)
              ( λ aᵉ → apᵉ fᵉ)
              ( λ bᵉ βᵉ → coherence-square-coneᵉ fᵉ gᵉ cᵉ uᵉ ∙ᵉ apᵉ gᵉ βᵉ)
              ( cᵉ)
              ( cone-ap'ᵉ uᵉ))
            ( is-equiv-is-contrᵉ _
              ( is-torsorial-Idᵉ (horizontal-map-coneᵉ fᵉ gᵉ cᵉ uᵉ))
              ( is-torsorial-Idᵉ (fᵉ (vertical-map-coneᵉ fᵉ gᵉ cᵉ uᵉ))))
            ( is-equiv-is-contrᵉ _
              ( is-torsorial-Idᵉ uᵉ)
              ( is-torsorial-Idᵉ (vertical-map-coneᵉ fᵉ gᵉ cᵉ uᵉ))))
          ( vᵉ))
```

## Table of files about pullbacks

Theᵉ followingᵉ tableᵉ listsᵉ filesᵉ thatᵉ areᵉ aboutᵉ pullbacksᵉ asᵉ aᵉ generalᵉ concept.ᵉ

{{#includeᵉ tables/pullbacks.mdᵉ}}