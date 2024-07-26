# Descent data for type families of function types over pushouts

```agda
{-# OPTIONSᵉ --lossy-unificationᵉ #-}

module synthetic-homotopy-theory.descent-data-function-types-over-pushoutsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-squares-of-mapsᵉ
open import foundation.commuting-triangles-of-mapsᵉ
open import foundation.contractible-mapsᵉ
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.fibers-of-mapsᵉ
open import foundation.function-extensionalityᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-dependent-function-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.homotopy-algebraᵉ
open import foundation.postcomposition-functionsᵉ
open import foundation.span-diagramsᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.universal-property-equivalencesᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ

open import synthetic-homotopy-theory.cocones-under-spansᵉ
open import synthetic-homotopy-theory.descent-data-pushoutsᵉ
open import synthetic-homotopy-theory.equivalences-descent-data-pushoutsᵉ
open import synthetic-homotopy-theory.families-descent-data-pushoutsᵉ
open import synthetic-homotopy-theory.morphisms-descent-data-pushoutsᵉ
open import synthetic-homotopy-theory.sections-descent-data-pushoutsᵉ
open import synthetic-homotopy-theory.universal-property-pushoutsᵉ
```

</details>

## Idea

Givenᵉ twoᵉ
[familiesᵉ with descentᵉ data](synthetic-homotopy-theory.families-descent-data-pushouts.mdᵉ)
forᵉ [pushouts](synthetic-homotopy-theory.pushouts.mdᵉ) `Pᵉ ≈ᵉ (PA,ᵉ PB,ᵉ PS)`ᵉ andᵉ
`Rᵉ ≈ᵉ (RA,ᵉ RB,ᵉ RS)`,ᵉ weᵉ showᵉ thatᵉ
[fiberwiseᵉ maps](foundation.families-of-maps.mdᵉ) `(xᵉ : Xᵉ) → Pᵉ xᵉ → Rᵉ x`ᵉ
correspondᵉ to
[morphisms](synthetic-homotopy-theory.morphisms-descent-data-pushouts.mdᵉ)
`(PA,ᵉ PB,ᵉ PSᵉ) → (RA,ᵉ RB,ᵉ RS)`.ᵉ

**Proof:**ᵉ Weᵉ firstᵉ characterizeᵉ theᵉ typeᵉ familyᵉ `xᵉ ↦ᵉ (Pᵉ xᵉ → Rᵉ x)`.ᵉ Theᵉ
correspondingᵉ [descentᵉ data](synthetic-homotopy-theory.descent-data-pushouts.mdᵉ)
consistsᵉ ofᵉ theᵉ typeᵉ familiesᵉ

```text
  aᵉ ↦ᵉ (PAᵉ aᵉ → RAᵉ aᵉ)
  bᵉ ↦ᵉ (PBᵉ bᵉ → RBᵉ b),ᵉ
```

andᵉ theᵉ gluingᵉ data sendingᵉ `hᵉ : PAᵉ (fsᵉ) → RAᵉ (fs)`ᵉ to
`(RSᵉ sᵉ ∘ᵉ hᵉ ∘ᵉ (PSᵉ s)⁻¹ᵉ) : PBᵉ (gsᵉ) → RBᵉ (gs)`.ᵉ

**Note:**ᵉ Itᵉ isᵉ importantᵉ to differentiateᵉ betweenᵉ familiesᵉ ofᵉ _functionᵉ types_,ᵉ
i.e.ᵉ aᵉ typeᵉ familyᵉ thatᵉ to everyᵉ `xᵉ : X`ᵉ assignsᵉ theᵉ _typeᵉ_ `Pᵉ xᵉ → Rᵉ x`,ᵉ andᵉ
familiesᵉ ofᵉ _functions_,ᵉ i.e.ᵉ aᵉ familyᵉ thatᵉ to everyᵉ `xᵉ : X`ᵉ assignsᵉ aᵉ
_functionᵉ_ fromᵉ `Pᵉ x`ᵉ to Rᵉ x`.ᵉ Descentᵉ data playsᵉ theᵉ roleᵉ ofᵉ aᵉ familyᵉ ofᵉ types,ᵉ
soᵉ itᵉ makesᵉ senseᵉ to talkᵉ aboutᵉ "descentᵉ data correspondingᵉ to aᵉ familyᵉ ofᵉ
functionᵉ types",ᵉ butᵉ itᵉ doesn'tᵉ makeᵉ senseᵉ to talkᵉ aboutᵉ "descentᵉ data
correspondingᵉ to aᵉ familyᵉ ofᵉ functions".ᵉ Theᵉ kindᵉ ofᵉ data thatᵉ correspondsᵉ to
familiesᵉ ofᵉ functionsᵉ areᵉ theᵉ _sectionsᵉ_ ofᵉ theᵉ descentᵉ data ofᵉ aᵉ familyᵉ ofᵉ
functionᵉ types.ᵉ

Itᵉ sufficesᵉ to showᵉ thatᵉ theᵉ sectionsᵉ correspondᵉ to morphisms.ᵉ Theᵉ firstᵉ twoᵉ
componentsᵉ ofᵉ aᵉ sectionᵉ andᵉ aᵉ morphismᵉ agree,ᵉ namelyᵉ theyᵉ areᵉ

```text
  sAᵉ : (aᵉ : Aᵉ) → PAᵉ aᵉ → RAᵉ aᵉ
  sBᵉ : (bᵉ : Bᵉ) → PBᵉ bᵉ → RBᵉ b,ᵉ
```

respectively.ᵉ Theᵉ coherenceᵉ datumᵉ ofᵉ aᵉ sectionᵉ hasᵉ theᵉ typeᵉ

```text
  (sᵉ : Sᵉ) → RSᵉ sᵉ ∘ᵉ sAᵉ (fsᵉ) ∘ᵉ (RSᵉ s)⁻¹ᵉ = sBᵉ (gs),ᵉ
```

whichᵉ weᵉ canᵉ massageᵉ intoᵉ aᵉ coherenceᵉ ofᵉ theᵉ morphismᵉ asᵉ

```text
  RSᵉ sᵉ ∘ᵉ sAᵉ (fsᵉ) ∘ᵉ (PSᵉ s)⁻¹ᵉ = sBᵉ (gsᵉ)
  ≃ᵉ RSᵉ sᵉ ∘ᵉ sAᵉ (fsᵉ) ∘ᵉ (PSᵉ s)⁻¹ᵉ ~ᵉ sBᵉ (gsᵉ)  byᵉ functionᵉ extensionalityᵉ
  ≃ᵉ RSᵉ sᵉ ∘ᵉ sAᵉ (fsᵉ) ~ᵉ sBᵉ (gsᵉ) ∘ᵉ PSᵉ sᵉ      byᵉ transpositionᵉ ofᵉ (PSᵉ sᵉ)
  ≃ᵉ sBᵉ (gsᵉ) ∘ᵉ PSᵉ sᵉ ~ᵉ RSᵉ sᵉ ∘ᵉ sAᵉ (fsᵉ)      byᵉ symmetryᵉ ofᵉ homotopies.ᵉ
```

## Definitions

### The type family of fiberwise functions with corresponding descent data for pushouts

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level} {𝒮ᵉ : span-diagramᵉ l1ᵉ l2ᵉ l3ᵉ}
  {Xᵉ : UUᵉ l4ᵉ} {cᵉ : cocone-span-diagramᵉ 𝒮ᵉ Xᵉ}
  (Pᵉ : family-with-descent-data-pushoutᵉ cᵉ l5ᵉ)
  (Rᵉ : family-with-descent-data-pushoutᵉ cᵉ l6ᵉ)
  where

  family-cocone-function-type-pushoutᵉ : Xᵉ → UUᵉ (l5ᵉ ⊔ l6ᵉ)
  family-cocone-function-type-pushoutᵉ xᵉ =
    family-cocone-family-with-descent-data-pushoutᵉ Pᵉ xᵉ →
    family-cocone-family-with-descent-data-pushoutᵉ Rᵉ xᵉ

  descent-data-function-type-pushoutᵉ : descent-data-pushoutᵉ 𝒮ᵉ (l5ᵉ ⊔ l6ᵉ)
  pr1ᵉ descent-data-function-type-pushoutᵉ aᵉ =
    left-family-family-with-descent-data-pushoutᵉ Pᵉ aᵉ →
    left-family-family-with-descent-data-pushoutᵉ Rᵉ aᵉ
  pr1ᵉ (pr2ᵉ descent-data-function-type-pushoutᵉ) bᵉ =
    right-family-family-with-descent-data-pushoutᵉ Pᵉ bᵉ →
    right-family-family-with-descent-data-pushoutᵉ Rᵉ bᵉ
  pr2ᵉ (pr2ᵉ descent-data-function-type-pushoutᵉ) sᵉ =
    ( equiv-postcompᵉ _
      ( equiv-family-family-with-descent-data-pushoutᵉ Rᵉ sᵉ)) ∘eᵉ
    ( equiv-precompᵉ
      ( inv-equivᵉ (equiv-family-family-with-descent-data-pushoutᵉ Pᵉ sᵉ))
      ( _))

  left-equiv-equiv-descent-data-function-type-pushoutᵉ :
    (aᵉ : domain-span-diagramᵉ 𝒮ᵉ) →
    ( family-cocone-family-with-descent-data-pushoutᵉ Pᵉ
        ( horizontal-map-coconeᵉ _ _ cᵉ aᵉ) →
      family-cocone-family-with-descent-data-pushoutᵉ Rᵉ
        ( horizontal-map-coconeᵉ _ _ cᵉ aᵉ)) ≃ᵉ
    ( left-family-family-with-descent-data-pushoutᵉ Pᵉ aᵉ →
      left-family-family-with-descent-data-pushoutᵉ Rᵉ aᵉ)
  left-equiv-equiv-descent-data-function-type-pushoutᵉ aᵉ =
    ( equiv-postcompᵉ _
      ( left-equiv-family-with-descent-data-pushoutᵉ Rᵉ aᵉ)) ∘eᵉ
    ( equiv-precompᵉ
      ( inv-equivᵉ (left-equiv-family-with-descent-data-pushoutᵉ Pᵉ aᵉ))
      ( _))

  right-equiv-equiv-descent-data-function-type-pushoutᵉ :
    (bᵉ : codomain-span-diagramᵉ 𝒮ᵉ) →
    ( family-cocone-family-with-descent-data-pushoutᵉ Pᵉ
        ( vertical-map-coconeᵉ _ _ cᵉ bᵉ) →
      family-cocone-family-with-descent-data-pushoutᵉ Rᵉ
        ( vertical-map-coconeᵉ _ _ cᵉ bᵉ)) ≃ᵉ
    ( right-family-family-with-descent-data-pushoutᵉ Pᵉ bᵉ →
      right-family-family-with-descent-data-pushoutᵉ Rᵉ bᵉ)
  right-equiv-equiv-descent-data-function-type-pushoutᵉ bᵉ =
    ( equiv-postcompᵉ _
      ( right-equiv-family-with-descent-data-pushoutᵉ Rᵉ bᵉ)) ∘eᵉ
    ( equiv-precompᵉ
      ( inv-equivᵉ (right-equiv-family-with-descent-data-pushoutᵉ Pᵉ bᵉ))
      ( _))

  coherence-equiv-descent-data-function-type-pushoutᵉ :
    (sᵉ : spanning-type-span-diagramᵉ 𝒮ᵉ) →
    coherence-square-mapsᵉ
      ( map-equivᵉ
        ( left-equiv-equiv-descent-data-function-type-pushoutᵉ
          ( left-map-span-diagramᵉ 𝒮ᵉ sᵉ)))
      ( trᵉ
        ( family-cocone-function-type-pushoutᵉ)
        ( coherence-square-coconeᵉ _ _ cᵉ sᵉ))
      ( map-family-descent-data-pushoutᵉ
        ( descent-data-function-type-pushoutᵉ)
        ( sᵉ))
      ( map-equivᵉ
        ( right-equiv-equiv-descent-data-function-type-pushoutᵉ
          ( right-map-span-diagramᵉ 𝒮ᵉ sᵉ)))
  coherence-equiv-descent-data-function-type-pushoutᵉ sᵉ =
    ( ( map-equivᵉ
        ( right-equiv-equiv-descent-data-function-type-pushoutᵉ
          ( right-map-span-diagramᵉ 𝒮ᵉ sᵉ))) ·lᵉ
      ( tr-function-typeᵉ
        ( family-cocone-family-with-descent-data-pushoutᵉ Pᵉ)
        ( family-cocone-family-with-descent-data-pushoutᵉ Rᵉ)
        ( coherence-square-coconeᵉ _ _ cᵉ sᵉ))) ∙hᵉ
    ( λ hᵉ →
      eq-htpyᵉ
        ( horizontal-concat-htpyᵉ
          ( coherence-family-with-descent-data-pushoutᵉ Rᵉ sᵉ ·rᵉ hᵉ)
          ( coherence-square-maps-inv-equivᵉ
            ( equiv-trᵉ
              ( family-cocone-family-with-descent-data-pushoutᵉ Pᵉ)
              ( coherence-square-coconeᵉ _ _ cᵉ sᵉ))
            ( left-equiv-family-with-descent-data-pushoutᵉ Pᵉ
              ( left-map-span-diagramᵉ 𝒮ᵉ sᵉ))
            ( right-equiv-family-with-descent-data-pushoutᵉ Pᵉ
              ( right-map-span-diagramᵉ 𝒮ᵉ sᵉ))
            ( equiv-family-family-with-descent-data-pushoutᵉ Pᵉ sᵉ)
            ( inv-htpyᵉ (coherence-family-with-descent-data-pushoutᵉ Pᵉ sᵉ)))))

  equiv-descent-data-function-type-pushoutᵉ :
    equiv-descent-data-pushoutᵉ
      ( descent-data-family-cocone-span-diagramᵉ cᵉ
        ( family-cocone-function-type-pushoutᵉ))
      ( descent-data-function-type-pushoutᵉ)
  pr1ᵉ equiv-descent-data-function-type-pushoutᵉ =
    left-equiv-equiv-descent-data-function-type-pushoutᵉ
  pr1ᵉ (pr2ᵉ equiv-descent-data-function-type-pushoutᵉ) =
    right-equiv-equiv-descent-data-function-type-pushoutᵉ
  pr2ᵉ (pr2ᵉ equiv-descent-data-function-type-pushoutᵉ) =
    coherence-equiv-descent-data-function-type-pushoutᵉ

  family-with-descent-data-function-type-pushoutᵉ :
    family-with-descent-data-pushoutᵉ cᵉ (l5ᵉ ⊔ l6ᵉ)
  pr1ᵉ family-with-descent-data-function-type-pushoutᵉ =
    family-cocone-function-type-pushoutᵉ
  pr1ᵉ (pr2ᵉ family-with-descent-data-function-type-pushoutᵉ) =
    descent-data-function-type-pushoutᵉ
  pr2ᵉ (pr2ᵉ family-with-descent-data-function-type-pushoutᵉ) =
    equiv-descent-data-function-type-pushoutᵉ
```

## Properties

### Sections of descent data for families of functions correspond to morphisms of descent data

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level} {𝒮ᵉ : span-diagramᵉ l1ᵉ l2ᵉ l3ᵉ}
  {Xᵉ : UUᵉ l4ᵉ} {cᵉ : cocone-span-diagramᵉ 𝒮ᵉ Xᵉ}
  (Pᵉ : family-with-descent-data-pushoutᵉ cᵉ l5ᵉ)
  (Rᵉ : family-with-descent-data-pushoutᵉ cᵉ l6ᵉ)
  where

  hom-section-descent-data-function-type-pushoutᵉ :
    section-descent-data-pushoutᵉ (descent-data-function-type-pushoutᵉ Pᵉ Rᵉ) →
    hom-descent-data-pushoutᵉ
      ( descent-data-family-with-descent-data-pushoutᵉ Pᵉ)
      ( descent-data-family-with-descent-data-pushoutᵉ Rᵉ)
  hom-section-descent-data-function-type-pushoutᵉ =
    totᵉ
      ( λ tAᵉ →
        totᵉ
        ( λ tBᵉ tSᵉ sᵉ →
          inv-htpyᵉ
            ( map-inv-equivᵉ
              ( equiv-coherence-triangle-maps-inv-top'ᵉ
                ( ( map-family-family-with-descent-data-pushoutᵉ Rᵉ sᵉ) ∘ᵉ
                  ( tAᵉ (left-map-span-diagramᵉ 𝒮ᵉ sᵉ)))
                ( tBᵉ (right-map-span-diagramᵉ 𝒮ᵉ sᵉ))
                ( equiv-family-family-with-descent-data-pushoutᵉ Pᵉ sᵉ))
              ( htpy-eqᵉ (tSᵉ sᵉ)))))

  abstract
    is-equiv-hom-section-descent-data-function-type-pushoutᵉ :
      is-equivᵉ
        ( hom-section-descent-data-function-type-pushoutᵉ)
    is-equiv-hom-section-descent-data-function-type-pushoutᵉ =
      is-equiv-tot-is-fiberwise-equivᵉ
        ( λ tAᵉ →
          is-equiv-tot-is-fiberwise-equivᵉ
            ( λ tBᵉ →
              is-equiv-map-Π-is-fiberwise-equivᵉ
                ( λ sᵉ →
                  is-equiv-compᵉ _ _
                    ( funextᵉ _ _)
                    ( is-equiv-compᵉ _ _
                      ( is-equiv-map-inv-equivᵉ
                        ( equiv-coherence-triangle-maps-inv-top'ᵉ
                          ( ( map-family-family-with-descent-data-pushoutᵉ Rᵉ sᵉ) ∘ᵉ
                            ( tAᵉ (left-map-span-diagramᵉ 𝒮ᵉ sᵉ)))
                          ( tBᵉ (right-map-span-diagramᵉ 𝒮ᵉ sᵉ))
                          ( equiv-family-family-with-descent-data-pushoutᵉ Pᵉ sᵉ)))
                      ( is-equiv-inv-htpyᵉ _ _)))))

  hom-descent-data-map-family-cocone-span-diagramᵉ :
    ( (xᵉ : Xᵉ) →
      family-cocone-family-with-descent-data-pushoutᵉ Pᵉ xᵉ →
      family-cocone-family-with-descent-data-pushoutᵉ Rᵉ xᵉ) →
    hom-descent-data-pushoutᵉ
      ( descent-data-family-with-descent-data-pushoutᵉ Pᵉ)
      ( descent-data-family-with-descent-data-pushoutᵉ Rᵉ)
  hom-descent-data-map-family-cocone-span-diagramᵉ =
    ( hom-section-descent-data-function-type-pushoutᵉ) ∘ᵉ
    ( section-descent-data-section-family-cocone-span-diagramᵉ
      ( family-with-descent-data-function-type-pushoutᵉ Pᵉ Rᵉ))

  abstract
    is-equiv-hom-descent-data-map-family-cocone-span-diagramᵉ :
      universal-property-pushoutᵉ _ _ cᵉ →
      is-equivᵉ hom-descent-data-map-family-cocone-span-diagramᵉ
    is-equiv-hom-descent-data-map-family-cocone-span-diagramᵉ up-cᵉ =
      is-equiv-compᵉ _ _
        ( is-equiv-section-descent-data-section-family-cocone-span-diagramᵉ _
          ( up-cᵉ))
        ( is-equiv-hom-section-descent-data-function-type-pushoutᵉ)
```

Asᵉ aᵉ corollary,ᵉ givenᵉ aᵉ morphismᵉ `(hA,ᵉ hB,ᵉ hSᵉ) : (PA,ᵉ PB,ᵉ PSᵉ) → (RA,ᵉ RB,ᵉ RS)`,ᵉ
thereᵉ isᵉ aᵉ uniqueᵉ familyᵉ ofᵉ mapsᵉ `hᵉ : (xᵉ : Xᵉ) → Pᵉ xᵉ → Rᵉ x`ᵉ suchᵉ thatᵉ itsᵉ inducedᵉ
morphismᵉ isᵉ homotopicᵉ to `(hA,ᵉ hB,ᵉ hS)`.ᵉ Theᵉ homotopyᵉ providesᵉ usᵉ in particularᵉ
with theᵉ component-wiseᵉ [homotopies](foundation-core.homotopies.mdᵉ)

```text
                 hAᵉ aᵉ                               hBᵉ aᵉ
          PAᵉ aᵉ -------->ᵉ RAᵉ aᵉ                PBᵉ bᵉ -------->ᵉ RBᵉ bᵉ
            |              ∧ᵉ                   |              ∧ᵉ
  (eᴾAᵉ a)⁻¹ᵉ |              | eᴿAᵉ aᵉ   (eᴾBᵉ b)⁻¹ᵉ |              | eᴿBᵉ bᵉ
            |              |                   |              |
            ∨ᵉ              |                   ∨ᵉ              |
         Pᵉ (iaᵉ) ------>ᵉ Rᵉ (iaᵉ)              Pᵉ (jbᵉ) ------>ᵉ Rᵉ (jbᵉ)
                hᵉ (iaᵉ)                             hᵉ (jbᵉ)
```

whichᵉ weᵉ canᵉ turnᵉ intoᵉ theᵉ computationᵉ rulesᵉ

```text
              eᴾAᵉ aᵉ                           eᴾBᵉ aᵉ
      Pᵉ (iaᵉ) ------->ᵉ PAᵉ aᵉ            Pᵉ (jbᵉ) ------->ᵉ PBᵉ bᵉ
         |              |                |              |
  hᵉ (iaᵉ) |              | hAᵉ aᵉ    hᵉ (jbᵉ) |              | hBᵉ bᵉ
         |              |                |              |
         ∨ᵉ              ∨ᵉ                ∨ᵉ              ∨ᵉ
      Rᵉ (iaᵉ) ------->ᵉ RAᵉ aᵉ            Rᵉ (jbᵉ) ------->ᵉ RBᵉ bᵉ
              eᴿAᵉ aᵉ                           eᴿBᵉ bᵉ
```

byᵉ invertingᵉ theᵉ invertedᵉ equivalences.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level} {𝒮ᵉ : span-diagramᵉ l1ᵉ l2ᵉ l3ᵉ}
  {Xᵉ : UUᵉ l4ᵉ} {cᵉ : cocone-span-diagramᵉ 𝒮ᵉ Xᵉ}
  (up-cᵉ : universal-property-pushoutᵉ _ _ cᵉ)
  (Pᵉ : family-with-descent-data-pushoutᵉ cᵉ l5ᵉ)
  (Rᵉ : family-with-descent-data-pushoutᵉ cᵉ l6ᵉ)
  (mᵉ :
    hom-descent-data-pushoutᵉ
      ( descent-data-family-with-descent-data-pushoutᵉ Pᵉ)
      ( descent-data-family-with-descent-data-pushoutᵉ Rᵉ))
  where

  abstract
    uniqueness-map-hom-descent-data-pushoutᵉ :
      is-contrᵉ
        ( Σᵉ ( (xᵉ : Xᵉ) →
              family-cocone-family-with-descent-data-pushoutᵉ Pᵉ xᵉ →
              family-cocone-family-with-descent-data-pushoutᵉ Rᵉ xᵉ)
            ( λ hᵉ →
              htpy-hom-descent-data-pushoutᵉ
                ( descent-data-family-with-descent-data-pushoutᵉ Pᵉ)
                ( descent-data-family-with-descent-data-pushoutᵉ Rᵉ)
                ( hom-descent-data-map-family-cocone-span-diagramᵉ Pᵉ Rᵉ hᵉ)
                ( mᵉ)))
    uniqueness-map-hom-descent-data-pushoutᵉ =
      is-contr-equiv'ᵉ
        ( fiberᵉ (hom-descent-data-map-family-cocone-span-diagramᵉ Pᵉ Rᵉ) mᵉ)
        ( equiv-totᵉ
          ( λ hᵉ → extensionality-hom-descent-data-pushoutᵉ _ _ _ mᵉ))
        ( is-contr-map-is-equivᵉ
          ( is-equiv-hom-descent-data-map-family-cocone-span-diagramᵉ Pᵉ Rᵉ up-cᵉ)
          ( mᵉ))

  map-hom-descent-data-pushoutᵉ :
    (xᵉ : Xᵉ) →
    family-cocone-family-with-descent-data-pushoutᵉ Pᵉ xᵉ →
    family-cocone-family-with-descent-data-pushoutᵉ Rᵉ xᵉ
  map-hom-descent-data-pushoutᵉ =
    pr1ᵉ (centerᵉ uniqueness-map-hom-descent-data-pushoutᵉ)

  compute-left-map-map-hom-descent-data-pushoutᵉ :
    (aᵉ : domain-span-diagramᵉ 𝒮ᵉ) →
    coherence-square-mapsᵉ
      ( left-map-family-with-descent-data-pushoutᵉ Pᵉ aᵉ)
      ( map-hom-descent-data-pushoutᵉ (horizontal-map-coconeᵉ _ _ cᵉ aᵉ))
      ( left-map-hom-descent-data-pushoutᵉ
        ( descent-data-family-with-descent-data-pushoutᵉ Pᵉ)
        ( descent-data-family-with-descent-data-pushoutᵉ Rᵉ)
        ( mᵉ)
        ( aᵉ))
      ( left-map-family-with-descent-data-pushoutᵉ Rᵉ aᵉ)
  compute-left-map-map-hom-descent-data-pushoutᵉ aᵉ =
    map-inv-equivᵉ
      ( equiv-coherence-triangle-maps-inv-top'ᵉ
        ( left-map-family-with-descent-data-pushoutᵉ Rᵉ aᵉ ∘ᵉ
          map-hom-descent-data-pushoutᵉ (horizontal-map-coconeᵉ _ _ cᵉ aᵉ))
        ( left-map-hom-descent-data-pushoutᵉ
          ( descent-data-family-with-descent-data-pushoutᵉ Pᵉ)
          ( descent-data-family-with-descent-data-pushoutᵉ Rᵉ)
          ( mᵉ)
          ( aᵉ))
        ( left-equiv-family-with-descent-data-pushoutᵉ Pᵉ aᵉ))
      ( pr1ᵉ (pr2ᵉ (centerᵉ uniqueness-map-hom-descent-data-pushoutᵉ)) aᵉ)

  compute-right-map-map-hom-descent-data-pushoutᵉ :
    (bᵉ : codomain-span-diagramᵉ 𝒮ᵉ) →
    coherence-square-mapsᵉ
      ( right-map-family-with-descent-data-pushoutᵉ Pᵉ bᵉ)
      ( map-hom-descent-data-pushoutᵉ (vertical-map-coconeᵉ _ _ cᵉ bᵉ))
      ( right-map-hom-descent-data-pushoutᵉ
        ( descent-data-family-with-descent-data-pushoutᵉ Pᵉ)
        ( descent-data-family-with-descent-data-pushoutᵉ Rᵉ)
        ( mᵉ)
        ( bᵉ))
      ( right-map-family-with-descent-data-pushoutᵉ Rᵉ bᵉ)
  compute-right-map-map-hom-descent-data-pushoutᵉ bᵉ =
    map-inv-equivᵉ
      ( equiv-coherence-triangle-maps-inv-top'ᵉ
        ( right-map-family-with-descent-data-pushoutᵉ Rᵉ bᵉ ∘ᵉ
          map-hom-descent-data-pushoutᵉ (vertical-map-coconeᵉ _ _ cᵉ bᵉ))
        ( right-map-hom-descent-data-pushoutᵉ
          ( descent-data-family-with-descent-data-pushoutᵉ Pᵉ)
          ( descent-data-family-with-descent-data-pushoutᵉ Rᵉ)
          ( mᵉ)
          ( bᵉ))
        ( right-equiv-family-with-descent-data-pushoutᵉ Pᵉ bᵉ))
      ( pr1ᵉ (pr2ᵉ (pr2ᵉ (centerᵉ uniqueness-map-hom-descent-data-pushoutᵉ))) bᵉ)
```