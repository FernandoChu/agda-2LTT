# Descent data for type families of equivalence types over pushouts

```agda
{-# OPTIONSᵉ --lossy-unificationᵉ #-}

module synthetic-homotopy-theory.descent-data-equivalence-types-over-pushoutsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-squares-of-mapsᵉ
open import foundation.commuting-triangles-of-mapsᵉ
open import foundation.contractible-mapsᵉ
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalence-extensionalityᵉ
open import foundation.equivalencesᵉ
open import foundation.fibers-of-mapsᵉ
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
[fiberwiseᵉ equivalences](foundation-core.families-of-equivalences.mdᵉ)
`(xᵉ : Xᵉ) → Pᵉ xᵉ ≃ᵉ Rᵉ x`ᵉ correspondᵉ to
[equivalences](synthetic-homotopy-theory.equivalences-descent-data-pushouts.mdᵉ)
`(PA,ᵉ PB,ᵉ PSᵉ) ≃ᵉ (RA,ᵉ RB,ᵉ RS)`.ᵉ

**Proof:**ᵉ Theᵉ proofᵉ followsᵉ exactlyᵉ theᵉ sameᵉ pattern asᵉ theᵉ oneᵉ in
[`descent-data-function-types-over-pushouts`](synthetic-homotopy-theory.descent-data-function-types-over-pushouts.md).ᵉ

## Definitions

### The type family of fiberwise equivalences with corresponding descent data for pushouts

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level} {𝒮ᵉ : span-diagramᵉ l1ᵉ l2ᵉ l3ᵉ}
  {Xᵉ : UUᵉ l4ᵉ} {cᵉ : cocone-span-diagramᵉ 𝒮ᵉ Xᵉ}
  (Pᵉ : family-with-descent-data-pushoutᵉ cᵉ l5ᵉ)
  (Rᵉ : family-with-descent-data-pushoutᵉ cᵉ l6ᵉ)
  where

  family-cocone-equivalence-type-pushoutᵉ : Xᵉ → UUᵉ (l5ᵉ ⊔ l6ᵉ)
  family-cocone-equivalence-type-pushoutᵉ xᵉ =
    family-cocone-family-with-descent-data-pushoutᵉ Pᵉ xᵉ ≃ᵉ
    family-cocone-family-with-descent-data-pushoutᵉ Rᵉ xᵉ

  descent-data-equivalence-type-pushoutᵉ : descent-data-pushoutᵉ 𝒮ᵉ (l5ᵉ ⊔ l6ᵉ)
  pr1ᵉ descent-data-equivalence-type-pushoutᵉ aᵉ =
    left-family-family-with-descent-data-pushoutᵉ Pᵉ aᵉ ≃ᵉ
    left-family-family-with-descent-data-pushoutᵉ Rᵉ aᵉ
  pr1ᵉ (pr2ᵉ descent-data-equivalence-type-pushoutᵉ) bᵉ =
    right-family-family-with-descent-data-pushoutᵉ Pᵉ bᵉ ≃ᵉ
    right-family-family-with-descent-data-pushoutᵉ Rᵉ bᵉ
  pr2ᵉ (pr2ᵉ descent-data-equivalence-type-pushoutᵉ) sᵉ =
    ( equiv-postcomp-equivᵉ
      ( equiv-family-family-with-descent-data-pushoutᵉ Rᵉ sᵉ)
      ( _)) ∘eᵉ
    ( equiv-precomp-equivᵉ
      ( inv-equivᵉ (equiv-family-family-with-descent-data-pushoutᵉ Pᵉ sᵉ))
      ( _))

  left-equiv-equiv-descent-data-equivalence-type-pushoutᵉ :
    (aᵉ : domain-span-diagramᵉ 𝒮ᵉ) →
    ( family-cocone-family-with-descent-data-pushoutᵉ Pᵉ
        ( horizontal-map-coconeᵉ _ _ cᵉ aᵉ) ≃ᵉ
      family-cocone-family-with-descent-data-pushoutᵉ Rᵉ
        ( horizontal-map-coconeᵉ _ _ cᵉ aᵉ)) ≃ᵉ
    ( left-family-family-with-descent-data-pushoutᵉ Pᵉ aᵉ ≃ᵉ
      left-family-family-with-descent-data-pushoutᵉ Rᵉ aᵉ)
  left-equiv-equiv-descent-data-equivalence-type-pushoutᵉ aᵉ =
    ( equiv-postcomp-equivᵉ
      ( left-equiv-family-with-descent-data-pushoutᵉ Rᵉ aᵉ)
      ( _)) ∘eᵉ
    ( equiv-precomp-equivᵉ
      ( inv-equivᵉ (left-equiv-family-with-descent-data-pushoutᵉ Pᵉ aᵉ))
      ( _))

  right-equiv-equiv-descent-data-equivalence-type-pushoutᵉ :
    (bᵉ : codomain-span-diagramᵉ 𝒮ᵉ) →
    ( family-cocone-family-with-descent-data-pushoutᵉ Pᵉ
        ( vertical-map-coconeᵉ _ _ cᵉ bᵉ) ≃ᵉ
      family-cocone-family-with-descent-data-pushoutᵉ Rᵉ
        ( vertical-map-coconeᵉ _ _ cᵉ bᵉ)) ≃ᵉ
    ( right-family-family-with-descent-data-pushoutᵉ Pᵉ bᵉ ≃ᵉ
      right-family-family-with-descent-data-pushoutᵉ Rᵉ bᵉ)
  right-equiv-equiv-descent-data-equivalence-type-pushoutᵉ bᵉ =
    ( equiv-postcomp-equivᵉ
      ( right-equiv-family-with-descent-data-pushoutᵉ Rᵉ bᵉ)
      ( _)) ∘eᵉ
    ( equiv-precomp-equivᵉ
      ( inv-equivᵉ (right-equiv-family-with-descent-data-pushoutᵉ Pᵉ bᵉ))
      ( _))

  coherence-equiv-descent-data-equivalence-type-pushoutᵉ :
    (sᵉ : spanning-type-span-diagramᵉ 𝒮ᵉ) →
    coherence-square-mapsᵉ
      ( map-equivᵉ
        ( left-equiv-equiv-descent-data-equivalence-type-pushoutᵉ
          ( left-map-span-diagramᵉ 𝒮ᵉ sᵉ)))
      ( trᵉ
        ( family-cocone-equivalence-type-pushoutᵉ)
        ( coherence-square-coconeᵉ _ _ cᵉ sᵉ))
      ( map-family-descent-data-pushoutᵉ
        ( descent-data-equivalence-type-pushoutᵉ)
        ( sᵉ))
      ( map-equivᵉ
        ( right-equiv-equiv-descent-data-equivalence-type-pushoutᵉ
          ( right-map-span-diagramᵉ 𝒮ᵉ sᵉ)))
  coherence-equiv-descent-data-equivalence-type-pushoutᵉ sᵉ =
    ( ( map-equivᵉ
      ( right-equiv-equiv-descent-data-equivalence-type-pushoutᵉ
        ( right-map-span-diagramᵉ 𝒮ᵉ sᵉ))) ·lᵉ
      ( tr-equiv-typeᵉ
        ( family-cocone-family-with-descent-data-pushoutᵉ Pᵉ)
        ( family-cocone-family-with-descent-data-pushoutᵉ Rᵉ)
        ( coherence-square-coconeᵉ _ _ cᵉ sᵉ))) ∙hᵉ
    ( λ eᵉ →
      eq-htpy-equivᵉ
        ( horizontal-concat-htpyᵉ
          ( coherence-family-with-descent-data-pushoutᵉ Rᵉ sᵉ ·rᵉ map-equivᵉ eᵉ)
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

  equiv-descent-data-equivalence-type-pushoutᵉ :
    equiv-descent-data-pushoutᵉ
      ( descent-data-family-cocone-span-diagramᵉ cᵉ
        ( family-cocone-equivalence-type-pushoutᵉ))
      ( descent-data-equivalence-type-pushoutᵉ)
  pr1ᵉ equiv-descent-data-equivalence-type-pushoutᵉ =
    left-equiv-equiv-descent-data-equivalence-type-pushoutᵉ
  pr1ᵉ (pr2ᵉ equiv-descent-data-equivalence-type-pushoutᵉ) =
    right-equiv-equiv-descent-data-equivalence-type-pushoutᵉ
  pr2ᵉ (pr2ᵉ equiv-descent-data-equivalence-type-pushoutᵉ) =
    coherence-equiv-descent-data-equivalence-type-pushoutᵉ

  family-with-descent-data-equivalence-type-pushoutᵉ :
    family-with-descent-data-pushoutᵉ cᵉ (l5ᵉ ⊔ l6ᵉ)
  pr1ᵉ family-with-descent-data-equivalence-type-pushoutᵉ =
    family-cocone-equivalence-type-pushoutᵉ
  pr1ᵉ (pr2ᵉ family-with-descent-data-equivalence-type-pushoutᵉ) =
    descent-data-equivalence-type-pushoutᵉ
  pr2ᵉ (pr2ᵉ family-with-descent-data-equivalence-type-pushoutᵉ) =
    equiv-descent-data-equivalence-type-pushoutᵉ
```

## Properties

### Sections of descent data for families of equivalences correspond to equivalences of descent data

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level} {𝒮ᵉ : span-diagramᵉ l1ᵉ l2ᵉ l3ᵉ}
  {Xᵉ : UUᵉ l4ᵉ} {cᵉ : cocone-span-diagramᵉ 𝒮ᵉ Xᵉ}
  (Pᵉ : family-with-descent-data-pushoutᵉ cᵉ l5ᵉ)
  (Rᵉ : family-with-descent-data-pushoutᵉ cᵉ l6ᵉ)
  where

  equiv-section-descent-data-equivalence-type-pushoutᵉ :
    section-descent-data-pushoutᵉ
      ( descent-data-equivalence-type-pushoutᵉ Pᵉ Rᵉ) →
    equiv-descent-data-pushoutᵉ
      ( descent-data-family-with-descent-data-pushoutᵉ Pᵉ)
      ( descent-data-family-with-descent-data-pushoutᵉ Rᵉ)
  equiv-section-descent-data-equivalence-type-pushoutᵉ =
    totᵉ
      ( λ tAᵉ →
        totᵉ
          ( λ tBᵉ tSᵉ sᵉ →
            inv-htpyᵉ
              ( map-inv-equivᵉ
                ( equiv-coherence-triangle-maps-inv-top'ᵉ
                  ( ( map-family-family-with-descent-data-pushoutᵉ Rᵉ sᵉ) ∘ᵉ
                    ( map-equivᵉ (tAᵉ (left-map-span-diagramᵉ 𝒮ᵉ sᵉ))))
                  ( map-equivᵉ (tBᵉ (right-map-span-diagramᵉ 𝒮ᵉ sᵉ)))
                  ( equiv-family-family-with-descent-data-pushoutᵉ Pᵉ sᵉ))
                ( htpy-eq-equivᵉ (tSᵉ sᵉ)))))

  abstract
    is-equiv-equiv-section-descent-data-equivalence-type-pushoutᵉ :
      is-equivᵉ equiv-section-descent-data-equivalence-type-pushoutᵉ
    is-equiv-equiv-section-descent-data-equivalence-type-pushoutᵉ =
      is-equiv-tot-is-fiberwise-equivᵉ
        ( λ tAᵉ →
          is-equiv-tot-is-fiberwise-equivᵉ
            ( λ tBᵉ →
              is-equiv-map-Π-is-fiberwise-equivᵉ
                ( λ sᵉ →
                  is-equiv-compᵉ _ _
                    ( is-equiv-map-equivᵉ (extensionality-equivᵉ _ _))
                    ( is-equiv-compᵉ _ _
                      ( is-equiv-map-inv-equivᵉ
                        ( equiv-coherence-triangle-maps-inv-top'ᵉ
                          ( (map-family-family-with-descent-data-pushoutᵉ Rᵉ sᵉ) ∘ᵉ
                            ( map-equivᵉ (tAᵉ (left-map-span-diagramᵉ 𝒮ᵉ sᵉ))))
                          ( map-equivᵉ (tBᵉ (right-map-span-diagramᵉ 𝒮ᵉ sᵉ)))
                          ( equiv-family-family-with-descent-data-pushoutᵉ Pᵉ sᵉ)))
                      ( is-equiv-inv-htpyᵉ _ _)))))

  equiv-descent-data-equiv-family-cocone-span-diagramᵉ :
    ( (xᵉ : Xᵉ) →
      family-cocone-family-with-descent-data-pushoutᵉ Pᵉ xᵉ ≃ᵉ
      family-cocone-family-with-descent-data-pushoutᵉ Rᵉ xᵉ) →
    equiv-descent-data-pushoutᵉ
      ( descent-data-family-with-descent-data-pushoutᵉ Pᵉ)
      ( descent-data-family-with-descent-data-pushoutᵉ Rᵉ)
  equiv-descent-data-equiv-family-cocone-span-diagramᵉ =
    ( equiv-section-descent-data-equivalence-type-pushoutᵉ) ∘ᵉ
    ( section-descent-data-section-family-cocone-span-diagramᵉ
      ( family-with-descent-data-equivalence-type-pushoutᵉ Pᵉ Rᵉ))

  abstract
    is-equiv-equiv-descent-data-equiv-family-cocone-span-diagramᵉ :
      universal-property-pushoutᵉ _ _ cᵉ →
      is-equivᵉ equiv-descent-data-equiv-family-cocone-span-diagramᵉ
    is-equiv-equiv-descent-data-equiv-family-cocone-span-diagramᵉ up-cᵉ =
      is-equiv-compᵉ _ _
        ( is-equiv-section-descent-data-section-family-cocone-span-diagramᵉ _
          ( up-cᵉ))
        ( is-equiv-equiv-section-descent-data-equivalence-type-pushoutᵉ)
```

Asᵉ aᵉ corollary,ᵉ givenᵉ anᵉ equivalenceᵉ
`(hA,ᵉ hB,ᵉ hSᵉ) : (PA,ᵉ PB,ᵉ PSᵉ) ≃ᵉ (RA,ᵉ RB,ᵉ RS)`,ᵉ thereᵉ isᵉ aᵉ uniqueᵉ familyᵉ ofᵉ
equivalencesᵉ `hᵉ : (xᵉ : Xᵉ) → Pᵉ xᵉ → Rᵉ x`ᵉ suchᵉ thatᵉ itsᵉ inducedᵉ equivalenceᵉ isᵉ
homotopicᵉ to `(hA,ᵉ hB,ᵉ hS)`.ᵉ Theᵉ homotopyᵉ providesᵉ usᵉ in particularᵉ with theᵉ
component-wiseᵉ [homotopies](foundation-core.homotopies.mdᵉ)

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
  (eᵉ :
    equiv-descent-data-pushoutᵉ
      ( descent-data-family-with-descent-data-pushoutᵉ Pᵉ)
      ( descent-data-family-with-descent-data-pushoutᵉ Rᵉ))
  where

  abstract
    uniqueness-equiv-equiv-descent-data-pushoutᵉ :
      is-contrᵉ
        ( Σᵉ ( (xᵉ : Xᵉ) →
              family-cocone-family-with-descent-data-pushoutᵉ Pᵉ xᵉ ≃ᵉ
              family-cocone-family-with-descent-data-pushoutᵉ Rᵉ xᵉ)
            ( λ hᵉ →
              htpy-equiv-descent-data-pushoutᵉ
                ( descent-data-family-with-descent-data-pushoutᵉ Pᵉ)
                ( descent-data-family-with-descent-data-pushoutᵉ Rᵉ)
                ( equiv-descent-data-equiv-family-cocone-span-diagramᵉ Pᵉ Rᵉ hᵉ)
                ( eᵉ)))
    uniqueness-equiv-equiv-descent-data-pushoutᵉ =
      is-contr-equiv'ᵉ
        ( fiberᵉ (equiv-descent-data-equiv-family-cocone-span-diagramᵉ Pᵉ Rᵉ) eᵉ)
        ( equiv-totᵉ
          ( λ fᵉ → extensionality-equiv-descent-data-pushoutᵉ _ eᵉ))
        ( is-contr-map-is-equivᵉ
          ( is-equiv-equiv-descent-data-equiv-family-cocone-span-diagramᵉ Pᵉ Rᵉ
            ( up-cᵉ))
          ( eᵉ))

  equiv-equiv-descent-data-pushoutᵉ :
    (xᵉ : Xᵉ) →
    family-cocone-family-with-descent-data-pushoutᵉ Pᵉ xᵉ ≃ᵉ
    family-cocone-family-with-descent-data-pushoutᵉ Rᵉ xᵉ
  equiv-equiv-descent-data-pushoutᵉ =
    pr1ᵉ (centerᵉ uniqueness-equiv-equiv-descent-data-pushoutᵉ)

  map-equiv-descent-data-pushoutᵉ :
    (xᵉ : Xᵉ) →
    family-cocone-family-with-descent-data-pushoutᵉ Pᵉ xᵉ →
    family-cocone-family-with-descent-data-pushoutᵉ Rᵉ xᵉ
  map-equiv-descent-data-pushoutᵉ xᵉ =
    map-equivᵉ (equiv-equiv-descent-data-pushoutᵉ xᵉ)

  compute-left-map-equiv-equiv-descent-data-pushoutᵉ :
    (aᵉ : domain-span-diagramᵉ 𝒮ᵉ) →
    coherence-square-mapsᵉ
      ( left-map-family-with-descent-data-pushoutᵉ Pᵉ aᵉ)
      ( map-equiv-descent-data-pushoutᵉ (horizontal-map-coconeᵉ _ _ cᵉ aᵉ))
      ( left-map-equiv-descent-data-pushoutᵉ
        ( descent-data-family-with-descent-data-pushoutᵉ Pᵉ)
        ( descent-data-family-with-descent-data-pushoutᵉ Rᵉ)
        ( eᵉ)
        ( aᵉ))
      ( left-map-family-with-descent-data-pushoutᵉ Rᵉ aᵉ)
  compute-left-map-equiv-equiv-descent-data-pushoutᵉ aᵉ =
    map-inv-equivᵉ
      ( equiv-coherence-triangle-maps-inv-top'ᵉ
        ( left-map-family-with-descent-data-pushoutᵉ Rᵉ aᵉ ∘ᵉ
          map-equiv-descent-data-pushoutᵉ (horizontal-map-coconeᵉ _ _ cᵉ aᵉ))
        ( left-map-equiv-descent-data-pushoutᵉ
          ( descent-data-family-with-descent-data-pushoutᵉ Pᵉ)
          ( descent-data-family-with-descent-data-pushoutᵉ Rᵉ)
          ( eᵉ)
          ( aᵉ))
        ( left-equiv-family-with-descent-data-pushoutᵉ Pᵉ aᵉ))
      ( pr1ᵉ (pr2ᵉ (centerᵉ uniqueness-equiv-equiv-descent-data-pushoutᵉ)) aᵉ)

  compute-right-map-equiv-equiv-descent-data-pushoutᵉ :
    (bᵉ : codomain-span-diagramᵉ 𝒮ᵉ) →
    coherence-square-mapsᵉ
      ( right-map-family-with-descent-data-pushoutᵉ Pᵉ bᵉ)
      ( map-equiv-descent-data-pushoutᵉ (vertical-map-coconeᵉ _ _ cᵉ bᵉ))
      ( right-map-equiv-descent-data-pushoutᵉ
        ( descent-data-family-with-descent-data-pushoutᵉ Pᵉ)
        ( descent-data-family-with-descent-data-pushoutᵉ Rᵉ)
        ( eᵉ)
        ( bᵉ))
      ( right-map-family-with-descent-data-pushoutᵉ Rᵉ bᵉ)
  compute-right-map-equiv-equiv-descent-data-pushoutᵉ bᵉ =
    map-inv-equivᵉ
      ( equiv-coherence-triangle-maps-inv-top'ᵉ
        ( right-map-family-with-descent-data-pushoutᵉ Rᵉ bᵉ ∘ᵉ
          map-equiv-descent-data-pushoutᵉ (vertical-map-coconeᵉ _ _ cᵉ bᵉ))
        ( right-map-equiv-descent-data-pushoutᵉ
          ( descent-data-family-with-descent-data-pushoutᵉ Pᵉ)
          ( descent-data-family-with-descent-data-pushoutᵉ Rᵉ)
          ( eᵉ)
          ( bᵉ))
        ( right-equiv-family-with-descent-data-pushoutᵉ Pᵉ bᵉ))
      ( pr1ᵉ (pr2ᵉ (pr2ᵉ (centerᵉ uniqueness-equiv-equiv-descent-data-pushoutᵉ))) bᵉ)
```