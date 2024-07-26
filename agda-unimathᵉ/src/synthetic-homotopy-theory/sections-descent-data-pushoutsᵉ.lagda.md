# Sections of descent data for pushouts

```agda
module synthetic-homotopy-theory.sections-descent-data-pushoutsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functionsᵉ
open import foundation.action-on-identifications-functionsᵉ
open import foundation.commuting-squares-of-identificationsᵉ
open import foundation.commuting-triangles-of-mapsᵉ
open import foundation.contractible-mapsᵉ
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.embeddingsᵉ
open import foundation.equivalencesᵉ
open import foundation.fibers-of-mapsᵉ
open import foundation.functoriality-dependent-function-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.homotopy-inductionᵉ
open import foundation.identity-typesᵉ
open import foundation.span-diagramsᵉ
open import foundation.structure-identity-principleᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.universe-levelsᵉ

open import synthetic-homotopy-theory.cocones-under-spansᵉ
open import synthetic-homotopy-theory.dependent-cocones-under-spansᵉ
open import synthetic-homotopy-theory.dependent-universal-property-pushoutsᵉ
open import synthetic-homotopy-theory.descent-data-pushoutsᵉ
open import synthetic-homotopy-theory.families-descent-data-pushoutsᵉ
open import synthetic-homotopy-theory.universal-property-pushoutsᵉ
```

</details>

## Idea

Givenᵉ [descentᵉ data](synthetic-homotopy-theory.descent-data-pushouts.mdᵉ)
`(PA,ᵉ PB,ᵉ PS)`ᵉ forᵉ theᵉ [pushout](synthetic-homotopy-theory.pushouts.mdᵉ) ofᵉ aᵉ
[spanᵉ diagram](foundation.span-diagrams.mdᵉ) `𝒮`,ᵉ weᵉ defineᵉ theᵉ typeᵉ ofᵉ
{{#conceptᵉ "sections"ᵉ Disambiguation="descentᵉ data forᵉ pushouts"ᵉ Agda=section-descent-data-pushoutᵉ}}
to beᵉ theᵉ typeᵉ ofᵉ triplesᵉ `(tA,ᵉ tB,ᵉ tS)`,ᵉ where

```text
  tAᵉ : (aᵉ : Aᵉ) → PAᵉ aᵉ
  tBᵉ : (bᵉ : Bᵉ) → PBᵉ bᵉ
```

areᵉ [sections](foundation.dependent-function-types.mdᵉ) ofᵉ theᵉ typeᵉ familiesᵉ `PA`ᵉ
andᵉ `PB`,ᵉ respectively,ᵉ andᵉ `tS`ᵉ isᵉ aᵉ coherenceᵉ datum,ᵉ witnessingᵉ thatᵉ forᵉ everyᵉ
`sᵉ : S`,ᵉ theᵉ dependentᵉ triangleᵉ

```text
           tAᵉ ∘ᵉ fᵉ
  (sᵉ : Sᵉ) -------->ᵉ PAᵉ (fᵉ sᵉ)
          \ᵉ       /ᵉ
    tBᵉ ∘ᵉ gᵉ  \ᵉ   /ᵉ PSᵉ sᵉ
             ∨ᵉ ∨ᵉ
          PBᵉ (gᵉ sᵉ)
```

[commutes](foundation.commuting-triangles-of-maps.md).ᵉ

Weᵉ showᵉ thatᵉ forᵉ aᵉ
[familyᵉ with descentᵉ data](synthetic-homotopy-theory.families-descent-data-pushouts.mdᵉ)
`Pᵉ ≈ᵉ (PA,ᵉ PB,ᵉ PS)`,ᵉ theᵉ typeᵉ ofᵉ sectionsᵉ `(xᵉ : Xᵉ) → Pᵉ x`ᵉ ofᵉ `P`ᵉ isᵉ
[equivalent](foundation-core.equivalences.mdᵉ) to theᵉ typeᵉ ofᵉ sectionsᵉ ofᵉ
`(PA,ᵉ PB,ᵉ PS)`.ᵉ

Furthermore,ᵉ aᵉ
{{#conceptᵉ "homotopy"ᵉ Disambiguation="sectionsᵉ ofᵉ descentᵉ data forᵉ pushouts"ᵉ Agda=htpy-section-descent-data-pushoutᵉ}}
betweenᵉ sectionsᵉ `(tA,ᵉ tB,ᵉ tS)`ᵉ andᵉ `(rA,ᵉ rB,ᵉ rS)`ᵉ consistsᵉ ofᵉ component-wiseᵉ
[homotopies](foundation-core.homotopies.mdᵉ)

```text
  HAᵉ : tAᵉ ~ᵉ rAᵉ
  HBᵉ : tBᵉ ~ᵉ rBᵉ
```

andᵉ aᵉ coherenceᵉ datumᵉ `HS`,ᵉ witnessingᵉ thatᵉ forᵉ eachᵉ `sᵉ : S`,ᵉ theᵉ squareᵉ ofᵉ
identificationsᵉ

```text
               PSᵉ sᵉ ·lᵉ HAᵉ fsᵉ
  PSᵉ sᵉ (tAᵉ fsᵉ) ------------>ᵉ PSᵉ sᵉ (rAᵉ fsᵉ)
       |                          |
  tSᵉ sᵉ |                          | rSᵉ sᵉ
       |                          |
       ∨ᵉ                          ∨ᵉ
     tBᵉ gsᵉ ------------------->ᵉ rBᵉ gsᵉ
                   HBᵉ gsᵉ
```

[commutes](foundation-core.commuting-squares-of-identifications.md).ᵉ

Weᵉ showᵉ thatᵉ theᵉ identityᵉ typesᵉ ofᵉ sectionsᵉ ofᵉ descentᵉ data areᵉ characterizedᵉ byᵉ
homotopiesᵉ betweenᵉ them.ᵉ

## Definitions

### Sections of descent data for pushouts

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {𝒮ᵉ : span-diagramᵉ l1ᵉ l2ᵉ l3ᵉ}
  (Pᵉ : descent-data-pushoutᵉ 𝒮ᵉ l4ᵉ)
  where

  section-descent-data-pushoutᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  section-descent-data-pushoutᵉ =
    Σᵉ ( (aᵉ : domain-span-diagramᵉ 𝒮ᵉ) → left-family-descent-data-pushoutᵉ Pᵉ aᵉ)
      ( λ tAᵉ →
        Σᵉ ( (bᵉ : codomain-span-diagramᵉ 𝒮ᵉ) →
            right-family-descent-data-pushoutᵉ Pᵉ bᵉ)
          ( λ tBᵉ →
            (sᵉ : spanning-type-span-diagramᵉ 𝒮ᵉ) →
            map-family-descent-data-pushoutᵉ Pᵉ sᵉ
              ( tAᵉ (left-map-span-diagramᵉ 𝒮ᵉ sᵉ)) ＝ᵉ
            tBᵉ (right-map-span-diagramᵉ 𝒮ᵉ sᵉ)))

  module _
    (tᵉ : section-descent-data-pushoutᵉ)
    where

    left-map-section-descent-data-pushoutᵉ :
      (aᵉ : domain-span-diagramᵉ 𝒮ᵉ) → left-family-descent-data-pushoutᵉ Pᵉ aᵉ
    left-map-section-descent-data-pushoutᵉ = pr1ᵉ tᵉ

    right-map-section-descent-data-pushoutᵉ :
      (bᵉ : codomain-span-diagramᵉ 𝒮ᵉ) → right-family-descent-data-pushoutᵉ Pᵉ bᵉ
    right-map-section-descent-data-pushoutᵉ = pr1ᵉ (pr2ᵉ tᵉ)

    coherence-section-descent-data-pushoutᵉ :
      (sᵉ : spanning-type-span-diagramᵉ 𝒮ᵉ) →
      map-family-descent-data-pushoutᵉ Pᵉ sᵉ
        ( left-map-section-descent-data-pushoutᵉ (left-map-span-diagramᵉ 𝒮ᵉ sᵉ)) ＝ᵉ
      right-map-section-descent-data-pushoutᵉ (right-map-span-diagramᵉ 𝒮ᵉ sᵉ)
    coherence-section-descent-data-pushoutᵉ = pr2ᵉ (pr2ᵉ tᵉ)
```

### Homotopies of sections of descent data for pushouts

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {𝒮ᵉ : span-diagramᵉ l1ᵉ l2ᵉ l3ᵉ}
  (Pᵉ : descent-data-pushoutᵉ 𝒮ᵉ l4ᵉ)
  (rᵉ tᵉ : section-descent-data-pushoutᵉ Pᵉ)
  where

  htpy-section-descent-data-pushoutᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  htpy-section-descent-data-pushoutᵉ =
    Σᵉ ( left-map-section-descent-data-pushoutᵉ Pᵉ rᵉ ~ᵉ
        left-map-section-descent-data-pushoutᵉ Pᵉ tᵉ)
      ( λ HAᵉ →
        Σᵉ ( right-map-section-descent-data-pushoutᵉ Pᵉ rᵉ ~ᵉ
            right-map-section-descent-data-pushoutᵉ Pᵉ tᵉ)
          ( λ HBᵉ →
            (sᵉ : spanning-type-span-diagramᵉ 𝒮ᵉ) →
            coherence-square-identificationsᵉ
              ( apᵉ
                ( map-family-descent-data-pushoutᵉ Pᵉ sᵉ)
                ( HAᵉ (left-map-span-diagramᵉ 𝒮ᵉ sᵉ)))
              ( coherence-section-descent-data-pushoutᵉ Pᵉ rᵉ sᵉ)
              ( coherence-section-descent-data-pushoutᵉ Pᵉ tᵉ sᵉ)
              ( HBᵉ (right-map-span-diagramᵉ 𝒮ᵉ sᵉ))))
```

### The reflexive homotopy of sections of descent data for pushouts

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {𝒮ᵉ : span-diagramᵉ l1ᵉ l2ᵉ l3ᵉ}
  (Pᵉ : descent-data-pushoutᵉ 𝒮ᵉ l4ᵉ)
  (rᵉ : section-descent-data-pushoutᵉ Pᵉ)
  where

  refl-htpy-section-descent-data-pushoutᵉ :
    htpy-section-descent-data-pushoutᵉ Pᵉ rᵉ rᵉ
  pr1ᵉ refl-htpy-section-descent-data-pushoutᵉ = refl-htpyᵉ
  pr1ᵉ (pr2ᵉ refl-htpy-section-descent-data-pushoutᵉ) = refl-htpyᵉ
  pr2ᵉ (pr2ᵉ refl-htpy-section-descent-data-pushoutᵉ) = right-unit-htpyᵉ
```

## Properties

### Characterization of identity types of sections of descent data for pushouts

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {𝒮ᵉ : span-diagramᵉ l1ᵉ l2ᵉ l3ᵉ}
  (Pᵉ : descent-data-pushoutᵉ 𝒮ᵉ l4ᵉ)
  (rᵉ : section-descent-data-pushoutᵉ Pᵉ)
  where

  htpy-eq-section-descent-data-pushoutᵉ :
    (tᵉ : section-descent-data-pushoutᵉ Pᵉ) →
    (rᵉ ＝ᵉ tᵉ) → htpy-section-descent-data-pushoutᵉ Pᵉ rᵉ tᵉ
  htpy-eq-section-descent-data-pushoutᵉ .rᵉ reflᵉ =
    refl-htpy-section-descent-data-pushoutᵉ Pᵉ rᵉ

  abstract
    is-torsorial-htpy-section-descent-data-pushoutᵉ :
      is-torsorialᵉ (htpy-section-descent-data-pushoutᵉ Pᵉ rᵉ)
    is-torsorial-htpy-section-descent-data-pushoutᵉ =
      is-torsorial-Eq-structureᵉ
        ( is-torsorial-htpyᵉ (left-map-section-descent-data-pushoutᵉ Pᵉ rᵉ))
        ( left-map-section-descent-data-pushoutᵉ Pᵉ rᵉ ,ᵉ refl-htpyᵉ)
        ( is-torsorial-Eq-structureᵉ
          ( is-torsorial-htpyᵉ (right-map-section-descent-data-pushoutᵉ Pᵉ rᵉ))
          ( right-map-section-descent-data-pushoutᵉ Pᵉ rᵉ ,ᵉ refl-htpyᵉ)
          ( is-torsorial-htpyᵉ
            ( coherence-section-descent-data-pushoutᵉ Pᵉ rᵉ ∙hᵉ refl-htpyᵉ)))

  is-equiv-htpy-eq-section-descent-data-pushoutᵉ :
    (tᵉ : section-descent-data-pushoutᵉ Pᵉ) →
    is-equivᵉ (htpy-eq-section-descent-data-pushoutᵉ tᵉ)
  is-equiv-htpy-eq-section-descent-data-pushoutᵉ =
    fundamental-theorem-idᵉ
      ( is-torsorial-htpy-section-descent-data-pushoutᵉ)
      ( htpy-eq-section-descent-data-pushoutᵉ)

  extensionality-section-descent-data-pushoutᵉ :
    (tᵉ : section-descent-data-pushoutᵉ Pᵉ) →
    (rᵉ ＝ᵉ tᵉ) ≃ᵉ htpy-section-descent-data-pushoutᵉ Pᵉ rᵉ tᵉ
  pr1ᵉ (extensionality-section-descent-data-pushoutᵉ tᵉ) =
    htpy-eq-section-descent-data-pushoutᵉ tᵉ
  pr2ᵉ (extensionality-section-descent-data-pushoutᵉ tᵉ) =
    is-equiv-htpy-eq-section-descent-data-pushoutᵉ tᵉ
```

### Sections of families over a pushout correspond to sections of the corresponding descent data

**Proof:**ᵉ Givenᵉ aᵉ familyᵉ with descentᵉ data `Pᵉ ≈ᵉ (PA,ᵉ PB,ᵉ PS)`,ᵉ noteᵉ thatᵉ aᵉ
sectionᵉ `tᵉ : (xᵉ : Xᵉ) → Pᵉ x`ᵉ ofᵉ `P`ᵉ inducesᵉ aᵉ sectionᵉ `(tA,ᵉ tB,ᵉ tS)`ᵉ ofᵉ
`(PA,ᵉ PB,ᵉ PS)`,ᵉ where

```text
  tAᵉ aᵉ :=ᵉ eAᵉ (tiaᵉ)
  tBᵉ bᵉ :=ᵉ eBᵉ (tjb),ᵉ
```

andᵉ `tSᵉ s`ᵉ isᵉ givenᵉ byᵉ theᵉ chainᵉ ofᵉ identificationsᵉ

```text
  PSᵉ sᵉ (eAᵉ (tifsᵉ))
  = eBᵉ (trᵉ Pᵉ (Hᵉ sᵉ) (tifsᵉ))   byᵉ coherenceᵉ ofᵉ Pᵉ ≈ᵉ (PA,ᵉ PB,ᵉ PSᵉ)
  = eBᵉ (tjgsᵉ)                byᵉ apdᵉ tᵉ (Hᵉ sᵉ)
```

Thisᵉ mapᵉ factorsᵉ throughᵉ theᵉ dependentᵉ coconeᵉ mapᵉ

```text
                dependent-cocone-mapᵉ
  (xᵉ : Xᵉ) → Pᵉ xᵉ -------------------->ᵉ dependent-coconeᵉ Pᵉ
                \ᵉ                  /ᵉ
                  \ᵉ              /ᵉ
                    \ᵉ          /ᵉ
                      ∨ᵉ      ∨ᵉ
                sectionᵉ (PA,ᵉ PB,ᵉ PS),ᵉ
```

where theᵉ rightᵉ mapᵉ takesᵉ `(dA,ᵉ dB,ᵉ dS)`ᵉ to

```text
  tAᵉ aᵉ :=ᵉ eAᵉ (dAᵉ aᵉ)
  tBᵉ bᵉ :=ᵉ eBᵉ (dBᵉ aᵉ)
  tSᵉ sᵉ : PSᵉ sᵉ (eAᵉ (dAᵉ fsᵉ))
         = eBᵉ (trᵉ Pᵉ (Hᵉ sᵉ) (dAᵉ fsᵉ))  byᵉ coherenceᵉ ofᵉ Pᵉ ≈ᵉ (PA,ᵉ PB,ᵉ PSᵉ)
         = eBᵉ (dBᵉ gsᵉ)               byᵉ dS.ᵉ
```

Theᵉ topᵉ mapᵉ isᵉ anᵉ equivalence,ᵉ sinceᵉ weᵉ assumeᵉ `X`ᵉ to beᵉ aᵉ pushout,ᵉ andᵉ theᵉ
rightᵉ mapᵉ isᵉ anᵉ equivalence,ᵉ sinceᵉ concatenatingᵉ anᵉ identificationᵉ isᵉ anᵉ
equivalence,ᵉ andᵉ theᵉ actionᵉ onᵉ identificationsᵉ ofᵉ equivalencesᵉ isᵉ anᵉ
equivalence.ᵉ Itᵉ followsᵉ thatᵉ theᵉ leftᵉ mapᵉ isᵉ anᵉ equivalenceᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level} {𝒮ᵉ : span-diagramᵉ l1ᵉ l2ᵉ l3ᵉ}
  {Xᵉ : UUᵉ l4ᵉ} {cᵉ : cocone-span-diagramᵉ 𝒮ᵉ Xᵉ}
  (Pᵉ : family-with-descent-data-pushoutᵉ cᵉ l5ᵉ)
  where

  section-descent-data-section-family-cocone-span-diagramᵉ :
    ((xᵉ : Xᵉ) → family-cocone-family-with-descent-data-pushoutᵉ Pᵉ xᵉ) →
    section-descent-data-pushoutᵉ
      ( descent-data-family-with-descent-data-pushoutᵉ Pᵉ)
  pr1ᵉ (section-descent-data-section-family-cocone-span-diagramᵉ fᵉ) aᵉ =
    left-map-family-with-descent-data-pushoutᵉ Pᵉ aᵉ
      ( fᵉ (horizontal-map-coconeᵉ _ _ cᵉ aᵉ))
  pr1ᵉ (pr2ᵉ (section-descent-data-section-family-cocone-span-diagramᵉ fᵉ)) bᵉ =
    right-map-family-with-descent-data-pushoutᵉ Pᵉ bᵉ
      ( fᵉ (vertical-map-coconeᵉ _ _ cᵉ bᵉ))
  pr2ᵉ (pr2ᵉ (section-descent-data-section-family-cocone-span-diagramᵉ fᵉ)) sᵉ =
    ( invᵉ
      ( coherence-family-with-descent-data-pushoutᵉ Pᵉ sᵉ
        ( fᵉ (horizontal-map-coconeᵉ _ _ cᵉ (left-map-span-diagramᵉ 𝒮ᵉ sᵉ))))) ∙ᵉ
    ( apᵉ
      ( right-map-family-with-descent-data-pushoutᵉ Pᵉ
        ( right-map-span-diagramᵉ 𝒮ᵉ sᵉ))
      ( apdᵉ fᵉ (coherence-square-coconeᵉ _ _ cᵉ sᵉ)))

  section-descent-data-dependent-cocone-span-diagramᵉ :
    dependent-cocone-span-diagramᵉ cᵉ
      ( family-cocone-family-with-descent-data-pushoutᵉ Pᵉ) →
    section-descent-data-pushoutᵉ
      ( descent-data-family-with-descent-data-pushoutᵉ Pᵉ)
  pr1ᵉ (section-descent-data-dependent-cocone-span-diagramᵉ dᵉ) aᵉ =
    left-map-family-with-descent-data-pushoutᵉ Pᵉ aᵉ
      ( horizontal-map-dependent-coconeᵉ _ _ _ _ dᵉ aᵉ)
  pr1ᵉ (pr2ᵉ (section-descent-data-dependent-cocone-span-diagramᵉ dᵉ)) bᵉ =
    right-map-family-with-descent-data-pushoutᵉ Pᵉ bᵉ
      ( vertical-map-dependent-coconeᵉ _ _ _ _ dᵉ bᵉ)
  pr2ᵉ (pr2ᵉ (section-descent-data-dependent-cocone-span-diagramᵉ dᵉ)) sᵉ =
    ( invᵉ (coherence-family-with-descent-data-pushoutᵉ Pᵉ sᵉ _)) ∙ᵉ
    ( apᵉ
      ( right-map-family-with-descent-data-pushoutᵉ Pᵉ
        ( right-map-span-diagramᵉ 𝒮ᵉ sᵉ))
      ( coherence-square-dependent-coconeᵉ _ _ _ _ dᵉ sᵉ))

  abstract
    is-equiv-section-descent-data-depedent-cocone-span-diagramᵉ :
      is-equivᵉ section-descent-data-dependent-cocone-span-diagramᵉ
    is-equiv-section-descent-data-depedent-cocone-span-diagramᵉ =
      is-equiv-map-Σᵉ _
        ( is-equiv-map-Π-is-fiberwise-equivᵉ
          ( is-equiv-left-map-family-with-descent-data-pushoutᵉ Pᵉ))
        ( λ tAᵉ →
          is-equiv-map-Σᵉ _
            ( is-equiv-map-Π-is-fiberwise-equivᵉ
              ( is-equiv-right-map-family-with-descent-data-pushoutᵉ Pᵉ))
            ( λ tBᵉ →
              is-equiv-map-Π-is-fiberwise-equivᵉ
                ( λ sᵉ →
                  is-equiv-compᵉ _ _
                    ( is-emb-equivᵉ
                      ( right-equiv-family-with-descent-data-pushoutᵉ Pᵉ
                        ( right-map-span-diagramᵉ 𝒮ᵉ sᵉ))
                      ( _)
                      ( _))
                    ( is-equiv-inv-concatᵉ _ _))))

  triangle-section-descent-data-section-family-cocone-span-diagramᵉ :
    coherence-triangle-mapsᵉ
      ( section-descent-data-section-family-cocone-span-diagramᵉ)
      ( section-descent-data-dependent-cocone-span-diagramᵉ)
      ( dependent-cocone-map-span-diagramᵉ cᵉ
        ( family-cocone-family-with-descent-data-pushoutᵉ Pᵉ))
  triangle-section-descent-data-section-family-cocone-span-diagramᵉ = refl-htpyᵉ

  abstract
    is-equiv-section-descent-data-section-family-cocone-span-diagramᵉ :
      universal-property-pushoutᵉ _ _ cᵉ →
      is-equivᵉ (section-descent-data-section-family-cocone-span-diagramᵉ)
    is-equiv-section-descent-data-section-family-cocone-span-diagramᵉ up-cᵉ =
      is-equiv-left-map-triangleᵉ
        ( section-descent-data-section-family-cocone-span-diagramᵉ)
        ( section-descent-data-dependent-cocone-span-diagramᵉ)
        ( dependent-cocone-map-span-diagramᵉ cᵉ
          ( family-cocone-family-with-descent-data-pushoutᵉ Pᵉ))
        ( triangle-section-descent-data-section-family-cocone-span-diagramᵉ)
        ( dependent-universal-property-universal-property-pushoutᵉ _ _ _ up-cᵉ
          ( family-cocone-family-with-descent-data-pushoutᵉ Pᵉ))
        ( is-equiv-section-descent-data-depedent-cocone-span-diagramᵉ)
```

Asᵉ aᵉ corollary,ᵉ forᵉ anyᵉ givenᵉ sectionᵉ `(tA,ᵉ tB,ᵉ tS)`ᵉ ofᵉ `(PA,ᵉ PB,ᵉ PS)`,ᵉ thereᵉ isᵉ
aᵉ uniqueᵉ sectionᵉ `tᵉ : (xᵉ : Xᵉ) → Pᵉ x`ᵉ ofᵉ `P`ᵉ suchᵉ thatᵉ itsᵉ inducedᵉ sectionᵉ ofᵉ
`(PA,ᵉ PB,ᵉ PS)`ᵉ isᵉ homotopicᵉ to `(tA,ᵉ tB,ᵉ tS)`.ᵉ

**Proof:**ᵉ Sinceᵉ theᵉ mapᵉ takingᵉ sectionsᵉ ofᵉ `P`ᵉ to sectionsᵉ ofᵉ `(PA,ᵉ PB,ᵉ PS)`ᵉ isᵉ
anᵉ equivalence,ᵉ itᵉ hasᵉ contractibleᵉ fibers.ᵉ Theᵉ fiberᵉ atᵉ `(tA,ᵉ tB,ᵉ tS)`ᵉ isᵉ theᵉ
typeᵉ ofᵉ sectionsᵉ ofᵉ `P`ᵉ thatᵉ induceᵉ aᵉ sectionᵉ ofᵉ `(PA,ᵉ PB,ᵉ PS)`ᵉ whichᵉ isᵉ
identifiedᵉ with `(tA,ᵉ tB,ᵉ tS)`,ᵉ andᵉ suchᵉ identificationsᵉ areᵉ characterizedᵉ byᵉ
homotopiesᵉ ofᵉ sectionsᵉ ofᵉ `(PA,ᵉ PB,ᵉ PS)`.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level} {𝒮ᵉ : span-diagramᵉ l1ᵉ l2ᵉ l3ᵉ}
  {Xᵉ : UUᵉ l4ᵉ} {cᵉ : cocone-span-diagramᵉ 𝒮ᵉ Xᵉ}
  (up-cᵉ : universal-property-pushoutᵉ _ _ cᵉ)
  (Pᵉ : family-with-descent-data-pushoutᵉ cᵉ l5ᵉ)
  (tᵉ :
    section-descent-data-pushoutᵉ
      ( descent-data-family-with-descent-data-pushoutᵉ Pᵉ))
  where

  abstract
    uniqueness-section-family-section-descent-data-pushoutᵉ :
      is-contrᵉ
        ( Σᵉ ( (xᵉ : Xᵉ) → family-cocone-family-with-descent-data-pushoutᵉ Pᵉ xᵉ)
            ( λ hᵉ →
              htpy-section-descent-data-pushoutᵉ
                ( descent-data-family-with-descent-data-pushoutᵉ Pᵉ)
                ( section-descent-data-section-family-cocone-span-diagramᵉ Pᵉ hᵉ)
                ( tᵉ)))
    uniqueness-section-family-section-descent-data-pushoutᵉ =
      is-contr-equiv'ᵉ
        ( fiberᵉ (section-descent-data-section-family-cocone-span-diagramᵉ Pᵉ) tᵉ)
        ( equiv-totᵉ
          ( λ hᵉ →
            extensionality-section-descent-data-pushoutᵉ
              ( descent-data-family-with-descent-data-pushoutᵉ Pᵉ)
              ( _)
              ( tᵉ)))
        ( is-contr-map-is-equivᵉ
          ( is-equiv-section-descent-data-section-family-cocone-span-diagramᵉ Pᵉ
            ( up-cᵉ))
          ( tᵉ))

  section-family-section-descent-data-pushoutᵉ :
    (xᵉ : Xᵉ) → family-cocone-family-with-descent-data-pushoutᵉ Pᵉ xᵉ
  section-family-section-descent-data-pushoutᵉ =
    pr1ᵉ (centerᵉ uniqueness-section-family-section-descent-data-pushoutᵉ)

  htpy-section-family-section-descent-data-pushoutᵉ :
    htpy-section-descent-data-pushoutᵉ
      ( descent-data-family-with-descent-data-pushoutᵉ Pᵉ)
      ( section-descent-data-section-family-cocone-span-diagramᵉ Pᵉ
        ( section-family-section-descent-data-pushoutᵉ))
      ( tᵉ)
  htpy-section-family-section-descent-data-pushoutᵉ =
    pr2ᵉ (centerᵉ uniqueness-section-family-section-descent-data-pushoutᵉ)
```