# The flattening lemma for sequential colimits

```agda
module synthetic-homotopy-theory.flattening-lemma-sequential-colimitsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.equivalences-double-arrowsᵉ
open import foundation.function-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ

open import synthetic-homotopy-theory.cocones-under-sequential-diagramsᵉ
open import synthetic-homotopy-theory.coforksᵉ
open import synthetic-homotopy-theory.coforks-cocones-under-sequential-diagramsᵉ
open import synthetic-homotopy-theory.dependent-universal-property-sequential-colimitsᵉ
open import synthetic-homotopy-theory.equivalences-coforks-under-equivalences-double-arrowsᵉ
open import synthetic-homotopy-theory.families-descent-data-sequential-colimitsᵉ
open import synthetic-homotopy-theory.flattening-lemma-coequalizersᵉ
open import synthetic-homotopy-theory.sequential-diagramsᵉ
open import synthetic-homotopy-theory.total-cocones-families-sequential-diagramsᵉ
open import synthetic-homotopy-theory.total-sequential-diagramsᵉ
open import synthetic-homotopy-theory.universal-property-coequalizersᵉ
open import synthetic-homotopy-theory.universal-property-sequential-colimitsᵉ
```

</details>

## Idea

Theᵉ
{{#conceptᵉ "flatteningᵉ lemma"ᵉ Disambiguation="sequentialᵉ colimits"ᵉ Agda=flattening-lemma-sequential-colimitᵉ}}
forᵉ
[sequentialᵉ colimits](synthetic-homotopy-theory.universal-property-sequential-colimits.mdᵉ)
statesᵉ thatᵉ sequentialᵉ colimitsᵉ commuteᵉ with
[dependentᵉ pairᵉ types](foundation.dependent-pair-types.md).ᵉ Specifically,ᵉ givenᵉ
aᵉ [cocone](synthetic-homotopy-theory.cocones-under-sequential-diagrams.mdᵉ)

```text
  A₀ᵉ --->ᵉ A₁ᵉ --->ᵉ A₂ᵉ --->ᵉ ⋯ᵉ --->ᵉ Xᵉ
```

with theᵉ universalᵉ propertyᵉ ofᵉ sequentialᵉ colimits,ᵉ andᵉ aᵉ familyᵉ `Pᵉ : Xᵉ → 𝒰`,ᵉ
theᵉ inducedᵉ coconeᵉ underᵉ theᵉ
[totalᵉ sequentialᵉ diagram](synthetic-homotopy-theory.total-sequential-diagrams.mdᵉ)

```text
  Σᵉ (aᵉ : A₀ᵉ) P(i₀ᵉ aᵉ) --->ᵉ Σᵉ (aᵉ : A₁ᵉ) P(i₁ᵉ aᵉ) --->ᵉ ⋯ᵉ --->ᵉ Σᵉ (xᵉ : Xᵉ) P(xᵉ)
```

isᵉ againᵉ aᵉ sequentialᵉ colimit.ᵉ

Theᵉ resultᵉ mayᵉ beᵉ readᵉ asᵉ
`colimₙᵉ (Σᵉ (aᵉ : Aₙᵉ) P(iₙᵉ aᵉ)) ≃ᵉ Σᵉ (aᵉ : colimₙᵉ Aₙᵉ) P(a)`.ᵉ

Moreᵉ generally,ᵉ givenᵉ aᵉ typeᵉ familyᵉ `Pᵉ : Xᵉ → 𝒰`ᵉ andᵉ
[descentᵉ data](synthetic-homotopy-theory.descent-data-sequential-colimits.mdᵉ)
`B`ᵉ
[associatedᵉ to it](synthetic-homotopy-theory.families-descent-data-sequential-colimits.md),ᵉ
weᵉ haveᵉ thatᵉ theᵉ inducedᵉ coconeᵉ

```text
  Σᵉ A₀ᵉ B₀ᵉ --->ᵉ Σᵉ A₁ᵉ B₁ᵉ --->ᵉ ⋯ᵉ --->ᵉ Σᵉ Xᵉ Pᵉ
```

isᵉ aᵉ sequentialᵉ colimit.ᵉ

## Theorems

### Flattening lemma for sequential colimits

Similarlyᵉ to theᵉ proofᵉ ofᵉ theᵉ
[flatteningᵉ lemmaᵉ forᵉ coequalizers](synthetic-homotopy-theory.flattening-lemma-coequalizers.md),ᵉ
thisᵉ proofᵉ usesᵉ theᵉ factᵉ thatᵉ sequentialᵉ colimitsᵉ correspondᵉ to certainᵉ
coequalizers,ᵉ whichᵉ isᵉ recordedᵉ in
[`synthetic-homotopy-theory.dependent-universal-property-sequential-colimits`](synthetic-homotopy-theory.dependent-universal-property-sequential-colimits.md),ᵉ
soᵉ itᵉ sufficesᵉ to invokeᵉ theᵉ flatteningᵉ lemmaᵉ forᵉ coequalizers.ᵉ

**Proof:**ᵉ Theᵉ diagramᵉ weᵉ constructᵉ isᵉ

```text
                               ------->ᵉ
  Σᵉ (nᵉ : ℕᵉ) Σᵉ (aᵉ : Aₙᵉ) P(iₙᵉ aᵉ) ------->ᵉ Σᵉ (nᵉ : ℕᵉ) Σᵉ (aᵉ : Aₙᵉ) P(iₙᵉ aᵉ) ---->ᵉ Σᵉ (xᵉ : Xᵉ) P(xᵉ)
             |                                     |                            |
 inv-assoc-Σᵉ | ≃ᵉ                       inv-assoc-Σᵉ | ≃ᵉ                       idᵉ | ≃ᵉ
             |                                     |                            |
             ∨ᵉ                --------->ᵉ           ∨ᵉ                            ∨ᵉ
   Σᵉ ((n,ᵉ aᵉ) : Σᵉ ℕᵉ Aᵉ) P(iₙᵉ aᵉ) --------->ᵉ Σᵉ ((n,ᵉ aᵉ) : Σᵉ ℕᵉ Aᵉ) P(iₙᵉ aᵉ) ----->ᵉ Σᵉ (xᵉ : Xᵉ) P(xᵉ) ,ᵉ
```

where theᵉ topᵉ isᵉ theᵉ coforkᵉ correspondingᵉ to theᵉ coconeᵉ forᵉ theᵉ flatteningᵉ
lemma,ᵉ andᵉ theᵉ bottomᵉ isᵉ theᵉ coforkᵉ obtainedᵉ byᵉ flatteningᵉ theᵉ coforkᵉ
correspondingᵉ to theᵉ givenᵉ baseᵉ cocone.ᵉ

Byᵉ assumption,ᵉ theᵉ originalᵉ coconeᵉ isᵉ aᵉ sequentialᵉ colimit,ᵉ whichᵉ impliesᵉ thatᵉ
itsᵉ correspondingᵉ coforkᵉ isᵉ aᵉ coequalizer.ᵉ Theᵉ flatteningᵉ lemmaᵉ forᵉ coequalizersᵉ
impliesᵉ thatᵉ theᵉ bottomᵉ coforkᵉ isᵉ aᵉ coequalizer,ᵉ whichᵉ in turnᵉ impliesᵉ thatᵉ theᵉ
topᵉ coforkᵉ isᵉ aᵉ coequalizer,ᵉ henceᵉ theᵉ flatteningᵉ ofᵉ theᵉ originalᵉ coconeᵉ isᵉ aᵉ
sequentialᵉ colimit.ᵉ

```agda
module _
  { l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ} {Xᵉ : UUᵉ l2ᵉ}
  ( cᵉ : cocone-sequential-diagramᵉ Aᵉ Xᵉ)
  ( Pᵉ : Xᵉ → UUᵉ l3ᵉ)
  where

  equiv-double-arrow-flattening-lemma-sequential-colimitᵉ :
    equiv-double-arrowᵉ
      ( double-arrow-sequential-diagramᵉ
        ( total-sequential-diagram-family-cocone-sequential-diagramᵉ cᵉ Pᵉ))
      ( double-arrow-flattening-lemma-coequalizerᵉ
        ( double-arrow-sequential-diagramᵉ Aᵉ)
        ( Pᵉ)
        ( cofork-cocone-sequential-diagramᵉ cᵉ))
  pr1ᵉ equiv-double-arrow-flattening-lemma-sequential-colimitᵉ =
    inv-associative-Σᵉ
      ( ℕᵉ)
      ( family-sequential-diagramᵉ Aᵉ)
      ( Pᵉ ∘ᵉ ind-Σᵉ (map-cocone-sequential-diagramᵉ cᵉ))
  pr1ᵉ (pr2ᵉ equiv-double-arrow-flattening-lemma-sequential-colimitᵉ) =
    inv-associative-Σᵉ
      ( ℕᵉ)
      ( family-sequential-diagramᵉ Aᵉ)
      ( Pᵉ ∘ᵉ ind-Σᵉ (map-cocone-sequential-diagramᵉ cᵉ))
  pr1ᵉ (pr2ᵉ (pr2ᵉ equiv-double-arrow-flattening-lemma-sequential-colimitᵉ)) =
    refl-htpyᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ equiv-double-arrow-flattening-lemma-sequential-colimitᵉ)) =
    refl-htpyᵉ

  equiv-cofork-flattening-lemma-sequential-colimitᵉ :
    equiv-cofork-equiv-double-arrowᵉ
      ( cofork-cocone-sequential-diagramᵉ
        ( total-cocone-family-cocone-sequential-diagramᵉ cᵉ Pᵉ))
      ( cofork-flattening-lemma-coequalizerᵉ
        ( double-arrow-sequential-diagramᵉ Aᵉ)
        ( Pᵉ)
        ( cofork-cocone-sequential-diagramᵉ cᵉ))
      ( equiv-double-arrow-flattening-lemma-sequential-colimitᵉ)
  pr1ᵉ equiv-cofork-flattening-lemma-sequential-colimitᵉ = id-equivᵉ
  pr1ᵉ (pr2ᵉ equiv-cofork-flattening-lemma-sequential-colimitᵉ) =
    refl-htpyᵉ
  pr2ᵉ (pr2ᵉ equiv-cofork-flattening-lemma-sequential-colimitᵉ) =
    inv-htpyᵉ
      ( ( right-unit-htpyᵉ) ∙hᵉ
        ( right-unit-htpyᵉ) ∙hᵉ
        ( left-unit-law-left-whisker-compᵉ
          ( coh-coforkᵉ _
            ( cofork-cocone-sequential-diagramᵉ
              ( total-cocone-family-cocone-sequential-diagramᵉ cᵉ Pᵉ)))))

  abstract
    flattening-lemma-sequential-colimitᵉ :
      universal-property-sequential-colimitᵉ cᵉ →
      universal-property-sequential-colimitᵉ
        ( total-cocone-family-cocone-sequential-diagramᵉ cᵉ Pᵉ)
    flattening-lemma-sequential-colimitᵉ up-cᵉ =
      universal-property-sequential-colimit-universal-property-coequalizerᵉ
        ( total-cocone-family-cocone-sequential-diagramᵉ cᵉ Pᵉ)
        ( universal-property-coequalizer-equiv-cofork-equiv-double-arrowᵉ
          ( cofork-cocone-sequential-diagramᵉ
            ( total-cocone-family-cocone-sequential-diagramᵉ cᵉ Pᵉ))
          ( cofork-flattening-lemma-coequalizerᵉ _
            ( Pᵉ)
            ( cofork-cocone-sequential-diagramᵉ cᵉ))
          ( equiv-double-arrow-flattening-lemma-sequential-colimitᵉ)
          ( equiv-cofork-flattening-lemma-sequential-colimitᵉ)
          ( flattening-lemma-coequalizerᵉ _
            ( Pᵉ)
            ( cofork-cocone-sequential-diagramᵉ cᵉ)
            ( universal-property-coequalizer-universal-property-sequential-colimitᵉ
              ( cᵉ)
              ( up-cᵉ))))
```

### Flattening lemma for sequential colimits with descent data

**Proof:**ᵉ Weᵉ haveᵉ shownᵉ in
[`total-cocones-families-sequential-diagrams`](synthetic-homotopy-theory.total-cocones-families-sequential-diagrams.mdᵉ)
thatᵉ givenᵉ aᵉ familyᵉ `Pᵉ : Xᵉ → 𝒰`ᵉ with itsᵉ descentᵉ data `B`,ᵉ thereᵉ isᵉ anᵉ
[equivalenceᵉ ofᵉ cocones](synthetic-homotopy-theory.equivalences-cocones-under-equivalences-sequential-diagrams.mdᵉ)

```text
     Σᵉ A₀ᵉ B₀ᵉ --------->ᵉ Σᵉ A₁ᵉ B₁ᵉ ------>ᵉ ⋯ᵉ ----->ᵉ Σᵉ Xᵉ Pᵉ
        |                  |                       |
        | ≃ᵉ                | ≃ᵉ                     | ≃ᵉ
        ∨ᵉ                  ∨ᵉ                       ∨ᵉ
  Σᵉ A₀ᵉ (Pᵉ ∘ᵉ i₀ᵉ) --->ᵉ Σᵉ A₁ᵉ (Pᵉ ∘ᵉ i₁ᵉ) --->ᵉ ⋯ᵉ ----->ᵉ Σᵉ Xᵉ Pᵉ .ᵉ
```

Theᵉ bottomᵉ coconeᵉ isᵉ aᵉ sequentialᵉ colimitᵉ byᵉ theᵉ flatteningᵉ lemma,ᵉ andᵉ theᵉ
universalᵉ propertyᵉ ofᵉ sequentialᵉ colimitsᵉ isᵉ preservedᵉ byᵉ equivalences,ᵉ asᵉ shownᵉ
in
[`universal-property-sequential-colimits`](synthetic-homotopy-theory.universal-property-sequential-colimits.md).ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ}
  {Xᵉ : UUᵉ l2ᵉ} (cᵉ : cocone-sequential-diagramᵉ Aᵉ Xᵉ)
  (Pᵉ : family-with-descent-data-sequential-colimitᵉ cᵉ l3ᵉ)
  where

  abstract
    flattening-lemma-descent-data-sequential-colimitᵉ :
      universal-property-sequential-colimitᵉ cᵉ →
      universal-property-sequential-colimitᵉ
        ( total-cocone-family-with-descent-data-sequential-colimitᵉ Pᵉ)
    flattening-lemma-descent-data-sequential-colimitᵉ up-cᵉ =
      universal-property-sequential-colimit-equiv-cocone-equiv-sequential-diagramᵉ
        ( equiv-total-sequential-diagram-family-with-descent-data-sequential-colimitᵉ
          ( Pᵉ))
        ( equiv-total-cocone-family-with-descent-data-sequential-colimitᵉ Pᵉ)
        ( flattening-lemma-sequential-colimitᵉ cᵉ
          ( family-cocone-family-with-descent-data-sequential-colimitᵉ Pᵉ)
          ( up-cᵉ))
```