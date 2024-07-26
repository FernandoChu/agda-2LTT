# Descent property of sequential colimits

```agda
module synthetic-homotopy-theory.descent-property-sequential-colimitsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.binary-homotopiesᵉ
open import foundation.commuting-triangles-of-mapsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equality-dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.functoriality-dependent-function-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.univalenceᵉ
open import foundation.universe-levelsᵉ

open import synthetic-homotopy-theory.cocones-under-sequential-diagramsᵉ
open import synthetic-homotopy-theory.descent-data-sequential-colimitsᵉ
open import synthetic-homotopy-theory.sequential-diagramsᵉ
open import synthetic-homotopy-theory.universal-property-sequential-colimitsᵉ
```

</details>

## Idea

Theᵉ
{{#conceptᵉ "descentᵉ property"ᵉ Disambiguation="sequentialᵉ colimits"ᵉ Agda=equiv-descent-data-family-cocone-sequential-diagramᵉ}}
ofᵉ
[sequentialᵉ colimits](synthetic-homotopy-theory.universal-property-sequential-colimits.mdᵉ)
characterizesᵉ typeᵉ familiesᵉ overᵉ sequentialᵉ colimitsᵉ asᵉ
[descentᵉ data](synthetic-homotopy-theory.descent-data-sequential-colimits.mdᵉ)
overᵉ theᵉ baseᵉ
[sequentialᵉ diagram](synthetic-homotopy-theory.sequential-diagrams.md).ᵉ

Givenᵉ aᵉ sequentialᵉ diagramᵉ `(A,ᵉ a)`ᵉ andᵉ aᵉ
[cocone](synthetic-homotopy-theory.cocones-under-sequential-diagrams.mdᵉ) with
vertexᵉ `X`,ᵉ thereᵉ isᵉ aᵉ commutingᵉ triangleᵉ

```text
          cocone-mapᵉ
  (Xᵉ → 𝒰ᵉ) --------->ᵉ coconeᵉ Aᵉ 𝒰ᵉ
           \ᵉ       /ᵉ
            \ᵉ     /ᵉ
             \ᵉ   /ᵉ
              ∨ᵉ ∨ᵉ
         descent-dataᵉ Aᵉ .ᵉ
```

Fromᵉ [univalence](foundation-core.univalence.mdᵉ) itᵉ followsᵉ thatᵉ theᵉ rightᵉ mapᵉ
isᵉ anᵉ equivalence.ᵉ Ifᵉ `X`ᵉ isᵉ aᵉ colimitᵉ ofᵉ `A`,ᵉ thenᵉ weᵉ haveᵉ thatᵉ theᵉ topᵉ mapᵉ isᵉ
anᵉ equivalence,ᵉ whichᵉ implesᵉ thatᵉ theᵉ leftᵉ mapᵉ isᵉ anᵉ equivalence.ᵉ

## Theorem

```agda
module _
  {l1ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ}
  where

  equiv-descent-data-cocone-sequential-diagramᵉ :
    {l2ᵉ : Level} →
    cocone-sequential-diagramᵉ Aᵉ (UUᵉ l2ᵉ) ≃ᵉ
    descent-data-sequential-colimitᵉ Aᵉ l2ᵉ
  equiv-descent-data-cocone-sequential-diagramᵉ =
    equiv-totᵉ
      ( λ Bᵉ →
        equiv-Π-equiv-familyᵉ
          ( λ nᵉ → equiv-Π-equiv-familyᵉ (λ aᵉ → equiv-univalenceᵉ)))

  descent-data-cocone-sequential-diagramᵉ :
    {l2ᵉ : Level} →
    cocone-sequential-diagramᵉ Aᵉ (UUᵉ l2ᵉ) →
    descent-data-sequential-colimitᵉ Aᵉ l2ᵉ
  descent-data-cocone-sequential-diagramᵉ =
    map-equivᵉ equiv-descent-data-cocone-sequential-diagramᵉ

  is-equiv-descent-data-cocone-sequential-diagramᵉ :
    {l2ᵉ : Level} → is-equivᵉ (descent-data-cocone-sequential-diagramᵉ {l2ᵉ})
  is-equiv-descent-data-cocone-sequential-diagramᵉ =
    is-equiv-map-equivᵉ equiv-descent-data-cocone-sequential-diagramᵉ

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ}
  {Xᵉ : UUᵉ l2ᵉ} (cᵉ : cocone-sequential-diagramᵉ Aᵉ Xᵉ)
  where

  triangle-descent-data-family-cocone-sequential-diagramᵉ :
    {l3ᵉ : Level} →
    coherence-triangle-mapsᵉ
      ( descent-data-family-cocone-sequential-diagramᵉ cᵉ)
      ( descent-data-cocone-sequential-diagramᵉ)
      ( cocone-map-sequential-diagramᵉ cᵉ {Yᵉ = UUᵉ l3ᵉ})
  triangle-descent-data-family-cocone-sequential-diagramᵉ Pᵉ =
    eq-pair-eq-fiberᵉ
      ( eq-binary-htpyᵉ _ _
        ( λ nᵉ aᵉ →
          invᵉ
            ( compute-equiv-eq-apᵉ
              ( coherence-cocone-sequential-diagramᵉ cᵉ nᵉ aᵉ))))

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ}
  {Xᵉ : UUᵉ l2ᵉ} {cᵉ : cocone-sequential-diagramᵉ Aᵉ Xᵉ}
  (up-cᵉ : universal-property-sequential-colimitᵉ cᵉ)
  where

  is-equiv-descent-data-family-cocone-sequential-diagramᵉ :
    is-equivᵉ (descent-data-family-cocone-sequential-diagramᵉ cᵉ {l3ᵉ})
  is-equiv-descent-data-family-cocone-sequential-diagramᵉ =
    is-equiv-left-map-triangleᵉ
      ( descent-data-family-cocone-sequential-diagramᵉ cᵉ)
      ( descent-data-cocone-sequential-diagramᵉ)
      ( cocone-map-sequential-diagramᵉ cᵉ)
      ( triangle-descent-data-family-cocone-sequential-diagramᵉ cᵉ)
      ( up-cᵉ (UUᵉ l3ᵉ))
      ( is-equiv-descent-data-cocone-sequential-diagramᵉ)

  equiv-descent-data-family-cocone-sequential-diagramᵉ :
    (Xᵉ → UUᵉ l3ᵉ) ≃ᵉ descent-data-sequential-colimitᵉ Aᵉ l3ᵉ
  pr1ᵉ equiv-descent-data-family-cocone-sequential-diagramᵉ =
    descent-data-family-cocone-sequential-diagramᵉ cᵉ
  pr2ᵉ equiv-descent-data-family-cocone-sequential-diagramᵉ =
    is-equiv-descent-data-family-cocone-sequential-diagramᵉ

  family-cocone-descent-data-sequential-colimitᵉ :
    descent-data-sequential-colimitᵉ Aᵉ l3ᵉ → (Xᵉ → UUᵉ l3ᵉ)
  family-cocone-descent-data-sequential-colimitᵉ =
    map-inv-equivᵉ
      ( equiv-descent-data-family-cocone-sequential-diagramᵉ)
```