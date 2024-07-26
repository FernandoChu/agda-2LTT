# The universal property of pushouts

```agda
{-# OPTIONSᵉ --lossy-unificationᵉ #-}

module synthetic-homotopy-theory.universal-property-pushoutsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.commuting-cubes-of-mapsᵉ
open import foundation.commuting-squares-of-mapsᵉ
open import foundation.cones-over-cospan-diagramsᵉ
open import foundation.contractible-mapsᵉ
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equality-dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.fibers-of-mapsᵉ
open import foundation.function-extensionalityᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.precomposition-functionsᵉ
open import foundation.pullbacksᵉ
open import foundation.standard-pullbacksᵉ
open import foundation.subtype-identity-principleᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.universal-property-equivalencesᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ

open import synthetic-homotopy-theory.cocones-under-spansᵉ
open import synthetic-homotopy-theory.pullback-property-pushoutsᵉ
```

</details>

## Idea

Considerᵉ aᵉ spanᵉ `𝒮`ᵉ ofᵉ typesᵉ

```text
      fᵉ     gᵉ
  Aᵉ <---ᵉ Sᵉ --->ᵉ B.ᵉ
```

andᵉ aᵉ typeᵉ `X`ᵉ equippedᵉ with aᵉ
[coconeᵉ structure](synthetic-homotopy-theory.cocones-under-spans.mdᵉ) ofᵉ `S`ᵉ intoᵉ
`X`.ᵉ Theᵉ **universalᵉ propertyᵉ ofᵉ theᵉ pushout**ᵉ ofᵉ `𝒮`ᵉ assertsᵉ thatᵉ `X`ᵉ isᵉ theᵉ
_initialᵉ_ typeᵉ equippedᵉ with suchᵉ coconeᵉ structure.ᵉ Inᵉ otherᵉ words,ᵉ theᵉ
universalᵉ propertyᵉ ofᵉ theᵉ pushoutᵉ ofᵉ `𝒮`ᵉ assertsᵉ thatᵉ theᵉ followingᵉ evaluationᵉ
mapᵉ isᵉ anᵉ equivalenceᵉ:

```text
  (Xᵉ → Yᵉ) → coconeᵉ 𝒮ᵉ Y.ᵉ
```

Thereᵉ areᵉ severalᵉ waysᵉ ofᵉ assertingᵉ aᵉ conditionᵉ equivalentᵉ to theᵉ universalᵉ
propertyᵉ ofᵉ pushouts.ᵉ Theᵉ statementsᵉ andᵉ proofsᵉ ofᵉ mutualᵉ equivalenceᵉ mayᵉ beᵉ
foundᵉ in theᵉ followingᵉ tableᵉ:

{{#includeᵉ tables/pushouts.mdᵉ}}

## Definition

### The universal property of pushouts at a universe level

**Warning.**ᵉ Thisᵉ definitionᵉ isᵉ hereᵉ onlyᵉ becauseᵉ ofᵉ backwardᵉ compatibilityᵉ
reasons,ᵉ andᵉ willᵉ beᵉ removedᵉ in theᵉ future.ᵉ Doᵉ notᵉ useᵉ thisᵉ definitionᵉ in newᵉ
formalizations.ᵉ

```agda
universal-property-pushout-Levelᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (lᵉ : Level) {Sᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ}
  (fᵉ : Sᵉ → Aᵉ) (gᵉ : Sᵉ → Bᵉ) {Xᵉ : UUᵉ l4ᵉ} →
  coconeᵉ fᵉ gᵉ Xᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ ⊔ lsuc lᵉ)
universal-property-pushout-Levelᵉ lᵉ fᵉ gᵉ cᵉ =
  (Yᵉ : UUᵉ lᵉ) → is-equivᵉ (cocone-mapᵉ fᵉ gᵉ {Yᵉ = Yᵉ} cᵉ)
```

### The universal property of pushouts

```agda
universal-property-pushoutᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Sᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ}
  (fᵉ : Sᵉ → Aᵉ) (gᵉ : Sᵉ → Bᵉ) {Xᵉ : UUᵉ l4ᵉ} →
  coconeᵉ fᵉ gᵉ Xᵉ → UUωᵉ
universal-property-pushoutᵉ fᵉ gᵉ cᵉ =
  {lᵉ : Level} → universal-property-pushout-Levelᵉ lᵉ fᵉ gᵉ cᵉ

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level}
  {Sᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ} {Xᵉ : UUᵉ l4ᵉ} {Yᵉ : UUᵉ l5ᵉ}
  (fᵉ : Sᵉ → Aᵉ) (gᵉ : Sᵉ → Bᵉ) (cᵉ : coconeᵉ fᵉ gᵉ Xᵉ)
  (up-cᵉ : universal-property-pushoutᵉ fᵉ gᵉ cᵉ)
  (dᵉ : coconeᵉ fᵉ gᵉ Yᵉ)
  where

  map-universal-property-pushoutᵉ : Xᵉ → Yᵉ
  map-universal-property-pushoutᵉ = map-inv-is-equivᵉ (up-cᵉ Yᵉ) dᵉ

  htpy-cocone-map-universal-property-pushoutᵉ :
    htpy-coconeᵉ fᵉ gᵉ (cocone-mapᵉ fᵉ gᵉ cᵉ map-universal-property-pushoutᵉ) dᵉ
  htpy-cocone-map-universal-property-pushoutᵉ =
    htpy-eq-coconeᵉ
      ( fᵉ)
      ( gᵉ)
      ( cocone-mapᵉ fᵉ gᵉ cᵉ map-universal-property-pushoutᵉ)
      ( dᵉ)
      ( is-section-map-inv-is-equivᵉ (up-cᵉ Yᵉ) dᵉ)

  horizontal-htpy-cocone-map-universal-property-pushoutᵉ :
    map-universal-property-pushoutᵉ ∘ᵉ horizontal-map-coconeᵉ fᵉ gᵉ cᵉ ~ᵉ
    horizontal-map-coconeᵉ fᵉ gᵉ dᵉ
  horizontal-htpy-cocone-map-universal-property-pushoutᵉ =
    horizontal-htpy-coconeᵉ
      ( fᵉ)
      ( gᵉ)
      ( cocone-mapᵉ fᵉ gᵉ cᵉ map-universal-property-pushoutᵉ)
      ( dᵉ)
      ( htpy-cocone-map-universal-property-pushoutᵉ)

  vertical-htpy-cocone-map-universal-property-pushoutᵉ :
    map-universal-property-pushoutᵉ ∘ᵉ vertical-map-coconeᵉ fᵉ gᵉ cᵉ ~ᵉ
    vertical-map-coconeᵉ fᵉ gᵉ dᵉ
  vertical-htpy-cocone-map-universal-property-pushoutᵉ =
    vertical-htpy-coconeᵉ
      ( fᵉ)
      ( gᵉ)
      ( cocone-mapᵉ fᵉ gᵉ cᵉ map-universal-property-pushoutᵉ)
      ( dᵉ)
      ( htpy-cocone-map-universal-property-pushoutᵉ)

  coherence-htpy-cocone-map-universal-property-pushoutᵉ :
    statement-coherence-htpy-coconeᵉ fᵉ gᵉ
      ( cocone-mapᵉ fᵉ gᵉ cᵉ map-universal-property-pushoutᵉ)
      ( dᵉ)
      ( horizontal-htpy-cocone-map-universal-property-pushoutᵉ)
      ( vertical-htpy-cocone-map-universal-property-pushoutᵉ)
  coherence-htpy-cocone-map-universal-property-pushoutᵉ =
    coherence-htpy-coconeᵉ
      ( fᵉ)
      ( gᵉ)
      ( cocone-mapᵉ fᵉ gᵉ cᵉ map-universal-property-pushoutᵉ)
      ( dᵉ)
      ( htpy-cocone-map-universal-property-pushoutᵉ)

  uniqueness-map-universal-property-pushoutᵉ :
    is-contrᵉ ( Σᵉ (Xᵉ → Yᵉ) (λ hᵉ → htpy-coconeᵉ fᵉ gᵉ (cocone-mapᵉ fᵉ gᵉ cᵉ hᵉ) dᵉ))
  uniqueness-map-universal-property-pushoutᵉ =
    is-contr-is-equiv'ᵉ
      ( fiberᵉ (cocone-mapᵉ fᵉ gᵉ cᵉ) dᵉ)
      ( totᵉ (λ hᵉ → htpy-eq-coconeᵉ fᵉ gᵉ (cocone-mapᵉ fᵉ gᵉ cᵉ hᵉ) dᵉ))
      ( is-equiv-tot-is-fiberwise-equivᵉ
        ( λ hᵉ → is-equiv-htpy-eq-coconeᵉ fᵉ gᵉ (cocone-mapᵉ fᵉ gᵉ cᵉ hᵉ) dᵉ))
      ( is-contr-map-is-equivᵉ (up-cᵉ Yᵉ) dᵉ)
```

## Properties

### The 3-for-2 property of pushouts

```agda
module _
  { l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level}
  { Sᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ} {Xᵉ : UUᵉ l4ᵉ} {Yᵉ : UUᵉ l5ᵉ}
  ( fᵉ : Sᵉ → Aᵉ) (gᵉ : Sᵉ → Bᵉ) (cᵉ : coconeᵉ fᵉ gᵉ Xᵉ) (dᵉ : coconeᵉ fᵉ gᵉ Yᵉ)
  ( hᵉ : Xᵉ → Yᵉ) (KLMᵉ : htpy-coconeᵉ fᵉ gᵉ (cocone-mapᵉ fᵉ gᵉ cᵉ hᵉ) dᵉ)
  where

  triangle-map-coconeᵉ :
    { l6ᵉ : Level} (Zᵉ : UUᵉ l6ᵉ) →
    ( cocone-mapᵉ fᵉ gᵉ dᵉ) ~ᵉ (cocone-mapᵉ fᵉ gᵉ cᵉ ∘ᵉ precompᵉ hᵉ Zᵉ)
  triangle-map-coconeᵉ Zᵉ kᵉ =
    invᵉ
      ( ( cocone-map-compᵉ fᵉ gᵉ cᵉ hᵉ kᵉ) ∙ᵉ
        ( apᵉ
          ( λ tᵉ → cocone-mapᵉ fᵉ gᵉ tᵉ kᵉ)
          ( eq-htpy-coconeᵉ fᵉ gᵉ (cocone-mapᵉ fᵉ gᵉ cᵉ hᵉ) dᵉ KLMᵉ)))

  is-equiv-up-pushout-up-pushoutᵉ :
    universal-property-pushoutᵉ fᵉ gᵉ cᵉ →
    universal-property-pushoutᵉ fᵉ gᵉ dᵉ →
    is-equivᵉ hᵉ
  is-equiv-up-pushout-up-pushoutᵉ up-cᵉ up-dᵉ =
    is-equiv-is-equiv-precompᵉ hᵉ
      ( λ Zᵉ →
        is-equiv-top-map-triangleᵉ
          ( cocone-mapᵉ fᵉ gᵉ dᵉ)
          ( cocone-mapᵉ fᵉ gᵉ cᵉ)
          ( precompᵉ hᵉ Zᵉ)
          ( triangle-map-coconeᵉ Zᵉ)
          ( up-cᵉ Zᵉ)
          ( up-dᵉ Zᵉ))

  up-pushout-up-pushout-is-equivᵉ :
    is-equivᵉ hᵉ →
    universal-property-pushoutᵉ fᵉ gᵉ cᵉ →
    universal-property-pushoutᵉ fᵉ gᵉ dᵉ
  up-pushout-up-pushout-is-equivᵉ is-equiv-hᵉ up-cᵉ Zᵉ =
    is-equiv-left-map-triangleᵉ
      ( cocone-mapᵉ fᵉ gᵉ dᵉ)
      ( cocone-mapᵉ fᵉ gᵉ cᵉ)
      ( precompᵉ hᵉ Zᵉ)
      ( triangle-map-coconeᵉ Zᵉ)
      ( is-equiv-precomp-is-equivᵉ hᵉ is-equiv-hᵉ Zᵉ)
      ( up-cᵉ Zᵉ)

  up-pushout-is-equiv-up-pushoutᵉ :
    universal-property-pushoutᵉ fᵉ gᵉ dᵉ →
    is-equivᵉ hᵉ →
    universal-property-pushoutᵉ fᵉ gᵉ cᵉ
  up-pushout-is-equiv-up-pushoutᵉ up-dᵉ is-equiv-hᵉ Zᵉ =
    is-equiv-right-map-triangleᵉ
      ( cocone-mapᵉ fᵉ gᵉ dᵉ)
      ( cocone-mapᵉ fᵉ gᵉ cᵉ)
      ( precompᵉ hᵉ Zᵉ)
      ( triangle-map-coconeᵉ Zᵉ)
      ( up-dᵉ Zᵉ)
      ( is-equiv-precomp-is-equivᵉ hᵉ is-equiv-hᵉ Zᵉ)
```

### Pushouts are uniquely unique

```agda
uniquely-unique-pushoutᵉ :
  { l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level}
  { Sᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ} {Xᵉ : UUᵉ l4ᵉ} {Yᵉ : UUᵉ l5ᵉ}
  ( fᵉ : Sᵉ → Aᵉ) (gᵉ : Sᵉ → Bᵉ) (cᵉ : coconeᵉ fᵉ gᵉ Xᵉ) (dᵉ : coconeᵉ fᵉ gᵉ Yᵉ) →
  universal-property-pushoutᵉ fᵉ gᵉ cᵉ →
  universal-property-pushoutᵉ fᵉ gᵉ dᵉ →
  is-contrᵉ
    ( Σᵉ (Xᵉ ≃ᵉ Yᵉ) (λ eᵉ → htpy-coconeᵉ fᵉ gᵉ (cocone-mapᵉ fᵉ gᵉ cᵉ (map-equivᵉ eᵉ)) dᵉ))
uniquely-unique-pushoutᵉ fᵉ gᵉ cᵉ dᵉ up-cᵉ up-dᵉ =
  is-torsorial-Eq-subtypeᵉ
    ( uniqueness-map-universal-property-pushoutᵉ fᵉ gᵉ cᵉ up-cᵉ dᵉ)
    ( is-property-is-equivᵉ)
    ( map-universal-property-pushoutᵉ fᵉ gᵉ cᵉ up-cᵉ dᵉ)
    ( htpy-cocone-map-universal-property-pushoutᵉ fᵉ gᵉ cᵉ up-cᵉ dᵉ)
    ( is-equiv-up-pushout-up-pushoutᵉ fᵉ gᵉ cᵉ dᵉ
      ( map-universal-property-pushoutᵉ fᵉ gᵉ cᵉ up-cᵉ dᵉ)
      ( htpy-cocone-map-universal-property-pushoutᵉ fᵉ gᵉ cᵉ up-cᵉ dᵉ)
      ( up-cᵉ)
      ( up-dᵉ))
```

### The universal property of pushouts is equivalent to the pullback property of pushouts

Inᵉ orderᵉ to showᵉ thatᵉ theᵉ universalᵉ propertyᵉ ofᵉ pushoutsᵉ isᵉ equivalentᵉ to theᵉ
pullbackᵉ property,ᵉ weᵉ showᵉ thatᵉ theᵉ mapsᵉ `cocone-map`ᵉ andᵉ theᵉ gapᵉ mapᵉ fitᵉ in aᵉ
commutingᵉ triangle,ᵉ where theᵉ thirdᵉ mapᵉ isᵉ anᵉ equivalence.ᵉ Theᵉ claimᵉ thenᵉ
followsᵉ fromᵉ theᵉ 3-for-2ᵉ propertyᵉ ofᵉ equivalences.ᵉ

```agda
triangle-pullback-property-pushout-universal-property-pushoutᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Sᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ}
  {Bᵉ : UUᵉ l3ᵉ} (fᵉ : Sᵉ → Aᵉ) (gᵉ : Sᵉ → Bᵉ) {Xᵉ : UUᵉ l4ᵉ} (cᵉ : coconeᵉ fᵉ gᵉ Xᵉ) →
  {lᵉ : Level} (Yᵉ : UUᵉ lᵉ) →
  cocone-mapᵉ fᵉ gᵉ cᵉ ~ᵉ
  ( totᵉ (λ i'ᵉ → totᵉ (λ j'ᵉ → htpy-eqᵉ)) ∘ᵉ
    gapᵉ (_∘ᵉ fᵉ) (_∘ᵉ gᵉ) (cone-pullback-property-pushoutᵉ fᵉ gᵉ cᵉ Yᵉ))
triangle-pullback-property-pushout-universal-property-pushoutᵉ fᵉ gᵉ cᵉ Yᵉ hᵉ =
    eq-pair-eq-fiberᵉ
      ( eq-pair-eq-fiberᵉ
        ( invᵉ (is-section-eq-htpyᵉ (hᵉ ·lᵉ coherence-square-coconeᵉ fᵉ gᵉ cᵉ))))

pullback-property-pushout-universal-property-pushoutᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Sᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ}
  {Bᵉ : UUᵉ l3ᵉ} (fᵉ : Sᵉ → Aᵉ) (gᵉ : Sᵉ → Bᵉ) {Xᵉ : UUᵉ l4ᵉ} (cᵉ : coconeᵉ fᵉ gᵉ Xᵉ) →
  universal-property-pushoutᵉ fᵉ gᵉ cᵉ → pullback-property-pushoutᵉ fᵉ gᵉ cᵉ
pullback-property-pushout-universal-property-pushoutᵉ fᵉ gᵉ cᵉ up-cᵉ Yᵉ =
  is-equiv-top-map-triangleᵉ
    ( cocone-mapᵉ fᵉ gᵉ cᵉ)
    ( totᵉ (λ i'ᵉ → totᵉ (λ j'ᵉ → htpy-eqᵉ)))
    ( gapᵉ (_∘ᵉ fᵉ) (_∘ᵉ gᵉ) (cone-pullback-property-pushoutᵉ fᵉ gᵉ cᵉ Yᵉ))
    ( triangle-pullback-property-pushout-universal-property-pushoutᵉ fᵉ gᵉ cᵉ Yᵉ)
    ( is-equiv-tot-is-fiberwise-equivᵉ
      ( λ i'ᵉ →
        is-equiv-tot-is-fiberwise-equivᵉ (λ j'ᵉ → funextᵉ (i'ᵉ ∘ᵉ fᵉ) (j'ᵉ ∘ᵉ gᵉ))))
    ( up-cᵉ Yᵉ)

universal-property-pushout-pullback-property-pushoutᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Sᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ}
  {Bᵉ : UUᵉ l3ᵉ} (fᵉ : Sᵉ → Aᵉ) (gᵉ : Sᵉ → Bᵉ) {Xᵉ : UUᵉ l4ᵉ} (cᵉ : coconeᵉ fᵉ gᵉ Xᵉ) →
  pullback-property-pushoutᵉ fᵉ gᵉ cᵉ → universal-property-pushoutᵉ fᵉ gᵉ cᵉ
universal-property-pushout-pullback-property-pushoutᵉ fᵉ gᵉ cᵉ pb-cᵉ Yᵉ =
  is-equiv-left-map-triangleᵉ
    ( cocone-mapᵉ fᵉ gᵉ cᵉ)
    ( totᵉ (λ i'ᵉ → totᵉ (λ j'ᵉ → htpy-eqᵉ)))
    ( gapᵉ (_∘ᵉ fᵉ) (_∘ᵉ gᵉ) (cone-pullback-property-pushoutᵉ fᵉ gᵉ cᵉ Yᵉ))
    ( triangle-pullback-property-pushout-universal-property-pushoutᵉ fᵉ gᵉ cᵉ Yᵉ)
    ( pb-cᵉ Yᵉ)
    ( is-equiv-tot-is-fiberwise-equivᵉ
      ( λ i'ᵉ →
        is-equiv-tot-is-fiberwise-equivᵉ (λ j'ᵉ → funextᵉ (i'ᵉ ∘ᵉ fᵉ) (j'ᵉ ∘ᵉ gᵉ))))
```

### If the vertical map of a span is an equivalence, then the vertical map of a cocone on it is an equivalence if and only if the cocone is a pushout

```agda
is-equiv-universal-property-pushoutᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Sᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ} {Cᵉ : UUᵉ l4ᵉ}
  (fᵉ : Sᵉ → Aᵉ) (gᵉ : Sᵉ → Bᵉ) (cᵉ : coconeᵉ fᵉ gᵉ Cᵉ) →
  is-equivᵉ fᵉ →
  universal-property-pushoutᵉ fᵉ gᵉ cᵉ →
  is-equivᵉ (vertical-map-coconeᵉ fᵉ gᵉ cᵉ)
is-equiv-universal-property-pushoutᵉ fᵉ gᵉ (iᵉ ,ᵉ jᵉ ,ᵉ Hᵉ) is-equiv-fᵉ up-cᵉ =
  is-equiv-is-equiv-precompᵉ jᵉ
    ( λ Tᵉ →
      is-equiv-horizontal-map-is-pullbackᵉ
        ( _∘ᵉ fᵉ)
        ( _∘ᵉ gᵉ)
        ( cone-pullback-property-pushoutᵉ fᵉ gᵉ (iᵉ ,ᵉ jᵉ ,ᵉ Hᵉ) Tᵉ)
        ( is-equiv-precomp-is-equivᵉ fᵉ is-equiv-fᵉ Tᵉ)
        ( pullback-property-pushout-universal-property-pushoutᵉ fᵉ gᵉ
          ( iᵉ ,ᵉ jᵉ ,ᵉ Hᵉ)
          ( up-cᵉ)
          ( Tᵉ)))

equiv-universal-property-pushoutᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Sᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ} {Cᵉ : UUᵉ l4ᵉ}
  (eᵉ : Sᵉ ≃ᵉ Aᵉ) (gᵉ : Sᵉ → Bᵉ) (cᵉ : coconeᵉ (map-equivᵉ eᵉ) gᵉ Cᵉ) →
  universal-property-pushoutᵉ (map-equivᵉ eᵉ) gᵉ cᵉ →
  Bᵉ ≃ᵉ Cᵉ
pr1ᵉ (equiv-universal-property-pushoutᵉ eᵉ gᵉ cᵉ up-cᵉ) =
  vertical-map-coconeᵉ (map-equivᵉ eᵉ) gᵉ cᵉ
pr2ᵉ (equiv-universal-property-pushoutᵉ eᵉ gᵉ cᵉ up-cᵉ) =
  is-equiv-universal-property-pushoutᵉ
    ( map-equivᵉ eᵉ)
    ( gᵉ)
    ( cᵉ)
    ( is-equiv-map-equivᵉ eᵉ)
    ( up-cᵉ)

universal-property-pushout-is-equivᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Sᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ} {Cᵉ : UUᵉ l4ᵉ}
  (fᵉ : Sᵉ → Aᵉ) (gᵉ : Sᵉ → Bᵉ) (cᵉ : coconeᵉ fᵉ gᵉ Cᵉ) →
  is-equivᵉ fᵉ → is-equivᵉ (vertical-map-coconeᵉ fᵉ gᵉ cᵉ) →
  universal-property-pushoutᵉ fᵉ gᵉ cᵉ
universal-property-pushout-is-equivᵉ
  fᵉ gᵉ (iᵉ ,ᵉ jᵉ ,ᵉ Hᵉ) is-equiv-fᵉ is-equiv-jᵉ {lᵉ} =
  let cᵉ = (iᵉ ,ᵉ jᵉ ,ᵉ Hᵉ) in
  universal-property-pushout-pullback-property-pushoutᵉ fᵉ gᵉ cᵉ
    ( λ Tᵉ →
      is-pullback-is-equiv-horizontal-mapsᵉ
        ( _∘ᵉ fᵉ)
        ( _∘ᵉ gᵉ)
        ( cone-pullback-property-pushoutᵉ fᵉ gᵉ cᵉ Tᵉ)
        ( is-equiv-precomp-is-equivᵉ fᵉ is-equiv-fᵉ Tᵉ)
        ( is-equiv-precomp-is-equivᵉ jᵉ is-equiv-jᵉ Tᵉ))
```

### If the horizontal map of a span is an equivalence, then the horizontal map of a cocone on it is an equivalence if and only if the cocone is a pushout

```agda
is-equiv-universal-property-pushout'ᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Sᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ} {Cᵉ : UUᵉ l4ᵉ}
  (fᵉ : Sᵉ → Aᵉ) (gᵉ : Sᵉ → Bᵉ) (cᵉ : coconeᵉ fᵉ gᵉ Cᵉ) →
  is-equivᵉ gᵉ →
  universal-property-pushoutᵉ fᵉ gᵉ cᵉ →
  is-equivᵉ (horizontal-map-coconeᵉ fᵉ gᵉ cᵉ)
is-equiv-universal-property-pushout'ᵉ fᵉ gᵉ cᵉ is-equiv-gᵉ up-cᵉ =
  is-equiv-is-equiv-precompᵉ
    ( horizontal-map-coconeᵉ fᵉ gᵉ cᵉ)
    ( λ Tᵉ →
      is-equiv-vertical-map-is-pullbackᵉ
        ( precompᵉ fᵉ Tᵉ)
        ( precompᵉ gᵉ Tᵉ)
        ( cone-pullback-property-pushoutᵉ fᵉ gᵉ cᵉ Tᵉ)
        ( is-equiv-precomp-is-equivᵉ gᵉ is-equiv-gᵉ Tᵉ)
        ( pullback-property-pushout-universal-property-pushoutᵉ fᵉ gᵉ cᵉ up-cᵉ Tᵉ))

equiv-universal-property-pushout'ᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Sᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ} {Cᵉ : UUᵉ l4ᵉ}
  (fᵉ : Sᵉ → Aᵉ) (eᵉ : Sᵉ ≃ᵉ Bᵉ) (cᵉ : coconeᵉ fᵉ (map-equivᵉ eᵉ) Cᵉ) →
  universal-property-pushoutᵉ fᵉ (map-equivᵉ eᵉ) cᵉ →
  Aᵉ ≃ᵉ Cᵉ
pr1ᵉ (equiv-universal-property-pushout'ᵉ fᵉ eᵉ cᵉ up-cᵉ) = pr1ᵉ cᵉ
pr2ᵉ (equiv-universal-property-pushout'ᵉ fᵉ eᵉ cᵉ up-cᵉ) =
  is-equiv-universal-property-pushout'ᵉ
    ( fᵉ)
    ( map-equivᵉ eᵉ)
    ( cᵉ)
    ( is-equiv-map-equivᵉ eᵉ)
    ( up-cᵉ)

universal-property-pushout-is-equiv'ᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Sᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ} {Cᵉ : UUᵉ l4ᵉ}
  (fᵉ : Sᵉ → Aᵉ) (gᵉ : Sᵉ → Bᵉ) (cᵉ : coconeᵉ fᵉ gᵉ Cᵉ) →
  is-equivᵉ gᵉ → is-equivᵉ (pr1ᵉ cᵉ) →
  universal-property-pushoutᵉ fᵉ gᵉ cᵉ
universal-property-pushout-is-equiv'ᵉ fᵉ gᵉ (iᵉ ,ᵉ jᵉ ,ᵉ Hᵉ) is-equiv-gᵉ is-equiv-iᵉ {lᵉ} =
  let cᵉ = (iᵉ ,ᵉ jᵉ ,ᵉ Hᵉ) in
  universal-property-pushout-pullback-property-pushoutᵉ fᵉ gᵉ cᵉ
    ( λ Tᵉ →
      is-pullback-is-equiv-vertical-mapsᵉ
        ( precompᵉ fᵉ Tᵉ)
        ( precompᵉ gᵉ Tᵉ)
        ( cone-pullback-property-pushoutᵉ fᵉ gᵉ cᵉ Tᵉ)
        ( is-equiv-precomp-is-equivᵉ gᵉ is-equiv-gᵉ Tᵉ)
        ( is-equiv-precomp-is-equivᵉ iᵉ is-equiv-iᵉ Tᵉ))
```

### The pushout pasting lemmas

#### The horizontal pushout pasting lemma

Ifᵉ in theᵉ followingᵉ diagramᵉ theᵉ leftᵉ squareᵉ isᵉ aᵉ pushout,ᵉ thenᵉ theᵉ outerᵉ
rectangleᵉ isᵉ aᵉ pushoutᵉ ifᵉ andᵉ onlyᵉ ifᵉ theᵉ rightᵉ squareᵉ isᵉ aᵉ pushout.ᵉ

```text
       gᵉ       kᵉ
    Aᵉ ---->ᵉ Bᵉ ---->ᵉ Cᵉ
    |       |       |
  fᵉ |       |       |
    ∨ᵉ       ∨ᵉ       ∨ᵉ
    Xᵉ ---->ᵉ Yᵉ ---->ᵉ Zᵉ
```

```agda
module _
  { l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level}
  { Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} {Xᵉ : UUᵉ l4ᵉ} {Yᵉ : UUᵉ l5ᵉ} {Zᵉ : UUᵉ l6ᵉ}
  ( fᵉ : Aᵉ → Xᵉ) (gᵉ : Aᵉ → Bᵉ) (kᵉ : Bᵉ → Cᵉ)
  ( cᵉ : coconeᵉ fᵉ gᵉ Yᵉ) (dᵉ : coconeᵉ (vertical-map-coconeᵉ fᵉ gᵉ cᵉ) kᵉ Zᵉ)
  ( up-cᵉ : universal-property-pushoutᵉ fᵉ gᵉ cᵉ)
  where

  universal-property-pushout-rectangle-universal-property-pushout-rightᵉ :
    universal-property-pushoutᵉ (vertical-map-coconeᵉ fᵉ gᵉ cᵉ) kᵉ dᵉ →
    universal-property-pushoutᵉ fᵉ (kᵉ ∘ᵉ gᵉ) (cocone-comp-horizontalᵉ fᵉ gᵉ kᵉ cᵉ dᵉ)
  universal-property-pushout-rectangle-universal-property-pushout-rightᵉ
    ( up-dᵉ)
    { lᵉ} =
    universal-property-pushout-pullback-property-pushoutᵉ fᵉ
      ( kᵉ ∘ᵉ gᵉ)
      ( cocone-comp-horizontalᵉ fᵉ gᵉ kᵉ cᵉ dᵉ)
      ( λ Wᵉ →
        trᵉ
          ( is-pullbackᵉ (precompᵉ fᵉ Wᵉ) (precompᵉ (kᵉ ∘ᵉ gᵉ) Wᵉ))
          ( invᵉ
            ( eq-htpy-coneᵉ
              ( precompᵉ fᵉ Wᵉ)
              ( precompᵉ (kᵉ ∘ᵉ gᵉ) Wᵉ)
              ( cone-pullback-property-pushoutᵉ
                ( fᵉ)
                ( kᵉ ∘ᵉ gᵉ)
                ( cocone-comp-horizontalᵉ fᵉ gᵉ kᵉ cᵉ dᵉ)
                ( Wᵉ))
              ( pasting-vertical-coneᵉ
                ( precompᵉ fᵉ Wᵉ)
                ( precompᵉ gᵉ Wᵉ)
                ( precompᵉ kᵉ Wᵉ)
                ( cone-pullback-property-pushoutᵉ fᵉ gᵉ cᵉ Wᵉ)
                ( cone-pullback-property-pushoutᵉ
                  ( vertical-map-coconeᵉ fᵉ gᵉ cᵉ)
                  ( kᵉ)
                  ( dᵉ)
                  ( Wᵉ)))
              ( refl-htpyᵉ ,ᵉ
                refl-htpyᵉ ,ᵉ
                ( right-unit-htpyᵉ) ∙hᵉ
                ( distributive-precomp-pasting-horizontal-coherence-square-mapsᵉ
                  ( Wᵉ)
                  ( gᵉ)
                  ( kᵉ)
                  ( fᵉ)
                  ( vertical-map-coconeᵉ fᵉ gᵉ cᵉ)
                  ( vertical-map-coconeᵉ (vertical-map-coconeᵉ fᵉ gᵉ cᵉ) kᵉ dᵉ)
                  ( horizontal-map-coconeᵉ fᵉ gᵉ cᵉ)
                  ( horizontal-map-coconeᵉ (vertical-map-coconeᵉ fᵉ gᵉ cᵉ) kᵉ dᵉ)
                  ( coherence-square-coconeᵉ fᵉ gᵉ cᵉ)
                  ( coherence-square-coconeᵉ (vertical-map-coconeᵉ fᵉ gᵉ cᵉ) kᵉ dᵉ)))))
          ( is-pullback-rectangle-is-pullback-top-squareᵉ
            ( precompᵉ fᵉ Wᵉ)
            ( precompᵉ gᵉ Wᵉ)
            ( precompᵉ kᵉ Wᵉ)
            ( cone-pullback-property-pushoutᵉ fᵉ gᵉ cᵉ Wᵉ)
            ( cone-pullback-property-pushoutᵉ (vertical-map-coconeᵉ fᵉ gᵉ cᵉ) kᵉ dᵉ Wᵉ)
            ( pullback-property-pushout-universal-property-pushoutᵉ fᵉ gᵉ cᵉ
              ( up-cᵉ)
              ( Wᵉ))
            ( pullback-property-pushout-universal-property-pushoutᵉ
              ( vertical-map-coconeᵉ fᵉ gᵉ cᵉ)
              ( kᵉ)
              ( dᵉ)
              ( up-dᵉ)
              ( Wᵉ))))

  universal-property-pushout-right-universal-property-pushout-rectangleᵉ :
    universal-property-pushoutᵉ fᵉ (kᵉ ∘ᵉ gᵉ) (cocone-comp-horizontalᵉ fᵉ gᵉ kᵉ cᵉ dᵉ) →
    universal-property-pushoutᵉ (vertical-map-coconeᵉ fᵉ gᵉ cᵉ) kᵉ dᵉ
  universal-property-pushout-right-universal-property-pushout-rectangleᵉ
    ( up-rᵉ)
    { lᵉ} =
    universal-property-pushout-pullback-property-pushoutᵉ
      ( vertical-map-coconeᵉ fᵉ gᵉ cᵉ)
      ( kᵉ)
      ( dᵉ)
      ( λ Wᵉ →
        is-pullback-top-square-is-pullback-rectangleᵉ
          ( precompᵉ fᵉ Wᵉ)
          ( precompᵉ gᵉ Wᵉ)
          ( precompᵉ kᵉ Wᵉ)
          ( cone-pullback-property-pushoutᵉ fᵉ gᵉ cᵉ Wᵉ)
          ( cone-pullback-property-pushoutᵉ (vertical-map-coconeᵉ fᵉ gᵉ cᵉ) kᵉ dᵉ Wᵉ)
          ( pullback-property-pushout-universal-property-pushoutᵉ fᵉ gᵉ cᵉ
            ( up-cᵉ)
            ( Wᵉ))
          ( trᵉ
            ( is-pullbackᵉ (precompᵉ fᵉ Wᵉ) (precompᵉ (kᵉ ∘ᵉ gᵉ) Wᵉ))
            ( eq-htpy-coneᵉ
              ( precompᵉ fᵉ Wᵉ)
              ( precompᵉ (kᵉ ∘ᵉ gᵉ) Wᵉ)
              ( cone-pullback-property-pushoutᵉ fᵉ
                ( kᵉ ∘ᵉ gᵉ)
                ( cocone-comp-horizontalᵉ fᵉ gᵉ kᵉ cᵉ dᵉ)
                ( Wᵉ))
              ( pasting-vertical-coneᵉ
                ( precompᵉ fᵉ Wᵉ)
                ( precompᵉ gᵉ Wᵉ)
                ( precompᵉ kᵉ Wᵉ)
                ( cone-pullback-property-pushoutᵉ fᵉ gᵉ cᵉ Wᵉ)
                ( cone-pullback-property-pushoutᵉ
                  ( vertical-map-coconeᵉ fᵉ gᵉ cᵉ)
                  ( kᵉ)
                  ( dᵉ)
                  ( Wᵉ)))
              ( refl-htpyᵉ ,ᵉ
                refl-htpyᵉ ,ᵉ
                ( right-unit-htpyᵉ) ∙hᵉ
                ( distributive-precomp-pasting-horizontal-coherence-square-mapsᵉ
                  ( Wᵉ)
                  ( gᵉ)
                  ( kᵉ)
                  ( fᵉ)
                  ( vertical-map-coconeᵉ fᵉ gᵉ cᵉ)
                  ( vertical-map-coconeᵉ (vertical-map-coconeᵉ fᵉ gᵉ cᵉ) kᵉ dᵉ)
                  ( horizontal-map-coconeᵉ fᵉ gᵉ cᵉ)
                  ( horizontal-map-coconeᵉ (vertical-map-coconeᵉ fᵉ gᵉ cᵉ) kᵉ dᵉ)
                  ( coherence-square-coconeᵉ fᵉ gᵉ cᵉ)
                  ( coherence-square-coconeᵉ (vertical-map-coconeᵉ fᵉ gᵉ cᵉ) kᵉ dᵉ))))
            ( pullback-property-pushout-universal-property-pushoutᵉ fᵉ
              ( kᵉ ∘ᵉ gᵉ)
              ( cocone-comp-horizontalᵉ fᵉ gᵉ kᵉ cᵉ dᵉ)
              ( up-rᵉ)
              ( Wᵉ))))
```

#### Extending pushouts by equivalences on the left

Asᵉ aᵉ specialᵉ caseᵉ ofᵉ theᵉ horizontalᵉ pushoutᵉ pastingᵉ lemmaᵉ weᵉ canᵉ extendᵉ aᵉ
pushoutᵉ squareᵉ byᵉ equivalencesᵉ onᵉ theᵉ left.ᵉ

Ifᵉ weᵉ haveᵉ aᵉ pushoutᵉ squareᵉ onᵉ theᵉ right,ᵉ equivalencesᵉ S'ᵉ ≃ᵉ Sᵉ andᵉ A'ᵉ ≃ᵉ A,ᵉ andᵉ aᵉ
mapᵉ f'ᵉ : S'ᵉ → A'ᵉ makingᵉ theᵉ leftᵉ squareᵉ commute,ᵉ thenᵉ theᵉ outerᵉ rectangleᵉ isᵉ
againᵉ aᵉ pushout.ᵉ

```text
         iᵉ       gᵉ
     S'ᵉ --->ᵉ Sᵉ ---->ᵉ Bᵉ
     |   ≃ᵉ   |       |
  f'ᵉ |       | fᵉ     |
     ∨ᵉ   ≃ᵉ   ∨ᵉ     ⌜ᵉ ∨ᵉ
     A'ᵉ --->ᵉ Aᵉ ---->ᵉ Xᵉ
         jᵉ
```

```agda
module _
  { l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level}
  { Sᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ} {Xᵉ : UUᵉ l4ᵉ} {S'ᵉ : UUᵉ l5ᵉ} {A'ᵉ : UUᵉ l6ᵉ}
  ( fᵉ : Sᵉ → Aᵉ) (gᵉ : Sᵉ → Bᵉ) (iᵉ : S'ᵉ → Sᵉ) (jᵉ : A'ᵉ → Aᵉ) (f'ᵉ : S'ᵉ → A'ᵉ)
  ( cᵉ : coconeᵉ fᵉ gᵉ Xᵉ)
  ( up-cᵉ : universal-property-pushoutᵉ fᵉ gᵉ cᵉ)
  ( cohᵉ : coherence-square-mapsᵉ iᵉ f'ᵉ fᵉ jᵉ)
  where

  universal-property-pushout-left-extended-by-equivalencesᵉ :
    is-equivᵉ iᵉ → is-equivᵉ jᵉ →
    universal-property-pushoutᵉ
      ( f'ᵉ)
      ( gᵉ ∘ᵉ iᵉ)
      ( cocone-comp-horizontal'ᵉ f'ᵉ iᵉ gᵉ fᵉ jᵉ cᵉ cohᵉ)
  universal-property-pushout-left-extended-by-equivalencesᵉ ieᵉ jeᵉ =
    universal-property-pushout-rectangle-universal-property-pushout-rightᵉ f'ᵉ iᵉ gᵉ
      ( jᵉ ,ᵉ fᵉ ,ᵉ cohᵉ)
      ( cᵉ)
      ( universal-property-pushout-is-equiv'ᵉ f'ᵉ iᵉ (jᵉ ,ᵉ fᵉ ,ᵉ cohᵉ) ieᵉ jeᵉ)
      ( up-cᵉ)

  universal-property-pushout-left-extension-by-equivalencesᵉ :
    {lᵉ : Level} → is-equivᵉ iᵉ → is-equivᵉ jᵉ →
    Σᵉ (coconeᵉ f'ᵉ (gᵉ ∘ᵉ iᵉ) Xᵉ) (universal-property-pushout-Levelᵉ lᵉ f'ᵉ (gᵉ ∘ᵉ iᵉ))
  pr1ᵉ (universal-property-pushout-left-extension-by-equivalencesᵉ ieᵉ jeᵉ) =
    cocone-comp-horizontal'ᵉ f'ᵉ iᵉ gᵉ fᵉ jᵉ cᵉ cohᵉ
  pr2ᵉ (universal-property-pushout-left-extension-by-equivalencesᵉ ieᵉ jeᵉ) =
    universal-property-pushout-left-extended-by-equivalencesᵉ ieᵉ jeᵉ
```

#### The vertical pushout pasting lemma

Ifᵉ in theᵉ followingᵉ diagramᵉ theᵉ topᵉ squareᵉ isᵉ aᵉ pushout,ᵉ thenᵉ theᵉ outerᵉ
rectangleᵉ isᵉ aᵉ pushoutᵉ ifᵉ andᵉ onlyᵉ ifᵉ theᵉ bottomᵉ squareᵉ isᵉ aᵉ pushout.ᵉ

```text
        gᵉ
    Aᵉ ----->ᵉ Xᵉ
    |        |
  fᵉ |        |
    ∨ᵉ      ⌜ᵉ ∨ᵉ
    Bᵉ ----->ᵉ Yᵉ
    |        |
  kᵉ |        |
    ∨ᵉ        ∨ᵉ
    Cᵉ ----->ᵉ Zᵉ
```

```agda
module _
  { l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level}
  { Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} {Xᵉ : UUᵉ l4ᵉ} {Yᵉ : UUᵉ l5ᵉ} {Zᵉ : UUᵉ l6ᵉ}
  ( fᵉ : Aᵉ → Bᵉ) (gᵉ : Aᵉ → Xᵉ) (kᵉ : Bᵉ → Cᵉ)
  ( cᵉ : coconeᵉ fᵉ gᵉ Yᵉ) (dᵉ : coconeᵉ kᵉ (horizontal-map-coconeᵉ fᵉ gᵉ cᵉ) Zᵉ)
  ( up-cᵉ : universal-property-pushoutᵉ fᵉ gᵉ cᵉ)
  where

  universal-property-pushout-rectangle-universal-property-pushout-topᵉ :
    universal-property-pushoutᵉ kᵉ (horizontal-map-coconeᵉ fᵉ gᵉ cᵉ) dᵉ →
    universal-property-pushoutᵉ (kᵉ ∘ᵉ fᵉ) gᵉ (cocone-comp-verticalᵉ fᵉ gᵉ kᵉ cᵉ dᵉ)
  universal-property-pushout-rectangle-universal-property-pushout-topᵉ up-dᵉ =
    universal-property-pushout-pullback-property-pushoutᵉ
      ( kᵉ ∘ᵉ fᵉ)
      ( gᵉ)
      ( cocone-comp-verticalᵉ fᵉ gᵉ kᵉ cᵉ dᵉ)
      ( λ Wᵉ →
        trᵉ
          ( is-pullbackᵉ (precompᵉ (kᵉ ∘ᵉ fᵉ) Wᵉ) (precompᵉ gᵉ Wᵉ))
          ( invᵉ
            ( eq-htpy-coneᵉ
              ( precompᵉ (kᵉ ∘ᵉ fᵉ) Wᵉ)
              ( precompᵉ gᵉ Wᵉ)
              ( cone-pullback-property-pushoutᵉ
                ( kᵉ ∘ᵉ fᵉ)
                ( gᵉ)
                ( cocone-comp-verticalᵉ fᵉ gᵉ kᵉ cᵉ dᵉ)
                ( Wᵉ))
              ( pasting-horizontal-coneᵉ
                ( precompᵉ kᵉ Wᵉ)
                ( precompᵉ fᵉ Wᵉ)
                ( precompᵉ gᵉ Wᵉ)
                ( cone-pullback-property-pushoutᵉ fᵉ gᵉ cᵉ Wᵉ)
                ( cone-pullback-property-pushoutᵉ kᵉ
                  ( horizontal-map-coconeᵉ fᵉ gᵉ cᵉ)
                  ( dᵉ)
                  ( Wᵉ)))
              ( refl-htpyᵉ ,ᵉ
                refl-htpyᵉ ,ᵉ
                ( right-unit-htpyᵉ) ∙hᵉ
                ( distributive-precomp-pasting-vertical-coherence-square-mapsᵉ Wᵉ
                  ( gᵉ)
                  ( fᵉ)
                  ( vertical-map-coconeᵉ fᵉ gᵉ cᵉ)
                  ( horizontal-map-coconeᵉ fᵉ gᵉ cᵉ)
                  ( kᵉ)
                  ( vertical-map-coconeᵉ kᵉ (horizontal-map-coconeᵉ fᵉ gᵉ cᵉ) dᵉ)
                  ( horizontal-map-coconeᵉ kᵉ (horizontal-map-coconeᵉ fᵉ gᵉ cᵉ) dᵉ)
                  ( coherence-square-coconeᵉ fᵉ gᵉ cᵉ)
                  ( coherence-square-coconeᵉ kᵉ
                    ( horizontal-map-coconeᵉ fᵉ gᵉ cᵉ)
                    ( dᵉ))))))
          ( is-pullback-rectangle-is-pullback-left-squareᵉ
            ( precompᵉ kᵉ Wᵉ)
            ( precompᵉ fᵉ Wᵉ)
            ( precompᵉ gᵉ Wᵉ)
            ( cone-pullback-property-pushoutᵉ fᵉ gᵉ cᵉ Wᵉ)
            ( cone-pullback-property-pushoutᵉ kᵉ
              ( horizontal-map-coconeᵉ fᵉ gᵉ cᵉ)
              ( dᵉ)
              ( Wᵉ))
            ( pullback-property-pushout-universal-property-pushoutᵉ fᵉ gᵉ cᵉ
              ( up-cᵉ)
              ( Wᵉ))
            ( pullback-property-pushout-universal-property-pushoutᵉ kᵉ
              ( horizontal-map-coconeᵉ fᵉ gᵉ cᵉ)
              ( dᵉ)
              ( up-dᵉ)
              ( Wᵉ))))

  universal-property-pushout-top-universal-property-pushout-rectangleᵉ :
    universal-property-pushoutᵉ (kᵉ ∘ᵉ fᵉ) gᵉ (cocone-comp-verticalᵉ fᵉ gᵉ kᵉ cᵉ dᵉ) →
    universal-property-pushoutᵉ kᵉ (horizontal-map-coconeᵉ fᵉ gᵉ cᵉ) dᵉ
  universal-property-pushout-top-universal-property-pushout-rectangleᵉ up-rᵉ =
    universal-property-pushout-pullback-property-pushoutᵉ kᵉ
      ( horizontal-map-coconeᵉ fᵉ gᵉ cᵉ)
      ( dᵉ)
      ( λ Wᵉ →
        is-pullback-left-square-is-pullback-rectangleᵉ
          ( precompᵉ kᵉ Wᵉ)
          ( precompᵉ fᵉ Wᵉ)
          ( precompᵉ gᵉ Wᵉ)
          ( cone-pullback-property-pushoutᵉ fᵉ gᵉ cᵉ Wᵉ)
          ( cone-pullback-property-pushoutᵉ kᵉ (horizontal-map-coconeᵉ fᵉ gᵉ cᵉ) dᵉ Wᵉ)
          ( pullback-property-pushout-universal-property-pushoutᵉ fᵉ gᵉ cᵉ up-cᵉ Wᵉ)
          ( trᵉ
            ( is-pullbackᵉ (precompᵉ (kᵉ ∘ᵉ fᵉ) Wᵉ) (precompᵉ gᵉ Wᵉ))
            ( eq-htpy-coneᵉ
              ( precompᵉ (kᵉ ∘ᵉ fᵉ) Wᵉ)
              ( precompᵉ gᵉ Wᵉ)
              ( cone-pullback-property-pushoutᵉ
                ( kᵉ ∘ᵉ fᵉ)
                ( gᵉ)
                ( cocone-comp-verticalᵉ fᵉ gᵉ kᵉ cᵉ dᵉ)
                ( Wᵉ))
              ( pasting-horizontal-coneᵉ
                ( precompᵉ kᵉ Wᵉ)
                ( precompᵉ fᵉ Wᵉ)
                ( precompᵉ gᵉ Wᵉ)
                ( cone-pullback-property-pushoutᵉ fᵉ gᵉ cᵉ Wᵉ)
                ( cone-pullback-property-pushoutᵉ kᵉ
                  ( horizontal-map-coconeᵉ fᵉ gᵉ cᵉ)
                  ( dᵉ)
                  ( Wᵉ)))
              ( refl-htpyᵉ ,ᵉ
                refl-htpyᵉ ,ᵉ
                ( right-unit-htpyᵉ) ∙hᵉ
                ( distributive-precomp-pasting-vertical-coherence-square-mapsᵉ Wᵉ
                  ( gᵉ)
                  ( fᵉ)
                  ( vertical-map-coconeᵉ fᵉ gᵉ cᵉ)
                  ( horizontal-map-coconeᵉ fᵉ gᵉ cᵉ)
                  ( kᵉ)
                  ( vertical-map-coconeᵉ kᵉ
                    ( horizontal-map-coconeᵉ fᵉ gᵉ cᵉ)
                    ( dᵉ))
                  ( horizontal-map-coconeᵉ kᵉ
                    ( horizontal-map-coconeᵉ fᵉ gᵉ cᵉ)
                    ( dᵉ))
                  ( coherence-square-coconeᵉ fᵉ gᵉ cᵉ)
                  ( coherence-square-coconeᵉ kᵉ
                    ( horizontal-map-coconeᵉ fᵉ gᵉ cᵉ)
                    ( dᵉ)))))
            ( pullback-property-pushout-universal-property-pushoutᵉ (kᵉ ∘ᵉ fᵉ) gᵉ
              ( cocone-comp-verticalᵉ fᵉ gᵉ kᵉ cᵉ dᵉ)
              ( up-rᵉ)
              ( Wᵉ))))
```

#### Extending pushouts by equivalences at the top

Ifᵉ weᵉ haveᵉ aᵉ pushoutᵉ squareᵉ onᵉ theᵉ right,ᵉ equivalencesᵉ `S'ᵉ ≃ᵉ S`ᵉ andᵉ `B'ᵉ ≃ᵉ B`,ᵉ
andᵉ aᵉ mapᵉ `g'ᵉ : S'ᵉ → B'`ᵉ makingᵉ theᵉ topᵉ squareᵉ commute,ᵉ thenᵉ theᵉ verticalᵉ
rectangleᵉ isᵉ againᵉ aᵉ pushout.ᵉ Thisᵉ isᵉ aᵉ specialᵉ caseᵉ ofᵉ theᵉ verticalᵉ pushoutᵉ
pastingᵉ lemma.ᵉ

```text
          g'ᵉ
      S'ᵉ --->ᵉ B'ᵉ
      |       |
    iᵉ | ≃ᵉ   ≃ᵉ | jᵉ
      ∨ᵉ   gᵉ   ∨ᵉ
      Sᵉ ---->ᵉ Bᵉ
      |       |
    fᵉ |       |
      ∨ᵉ     ⌜ᵉ ∨ᵉ
      Aᵉ ---->ᵉ Xᵉ
```

```agda
module _
  { l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level}
  { Sᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ} {Xᵉ : UUᵉ l4ᵉ} {S'ᵉ : UUᵉ l5ᵉ} {B'ᵉ : UUᵉ l6ᵉ}
  ( fᵉ : Sᵉ → Aᵉ) (gᵉ : Sᵉ → Bᵉ) (iᵉ : S'ᵉ → Sᵉ) (jᵉ : B'ᵉ → Bᵉ) (g'ᵉ : S'ᵉ → B'ᵉ)
  ( cᵉ : coconeᵉ fᵉ gᵉ Xᵉ)
  ( up-cᵉ : universal-property-pushoutᵉ fᵉ gᵉ cᵉ)
  ( cohᵉ : coherence-square-mapsᵉ g'ᵉ iᵉ jᵉ gᵉ)
  where

  universal-property-pushout-top-extended-by-equivalencesᵉ :
    is-equivᵉ iᵉ → is-equivᵉ jᵉ →
    universal-property-pushoutᵉ
      ( fᵉ ∘ᵉ iᵉ)
      ( g'ᵉ)
      ( cocone-comp-vertical'ᵉ iᵉ g'ᵉ jᵉ gᵉ fᵉ cᵉ cohᵉ)
  universal-property-pushout-top-extended-by-equivalencesᵉ ieᵉ jeᵉ =
    universal-property-pushout-rectangle-universal-property-pushout-topᵉ iᵉ g'ᵉ fᵉ
      ( gᵉ ,ᵉ jᵉ ,ᵉ cohᵉ)
      ( cᵉ)
      ( universal-property-pushout-is-equivᵉ iᵉ g'ᵉ (gᵉ ,ᵉ jᵉ ,ᵉ cohᵉ) ieᵉ jeᵉ)
      ( up-cᵉ)

  universal-property-pushout-top-extension-by-equivalencesᵉ :
    {lᵉ : Level} → is-equivᵉ iᵉ → is-equivᵉ jᵉ →
    Σᵉ (coconeᵉ (fᵉ ∘ᵉ iᵉ) g'ᵉ Xᵉ) (universal-property-pushout-Levelᵉ lᵉ (fᵉ ∘ᵉ iᵉ) g'ᵉ)
  pr1ᵉ (universal-property-pushout-top-extension-by-equivalencesᵉ ieᵉ jeᵉ) =
    cocone-comp-vertical'ᵉ iᵉ g'ᵉ jᵉ gᵉ fᵉ cᵉ cohᵉ
  pr2ᵉ (universal-property-pushout-top-extension-by-equivalencesᵉ ieᵉ jeᵉ) =
    universal-property-pushout-top-extended-by-equivalencesᵉ ieᵉ jeᵉ
```

### Extending pushouts by equivalences of cocones

Givenᵉ aᵉ commutativeᵉ diagramᵉ where `i`,ᵉ `j`ᵉ andᵉ `k`ᵉ areᵉ equivalences,ᵉ

```text
           g'ᵉ
       S'ᵉ --->ᵉ B'ᵉ
      /ᵉ \ᵉ       \ᵉ
  f'ᵉ /ᵉ   \ᵉ kᵉ     \ᵉ jᵉ
    /ᵉ     ∨ᵉ   gᵉ   ∨ᵉ
   A'ᵉ     Sᵉ ---->ᵉ Bᵉ
     \ᵉ    |       |
    iᵉ \ᵉ   | fᵉ     |
       \ᵉ  ∨ᵉ     ⌜ᵉ ∨ᵉ
        >ᵉ Aᵉ ---->ᵉ Xᵉ
```

theᵉ inducedᵉ squareᵉ isᵉ aᵉ pushoutᵉ:

```text
  S'ᵉ --->ᵉ B'ᵉ
  |       |
  |       |
  ∨ᵉ     ⌜ᵉ ∨ᵉ
  A'ᵉ --->ᵉ X.ᵉ
```

Thisᵉ combinesᵉ bothᵉ specialᵉ casesᵉ ofᵉ theᵉ pushoutᵉ pastingᵉ lemmasᵉ forᵉ equivalences.ᵉ

Noticeᵉ thatᵉ theᵉ tripleᵉ `(i,j,k)`ᵉ isᵉ reallyᵉ anᵉ equivalenceᵉ ofᵉ spans.ᵉ Thus,ᵉ thisᵉ
resultᵉ canᵉ beᵉ phrasedᵉ asᵉ: theᵉ pushoutᵉ isᵉ invariantᵉ underᵉ equivalenceᵉ ofᵉ spans.ᵉ

```agda
module _
  { l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ l7ᵉ : Level}
  { Sᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ} {Xᵉ : UUᵉ l4ᵉ}
  { S'ᵉ : UUᵉ l5ᵉ} {A'ᵉ : UUᵉ l6ᵉ} {B'ᵉ : UUᵉ l7ᵉ}
  ( fᵉ : Sᵉ → Aᵉ) (gᵉ : Sᵉ → Bᵉ) (f'ᵉ : S'ᵉ → A'ᵉ) (g'ᵉ : S'ᵉ → B'ᵉ)
  ( iᵉ : A'ᵉ → Aᵉ) (jᵉ : B'ᵉ → Bᵉ) (kᵉ : S'ᵉ → Sᵉ)
  ( cᵉ : coconeᵉ fᵉ gᵉ Xᵉ)
  ( up-cᵉ : universal-property-pushoutᵉ fᵉ gᵉ cᵉ)
  ( coh-lᵉ : coherence-square-mapsᵉ kᵉ f'ᵉ fᵉ iᵉ)
  ( coh-rᵉ : coherence-square-mapsᵉ g'ᵉ kᵉ jᵉ gᵉ)
  where

  universal-property-pushout-extension-by-equivalencesᵉ :
    {lᵉ : Level} → is-equivᵉ iᵉ → is-equivᵉ jᵉ → is-equivᵉ kᵉ →
    Σᵉ (coconeᵉ f'ᵉ g'ᵉ Xᵉ) (universal-property-pushout-Levelᵉ lᵉ f'ᵉ g'ᵉ)
  universal-property-pushout-extension-by-equivalencesᵉ ieᵉ jeᵉ keᵉ =
    universal-property-pushout-top-extension-by-equivalencesᵉ
      ( f'ᵉ)
      ( gᵉ ∘ᵉ kᵉ)
      ( idᵉ)
      ( jᵉ)
      ( g'ᵉ)
      ( cocone-comp-horizontal'ᵉ f'ᵉ kᵉ gᵉ fᵉ iᵉ cᵉ coh-lᵉ)
      ( universal-property-pushout-left-extended-by-equivalencesᵉ fᵉ gᵉ kᵉ iᵉ
        ( f'ᵉ)
        ( cᵉ)
        ( up-cᵉ)
        ( coh-lᵉ)
        ( keᵉ)
        ( ieᵉ))
      ( coh-rᵉ)
      ( is-equiv-idᵉ)
      ( jeᵉ)

  universal-property-pushout-extended-by-equivalencesᵉ :
    is-equivᵉ iᵉ → is-equivᵉ jᵉ → is-equivᵉ kᵉ →
    universal-property-pushoutᵉ
      ( f'ᵉ)
      ( g'ᵉ)
      ( comp-cocone-hom-spanᵉ fᵉ gᵉ f'ᵉ g'ᵉ iᵉ jᵉ kᵉ cᵉ coh-lᵉ coh-rᵉ)
  universal-property-pushout-extended-by-equivalencesᵉ ieᵉ jeᵉ keᵉ =
    pr2ᵉ (universal-property-pushout-extension-by-equivalencesᵉ ieᵉ jeᵉ keᵉ)
```

### In a commuting cube where the vertical maps are equivalences, the bottom square is a pushout if and only if the top square is a pushout

```agda
module _
  { l1ᵉ l2ᵉ l3ᵉ l4ᵉ l1'ᵉ l2'ᵉ l3'ᵉ l4'ᵉ : Level}
  { Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} {Dᵉ : UUᵉ l4ᵉ}
  ( fᵉ : Aᵉ → Bᵉ) (gᵉ : Aᵉ → Cᵉ) (hᵉ : Bᵉ → Dᵉ) (kᵉ : Cᵉ → Dᵉ)
  { A'ᵉ : UUᵉ l1'ᵉ} {B'ᵉ : UUᵉ l2'ᵉ} {C'ᵉ : UUᵉ l3'ᵉ} {D'ᵉ : UUᵉ l4'ᵉ}
  ( f'ᵉ : A'ᵉ → B'ᵉ) (g'ᵉ : A'ᵉ → C'ᵉ) (h'ᵉ : B'ᵉ → D'ᵉ) (k'ᵉ : C'ᵉ → D'ᵉ)
  ( hAᵉ : A'ᵉ → Aᵉ) (hBᵉ : B'ᵉ → Bᵉ) (hCᵉ : C'ᵉ → Cᵉ) (hDᵉ : D'ᵉ → Dᵉ)
  ( topᵉ : coherence-square-mapsᵉ g'ᵉ f'ᵉ k'ᵉ h'ᵉ)
  ( back-leftᵉ : coherence-square-mapsᵉ f'ᵉ hAᵉ hBᵉ fᵉ)
  ( back-rightᵉ : coherence-square-mapsᵉ g'ᵉ hAᵉ hCᵉ gᵉ)
  ( front-leftᵉ : coherence-square-mapsᵉ h'ᵉ hBᵉ hDᵉ hᵉ)
  ( front-rightᵉ : coherence-square-mapsᵉ k'ᵉ hCᵉ hDᵉ kᵉ)
  ( bottomᵉ : coherence-square-mapsᵉ gᵉ fᵉ kᵉ hᵉ)
  ( cᵉ :
    coherence-cube-mapsᵉ fᵉ gᵉ hᵉ kᵉ f'ᵉ g'ᵉ h'ᵉ k'ᵉ hAᵉ hBᵉ hCᵉ hDᵉ
      ( topᵉ)
      ( back-leftᵉ)
      ( back-rightᵉ)
      ( front-leftᵉ)
      ( front-rightᵉ)
      ( bottomᵉ))
  ( is-equiv-hAᵉ : is-equivᵉ hAᵉ) (is-equiv-hBᵉ : is-equivᵉ hBᵉ)
  ( is-equiv-hCᵉ : is-equivᵉ hCᵉ) (is-equiv-hDᵉ : is-equivᵉ hDᵉ)
  where

  universal-property-pushout-top-universal-property-pushout-bottom-cube-is-equivᵉ :
    universal-property-pushoutᵉ fᵉ gᵉ (hᵉ ,ᵉ kᵉ ,ᵉ bottomᵉ) →
    universal-property-pushoutᵉ f'ᵉ g'ᵉ (h'ᵉ ,ᵉ k'ᵉ ,ᵉ topᵉ)
  universal-property-pushout-top-universal-property-pushout-bottom-cube-is-equivᵉ
    ( up-bottomᵉ)
    { lᵉ = lᵉ} =
    universal-property-pushout-pullback-property-pushoutᵉ f'ᵉ g'ᵉ
      ( h'ᵉ ,ᵉ k'ᵉ ,ᵉ topᵉ)
      ( λ Wᵉ →
        is-pullback-bottom-is-pullback-top-cube-is-equivᵉ
          ( precompᵉ h'ᵉ Wᵉ)
          ( precompᵉ k'ᵉ Wᵉ)
          ( precompᵉ f'ᵉ Wᵉ)
          ( precompᵉ g'ᵉ Wᵉ)
          ( precompᵉ hᵉ Wᵉ)
          ( precompᵉ kᵉ Wᵉ)
          ( precompᵉ fᵉ Wᵉ)
          ( precompᵉ gᵉ Wᵉ)
          ( precompᵉ hDᵉ Wᵉ)
          ( precompᵉ hBᵉ Wᵉ)
          ( precompᵉ hCᵉ Wᵉ)
          ( precompᵉ hAᵉ Wᵉ)
          ( precomp-coherence-square-mapsᵉ gᵉ fᵉ kᵉ hᵉ bottomᵉ Wᵉ)
          ( precomp-coherence-square-mapsᵉ hBᵉ h'ᵉ hᵉ hDᵉ (inv-htpyᵉ front-leftᵉ) Wᵉ)
          ( precomp-coherence-square-mapsᵉ hCᵉ k'ᵉ kᵉ hDᵉ (inv-htpyᵉ front-rightᵉ) Wᵉ)
          ( precomp-coherence-square-mapsᵉ hAᵉ f'ᵉ fᵉ hBᵉ (inv-htpyᵉ back-leftᵉ) Wᵉ)
          ( precomp-coherence-square-mapsᵉ hAᵉ g'ᵉ gᵉ hCᵉ (inv-htpyᵉ back-rightᵉ) Wᵉ)
          ( precomp-coherence-square-mapsᵉ g'ᵉ f'ᵉ k'ᵉ h'ᵉ topᵉ Wᵉ)
          ( precomp-coherence-cube-mapsᵉ fᵉ gᵉ hᵉ kᵉ f'ᵉ g'ᵉ h'ᵉ k'ᵉ hAᵉ hBᵉ hCᵉ hDᵉ
            ( topᵉ)
            ( back-leftᵉ)
            ( back-rightᵉ)
            ( front-leftᵉ)
            ( front-rightᵉ)
            ( bottomᵉ)
            ( cᵉ)
            ( Wᵉ))
          ( is-equiv-precomp-is-equivᵉ hDᵉ is-equiv-hDᵉ Wᵉ)
          ( is-equiv-precomp-is-equivᵉ hBᵉ is-equiv-hBᵉ Wᵉ)
          ( is-equiv-precomp-is-equivᵉ hCᵉ is-equiv-hCᵉ Wᵉ)
          ( is-equiv-precomp-is-equivᵉ hAᵉ is-equiv-hAᵉ Wᵉ)
          ( pullback-property-pushout-universal-property-pushoutᵉ fᵉ gᵉ
            ( hᵉ ,ᵉ kᵉ ,ᵉ bottomᵉ)
            ( up-bottomᵉ)
            ( Wᵉ)))

  universal-property-pushout-bottom-universal-property-pushout-top-cube-is-equivᵉ :
    universal-property-pushoutᵉ f'ᵉ g'ᵉ (h'ᵉ ,ᵉ k'ᵉ ,ᵉ topᵉ) →
    universal-property-pushoutᵉ fᵉ gᵉ (hᵉ ,ᵉ kᵉ ,ᵉ bottomᵉ)
  universal-property-pushout-bottom-universal-property-pushout-top-cube-is-equivᵉ
    ( up-topᵉ)
    { lᵉ = lᵉ} =
    universal-property-pushout-pullback-property-pushoutᵉ fᵉ gᵉ
      ( hᵉ ,ᵉ kᵉ ,ᵉ bottomᵉ)
      ( λ Wᵉ →
        is-pullback-top-is-pullback-bottom-cube-is-equivᵉ
          ( precompᵉ h'ᵉ Wᵉ)
          ( precompᵉ k'ᵉ Wᵉ)
          ( precompᵉ f'ᵉ Wᵉ)
          ( precompᵉ g'ᵉ Wᵉ)
          ( precompᵉ hᵉ Wᵉ)
          ( precompᵉ kᵉ Wᵉ)
          ( precompᵉ fᵉ Wᵉ)
          ( precompᵉ gᵉ Wᵉ)
          ( precompᵉ hDᵉ Wᵉ)
          ( precompᵉ hBᵉ Wᵉ)
          ( precompᵉ hCᵉ Wᵉ)
          ( precompᵉ hAᵉ Wᵉ)
          ( precomp-coherence-square-mapsᵉ gᵉ fᵉ kᵉ hᵉ bottomᵉ Wᵉ)
          ( precomp-coherence-square-mapsᵉ hBᵉ h'ᵉ hᵉ hDᵉ (inv-htpyᵉ front-leftᵉ) Wᵉ)
          ( precomp-coherence-square-mapsᵉ hCᵉ k'ᵉ kᵉ hDᵉ (inv-htpyᵉ front-rightᵉ) Wᵉ)
          ( precomp-coherence-square-mapsᵉ hAᵉ f'ᵉ fᵉ hBᵉ (inv-htpyᵉ back-leftᵉ) Wᵉ)
          ( precomp-coherence-square-mapsᵉ hAᵉ g'ᵉ gᵉ hCᵉ (inv-htpyᵉ back-rightᵉ) Wᵉ)
          ( precomp-coherence-square-mapsᵉ g'ᵉ f'ᵉ k'ᵉ h'ᵉ topᵉ Wᵉ)
          ( precomp-coherence-cube-mapsᵉ fᵉ gᵉ hᵉ kᵉ f'ᵉ g'ᵉ h'ᵉ k'ᵉ hAᵉ hBᵉ hCᵉ hDᵉ
            ( topᵉ)
            ( back-leftᵉ)
            ( back-rightᵉ)
            ( front-leftᵉ)
            ( front-rightᵉ)
            ( bottomᵉ)
            ( cᵉ)
            ( Wᵉ))
          ( is-equiv-precomp-is-equivᵉ hDᵉ is-equiv-hDᵉ Wᵉ)
          ( is-equiv-precomp-is-equivᵉ hBᵉ is-equiv-hBᵉ Wᵉ)
          ( is-equiv-precomp-is-equivᵉ hCᵉ is-equiv-hCᵉ Wᵉ)
          ( is-equiv-precomp-is-equivᵉ hAᵉ is-equiv-hAᵉ Wᵉ)
          ( pullback-property-pushout-universal-property-pushoutᵉ f'ᵉ g'ᵉ
            ( h'ᵉ ,ᵉ k'ᵉ ,ᵉ topᵉ)
            ( up-topᵉ)
            ( Wᵉ)))
```